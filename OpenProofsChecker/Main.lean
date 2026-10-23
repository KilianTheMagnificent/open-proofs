/-
`opcheck`: the Lean half of the open-proofs checker.

It loads compiled `.olean` files at run time and inspects them. It never imports a
result module at compile time, and it never runs code from the modules it inspects
(no `initialize` blocks, no environment-extension import hooks, no pretty-printer
extensions).

Checks for one claim (`--theorem T` in `--module M`, compared with `--ref-theorem R`
in `--ref-module RM`):

* `ref_trusted`      the reference declaration is a theorem in the named reference module,
                     which comes from the pinned upstream package (`--ref-kind upstream`)
                     or from this repository's `OpenProofs.Statements.*` (`--ref-kind variant`).
* `theorem_found`    the claimed declaration is a theorem defined in `M`, and `M` is
                     candidate code (compiled from this repository, not a dependency).
* `statement_match`  the claimed theorem's type is the same `Expr` as the reference type
                     (up to binder names and binder annotations, after aligning universe
                     parameters) -- "syntactic" identity -- or, failing that, the kernel
                     accepts `theorem _ : <reference type> := <claimed theorem>` --
                     "kernel-defeq" identity (e.g. a different but defeq instance path).
* `statement_consts` every constant in the reference statement comes from a trusted module
                     (core, Mathlib, upstream), never from candidate code.
* `axioms`           the axioms reachable from the claimed theorem, found by walking every
                     constant body, are a subset of `propext`, `Classical.choice`,
                     `Quot.sound`. The walk does not trust any precomputed axiom data.
* `candidate_decls`  every declaration in candidate modules of the import closure lives
                     under `OpenProofs.`, shadows no trusted name (a theorem may mirror a
                     trusted theorem's name; nothing may mirror a definition), and is not an axiom,
                     `opaque`, `unsafe`, `partial`, `implemented_by`, `extern`, `export`
                     or `init` declaration. (`csimp` only affects compiled code, so it can
                     only matter through native evaluation, which the axiom check rejects;
                     the source lint also bans it.)
* `closure_clean`    the result does not import `OpenProofs.Statements.*` or the checker.
* `kernel_replay`    every candidate module in the closure is re-checked by the kernel
                     against its imports (like `leanchecker`), which catches environment
                     hacking such as `debug.skipKernelTC` or `addDeclWithoutChecking`.

Output: one JSON object on stdout. Exit code 0 iff the verdict is PASS.
-/
import Lean
import Lean.Replay
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr
import Lean.Compiler.ExportAttr
import Lean.Compiler.InitAttr

open Lean

namespace OpenProofsChecker

/-- The only axioms a result may depend on. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

structure CheckResult where
  name : String
  ok : Bool
  detail : String := ""
deriving ToJson

structure Args where
  module : Name := .anonymous
  thm : Name := .anonymous
  refModule : Name := .anonymous
  refThm : Name := .anonymous
  refKind : String := "upstream"
  noReplay : Bool := false

/-- Parse a dotted Lean name, honouring `«...»` escapes (`FormalConjectures.ErdosProblems.«1»`). -/
def parseName (s : String) : Name := Id.run do
  let mut parts : Array String := #[]
  let mut cur : String := ""
  let mut inEsc := false
  for c in s.toList do
    if inEsc then
      if c == '»' then inEsc := false else cur := cur.push c
    else if c == '«' then inEsc := true
    else if c == '.' then
      parts := parts.push cur
      cur := ""
    else cur := cur.push c
  parts := parts.push cur
  return parts.foldl (fun n p => Name.mkStr n p) Name.anonymous

partial def parseArgs : List String → Args → Except String Args
  | [], a => .ok a
  | "--module" :: v :: rest, a => parseArgs rest { a with module := parseName v }
  | "--theorem" :: v :: rest, a => parseArgs rest { a with thm := parseName v }
  | "--ref-module" :: v :: rest, a => parseArgs rest { a with refModule := parseName v }
  | "--ref-theorem" :: v :: rest, a => parseArgs rest { a with refThm := parseName v }
  | "--ref-kind" :: v :: rest, a => parseArgs rest { a with refKind := v }
  | "--no-replay" :: rest, a => parseArgs rest { a with noReplay := true }
  | x :: _, _ => .error s!"unknown or incomplete argument: {x}"

/-- Where a module's `.olean` lives decides whether it is trusted dependency code
or candidate code compiled from this repository. -/
inductive Origin where
  | core        -- Lean toolchain (Init, Std, Lean, Lake)
  | package (name : String) -- `.lake/packages/<name>/...`
  | candidate   -- `.lake/build/...` of this repository
  | unknown (path : String)
deriving Inhabited, BEq

def Origin.toString : Origin → String
  | .core => "core"
  | .package n => s!"package:{n}"
  | .candidate => "candidate"
  | .unknown p => s!"unknown:{p}"

def originOf (root sysroot : System.FilePath) (mod : Name) : IO Origin := do
  let path ← findOLean mod
  let p ← IO.FS.realPath path
  let ps := p.toString
  let sys := (← IO.FS.realPath sysroot).toString
  let pkgs := (← IO.FS.realPath (root / ".lake" / "packages")).toString ++ "/"
  let build := (← IO.FS.realPath (root / ".lake" / "build")).toString ++ "/"
  if ps.startsWith (sys ++ "/") then return .core
  if ps.startsWith pkgs then
    let rest := (ps.drop pkgs.length).toString
    let name := (rest.splitOn "/").headD ""
    return .package name
  if ps.startsWith build then return .candidate
  return .unknown ps

/-- All modules in the import closure of `mod` (including `mod`), using module data. -/
partial def importClosure (env : Environment) (mod : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[mod]
  while h : todo.size > 0 do
    let m := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains m then continue
    seen := seen.insert m
    if let some idx := env.getModuleIdx? m then
      if let some data := env.header.moduleData[idx.toNat]? then
        for i in data.imports do
          unless seen.contains i.module do todo := todo.push i.module
  return seen

/-- Walk constant bodies to collect every axiom reachable from `c`.
Does not consult any precomputed axiom data stored in `.olean` files. -/
partial def walkAxioms (env : Environment) (c : Name) : StateM (NameSet × NameSet) Unit := do
  let (seen, _) ← get
  if seen.contains c then return
  modify fun (s, a) => (s.insert c, a)
  let visit (e : Expr) : StateM (NameSet × NameSet) Unit := do
    for n in e.getUsedConstants do walkAxioms env n
  match env.find? c with
  | some (.axiomInfo v) =>
    modify fun (s, a) => (s, a.insert c)
    visit v.type
  | some (.defnInfo v) => visit v.type; visit v.value
  | some (.thmInfo v) => visit v.type; visit v.value
  | some (.opaqueInfo v) => visit v.type; visit v.value
  | some (.quotInfo v) => visit v.type
  | some (.ctorInfo v) => visit v.type
  | some (.recInfo v) => visit v.type
  | some (.inductInfo v) =>
    visit v.type
    for ctor in v.ctors do walkAxioms env ctor
  | none =>
    -- A referenced constant that does not exist is itself a failure; record it as an axiom
    -- under a sentinel name so the verdict fails loudly.
    modify fun (s, a) => (s, a.insert (`__missing_constant__ ++ c))

/-- Replay one module's constants through the kernel on top of its imports
(the same procedure as `leanchecker`'s `replayFromImports`). -/
def replayModule (module : Name) : IO Unit := do
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {module} does not exist"
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push pFile
  let parts ← readModuleDataParts fnames
  if h : parts.size = 0 then throw <| IO.userError "failed to read module data" else
  let (mod, _) := parts[0]
  let (_, s) ← importModulesCore mod.imports |>.run
  let env ← finalizeImport s mod.imports {} 0 false false (isModule := true)
  let mut newConstants := {}
  for name in parts[parts.size-1].1.constNames, ci in parts[parts.size-1].1.constants do
    newConstants := newConstants.insert name ci
  discard <| env.replay newConstants

/-- Strip the private-name prefix, if any. -/
def userName (n : Name) : Name := (privateToUserName? n).getD n

/-- Proper suffixes of a name: `A.B.c` ↦ `[B.c, c]`. -/
def properSuffixes (n : Name) : List Name :=
  let comps := n.components
  (List.range (comps.length - 1)).map fun i =>
    (comps.drop (i + 1)).foldl (fun acc c => acc ++ c) Name.anonymous

/-- Compiler- or elaborator-generated names that are not user declarations. -/
def isGeneratedName (n : Name) : Bool :=
  n.isInternal || n.isInternalDetail ||
  (match n with
   | .str _ s => s.startsWith "eq_" || s == "eq_def" || s == "eq_unfold" ||
                 s.startsWith "match_" || s.startsWith "proof_" || s == "_unsafe_rec" ||
                 s.startsWith "_" || s.startsWith "sizeOf_spec" || s == "injEq" || s == "inj" ||
                 s == "noConfusion" || s == "noConfusionType" || s == "casesOn" || s == "recOn" ||
                 s == "rec" || s == "below" || s == "brecOn" || s == "binductionOn" || s == "ibelow"
   | _ => false)

def jsonOfChecks (args : Args) (checks : Array CheckResult) (axioms : Array Name)
    (candidates : Array Name) (identity : String := "none") : Json :=
  let ok := checks.all (·.ok)
  Json.mkObj [
    ("verdict", Json.str (if ok then "PASS" else "FAIL")),
    ("theorem", Json.str args.thm.toString),
    ("module", Json.str args.module.toString),
    ("ref_theorem", Json.str args.refThm.toString),
    ("ref_module", Json.str args.refModule.toString),
    ("ref_kind", Json.str args.refKind),
    ("lean_version", Json.str Lean.versionString),
    ("statement_identity", Json.str identity),
    ("axioms", toJson (axioms.map (·.toString))),
    ("candidate_modules", toJson (candidates.map (·.toString))),
    ("checks", toJson checks)
  ]

def run (args : Args) : IO UInt32 := do
  let sysroot ← findSysroot
  initSearchPath sysroot
  let root ← IO.currentDir
  let mut checks : Array CheckResult := #[]
  let fail (checks : Array CheckResult) (name detail : String) : IO UInt32 := do
    let checks := checks.push { name, ok := false, detail }
    IO.println (jsonOfChecks args checks #[] #[]).compress
    return 1
  if args.module.isAnonymous || args.thm.isAnonymous || args.refModule.isAnonymous ||
      args.refThm.isAnonymous then
    return ← fail checks "arguments" "need --module, --theorem, --ref-module, --ref-theorem"
  unless args.refKind == "upstream" || args.refKind == "variant" do
    return ← fail checks "arguments" "--ref-kind must be `upstream` or `variant`"
  -- Load the environment: the result module and the reference module, all data, and
  -- no extension import hooks (`loadExts := false`), so no imported code runs.
  let env ← try
      importModules #[{ module := args.module }, { module := args.refModule }] {}
        (trustLevel := 0) (loadExts := false) (level := .private)
    catch e => return ← fail checks "load" s!"failed to import modules: {e}"
  -- Classify every loaded module by origin.
  let mut origins : Std.HashMap Name Origin := {}
  for m in env.header.moduleNames do
    origins := origins.insert m (← originOf root sysroot m)
  let unknown := env.header.moduleNames.filter fun m =>
    match origins[m]? with | some (.unknown _) => true | _ => false
  checks := checks.push {
    name := "module_origins", ok := unknown.isEmpty,
    detail := if unknown.isEmpty then "all modules are core, package or candidate"
      else s!"modules of unknown origin: {unknown.toList}" }
  let isCandidate (m : Name) : Bool := origins[m]? == some .candidate
  let modOf (c : Name) : Option Name :=
    (env.getModuleIdxFor? c).bind fun idx => env.header.moduleNames[idx.toNat]?
  -- Reference declaration.
  let refOrigin := origins[args.refModule]?.getD (.unknown "?")
  let refOriginOk := match args.refKind with
    | "upstream" => refOrigin == .package "formal_conjectures" &&
        (`FormalConjectures).isPrefixOf args.refModule
    | _ => refOrigin == .candidate && (`OpenProofs.Statements).isPrefixOf args.refModule
  let some refCi := env.find? args.refThm
    | return ← fail checks "ref_trusted" s!"reference {args.refThm} not found"
  let refInModule := modOf args.refThm == some args.refModule
  let refIsThm := match refCi with | .thmInfo _ => true | _ => false
  checks := checks.push {
    name := "ref_trusted", ok := refOriginOk && refInModule && refIsThm,
    detail := s!"ref module origin {refOrigin.toString}; declared in ref module: {refInModule}; \
      is theorem: {refIsThm}" }
  -- Claimed theorem.
  let some ci := env.find? args.thm
    | return ← fail checks "theorem_found" s!"theorem {args.thm} not found"
  let inModule := modOf args.thm == some args.module
  let isThm := match ci with | .thmInfo _ => true | _ => false
  let modCandidate := isCandidate args.module
  checks := checks.push {
    name := "theorem_found", ok := inModule && isThm && modCandidate && !ci.isUnsafe,
    detail := s!"declared in module: {inModule}; is theorem: {isThm}; \
      module is candidate code: {modCandidate}; unsafe: {ci.isUnsafe}" }
  -- Statement identity. First try syntactic identity of the elaborated types. If that fails,
  -- ask the kernel to check a bridge declaration `theorem _ : <reference type> := <claimed
  -- theorem>`: if the kernel accepts it, the claimed proof literally proves the reference
  -- statement (the two types are definitionally equal, e.g. they differ only in which
  -- instance path elaboration picked). Anything else is a mismatch.
  let lvlOk := ci.levelParams.length == refCi.levelParams.length
  let refLvls := refCi.levelParams.map Level.param
  let ty := ci.type.instantiateLevelParams ci.levelParams refLvls
  let same := lvlOk && ty == refCi.type
  let strict := lvlOk && Expr.equal ty refCi.type
  let mut identity := if same then "syntactic" else "none"
  let mut bridgeErr := ""
  if lvlOk && !same && isThm then
    let bridge := Declaration.thmDecl
      { name := `_opcheck_statement_bridge, levelParams := refCi.levelParams,
        type := refCi.type, value := mkConst args.thm refLvls }
    match Kernel.Environment.addDecl env.toKernelEnv {} bridge with
    | .ok _ => identity := "kernel-defeq"
    | .error e => bridgeErr := (← (e.toMessageData {}).toString).take 600 |>.toString
  checks := checks.push {
    name := "statement_match", ok := identity != "none",
    detail := if same then
        s!"types are identical Exprs (strict incl. binder names: {strict})"
      else if identity == "kernel-defeq" then
        "types differ syntactically but the kernel accepts the claimed proof at the \
        reference type (definitional equality)"
      else if !lvlOk then "universe parameter counts differ"
      else s!"types differ and the kernel rejects the bridge: {bridgeErr}" }
  -- Constants used by the reference statement must all be trusted.
  let refConsts := refCi.type.getUsedConstants
  let badRefConsts := refConsts.filter fun c =>
    match modOf c with
    | some m => isCandidate m
    | none => true
  checks := checks.push {
    name := "statement_consts", ok := badRefConsts.isEmpty,
    detail := if badRefConsts.isEmpty then s!"{refConsts.size} constants, all from trusted modules"
      else s!"statement uses candidate or unknown constants: {badRefConsts.toList}" }
  -- Axioms, by a full body walk.
  let ((), (_, axs)) := (walkAxioms env args.thm).run ({}, {})
  let axioms := axs.toArray.qsort Name.lt
  let badAx := axioms.filter (!allowedAxioms.contains ·)
  checks := checks.push {
    name := "axioms", ok := badAx.isEmpty,
    detail := if badAx.isEmpty then s!"{axioms.toList}"
      else s!"disallowed axioms: {badAx.toList}" ++
        (if badAx.any (fun a => a == ``sorryAx) then " (sorry)" else "") ++
        (if badAx.any (fun a => a == ``Lean.ofReduceBool || a == ``Lean.trustCompiler ||
            (a.toString.splitOn "_native").length > 1) then " (native evaluation)" else "") }
  -- Candidate modules in the closure of the result module.
  let closure := importClosure env args.module
  let candidates := (closure.toArray.filter isCandidate).qsort Name.lt
  let badImports := candidates.filter fun m =>
    (`OpenProofs.Statements).isPrefixOf m || (`OpenProofsChecker).isPrefixOf m
  checks := checks.push {
    name := "closure_clean", ok := badImports.isEmpty,
    detail := if badImports.isEmpty then s!"candidate modules: {candidates.toList}"
      else s!"result imports forbidden candidate modules: {badImports.toList}" }
  let mut problems : Array String := #[]
  for m in candidates do
    let some idx := env.getModuleIdx? m | continue
    let some data := env.header.moduleData[idx.toNat]? | continue
    for c in data.constNames, cinfo in data.constants do
      let u := userName c
      let kindBad : Option String := match cinfo with
        | .axiomInfo _ => some "axiom"
        | .opaqueInfo _ => some "opaque"
        | .quotInfo _ => some "quot"
        | _ => none
      if let some k := kindBad then problems := problems.push s!"{c}: {k} declaration"
      if cinfo.isUnsafe then problems := problems.push s!"{c}: unsafe"
      if cinfo.isPartial then problems := problems.push s!"{c}: partial"
      if (Compiler.getImplementedBy? env c).isSome then
        problems := problems.push s!"{c}: @[implemented_by]"
      if isExtern env c then problems := problems.push s!"{c}: @[extern]"
      if (getExportNameFor? env c).isSome then problems := problems.push s!"{c}: @[export]"
      if hasInitAttr env c then problems := problems.push s!"{c}: @[init]"
      unless (`OpenProofs).isPrefixOf u do
        problems := problems.push s!"{c}: declared outside the `OpenProofs` namespace"
      -- Shadowing: a candidate declaration whose name ends in the full name of a trusted
      -- declaration would win name resolution inside its namespace. A theorem that mirrors
      -- a trusted theorem's name (e.g. `OpenProofs.Erdos1.erdos_1` for `Erdos1.erdos_1`) is
      -- harmless and allowed; any other shadowing (of or by a definition, instance,
      -- structure, ...) is rejected.
      unless isGeneratedName u do
        let cIsThm := match cinfo with | .thmInfo _ => true | _ => false
        for s in properSuffixes u do
          if let some sm := modOf s then
            unless isCandidate sm do
              let sIsThm := match env.find? s with | some (.thmInfo _) => true | _ => false
              unless cIsThm && sIsThm do
                problems := problems.push s!"{c}: shadows trusted declaration {s} (from {sm})"
  checks := checks.push {
    name := "candidate_decls", ok := problems.isEmpty,
    detail := if problems.isEmpty then "no forbidden declarations"
      else String.intercalate "; " (problems.toList.take 20) }
  -- Kernel replay of every candidate module in the closure.
  if args.noReplay then
    checks := checks.push { name := "kernel_replay", ok := false, detail := "skipped (--no-replay)" }
  else
    let mut replayErrs : Array String := #[]
    for m in candidates do
      try replayModule m
      catch e => replayErrs := replayErrs.push s!"{m}: {e}"
    checks := checks.push {
      name := "kernel_replay", ok := replayErrs.isEmpty,
      detail := if replayErrs.isEmpty then s!"replayed {candidates.size} candidate module(s)"
        else String.intercalate "; " replayErrs.toList }
  let out := jsonOfChecks args checks axioms candidates identity
  IO.println out.compress
  return if checks.all (·.ok) then 0 else 1

end OpenProofsChecker

def main (argv : List String) : IO UInt32 := do
  match OpenProofsChecker.parseArgs argv {} with
  | .error e =>
    IO.eprintln s!"opcheck: {e}"
    IO.eprintln "usage: opcheck --module M --theorem T --ref-module RM --ref-theorem R \
      [--ref-kind upstream|variant] [--no-replay]"
    return 2
  | .ok a => OpenProofsChecker.run a
