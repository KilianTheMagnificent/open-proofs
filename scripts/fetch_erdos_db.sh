#!/bin/sh
# Fetch the erdosproblems.com status database (teorth/erdosproblems data/problems.yaml) at the
# commit pinned in upstream.json into work/erdos-db/ (gitignored). Used only for triage.
set -eu
cd "$(dirname "$0")/.."
commit=$(python3 -c 'import json;print(json.load(open("upstream.json"))["erdosproblems_db"]["commit"])')
mkdir -p work/erdos-db
curl -sSfL -o work/erdos-db/problems.yaml \
  "https://raw.githubusercontent.com/teorth/erdosproblems/${commit}/data/problems.yaml"
echo "fetched teorth/erdosproblems@${commit} -> work/erdos-db/problems.yaml"
