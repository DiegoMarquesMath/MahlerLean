#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

# This source-level guard is supplementary. Kernel checking and a statement
# audit remain necessary. Never weaken the script to make a proof pass.
if grep -nE '(^|[[:space:]])(sorry|admit|axiom|opaque|unsafe|native_decide)([[:space:]]|$)' \
    AnalyticGraphs.lean AnalyticGraphs/*.lean; then
  echo 'Unapproved proof escape or declaration in AnalyticGraphs sources.' >&2
  exit 1
fi

lake build AnalyticGraphs

for source_file in AnalyticGraphs/*.lean; do
  lake env lean -DwarningAsError=true "$source_file"
done

audit_log="$(mktemp -t analytic-graphs-audit.XXXXXX)"
trap 'rm -f "$audit_log"' EXIT
lake env lean -DwarningAsError=true scripts/AuditAnalyticGraphs.lean | tee "$audit_log"
if grep -q 'sorryAx' "$audit_log"; then
  echo 'The axiom audit exposed a sorryAx dependency.' >&2
  exit 1
fi
echo 'AnalyticGraphs scaffold and the listed declarations passed the local checks.'
echo 'This does NOT certify the new counting, Cantor or descent theorems.'
