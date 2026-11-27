#!/usr/bin/env bash
set -uo pipefail
project='/home/lazyinspirit/Projects/mackey-bimodule-diagrams-lean'
workflow='/home/lazyinspirit/Projects/workflow-engines'

while systemctl --user is-active --quiet mackey-diagram-lean-plan.service; do
  sleep 10
done

cd "$workflow" || exit
fixed_boundary_worker="$project/.lake/lean-workflow-supervision/fixed-boundary-worker"
if [[ -z ${CODEX_BIN:-} && -x "$fixed_boundary_worker" ]]; then
  export CODEX_BIN="$fixed_boundary_worker"
fi
bash tools/lean-workflow/run-bounded.sh "$project"
status=$?

cd "$project" || exit
python3 readme-appendix.py || exit
exit "$status"
