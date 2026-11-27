#!/usr/bin/env bash
exec bash "/home/lazyinspirit/Projects/workflow-engines/tools/lean-workflow/compile-with-slot.sh" "/run/user/1000/leanworkflow-0aa9ed909906d606.compile.lock" "/home/lazyinspirit/.elan/toolchains/leanprover--lean4---v4.36.0-rc2/bin/lean" -j1 "$@"
