#!/usr/bin/env bash
set -euo pipefail

cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"

nice -n 10 lake --wfail build
nice -n 10 lake env lean scripts/PrintAxioms.lean > .lake/main-axioms.log
nice -n 10 lake env lean scripts/Audit.lean > .lake/axiom-audit.tsv
nice -n 10 lake env lean scripts/PrintStatements.lean > .lake/statement-types.log
nice -n 10 lake env leanchecker --verbose LeanestEllipse > .lake/kernel-modules.log 2>&1
nice -n 10 lake env leanchecker --fresh --verbose LeanestEllipse > .lake/kernel-fresh.log 2>&1
tail -n 1 .lake/axiom-audit.tsv
