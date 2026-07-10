#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG="$(mktemp)"; trap 'rm -f "$LOG"' EXIT

# rg wrapper that fails CLOSED: exit 0 (match found) => gate fails;
# exit 1 (no match) => gate passes; exit >1 (rg error) => gate fails.
forbid() {
  local rc=0
  rg "$@" && rc=0 || rc=$?
  case "$rc" in
    0) echo "FORBIDDEN PATTERN FOUND (above)"; return 1 ;;
    1) return 0 ;;
    *) echo "rg failed with exit $rc (scan error)"; return 1 ;;
  esac
}

echo "== Gate 1: build =="
lake build 2>&1 | tee "$LOG"

# Scan only paths that exist (fail-closed rg errors on missing paths; the library
# directory appears in Phase 1). Missing REQUIRED paths still fail via the root file.
lib_paths=(RegularityLemmata.lean)
[ -d RegularityLemmata ] && lib_paths+=(RegularityLemmata)

echo "== Gate 2: no sorry/admit/axiom in library source =="
forbid -n --glob '*.lean' -e '\bsorry\b' -e '\badmit\b' -e '^\s*axiom\b' \
    "${lib_paths[@]}"

echo "== Gate 3: no sorry warnings in the build log =="
forbid "declaration uses 'sorry'" "$LOG"

echo "== Gate 4: axiom audit (every declaration in the library namespace) =="
lake exe axiom_audit

echo "== check.sh: all gates passed =="
