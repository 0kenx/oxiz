#!/usr/bin/env bash
# Delta-debug reducer for a single .smt2 discrepancy file.
# Reduces to a minimal set of assertions that still reproduces a
# z3/oxiz sat-vs-unsat disagreement. Operates at the (assert ...) granularity.
#
# Usage: ./reduce.sh <file.smt2> [oxiz] [z3]
set -uo pipefail

f="$1"; OXIZ="${2:-./target/release/oxiz}"; Z3="${3:-z3}"

# Strip the leading `; DISCREPANCY`/`; z3=`/`; oxiz=`/`; grammar-fuzzer` header lines.
sed -n '
  /^; DISCREPANCY/d
  /^; z3=/d
  /^; z3-out=/d
  /^; grammar-fuzzer/d
  p
' "$f" > /tmp/reduce_in.smt2

verdict() {
  local prog="$1"; local script="$2"
  local out
  out=$(printf '%s' "$script" | "$prog" --quiet 2>/dev/null || true)
  [ "$prog" = "$Z3" ] && out=$(printf '%s' "$script" | "$Z3" -in 2>/dev/null || true)
  out=$(printf '%s' "$out" | head -1)
  case "$out" in
    sat) echo sat;;
    unsat) echo unsat;;
    *) echo other;;
  esac
}

disagrees() {
  local script="$1"
  local z o
  z=$(verdict "$Z3"   "$script")
  o=$(verdict "$OXIZ" "$script")
  [ "$z" != "$o" ] && [ "$z" != "other" ] && [ "$o" != "other" ]
}

full=$(cat /tmp/reduce_in.smt2)
if ! disagrees "$full"; then
  echo "ERROR: input does not reproduce a sat/unsat disagreement" >&2
  exit 1
fi

# Collect assert lines + the scaffolding (set-logic, declares, check-sat, exit).
mapfile -t asserts < <(grep '^(assert ' /tmp/reduce_in.smt2)
# Preamble = everything that is neither an assert nor the trailing check-sat/exit.
preamble=$(grep -v '^(assert ' /tmp/reduce_in.smt2 | grep -v '^(check-sat)' | grep -v '^(exit)')

# Granularity reduction: try dropping each assert.
changed=1
cur=("${asserts[@]}")
while [ "$changed" = 1 ]; do
  changed=0
  for i in "${!cur[@]}"; do
    tmp=("${cur[@]}")
    unset 'tmp[i]'
    [ ${#tmp[@]} -eq 0 ] && continue
    script=$(printf '%s\n%s\n(check-sat)\n(exit)\n' "$preamble" "$(printf '%s\n' "${tmp[@]}")")
    if disagrees "$script"; then
      cur=("${tmp[@]}")
      changed=1
    fi
  done
done

minimal=$(printf '%s\n%s\n(check-sat)\n(exit)\n' "$preamble" "$(printf '%s\n' "${cur[@]}")")
echo "# reduced: ${#cur[@]} assertion(s) (from ${#asserts[@]})"
echo "# z3=$(verdict "$Z3" "$minimal")  oxiz=$(verdict "$OXIZ" "$minimal")"
echo "$minimal"
