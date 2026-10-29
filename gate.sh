#!/bin/bash
# Gate for the CircleSystems Lean formalisation (power of a point, radical axes and the radical
# center, coaxal pencils, Johnson's three-circle theorem, Simson-Wallace and Steiner lines). Passes only if all of these hold:
#  * the sources contain no `sorry`, `admit`, `native_decide`, `axiom`, `#eval`, `run_cmd`,
#    `initialize`, `IO`, `set_option`, or syntax-extension commands (which could redefine
#    `#print axioms`);
#  * the library builds without errors;
#  * the gate itself generates the `#print axioms` report for each REQUIRED theorem;
#  * each REQUIRED theorem uses only Lean's standard axioms (propext, Classical.choice, Quot.sound).
# SCAFFOLD=1 skips the forbidden-token check and also tolerates `sorryAx`, so a partially
# finished development can be checked while it still contains `sorry`.
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")" || exit 1
NS="CircleSystems"
LIB="CircleSystems"
REQUIRED="CircleSystems.pencilPow CircleSystems.pencilCenter CircleSystems.pencilRadSq CircleSystems.pencilPow_eq_powPt CircleSystems.pencilPow_zero CircleSystems.pencilPow_one CircleSystems.pencilCenter_mem_line CircleSystems.pencilPow_eq_iff CircleSystems.pencil_radicalAxis CircleSystems.pencil_through_common_point CircleSystems.IsOrthogonal CircleSystems.isOrthogonal_iff CircleSystems.powPt_eq_sq_iff_dist CircleSystems.orthogonal_of_center_on_radicalAxis CircleSystems.johnson_mem_circles CircleSystems.johnson_circle CircleSystems.johnson_orthocenter CircleSystems.johnson_orthocenter_eq CircleSystems.johnson_reflection CircleSystems.johnson_congruent CircleSystems.foot_alg_x CircleSystems.foot_alg_y CircleSystems.simson_alg CircleSystems.steiner_alg_AB CircleSystems.steiner_alg_AC CircleSystems.steiner_alg_BC CircleSystems.foot_props CircleSystems.reflection_eq CircleSystems.foot_coord CircleSystems.R_ne_zero CircleSystems.simson_det_eq_circumcircle_power CircleSystems.simson_wallace CircleSystems.steiner_line CircleSystems.steiner_line_orthocenter CircleSystems.cx CircleSystems.cy CircleSystems.cross CircleSystems.exists_basis CircleSystems.cx_add CircleSystems.cy_add CircleSystems.cx_sub CircleSystems.cy_sub CircleSystems.cx_smul CircleSystems.cy_smul CircleSystems.cx_zero' CircleSystems.cy_zero' CircleSystems.cx_b0 CircleSystems.cy_b0 CircleSystems.cx_b1 CircleSystems.cy_b1 CircleSystems.eq_coord CircleSystems.ext_coord CircleSystems.inner_coord CircleSystems.norm_sq_coord CircleSystems.dist_sq_coord CircleSystems.eq_smul_of_cross_eq_zero CircleSystems.collinear_of_forall_smul CircleSystems.collinear_four_of_cross CircleSystems.collinear_iff_cross CircleSystems.powPt CircleSystems.radicalAxis CircleSystems.powPt_eq_inner CircleSystems.powPt_eq_zero_iff CircleSystems.powPt_sub_powPt CircleSystems.radConst CircleSystems.mem_radicalAxis_iff CircleSystems.radicalAxis_eq_inner CircleSystems.radicalAxis_comm CircleSystems.mem_radicalAxis_of_mem_circles CircleSystems.inner_sub_eq_zero_of_mem_radicalAxis CircleSystems.radBase CircleSystems.radBase_mem CircleSystems.radicalAxis_eq_mk' CircleSystems.mem_radicalAxis_trans CircleSystems.powPt_coord CircleSystems.cx_mk CircleSystems.cy_mk CircleSystems.radical_center_concurrent"
SOURCES="$(ls CircleSystems/*.lean) CircleSystems.lean"
[ -e .lake/packages/mathlib ] || { echo "FAIL: Mathlib packages missing (run setup by hand)"; exit 1; }
if [ "${SCAFFOLD:-0}" != "1" ]; then
  if grep -nE "\bsorry\b|\badmit\b|native_decide|\baxiom\b|#eval|\brun_cmd\b|\binitialize\b|\bIO\b|\bdebug\.|\bmacro|\belab|\bsyntax\b|\bnotation\b|\binfix|\bprefix\b|\bpostfix\b|import Lean|open Lean|\bset_option\b" $SOURCES; then
    echo "FAIL: forbidden token"; exit 1; fi
fi
build=$(lake build $LIB 2>&1); bstatus=$?
printf '%s\n' "$build" | tail -3
[ "$bstatus" -eq 0 ] || { printf '%s\n' "$build"; echo "FAIL: build"; exit 1; }
root=$(lake env lean "$LIB.lean" 2>&1) || { printf '%s\n' "$root"; echo "FAIL: build (root file)"; exit 1; }
chk=".gatecheck_$$.lean"
trap 'rm -f "$chk"' EXIT
{ echo "import $LIB"; for t in $REQUIRED; do echo "#print axioms $t"; done; } > "$chk"
out=$(lake env lean "$chk" 2>&1); status=$?
printf '%s\n' "$out"
[ "$status" -eq 0 ] || { echo "FAIL: axiom report"; exit 1; }
echo "$out" | grep -qE "(^|:)[[:space:]]*error" && { echo "FAIL: Lean reported an error"; exit 1; }
flat=$(printf '%s\n' "$out" | awk '/^'"'"'/{if(buf!="")print buf; buf=$0; next} {buf=buf" "$0} END{if(buf!="")print buf}')
reports=$(printf '%s\n' "$flat" | grep -E "depends on axioms|does not depend on any axioms")
n=0
for t in $REQUIRED; do
  te=$(printf '%s' "$t" | sed 's/[.]/\\./g')
  c=$(printf '%s\n' "$reports" | grep -cE "^'$te' (depends on axioms|does not depend)")
  [ "$c" -eq 1 ] || { echo "FAIL: expected one axiom report for $t, found $c"; exit 1; }
  n=$((n+1))
done
[ "$(printf '%s\n' "$reports" | grep -c .)" -eq "$n" ] || { echo "FAIL: unexpected extra reports"; exit 1; }
printf '%s\n' "$reports" | grep "depends on axioms" | grep -qv '\]' && { echo "FAIL: unterminated axiom list"; exit 1; }
if [ "${SCAFFOLD:-0}" = "1" ]; then ALLOW='^(propext|Classical\.choice|Quot\.sound|sorryAx)$'; else ALLOW='^(propext|Classical\.choice|Quot\.sound)$'; fi
bad=$(printf '%s\n' "$reports" | grep "depends on axioms" | sed 's/.*depends on axioms: *\[//; s/\].*//' \
      | tr ',' '\n' | sed 's/^ *//; s/ *$//' | grep -v '^$' | sort -u | grep -vE "$ALLOW")
[ -n "$bad" ] && { echo "FAIL: nonstandard axioms: $bad"; exit 1; }
echo "PASS ($n declarations, standard axioms only)"
