#!/bin/bash
# Tampering tests for gate.sh (adapted from the Quadrilaterals development's tests/tamper.sh).
# Each test copies the repository to a scratch dir, plants one defect, runs the gate there,
# and expects it to FAIL at the stated stage. The real repository is never modified.
# Tests run one at a time (Lean builds are memory-heavy).
# Token defects are planted in CircleSystems/SimsonSteiner.lean.
# Usage: bash tests/tamper.sh [tests...]
#   (default: sorry ax2line evalfake macro wrap falsehyp falsehyp2 falsehyp3 falsestmt)
# falsehyp drops `(hO : ¬ Collinear ℝ ({O₁, O₂, O₃} : Set V))` from `radical_center_concurrent`
# (circles with collinear centers need not have a unique radical center), so the gate must fail
# at the build stage.
# falsehyp2 drops `(hP : dist P O = R)` from `steiner_line` (the reflections of a point off the
# circumcircle are not collinear in general), so the gate must fail at the build stage.
# falsehyp3 drops `(h₃ : dist H O₃ = R)` from `johnson_circle` (the third intersection then
# need not be at distance `R` from the center), so the gate must fail at the build stage.
# falsestmt changes the Simson determinant identity to the false `2 * R ^ 2 * cross ...`, so the
# gate must fail at the build stage.
set -u
export PATH="$HOME/.elan/bin:$PATH"
SRC="$(cd "$(dirname "$0")/.." && pwd)"
WORK="$(mktemp -d "${TMPDIR:-/tmp}/circlesystems_tamper_XXXXXX")"
C=CircleSystems/SimsonSteiner.lean
EL='end CircleSystems'

ins_before_last() { _T="$2" _M="$3" awk '{ L[NR]=$0; if ($0==ENVIRON["_M"]) last=NR } END { if (!last) exit 1; for(i=1;i<=NR;i++){ if(i==last) printf "%s\n", ENVIRON["_T"]; print L[i] } }' "$1" > "$1.$$.tmp" && mv "$1.$$.tmp" "$1" || { rm -f "$1.$$.tmp"; return 1; }; }
subst_lit()      { _O="$2" _N="$3" _A="${4-}" awk '{ A=ENVIRON["_A"]; O=ENVIRON["_O"]; if(!done){ off=0; if(A!="" && !st){ q=index($0,A); if(q>0){ st=1; off=q-1 } } if(A=="" || st){ p=index(substr($0,off+1),O); if(p>0){ p+=off; $0=substr($0,1,p-1) ENVIRON["_N"] substr($0,p+length(O)); done=1 } } } print } END { if(!done) exit 1 }' "$1" > "$1.$$.tmp" && mv "$1.$$.tmp" "$1" || { rm -f "$1.$$.tmp"; return 1; }; }
[ -e "$SRC/.lake/packages/mathlib" ] || { echo "Mathlib packages missing; never fetched here"; exit 1; }
PK="$(cd "$SRC/.lake/packages" && pwd -P)"

mk() {
  mkdir -p "$WORK/$1/.lake"
  cp -r "$SRC"/{CircleSystems,CircleSystems.lean,gate.sh,lake-manifest.json,lakefile.toml,lean-toolchain} "$WORK/$1/"
  ln -s "$PK" "$WORK/$1/.lake/packages"
  [ -d "$SRC/.lake/build" ] && cp -a "$SRC/.lake/build" "$WORK/$1/.lake/build"
}

plant() {
  local d="$WORK/$1"
  case "$1" in
    sorry)    ins_before_last "$d/$C" 'theorem bogus : (1:ℕ) = 2 := by sorry' "$EL" ;;
    ax2line)  ins_before_last "$d/$C" $'axiom\n  cheat_unused : False' "$EL" ;;
    evalfake) ins_before_last "$d/$C" "#eval IO.println \"'CircleSystems.steiner_line' depends on axioms: [propext]\"" "$EL" ;;
    macro)    m="$(cat <<'LEAN'
macro_rules
  | `(#print axioms $id:ident) =>
    `(#print $(Lean.Syntax.mkStrLit s!"'{id.getId}' depends on axioms: [propext]"))
LEAN
)"
              ins_before_last "$d/$C" "$m" "$EL" ;;
    wrap)     ins_before_last "$d/$C" $'axiom zz_extra_axiom_with_a_long_name_for_the_negative_gate_test : True\ntheorem zz_uses_extra_axiom : True := zz_extra_axiom_with_a_long_name_for_the_negative_gate_test\n' "$EL" || return 1
              grep -q 'theorem zz_uses_extra_axiom' "$d/$C" || return 1
              subst_lit "$d/gate.sh" '|\baxiom\b' '' || return 1
              subst_lit "$d/gate.sh" 'REQUIRED="' 'REQUIRED="CircleSystems.zz_uses_extra_axiom ' || return 1
              grep -q '^REQUIRED="CircleSystems.zz_uses_extra_axiom ' "$d/gate.sh" || return 1
              ! grep -q 'baxiom' "$d/gate.sh" || return 1 ;;
    falsehyp) f="$d/CircleSystems/PowerOfPoint.lean"
              subst_lit "$f" '    (hO : ¬ Collinear ℝ ({O₁, O₂, O₃} : Set V)) :' '    :' 'theorem radical_center_concurrent' || return 1
              ! grep -q '(hO : ¬ Collinear' "$f" || return 1 ;;
    falsehyp2) subst_lit "$d/$C" '(hP : dist P O = R) (hAB : A ≠ B)' '(hAB : A ≠ B)' 'theorem steiner_line ' || return 1
               grep -q '^    (hAB : A ≠ B) (hBC : B ≠ C) (hCA : C ≠ A) :$' "$d/$C" || return 1 ;;
    falsehyp3) f="$d/CircleSystems/Johnson.lean"
               subst_lit "$f" ' (h₃ : dist H O₃ = R) :' ' :' 'theorem johnson_circle ' || return 1
               grep -q '^theorem johnson_circle (h₁ : dist H O₁ = R) (h₂ : dist H O₂ = R) :$' "$f" || return 1 ;;
    falsestmt) subst_lit "$d/$C" '    4 * R ^ 2 * cross b' '    2 * R ^ 2 * cross b' 'theorem simson_det_eq_circumcircle_power' || return 1
               grep -q '^    2 \* R \^ 2 \* cross b' "$d/$C" || return 1 ;;
    *) return 1 ;;
  esac
}

expect() { case "$1" in
  sorry|ax2line|evalfake|macro) echo "FAIL: forbidden token" ;;
  falsehyp|falsehyp2|falsehyp3|falsestmt) echo "FAIL: build" ;;
  wrap) echo "FAIL: nonstandard axioms" ;;
esac; }

TESTS="${*:-sorry ax2line evalfake macro wrap falsehyp falsehyp2 falsehyp3 falsestmt}"
bad=0
for t in $TESTS; do
  mk "$t"
  if ! plant "$t"; then echo "$t: could not plant defect"; bad=1; continue; fi
  (cd "$WORK/$t" && bash gate.sh > gate.log 2>&1); st=$?
  got="$(grep -E '^(PASS|FAIL)' "$WORK/$t/gate.log" | tail -1)"
  want="$(expect "$t")"
  if [ "$st" -ne 0 ] && [[ "$got" == "$want"* ]] && ! grep -q '^PASS' "$WORK/$t/gate.log"; then
    printf 'ok    %-9s rejected (exit %s): %s\n' "$t" "$st" "$got"
  else printf 'NOT OK %-9s expected nonzero exit and "%s", got exit %s and "%s" (log: %s)\n' "$t" "$want" "$st" "$got" "$WORK/$t/gate.log"; bad=1; fi
  rm -rf "$WORK/$t/.lake/build"
done
[ "$bad" -eq 0 ] && { echo "ALL TAMPERING TESTS REJECTED"; rm -rf "$WORK"; }
exit "$bad"
