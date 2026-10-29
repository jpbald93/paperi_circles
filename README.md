# CircleSystems — systems of circles in Lean 4 / Mathlib

Lean v4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` (`.lake/packages` is a symlink to
`~/paperi_quad/.lake/packages`). Points are vectors of a real inner product space `V`; plane results
assume `Fact (finrank ℝ V = 2)` and are proved in orthonormal coordinates (`CircleSystems/Coord.lean`).

| File | Main results |
|---|---|
| `PowerOfPoint.lean` | `powPt P O R = dist P O ^ 2 - R ^ 2`; `radicalAxis_eq_inner` (level set of `⟪·, O₁ − O₂⟫`), `radicalAxis_eq_mk'` (affine hyperplane with direction `(ℝ ∙ (O₁ − O₂))ᗮ`), `radical_center_concurrent` (Monge: non-collinear centers ⇒ `∃!` common point of the three radical axes) |
| `Coaxal.lean` | pencil `pencilPow t = (1−t)·pow₁ + t·pow₂` is a circle (`pencilPow_eq_powPt`), centers on line `O₁O₂`, `pencil_radicalAxis` (common radical axis), `isOrthogonal_iff` (orthogonal ⇔ `powPt O₁ O₂ R₂ = R₁²`) |
| `Johnson.lean` | `johnson_circle` (A, B, C on the circle of radius R about `O₁+O₂+O₃−2H`), `johnson_orthocenter`, `johnson_orthocenter_eq` (Mathlib `orthocenter = H`, `circumcenter = J`), `johnson_reflection`, `johnson_congruent` (Mathlib `Congruent`) |
| `SimsonSteiner.lean` | `simson_det_eq_circumcircle_power` (`4R²·(E−D)×(F−D) = −(B−A)×(C−A)·powPt P O R`, feet = Mathlib `orthogonalProjection`), `simson_wallace` (iff), `steiner_line`, `steiner_line_orthocenter` (Mathlib `reflection`, `orthocenter`) |

`bash gate.sh`: no sorry/axiom/etc., build, `#print axioms` for 78 declarations (standard axioms only).
`bash tests/tamper.sh`: 9 planted defects, all must be rejected.
