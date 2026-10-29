import CircleSystems.PowerOfPoint

/-!
# Simson–Wallace line and Steiner line

Points are vectors of a real inner product plane `V`; `b` is an orthonormal basis of `V` and
`cross b` the planar cross product. The triangle `ABC` is inscribed in the circle with center `O`
and radius `R > 0`; `P` is any point. The feet of the perpendiculars from `P` to the side lines are
Mathlib's orthogonal projections `D`, `E`, `F` of `P` onto `line[ℝ, B, C]`, `line[ℝ, C, A]`,
`line[ℝ, A, B]`.

* `simson_det_eq_circumcircle_power`: `4 R² · ((E − D) × (F − D)) = −((B − A) × (C − A)) · powPt P O R`
  (twice the signed area of the pedal triangle is proportional to the power of `P`).
* `simson_wallace`: for a nondegenerate triangle, `D, E, F` are collinear iff `P` lies on the
  circumcircle.
* `steiner_line`: if `P` is on the circumcircle, the reflections of `P` in the three side lines
  (Mathlib's `EuclideanGeometry.reflection`) and the point `A + B + C − 2 O` are collinear;
  `steiner_line_orthocenter`: for a Mathlib triangle `t` this point is `t.orthocenter`.

The proofs reduce to polynomial identities over `ℝ` (`foot_alg`, `simson_alg`, `steiner_alg_*`)
whose certificates were found by Gröbner-basis reduction; `linear_combination` checks them.
-/

open Module EuclideanGeometry
open scoped RealInnerProductSpace

namespace CircleSystems

section Algebra

/-- Coordinates of the foot of a perpendicular onto a chord `XY` of the circle `|·| = R`. -/
theorem foot_alg_x (x1 x2 y1 y2 p1 p2 d1 d2 R : ℝ) (hX : x1 ^ 2 + x2 ^ 2 = R ^ 2)
    (hY : y1 ^ 2 + y2 ^ 2 = R ^ 2) (hl : (y1 - x1) * (d2 - x2) - (y2 - x2) * (d1 - x1) = 0)
    (hp : (p1 - d1) * (y1 - x1) + (p2 - d2) * (y2 - x2) = 0) :
    ((y1 - x1) ^ 2 + (y2 - x2) ^ 2) *
      (2 * R ^ 2 * d1 - (R^2*(p1 + x1 + y1) - p1*(x1*y1 - x2*y2) - p2*(x1*y2 + x2*y1))) = 0 := by
  linear_combination (-2*R^2*(-x1 + y1)) * hp + (-2*R^2*(-x2 + y2)) * hl + (R^2*p1 - R^2*x1 + R^2*y1 + p1*x1*y1 - p1*x2*y2 - 2*p1*y1^2 + p2*x1*y2 + p2*x2*y1 - 2*p2*y1*y2) * hX + (-R^2*p1 + R^2*x1 - R^2*y1 + p1*x1*y1 + 2*p1*x2^2 - p1*x2*y2 - 2*p2*x1*x2 + p2*x1*y2 + p2*x2*y1) * hY

theorem foot_alg_y (x1 x2 y1 y2 p1 p2 d1 d2 R : ℝ) (hX : x1 ^ 2 + x2 ^ 2 = R ^ 2)
    (hY : y1 ^ 2 + y2 ^ 2 = R ^ 2) (hl : (y1 - x1) * (d2 - x2) - (y2 - x2) * (d1 - x1) = 0)
    (hp : (p1 - d1) * (y1 - x1) + (p2 - d2) * (y2 - x2) = 0) :
    ((y1 - x1) ^ 2 + (y2 - x2) ^ 2) *
      (2 * R ^ 2 * d2 - (R^2*(p2 + x2 + y2) - p1*(x1*y2 + x2*y1) + p2*(x1*y1 - x2*y2))) = 0 := by
  linear_combination (-2*R^2*(-x2 + y2)) * hp + (2*R^2*(-x1 + y1)) * hl + (-R^2*p2 - R^2*x2 + R^2*y2 + p1*x1*y2 + p1*x2*y1 - 2*p1*y1*y2 - p2*x1*y1 + p2*x2*y2 + 2*p2*y1^2) * hX + (R^2*p2 + R^2*x2 - R^2*y2 - 2*p1*x1*x2 + p1*x1*y2 + p1*x2*y1 - p2*x1*y1 - 2*p2*x2^2 + p2*x2*y2) * hY

/-- The Simson determinant identity in coordinates centered at the circumcenter. -/
theorem simson_alg (a1 a2 b1 b2 c1 c2 p1 p2 R d1 d2 e1 e2 f1 f2 : ℝ)
    (hA : a1 ^ 2 + a2 ^ 2 = R ^ 2) (hB : b1 ^ 2 + b2 ^ 2 = R ^ 2) (hC : c1 ^ 2 + c2 ^ 2 = R ^ 2)
    (hD1 : 2 * R ^ 2 * d1 = R^2*(p1 + b1 + c1) - p1*(b1*c1 - b2*c2) - p2*(b1*c2 + b2*c1)) (hD2 : 2 * R ^ 2 * d2 = R^2*(p2 + b2 + c2) - p1*(b1*c2 + b2*c1) + p2*(b1*c1 - b2*c2))
    (hE1 : 2 * R ^ 2 * e1 = R^2*(p1 + c1 + a1) - p1*(c1*a1 - c2*a2) - p2*(c1*a2 + c2*a1)) (hE2 : 2 * R ^ 2 * e2 = R^2*(p2 + c2 + a2) - p1*(c1*a2 + c2*a1) + p2*(c1*a1 - c2*a2))
    (hF1 : 2 * R ^ 2 * f1 = R^2*(p1 + a1 + b1) - p1*(a1*b1 - a2*b2) - p2*(a1*b2 + a2*b1)) (hF2 : 2 * R ^ 2 * f2 = R^2*(p2 + a2 + b2) - p1*(a1*b2 + a2*b1) + p2*(a1*b1 - a2*b2)) :
    R ^ 2 * (4 * R ^ 2 * ((e1 - d1) * (f2 - d2) - (e2 - d2) * (f1 - d1)) -
      ((b1 - a1) * (c2 - a2) - (b2 - a2) * (c1 - a1)) * (R ^ 2 - (p1 ^ 2 + p2 ^ 2))) = 0 := by
  linear_combination (2*R^2*(e2 - f2)) * hD1 + (-2*R^2*(e1 - f1)) * hD2 + (-R^2*b2 - R^2*c2 + 2*R^2*f2 - R^2*p2 - b1*c1*p2 + b1*c2*p1 + b2*c1*p1 + b2*c2*p2) * hE1 + (R^2*b1 + R^2*c1 - 2*R^2*f1 + R^2*p1 - b1*c1*p1 - b1*c2*p2 - b2*c1*p2 + b2*c2*p1) * hE2 + (-R^2*a2 + R^2*b2 - a1*c1*p2 + a1*c2*p1 + a2*c1*p1 + a2*c2*p2 + b1*c1*p2 - b1*c2*p1 - b2*c1*p1 - b2*c2*p2) * hF1 + (R^2*a1 - R^2*b1 - a1*c1*p1 - a1*c2*p2 - a2*c1*p2 + a2*c2*p1 + b1*c1*p1 + b1*c2*p2 + b2*c1*p2 - b2*c2*p1) * hF2 + (R^2*b1*p2 - R^2*b2*p1 - R^2*c1*p2 + R^2*c2*p1 - b1*c2*p1^2 - b1*c2*p2^2 + b2*c1*p1^2 + b2*c1*p2^2) * hA + (-R^2*a1*p2 + R^2*a2*p1 + R^2*c1*p2 - R^2*c2*p1 + a1*c2*p1^2 + a1*c2*p2^2 - a2*c1*p1^2 - a2*c1*p2^2) * hB + (R^2*a1*p2 - R^2*a2*p1 - R^2*b1*p2 + R^2*b2*p1 - a1*b2*p1^2 - a1*b2*p2^2 + a2*b1*p1^2 + a2*b1*p2^2) * hC

/-- A Steiner-line cross product in coordinates centered at the circumcenter. -/
theorem steiner_alg_AB (a1 a2 b1 b2 c1 c2 p1 p2 R d1 d2 e1 e2 f1 f2 : ℝ)
    (hA : a1 ^ 2 + a2 ^ 2 = R ^ 2) (hB : b1 ^ 2 + b2 ^ 2 = R ^ 2) (hC : c1 ^ 2 + c2 ^ 2 = R ^ 2)
    (hD1 : 2 * R ^ 2 * d1 = R^2*(p1 + b1 + c1) - p1*(b1*c1 - b2*c2) - p2*(b1*c2 + b2*c1)) (hD2 : 2 * R ^ 2 * d2 = R^2*(p2 + b2 + c2) - p1*(b1*c2 + b2*c1) + p2*(b1*c1 - b2*c2))
    (hE1 : 2 * R ^ 2 * e1 = R^2*(p1 + c1 + a1) - p1*(c1*a1 - c2*a2) - p2*(c1*a2 + c2*a1)) (hE2 : 2 * R ^ 2 * e2 = R^2*(p2 + c2 + a2) - p1*(c1*a2 + c2*a1) + p2*(c1*a1 - c2*a2))
    (_hF1 : 2 * R ^ 2 * f1 = R^2*(p1 + a1 + b1) - p1*(a1*b1 - a2*b2) - p2*(a1*b2 + a2*b1)) (_hF2 : 2 * R ^ 2 * f2 = R^2*(p2 + a2 + b2) - p1*(a1*b2 + a2*b1) + p2*(a1*b1 - a2*b2))
    (hP : p1 ^ 2 + p2 ^ 2 = R ^ 2) :
    R ^ 4 * ((2 * d1 - p1 - (a1 + b1 + c1)) * (2 * e2 - p2 - (a2 + b2 + c2)) -
      (2 * d2 - p2 - (a2 + b2 + c2)) * (2 * e1 - p1 - (a1 + b1 + c1))) = 0 := by
  linear_combination (-R^2*(a2 + b2 + c2 - 2*e2 + p2)) * hD1 + (R^2*(a1 + b1 + c1 - 2*e1 + p1)) * hD2 + (R^2*a2 - b1*c1*p2 + b1*c2*p1 + b2*c1*p1 + b2*c2*p2) * hE1 + (-R^2*a1 - b1*c1*p1 - b1*c2*p2 - b2*c1*p2 + b2*c2*p1) * hE2 + (-(c1^2 + c2^2)*(a1*b2 - a2*b1)) * hP + (R^2*(-c1*p2 + c2*p1)) * hA + (-R^2*(-c1*p2 + c2*p1)) * hB + (-R^2*(a1*b2 - a2*b1)) * hC

/-- A Steiner-line cross product in coordinates centered at the circumcenter. -/
theorem steiner_alg_AC (a1 a2 b1 b2 c1 c2 p1 p2 R d1 d2 e1 e2 f1 f2 : ℝ)
    (hA : a1 ^ 2 + a2 ^ 2 = R ^ 2) (hB : b1 ^ 2 + b2 ^ 2 = R ^ 2) (hC : c1 ^ 2 + c2 ^ 2 = R ^ 2)
    (hD1 : 2 * R ^ 2 * d1 = R^2*(p1 + b1 + c1) - p1*(b1*c1 - b2*c2) - p2*(b1*c2 + b2*c1)) (hD2 : 2 * R ^ 2 * d2 = R^2*(p2 + b2 + c2) - p1*(b1*c2 + b2*c1) + p2*(b1*c1 - b2*c2))
    (_hE1 : 2 * R ^ 2 * e1 = R^2*(p1 + c1 + a1) - p1*(c1*a1 - c2*a2) - p2*(c1*a2 + c2*a1)) (_hE2 : 2 * R ^ 2 * e2 = R^2*(p2 + c2 + a2) - p1*(c1*a2 + c2*a1) + p2*(c1*a1 - c2*a2))
    (hF1 : 2 * R ^ 2 * f1 = R^2*(p1 + a1 + b1) - p1*(a1*b1 - a2*b2) - p2*(a1*b2 + a2*b1)) (hF2 : 2 * R ^ 2 * f2 = R^2*(p2 + a2 + b2) - p1*(a1*b2 + a2*b1) + p2*(a1*b1 - a2*b2))
    (hP : p1 ^ 2 + p2 ^ 2 = R ^ 2) :
    R ^ 4 * ((2 * d1 - p1 - (a1 + b1 + c1)) * (2 * f2 - p2 - (a2 + b2 + c2)) -
      (2 * d2 - p2 - (a2 + b2 + c2)) * (2 * f1 - p1 - (a1 + b1 + c1))) = 0 := by
  linear_combination (-R^2*(a2 + b2 + c2 - 2*f2 + p2)) * hD1 + (R^2*(a1 + b1 + c1 - 2*f1 + p1)) * hD2 + (R^2*a2 - b1*c1*p2 + b1*c2*p1 + b2*c1*p1 + b2*c2*p2) * hF1 + (-R^2*a1 - b1*c1*p1 - b1*c2*p2 - b2*c1*p2 + b2*c2*p1) * hF2 + (-(b1^2 + b2^2)*(a1*c2 - a2*c1)) * hP + (R^2*(-b1*p2 + b2*p1)) * hA + (-R^2*(a1*c2 - a2*c1)) * hB + (-R^2*(-b1*p2 + b2*p1)) * hC

/-- A Steiner-line cross product in coordinates centered at the circumcenter. -/
theorem steiner_alg_BC (a1 a2 b1 b2 c1 c2 p1 p2 R d1 d2 e1 e2 f1 f2 : ℝ)
    (hA : a1 ^ 2 + a2 ^ 2 = R ^ 2) (hB : b1 ^ 2 + b2 ^ 2 = R ^ 2) (hC : c1 ^ 2 + c2 ^ 2 = R ^ 2)
    (_hD1 : 2 * R ^ 2 * d1 = R^2*(p1 + b1 + c1) - p1*(b1*c1 - b2*c2) - p2*(b1*c2 + b2*c1)) (_hD2 : 2 * R ^ 2 * d2 = R^2*(p2 + b2 + c2) - p1*(b1*c2 + b2*c1) + p2*(b1*c1 - b2*c2))
    (hE1 : 2 * R ^ 2 * e1 = R^2*(p1 + c1 + a1) - p1*(c1*a1 - c2*a2) - p2*(c1*a2 + c2*a1)) (hE2 : 2 * R ^ 2 * e2 = R^2*(p2 + c2 + a2) - p1*(c1*a2 + c2*a1) + p2*(c1*a1 - c2*a2))
    (hF1 : 2 * R ^ 2 * f1 = R^2*(p1 + a1 + b1) - p1*(a1*b1 - a2*b2) - p2*(a1*b2 + a2*b1)) (hF2 : 2 * R ^ 2 * f2 = R^2*(p2 + a2 + b2) - p1*(a1*b2 + a2*b1) + p2*(a1*b1 - a2*b2))
    (hP : p1 ^ 2 + p2 ^ 2 = R ^ 2) :
    R ^ 4 * ((2 * e1 - p1 - (a1 + b1 + c1)) * (2 * f2 - p2 - (a2 + b2 + c2)) -
      (2 * e2 - p2 - (a2 + b2 + c2)) * (2 * f1 - p1 - (a1 + b1 + c1))) = 0 := by
  linear_combination (-R^2*(a2 + b2 + c2 - 2*f2 + p2)) * hE1 + (R^2*(a1 + b1 + c1 - 2*f1 + p1)) * hE2 + (R^2*b2 - a1*c1*p2 + a1*c2*p1 + a2*c1*p1 + a2*c2*p2) * hF1 + (-R^2*b1 - a1*c1*p1 - a1*c2*p2 - a2*c1*p2 + a2*c2*p1) * hF2 + (-(a1^2 + a2^2)*(b1*c2 - b2*c1)) * hP + (-R^2*(b1*c2 - b2*c1)) * hA + (R^2*(-a1*p2 + a2*p1)) * hB + (-R^2*(-a1*p2 + a2*p1)) * hC

end Algebra

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (b : OrthonormalBasis (Fin 2) ℝ V)

/-- The foot of the perpendicular from `P` to `line[ℝ, X, Y]` lies on the line and `P − D` is
perpendicular to `Y − X`. -/
theorem foot_props (X Y P : V) :
    cross b (Y - X) ((orthogonalProjection line[ℝ, X, Y] P : V) - X) = 0 ∧
      ⟪Y - X, P - (orthogonalProjection line[ℝ, X, Y] P : V)⟫ = 0 := by
  constructor
  · obtain ⟨r, hr⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1
      (orthogonalProjection_mem (s := line[ℝ, X, Y]) P)
    rw [← hr, AffineMap.lineMap_apply, vadd_eq_add, add_sub_cancel_right, vsub_eq_sub, cross, cx_smul,
      cy_smul]
    ring
  · exact Submodule.inner_right_of_mem_orthogonal
      (AffineSubspace.vsub_mem_direction (right_mem_affineSpan_pair ℝ X Y)
        (left_mem_affineSpan_pair ℝ X Y))
      (vsub_orthogonalProjection_mem_direction_orthogonal _ P)

/-- The reflection of `P` in `line[ℝ, X, Y]` is `2 D − P` for the foot `D`. -/
theorem reflection_eq (X Y P : V) :
    reflection line[ℝ, X, Y] P = (2 : ℝ) • (orthogonalProjection line[ℝ, X, Y] P : V) - P := by
  rw [reflection_apply', vsub_eq_sub, vadd_eq_add, two_smul]; abel

/-- Coordinates of the foot of the perpendicular from `P` to a chord `XY` of the circle `(O, R)`,
relative to `O`. -/
theorem foot_coord {O X Y P : V} {R : ℝ} (hX : dist X O = R) (hY : dist Y O = R) (hXY : X ≠ Y) :
    2 * R ^ 2 * (cx b (orthogonalProjection line[ℝ, X, Y] P : V) - cx b O) =
      R^2*((cx b P - cx b O) + (cx b X - cx b O) + (cx b Y - cx b O)) - (cx b P - cx b O)*((cx b X - cx b O)*(cx b Y - cx b O) - (cy b X - cy b O)*(cy b Y - cy b O)) - (cy b P - cy b O)*((cx b X - cx b O)*(cy b Y - cy b O) + (cy b X - cy b O)*(cx b Y - cx b O)) ∧
    2 * R ^ 2 * (cy b (orthogonalProjection line[ℝ, X, Y] P : V) - cy b O) =
      R^2*((cy b P - cy b O) + (cy b X - cy b O) + (cy b Y - cy b O)) - (cx b P - cx b O)*((cx b X - cx b O)*(cy b Y - cy b O) + (cy b X - cy b O)*(cx b Y - cx b O)) + (cy b P - cy b O)*((cx b X - cx b O)*(cx b Y - cx b O) - (cy b X - cy b O)*(cy b Y - cy b O)) := by
  obtain ⟨hl, hp⟩ := foot_props b X Y P
  set D := (orthogonalProjection line[ℝ, X, Y] P : V)
  rw [inner_coord] at hp
  simp only [cross, cx_sub, cy_sub] at hl hp
  have hX' : (cx b X - cx b O) ^ 2 + (cy b X - cy b O) ^ 2 = R ^ 2 := by
    rw [← dist_sq_coord, hX]
  have hY' : (cx b Y - cx b O) ^ 2 + (cy b Y - cy b O) ^ 2 = R ^ 2 := by
    rw [← dist_sq_coord, hY]
  have hn : ((cx b Y - cx b O) - (cx b X - cx b O)) ^ 2 +
      ((cy b Y - cy b O) - (cy b X - cy b O)) ^ 2 ≠ 0 := by
    intro h
    apply hXY
    have : dist Y X ^ 2 = 0 := by rw [dist_sq_coord]; linear_combination h
    exact (dist_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)).symm
  constructor
  · have := foot_alg_x (cx b X - cx b O) (cy b X - cy b O) (cx b Y - cx b O) (cy b Y - cy b O)
      (cx b P - cx b O) (cy b P - cy b O) (cx b D - cx b O) (cy b D - cy b O) R hX' hY'
      (by linear_combination hl) (by linear_combination hp)
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hn)
  · have := foot_alg_y (cx b X - cx b O) (cy b X - cy b O) (cx b Y - cx b O) (cy b Y - cy b O)
      (cx b P - cx b O) (cy b P - cy b O) (cx b D - cx b O) (cy b D - cy b O) R hX' hY'
      (by linear_combination hl) (by linear_combination hp)
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hn)

section Triangle

variable {A B C O P : V} {R : ℝ}

omit [InnerProductSpace ℝ V] in
theorem R_ne_zero (hA : dist A O = R) (hB : dist B O = R) (hAB : A ≠ B) : R ≠ 0 := by
  rintro rfl
  exact hAB ((dist_eq_zero.1 hA).trans (dist_eq_zero.1 hB).symm)

/-- **Simson determinant identity.** For a triangle `ABC` inscribed in the circle `(O, R)` and the
feet `D, E, F` of the perpendiculars from any point `P` to `BC, CA, AB`:
`4 R² · ((E − D) × (F − D)) = −((B − A) × (C − A)) · powPt P O R`. -/
theorem simson_det_eq_circumcircle_power (hA : dist A O = R) (hB : dist B O = R)
    (hC : dist C O = R) (hAB : A ≠ B) (hBC : B ≠ C) (hCA : C ≠ A) :
    4 * R ^ 2 * cross b ((orthogonalProjection line[ℝ, C, A] P : V) -
        (orthogonalProjection line[ℝ, B, C] P : V))
      ((orthogonalProjection line[ℝ, A, B] P : V) - (orthogonalProjection line[ℝ, B, C] P : V)) =
      -cross b (B - A) (C - A) * powPt P O R := by
  have hR := R_ne_zero hA hB hAB
  obtain ⟨hD1, hD2⟩ := foot_coord b (P := P) hB hC hBC
  obtain ⟨hE1, hE2⟩ := foot_coord b (P := P) hC hA hCA
  obtain ⟨hF1, hF2⟩ := foot_coord b (P := P) hA hB hAB
  set D := (orthogonalProjection line[ℝ, B, C] P : V)
  set E := (orthogonalProjection line[ℝ, C, A] P : V)
  set F := (orthogonalProjection line[ℝ, A, B] P : V)
  have hA' : (cx b A - cx b O) ^ 2 + (cy b A - cy b O) ^ 2 = R ^ 2 := by rw [← dist_sq_coord, hA]
  have hB' : (cx b B - cx b O) ^ 2 + (cy b B - cy b O) ^ 2 = R ^ 2 := by rw [← dist_sq_coord, hB]
  have hC' : (cx b C - cx b O) ^ 2 + (cy b C - cy b O) ^ 2 = R ^ 2 := by rw [← dist_sq_coord, hC]
  have key := simson_alg (cx b A - cx b O) (cy b A - cy b O) (cx b B - cx b O) (cy b B - cy b O)
    (cx b C - cx b O) (cy b C - cy b O) (cx b P - cx b O) (cy b P - cy b O) R
    (cx b D - cx b O) (cy b D - cy b O) (cx b E - cx b O) (cy b E - cy b O)
    (cx b F - cx b O) (cy b F - cy b O) hA' hB' hC' hD1 hD2 hE1 hE2 hF1 hF2
  have hR2 : R ^ 2 ≠ 0 := pow_ne_zero 2 hR
  rw [powPt_coord b]
  simp only [cross, cx_sub, cy_sub]
  apply mul_left_cancel₀ hR2
  linear_combination key

/-- **Simson–Wallace theorem.** For a nondegenerate triangle `ABC` inscribed in the circle
`(O, R)`, the feet of the perpendiculars from `P` to the three side lines are collinear iff `P`
lies on the circle. -/
theorem simson_wallace [Fact (finrank ℝ V = 2)] (hA : dist A O = R) (hB : dist B O = R) (hC : dist C O = R)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set V)) :
    Collinear ℝ ({(orthogonalProjection line[ℝ, B, C] P : V),
      (orthogonalProjection line[ℝ, C, A] P : V), (orthogonalProjection line[ℝ, A, B] P : V)} :
        Set V) ↔ dist P O = R := by
  obtain ⟨b⟩ := exists_basis (V := V)
  rw [collinear_iff_cross b] at hABC
  have hAB : A ≠ B := by rintro rfl; apply hABC; simp only [cross, sub_self, cx_zero', cy_zero']; ring
  have hBC : B ≠ C := by rintro rfl; apply hABC; simp only [cross]; ring
  have hCA : C ≠ A := by rintro rfl; apply hABC; simp only [cross, sub_self, cx_zero', cy_zero']; ring
  have hR := R_ne_zero hA hB hAB
  have h := simson_det_eq_circumcircle_power b (P := P) hA hB hC hAB hBC hCA
  rw [collinear_iff_cross b, ← powPt_eq_zero_iff (hA ▸ dist_nonneg)]
  constructor
  · intro h0
    rw [h0, mul_zero, zero_eq_mul, neg_eq_zero] at h
    exact h.resolve_left hABC
  · intro h0
    rw [h0, mul_zero] at h
    exact (mul_eq_zero.1 h).resolve_left (by positivity)

/-- **Steiner line.** If `P` lies on the circumcircle `(O, R)` of the triangle `ABC`, the
reflections of `P` in the three side lines are collinear with `A + B + C − 2 O` (the orthocenter,
see `steiner_line_orthocenter`). -/
theorem steiner_line [Fact (finrank ℝ V = 2)] (hA : dist A O = R) (hB : dist B O = R)
    (hC : dist C O = R)
    (hP : dist P O = R) (hAB : A ≠ B) (hBC : B ≠ C) (hCA : C ≠ A) :
    Collinear ℝ ({A + B + C - (2 : ℝ) • O, reflection line[ℝ, B, C] P,
      reflection line[ℝ, C, A] P, reflection line[ℝ, A, B] P} : Set V) := by
  obtain ⟨b⟩ := exists_basis (V := V)
  have hR := R_ne_zero hA hB hAB
  obtain ⟨hD1, hD2⟩ := foot_coord b (P := P) hB hC hBC
  obtain ⟨hE1, hE2⟩ := foot_coord b (P := P) hC hA hCA
  obtain ⟨hF1, hF2⟩ := foot_coord b (P := P) hA hB hAB
  simp only [reflection_eq]
  set D := (orthogonalProjection line[ℝ, B, C] P : V)
  set E := (orthogonalProjection line[ℝ, C, A] P : V)
  set F := (orthogonalProjection line[ℝ, A, B] P : V)
  have hA' : (cx b A - cx b O) ^ 2 + (cy b A - cy b O) ^ 2 = R ^ 2 := by rw [← dist_sq_coord, hA]
  have hB' : (cx b B - cx b O) ^ 2 + (cy b B - cy b O) ^ 2 = R ^ 2 := by rw [← dist_sq_coord, hB]
  have hC' : (cx b C - cx b O) ^ 2 + (cy b C - cy b O) ^ 2 = R ^ 2 := by rw [← dist_sq_coord, hC]
  have hP' : (cx b P - cx b O) ^ 2 + (cy b P - cy b O) ^ 2 = R ^ 2 := by rw [← dist_sq_coord, hP]
  have hR4 : R ^ 4 ≠ 0 := pow_ne_zero 4 hR
  apply collinear_four_of_cross b <;> simp only [cross, cx_sub, cy_sub, cx_add, cy_add, cx_smul,
    cy_smul] <;> apply mul_left_cancel₀ hR4
  · linear_combination steiner_alg_AB (cx b A - cx b O) (cy b A - cy b O) (cx b B - cx b O)
      (cy b B - cy b O) (cx b C - cx b O) (cy b C - cy b O) (cx b P - cx b O) (cy b P - cy b O) R
      (cx b D - cx b O) (cy b D - cy b O) (cx b E - cx b O) (cy b E - cy b O)
      (cx b F - cx b O) (cy b F - cy b O) hA' hB' hC' hD1 hD2 hE1 hE2 hF1 hF2 hP'
  · linear_combination steiner_alg_AC (cx b A - cx b O) (cy b A - cy b O) (cx b B - cx b O)
      (cy b B - cy b O) (cx b C - cx b O) (cy b C - cy b O) (cx b P - cx b O) (cy b P - cy b O) R
      (cx b D - cx b O) (cy b D - cy b O) (cx b E - cx b O) (cy b E - cy b O)
      (cx b F - cx b O) (cy b F - cy b O) hA' hB' hC' hD1 hD2 hE1 hE2 hF1 hF2 hP'
  · linear_combination steiner_alg_BC (cx b A - cx b O) (cy b A - cy b O) (cx b B - cx b O)
      (cy b B - cy b O) (cx b C - cx b O) (cy b C - cy b O) (cx b P - cx b O) (cy b P - cy b O) R
      (cx b D - cx b O) (cy b D - cy b O) (cx b E - cx b O) (cy b E - cy b O)
      (cx b F - cx b O) (cy b F - cy b O) hA' hB' hC' hD1 hD2 hE1 hE2 hF1 hF2 hP'

end Triangle

/-- **Steiner line through the orthocenter.** For a triangle `t` (Mathlib's `Affine.Triangle`) and
a point `P` on its circumcircle, the reflections of `P` in the three side lines are collinear with
the orthocenter of `t`. -/
theorem steiner_line_orthocenter [Fact (finrank ℝ V = 2)] (t : Affine.Triangle ℝ V) {P : V}
    (hP : dist P t.circumcenter = t.circumradius) :
    Collinear ℝ ({t.orthocenter, reflection line[ℝ, t.points 1, t.points 2] P,
      reflection line[ℝ, t.points 2, t.points 0] P,
      reflection line[ℝ, t.points 0, t.points 1] P} : Set V) := by
  have hH : t.orthocenter = t.points 0 + t.points 1 + t.points 2 - (2 : ℝ) • t.circumcenter := by
    have hs := t.orthocenter_vsub_circumcenter_eq_sum_vsub
    rw [Fin.sum_univ_three] at hs
    simp only [vsub_eq_sub] at hs
    rw [← sub_eq_zero, ← sub_eq_zero.2 hs, two_smul]
    abel
  rw [hH]
  have hinj := t.independent.injective
  exact steiner_line (t.dist_circumcenter_eq_circumradius 0)
    (t.dist_circumcenter_eq_circumradius 1) (t.dist_circumcenter_eq_circumradius 2) hP
    (fun h => by simpa using hinj h) (fun h => by simpa using hinj h)
    (fun h => by simpa using hinj h)

end CircleSystems
