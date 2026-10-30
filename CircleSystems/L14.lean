import CircleSystems.Coaxal
import CircleSystems.Johnson
import CircleSystems.SimsonSteiner

/-!
# Layer 14: Mathlib-only restatements and explicit witnesses

`l14_<name>` restates each main theorem with the local definitions (`powPt`, `radicalAxis`,
`radConst`, `radBase`, `pencilPow`, `pencilCenter`, `pencilRadSq`, `IsOrthogonal`, `cx`, `cy`,
`cross`) unfolded, so that its type mentions only Mathlib notions; each is proved from the
library theorem.

`l14w_<name>` gives a concrete configuration in `ℂ` satisfying every hypothesis, with a
non-degenerate conclusion. The triangle is `A = 5`, `B = 5i`, `C = -3 - 4i` on the circle
`|z| = 5` (orthocentre `A + B + C = 2 + i`).
-/

open Module EuclideanGeometry
open scoped RealInnerProductSpace

namespace CircleSystems

section Restatements

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Power of a point / radical axis as the level set of `⟪·, O₁ − O₂⟫`. -/
theorem l14_radicalAxis_eq_inner (O₁ O₂ : V) (R₁ R₂ : ℝ) :
    {P : V | dist P O₁ ^ 2 - R₁ ^ 2 = dist P O₂ ^ 2 - R₂ ^ 2} =
      {P | ⟪P, O₁ - O₂⟫ = (⟪O₁, O₁⟫ - R₁ ^ 2 - (⟪O₂, O₂⟫ - R₂ ^ 2)) / 2} :=
  radicalAxis_eq_inner O₁ O₂ R₁ R₂

/-- The radical axis of circles with distinct centres is an affine line (hyperplane) with
direction `(ℝ ∙ (O₁ − O₂))ᗮ`. -/
theorem l14_radicalAxis_eq_affine {O₁ O₂ : V} (R₁ R₂ : ℝ) (h : O₁ ≠ O₂) :
    {P : V | dist P O₁ ^ 2 - R₁ ^ 2 = dist P O₂ ^ 2 - R₂ ^ 2} =
      (AffineSubspace.mk'
        (((((⟪O₁, O₁⟫ - R₁ ^ 2 - (⟪O₂, O₂⟫ - R₂ ^ 2)) / 2) - ⟪O₂, O₁ - O₂⟫) / ‖O₁ - O₂‖ ^ 2) •
          (O₁ - O₂) + O₂) (ℝ ∙ (O₁ - O₂))ᗮ : Set V) :=
  radicalAxis_eq_mk' R₁ R₂ h

/-- **Radical centre** (Monge). -/
theorem l14_radical_center_concurrent [Fact (finrank ℝ V = 2)] {O₁ O₂ O₃ : V} (R₁ R₂ R₃ : ℝ)
    (hO : ¬ Collinear ℝ ({O₁, O₂, O₃} : Set V)) :
    ∃! X : V, dist X O₁ ^ 2 - R₁ ^ 2 = dist X O₂ ^ 2 - R₂ ^ 2 ∧
      dist X O₂ ^ 2 - R₂ ^ 2 = dist X O₃ ^ 2 - R₃ ^ 2 ∧
      dist X O₃ ^ 2 - R₃ ^ 2 = dist X O₁ ^ 2 - R₁ ^ 2 :=
  radical_center_concurrent R₁ R₂ R₃ hO

/-- Each member of the coaxal pencil is a circle centred on the line of centres. -/
theorem l14_pencilPow_eq_powPt (O₁ O₂ : V) (R₁ R₂ t : ℝ) (P : V) :
    (1 - t) * (dist P O₁ ^ 2 - R₁ ^ 2) + t * (dist P O₂ ^ 2 - R₂ ^ 2) =
      dist P ((1 - t) • O₁ + t • O₂) ^ 2 -
        ((1 - t) * R₁ ^ 2 + t * R₂ ^ 2 - t * (1 - t) * dist O₁ O₂ ^ 2) :=
  pencilPow_eq_powPt O₁ O₂ R₁ R₂ t P

theorem l14_pencilCenter_mem_line (O₁ O₂ : V) (t : ℝ) :
    (1 - t) • O₁ + t • O₂ ∈ line[ℝ, O₁, O₂] :=
  pencilCenter_mem_line O₁ O₂ t

/-- Any two distinct members of the pencil have the radical axis of the generating circles. -/
theorem l14_pencil_radicalAxis (O₁ O₂ : V) (R₁ R₂ : ℝ) {s t : ℝ} (hst : s ≠ t) :
    {P : V | dist P ((1 - s) • O₁ + s • O₂) ^ 2 -
          ((1 - s) * R₁ ^ 2 + s * R₂ ^ 2 - s * (1 - s) * dist O₁ O₂ ^ 2) =
        dist P ((1 - t) • O₁ + t • O₂) ^ 2 -
          ((1 - t) * R₁ ^ 2 + t * R₂ ^ 2 - t * (1 - t) * dist O₁ O₂ ^ 2)} =
      {P | dist P O₁ ^ 2 - R₁ ^ 2 = dist P O₂ ^ 2 - R₂ ^ 2} :=
  pencil_radicalAxis O₁ O₂ R₁ R₂ hst

/-- **Orthogonal circles.** -/
theorem l14_isOrthogonal_iff [Fact (finrank ℝ V = 2)] {O₁ O₂ : V} {R₁ R₂ : ℝ} (h₁ : 0 < R₁)
    (h₂ : 0 < R₂) :
    (∃ X : V, dist X O₁ = R₁ ∧ dist X O₂ = R₂ ∧ ⟪X - O₁, X - O₂⟫ = 0) ↔
      dist O₁ O₂ ^ 2 - R₂ ^ 2 = R₁ ^ 2 :=
  isOrthogonal_iff h₁ h₂

/-- **Johnson's theorem.** -/
theorem l14_johnson_circle {H O₁ O₂ O₃ : V} {R : ℝ} (h₁ : dist H O₁ = R) (h₂ : dist H O₂ = R)
    (h₃ : dist H O₃ = R) :
    dist (O₂ + O₃ - H) (O₁ + O₂ + O₃ - (2 : ℝ) • H) = R ∧
    dist (O₃ + O₁ - H) (O₁ + O₂ + O₃ - (2 : ℝ) • H) = R ∧
    dist (O₁ + O₂ - H) (O₁ + O₂ + O₃ - (2 : ℝ) • H) = R :=
  johnson_circle h₁ h₂ h₃

theorem l14_johnson_orthocenter_eq [Fact (finrank ℝ V = 2)] {H O₁ O₂ O₃ : V} {R : ℝ}
    (h₁ : dist H O₁ = R) (h₂ : dist H O₂ = R) (h₃ : dist H O₃ = R)
    (hind : AffineIndependent ℝ ![O₂ + O₃ - H, O₃ + O₁ - H, O₁ + O₂ - H]) :
    (⟨_, hind⟩ : Affine.Triangle ℝ V).circumcenter = O₁ + O₂ + O₃ - (2 : ℝ) • H ∧
      Affine.Triangle.orthocenter (⟨_, hind⟩ : Affine.Triangle ℝ V) = H :=
  johnson_orthocenter_eq h₁ h₂ h₃ hind

omit [InnerProductSpace ℝ V] in
theorem l14_johnson_congruent (H O₁ O₂ O₃ : V) :
    Congruent ![O₁, O₂, O₃] ![O₂ + O₃ - H, O₃ + O₁ - H, O₁ + O₂ - H] :=
  johnson_congruent H O₁ O₂ O₃

/-- Signed area of the pedal triangle vs. the power of `P` (cross product written with inner
products against an orthonormal basis `b`). -/
theorem l14_simson_det_eq_circumcircle_power (b : OrthonormalBasis (Fin 2) ℝ V) {A B C O P : V}
    {R : ℝ} (hA : dist A O = R) (hB : dist B O = R)
    (hC : dist C O = R) (hAB : A ≠ B) (hBC : B ≠ C) (hCA : C ≠ A) :
    4 * R ^ 2 *
      (⟪b 0, (orthogonalProjection line[ℝ, C, A] P : V) - (orthogonalProjection line[ℝ, B, C] P : V)⟫ *
        ⟪b 1, (orthogonalProjection line[ℝ, A, B] P : V) - (orthogonalProjection line[ℝ, B, C] P : V)⟫ -
       ⟪b 1, (orthogonalProjection line[ℝ, C, A] P : V) - (orthogonalProjection line[ℝ, B, C] P : V)⟫ *
        ⟪b 0, (orthogonalProjection line[ℝ, A, B] P : V) - (orthogonalProjection line[ℝ, B, C] P : V)⟫) =
      -(⟪b 0, B - A⟫ * ⟪b 1, C - A⟫ - ⟪b 1, B - A⟫ * ⟪b 0, C - A⟫) * (dist P O ^ 2 - R ^ 2) :=
  simson_det_eq_circumcircle_power b hA hB hC hAB hBC hCA

/-- **Simson–Wallace.** -/
theorem l14_simson_wallace [Fact (finrank ℝ V = 2)] {A B C O P : V} {R : ℝ} (hA : dist A O = R)
    (hB : dist B O = R) (hC : dist C O = R) (hABC : ¬ Collinear ℝ ({A, B, C} : Set V)) :
    Collinear ℝ ({(orthogonalProjection line[ℝ, B, C] P : V),
      (orthogonalProjection line[ℝ, C, A] P : V), (orthogonalProjection line[ℝ, A, B] P : V)} :
        Set V) ↔ dist P O = R :=
  simson_wallace hA hB hC hABC

/-- **Steiner line.** -/
theorem l14_steiner_line [Fact (finrank ℝ V = 2)] {A B C O P : V} {R : ℝ} (hA : dist A O = R)
    (hB : dist B O = R) (hC : dist C O = R) (hP : dist P O = R) (hAB : A ≠ B) (hBC : B ≠ C)
    (hCA : C ≠ A) :
    Collinear ℝ ({A + B + C - (2 : ℝ) • O, reflection line[ℝ, B, C] P,
      reflection line[ℝ, C, A] P, reflection line[ℝ, A, B] P} : Set V) :=
  steiner_line hA hB hC hP hAB hBC hCA

theorem l14_steiner_line_orthocenter [Fact (finrank ℝ V = 2)] (t : Affine.Triangle ℝ V) {P : V}
    (hP : dist P t.circumcenter = t.circumradius) :
    Collinear ℝ ({t.orthocenter, reflection line[ℝ, t.points 1, t.points 2] P,
      reflection line[ℝ, t.points 2, t.points 0] P,
      reflection line[ℝ, t.points 0, t.points 1] P} : Set V) :=
  steiner_line_orthocenter t hP

end Restatements

/-! ### Witnesses in `ℂ` -/

section Witnesses

theorem l14h_dist {z w : ℂ} {d : ℝ} (hd : 0 ≤ d)
    (h : (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 = d ^ 2) : dist z w = d := by
  rw [Complex.dist_eq_re_im, h, Real.sqrt_sq hd]

theorem l14h_inner (z w : ℂ) : ⟪z, w⟫ = z.re * w.re + z.im * w.im := by
  simp [Complex.inner]; ring

theorem l14h_collinear_iff {A B C : ℂ} :
    Collinear ℝ ({A, B, C} : Set ℂ) ↔
      (B.re - A.re) * (C.im - A.im) - (B.im - A.im) * (C.re - A.re) = 0 := by
  have := collinear_iff_cross Complex.orthonormalBasisOneI (X := A) (Y := B) (Z := C)
  rw [this]
  simp [cross, cx, cy, Complex.coe_orthonormalBasisOneI, Complex.inner]

/-- Foot of a perpendicular in coordinates. -/
theorem l14h_foot {X Y P q : ℂ} (t : ℝ) (hq : q = X + (t : ℂ) * (Y - X))
    (hperp : (P.re - q.re) * (X.re - Y.re) + (P.im - q.im) * (X.im - Y.im) = 0) :
    (orthogonalProjection line[ℝ, X, Y] P : ℂ) = q := by
  rw [coe_orthogonalProjection_eq_iff_mem]
  refine ⟨?_, ?_⟩
  · have : q = AffineMap.lineMap X Y t := by
      rw [hq, AffineMap.lineMap_apply]; simp [Complex.real_smul]; ring
    rw [this]; exact AffineMap.lineMap_mem_affineSpan_pair _ _ _
  · rw [direction_affineSpan, vectorSpan_pair, Submodule.mem_orthogonal_singleton_iff_inner_right,
      l14h_inner]
    simp only [vsub_eq_sub, Complex.sub_re, Complex.sub_im]
    linear_combination hperp

theorem l14h_reflection {X Y P q : ℂ} (t : ℝ) (hq : q = X + (t : ℂ) * (Y - X))
    (hperp : (P.re - q.re) * (X.re - Y.re) + (P.im - q.im) * (X.im - Y.im) = 0) :
    reflection line[ℝ, X, Y] P = 2 * q - P := by
  rw [reflection_eq, l14h_foot t hq hperp]; simp [Complex.real_smul]

/-- **Witness for the radical centre.** The circles `(0, 1)`, `(4, 1)`, `(4i, 3)` have
non-collinear centres; the radical centre is `2 + i` (common power `4`). -/
theorem l14w_radical_center_concurrent :
    ∃ (O₁ O₂ O₃ : ℂ) (R₁ R₂ R₃ : ℝ), ¬ Collinear ℝ ({O₁, O₂, O₃} : Set ℂ) ∧
      ∀ X : ℂ, (dist X O₁ ^ 2 - R₁ ^ 2 = dist X O₂ ^ 2 - R₂ ^ 2 ∧
        dist X O₂ ^ 2 - R₂ ^ 2 = dist X O₃ ^ 2 - R₃ ^ 2 ∧
        dist X O₃ ^ 2 - R₃ ^ 2 = dist X O₁ ^ 2 - R₁ ^ 2) ↔ X = ⟨2, 1⟩ := by
  refine ⟨0, 4, ⟨0, 4⟩, 1, 1, 3, ?_, fun X => ?_⟩
  · rw [l14h_collinear_iff]; norm_num
  · simp only [Complex.dist_eq_re_im]
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    simp
    constructor
    · rintro ⟨h1, h2, -⟩
      apply Complex.ext <;> simp <;> nlinarith
    · rintro rfl; norm_num

/-- **Witness for the pencil.** For the circles `(0, 1)`, `(4, 1)` and members `s = 0`,
`t = 1/2`, the common radical axis contains `2` but not `0`. -/
theorem l14w_pencil_radicalAxis :
    ∃ (O₁ O₂ : ℂ) (R₁ R₂ s t : ℝ), s ≠ t ∧
      (2 : ℂ) ∈ {P : ℂ | dist P O₁ ^ 2 - R₁ ^ 2 = dist P O₂ ^ 2 - R₂ ^ 2} ∧
      (0 : ℂ) ∉ {P : ℂ | dist P O₁ ^ 2 - R₁ ^ 2 = dist P O₂ ^ 2 - R₂ ^ 2} := by
  refine ⟨0, 4, 1, 1, 0, 1 / 2, by norm_num, ?_, ?_⟩
  · show _ = _
    rw [l14h_dist (d := 2) (by norm_num) (by norm_num), l14h_dist (d := 2) (by norm_num) (by norm_num)]
  · intro h
    have h' : dist (0 : ℂ) 0 ^ 2 - 1 ^ 2 = dist (0 : ℂ) 4 ^ 2 - 1 ^ 2 := h
    rw [l14h_dist (d := 0) (by norm_num) (by norm_num),
      l14h_dist (d := 4) (by norm_num) (by norm_num)] at h'
    norm_num at h'

/-- **Witness for orthogonal circles.** The circles `(0, 3)` and `(5, 4)` are orthogonal: they
meet at `X = (9 + 12i)/5` with perpendicular radii, and `dist² = 25 = 3² + 4²`. -/
theorem l14w_isOrthogonal_iff :
    ∃ (O₁ O₂ X : ℂ) (R₁ R₂ : ℝ), 0 < R₁ ∧ 0 < R₂ ∧
      (dist X O₁ = R₁ ∧ dist X O₂ = R₂ ∧ ⟪X - O₁, X - O₂⟫ = 0) ∧
      dist O₁ O₂ ^ 2 - R₂ ^ 2 = R₁ ^ 2 := by
  refine ⟨0, 5, ⟨9/5, 12/5⟩, 3, 4, by norm_num, by norm_num,
    ⟨l14h_dist (by norm_num) (by norm_num), l14h_dist (by norm_num) (by norm_num), ?_⟩, ?_⟩
  · rw [l14h_inner]; norm_num
  · rw [l14h_dist (d := 5) (by norm_num) (by norm_num)]; norm_num

/-- **Witness for Johnson.** Three circles of radius `5` through `H = 0` with centres `3 + 4i`,
`-3 + 4i`, `-5i`; the second intersections `-3 - i`, `3 - i`, `8i` are pairwise distinct (in
fact non-collinear) and lie on the circle of radius `5` about `3i`. -/
theorem l14w_johnson_circle :
    ∃ (H O₁ O₂ O₃ : ℂ) (R : ℝ), dist H O₁ = R ∧ dist H O₂ = R ∧ dist H O₃ = R ∧ 0 < R ∧
      ¬ Collinear ℝ ({O₂ + O₃ - H, O₃ + O₁ - H, O₁ + O₂ - H} : Set ℂ) ∧
      O₁ + O₂ + O₃ - (2 : ℝ) • H = ⟨0, 3⟩ := by
  refine ⟨0, ⟨3, 4⟩, ⟨-3, 4⟩, ⟨0, -5⟩, 5, l14h_dist (by norm_num) (by norm_num),
    l14h_dist (by norm_num) (by norm_num), l14h_dist (by norm_num) (by norm_num), by norm_num,
    ?_, ?_⟩
  · rw [l14h_collinear_iff]; norm_num
  · apply Complex.ext <;> norm_num

/-- **Witness for Johnson (Mathlib triangle).** The same configuration gives an affinely
independent triangle; its circumcentre is `3i` and its orthocentre `0`. -/
theorem l14w_johnson_orthocenter_eq :
    ∃ (H O₁ O₂ O₃ : ℂ) (R : ℝ), dist H O₁ = R ∧ dist H O₂ = R ∧ dist H O₃ = R ∧ 0 < R ∧
      AffineIndependent ℝ ![O₂ + O₃ - H, O₃ + O₁ - H, O₁ + O₂ - H] ∧
      O₁ + O₂ + O₃ - (2 : ℝ) • H = ⟨0, 3⟩ := by
  obtain ⟨H, O₁, O₂, O₃, R, h1, h2, h3, hR, hn, hJ⟩ := l14w_johnson_circle
  exact ⟨H, O₁, O₂, O₃, R, h1, h2, h3, hR, affineIndependent_iff_not_collinear_set.2 hn, hJ⟩

/-- The witness triangle and the feet of the perpendiculars from `0`, `4 - 3i`, `-5i`. -/
theorem l14h_feet :
    let A : ℂ := 5; let B : ℂ := ⟨0, 5⟩; let C : ℂ := ⟨-3, -4⟩
    (orthogonalProjection line[ℝ, B, C] (0 : ℂ) : ℂ) = ⟨-3/2, 1/2⟩ ∧
    (orthogonalProjection line[ℝ, C, A] (0 : ℂ) : ℂ) = ⟨1, -2⟩ ∧
    (orthogonalProjection line[ℝ, A, B] (0 : ℂ) : ℂ) = ⟨5/2, 5/2⟩ ∧
    (orthogonalProjection line[ℝ, B, C] (⟨4, -3⟩ : ℂ) : ℂ) = ⟨-2, -1⟩ ∧
    (orthogonalProjection line[ℝ, C, A] (⟨4, -3⟩ : ℂ) : ℂ) = ⟨3, -1⟩ ∧
    (orthogonalProjection line[ℝ, A, B] (⟨4, -3⟩ : ℂ) : ℂ) = ⟨6, -1⟩ ∧
    reflection line[ℝ, B, C] (⟨0, -5⟩ : ℂ) = ⟨-6, -3⟩ ∧
    reflection line[ℝ, C, A] (⟨0, -5⟩ : ℂ) = ⟨-2, -1⟩ ∧
    reflection line[ℝ, A, B] (⟨0, -5⟩ : ℂ) = ⟨10, 5⟩ := by
  intro A B C
  refine ⟨l14h_foot (1/2) ?_ ?_, l14h_foot (1/2) ?_ ?_, l14h_foot (1/2) ?_ ?_,
    l14h_foot (2/3) ?_ ?_, l14h_foot (3/4) ?_ ?_, l14h_foot (-1/5) ?_ ?_,
    (l14h_reflection (q := ⟨-3, -4⟩) 1 ?_ ?_).trans ?_,
    (l14h_reflection (q := ⟨-1, -3⟩) (1/4) ?_ ?_).trans ?_,
    (l14h_reflection (q := 5) 0 ?_ ?_).trans ?_⟩
  all_goals first
    | (apply Complex.ext <;> norm_num [A, B, C])
    | norm_num [A, B, C]

/-- **Witness for Simson–Wallace.** For the triangle `5, 5i, -3 - 4i` on `|z| = 5`, the point
`4 - 3i` on the circle has collinear feet `-2 - i, 3 - i, 6 - i` (pairwise distinct), while the
centre `0` (off the circle) has non-collinear feet: both directions of the `iff` are exercised. -/
theorem l14w_simson_wallace :
    ∃ (A B C O : ℂ) (R : ℝ), dist A O = R ∧ dist B O = R ∧ dist C O = R ∧
      ¬ Collinear ℝ ({A, B, C} : Set ℂ) ∧
      dist (⟨4, -3⟩ : ℂ) O = R ∧
      Collinear ℝ ({(orthogonalProjection line[ℝ, B, C] (⟨4, -3⟩ : ℂ) : ℂ),
        (orthogonalProjection line[ℝ, C, A] (⟨4, -3⟩ : ℂ) : ℂ),
        (orthogonalProjection line[ℝ, A, B] (⟨4, -3⟩ : ℂ) : ℂ)} : Set ℂ) ∧
      (orthogonalProjection line[ℝ, B, C] (⟨4, -3⟩ : ℂ) : ℂ) ≠
        (orthogonalProjection line[ℝ, C, A] (⟨4, -3⟩ : ℂ) : ℂ) ∧
      dist (0 : ℂ) O ≠ R ∧
      ¬ Collinear ℝ ({(orthogonalProjection line[ℝ, B, C] (0 : ℂ) : ℂ),
        (orthogonalProjection line[ℝ, C, A] (0 : ℂ) : ℂ),
        (orthogonalProjection line[ℝ, A, B] (0 : ℂ) : ℂ)} : Set ℂ) := by
  obtain ⟨f1, f2, f3, g1, g2, g3, -⟩ := l14h_feet
  refine ⟨5, ⟨0, 5⟩, ⟨-3, -4⟩, 0, 5, l14h_dist (by norm_num) (by norm_num),
    l14h_dist (by norm_num) (by norm_num), l14h_dist (by norm_num) (by norm_num), ?_,
    l14h_dist (by norm_num) (by norm_num), ?_, ?_, ?_, ?_⟩
  · rw [l14h_collinear_iff]; norm_num
  · rw [g1, g2, g3, l14h_collinear_iff]; norm_num
  · rw [g1, g2]; intro h; have := congrArg Complex.re h; norm_num at this
  · rw [dist_self]; norm_num
  · rw [f1, f2, f3, l14h_collinear_iff]; norm_num

/-- **Witness for the Simson determinant.** For `P = 0` (the centre) both sides equal `1500`. -/
theorem l14w_simson_det_eq_circumcircle_power :
    ∃ (A B C O P : ℂ) (R : ℝ), dist A O = R ∧ dist B O = R ∧ dist C O = R ∧ A ≠ B ∧ B ≠ C ∧
      C ≠ A ∧
      -(⟪Complex.orthonormalBasisOneI 0, B - A⟫ * ⟪Complex.orthonormalBasisOneI 1, C - A⟫ -
        ⟪Complex.orthonormalBasisOneI 1, B - A⟫ * ⟪Complex.orthonormalBasisOneI 0, C - A⟫) *
        (dist P O ^ 2 - R ^ 2) = 1500 := by
  refine ⟨5, ⟨0, 5⟩, ⟨-3, -4⟩, 0, 0, 5, l14h_dist (by norm_num) (by norm_num),
    l14h_dist (by norm_num) (by norm_num), l14h_dist (by norm_num) (by norm_num), ?_, ?_, ?_, ?_⟩
  · intro h; have := congrArg Complex.im h; norm_num at this
  · intro h; have := congrArg Complex.re h; norm_num at this
  · intro h; have := congrArg Complex.re h; norm_num at this
  · simp [Complex.coe_orthonormalBasisOneI, Complex.inner]; norm_num

/-- **Witness for the Steiner line.** For the triangle above and `P = -5i` on the circle, the
four points `2 + i` (orthocentre), `-6 - 3i`, `-2 - i`, `10 + 5i` are pairwise distinct. -/
theorem l14w_steiner_line :
    ∃ (A B C O P : ℂ) (R : ℝ), dist A O = R ∧ dist B O = R ∧ dist C O = R ∧ dist P O = R ∧
      A ≠ B ∧ B ≠ C ∧ C ≠ A ∧
      A + B + C - (2 : ℝ) • O = ⟨2, 1⟩ ∧ reflection line[ℝ, B, C] P = ⟨-6, -3⟩ ∧
      reflection line[ℝ, C, A] P = ⟨-2, -1⟩ ∧ reflection line[ℝ, A, B] P = ⟨10, 5⟩ := by
  obtain ⟨-, -, -, -, -, -, r1, r2, r3⟩ := l14h_feet
  refine ⟨5, ⟨0, 5⟩, ⟨-3, -4⟩, 0, ⟨0, -5⟩, 5, l14h_dist (by norm_num) (by norm_num),
    l14h_dist (by norm_num) (by norm_num), l14h_dist (by norm_num) (by norm_num),
    l14h_dist (by norm_num) (by norm_num), ?_, ?_, ?_, ?_, r1, r2, r3⟩
  · intro h; have := congrArg Complex.im h; norm_num at this
  · intro h; have := congrArg Complex.re h; norm_num at this
  · intro h; have := congrArg Complex.re h; norm_num at this
  · apply Complex.ext <;> norm_num

end Witnesses

end CircleSystems
