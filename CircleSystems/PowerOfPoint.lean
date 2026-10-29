import CircleSystems.Coord

/-!
# Power of a point, radical axis, radical center

Points are vectors of a real inner product space `V`; a circle is given by its center `O : V` and
radius `R : ℝ`.

* `powPt P O R = dist(P, O)² − R²` is the power of `P` with respect to the circle `(O, R)`.
* `radicalAxis O₁ R₁ O₂ R₂ = {P | powPt P O₁ R₁ = powPt P O₂ R₂}`.
* `radicalAxis_eq_inner`: the radical axis is the level set `{P | ⟪P, O₁ − O₂⟫ = c}` of a linear
  functional; `radicalAxis_eq_mk'`: for `O₁ ≠ O₂` it is the affine hyperplane through a point `P₀`
  with direction `(ℝ ∙ (O₁ − O₂))ᗮ`, i.e. perpendicular to the line of centers.
* `radical_center_concurrent` (**Monge's radical center theorem**): in the plane, the three
  pairwise radical axes of three circles with non-collinear centers pass through exactly one
  common point.
-/

open Module
open scoped RealInnerProductSpace

namespace CircleSystems

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The power of the point `P` with respect to the circle with center `O` and radius `R`. -/
noncomputable def powPt (P O : V) (R : ℝ) : ℝ := dist P O ^ 2 - R ^ 2

/-- The radical axis of the circles `(O₁, R₁)` and `(O₂, R₂)`: the points of equal power. -/
def radicalAxis (O₁ : V) (R₁ : ℝ) (O₂ : V) (R₂ : ℝ) : Set V :=
  {P | powPt P O₁ R₁ = powPt P O₂ R₂}

theorem powPt_eq_inner (P O : V) (R : ℝ) :
    powPt P O R = ⟪P, P⟫ - 2 * ⟪P, O⟫ + ⟪O, O⟫ - R ^ 2 := by
  rw [powPt, dist_eq_norm, ← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    inner_sub_right, real_inner_comm O P]
  ring

omit [InnerProductSpace ℝ V] in
/-- A point lies on the circle iff its power is zero. -/
theorem powPt_eq_zero_iff {P O : V} {R : ℝ} (hR : 0 ≤ R) : powPt P O R = 0 ↔ dist P O = R := by
  rw [powPt, sub_eq_zero]
  exact ⟨fun h => (sq_eq_sq₀ dist_nonneg hR).1 h, fun h => by rw [h]⟩

/-- The difference of the powers with respect to two circles is an affine function of `P`. -/
theorem powPt_sub_powPt (P O₁ O₂ : V) (R₁ R₂ : ℝ) :
    powPt P O₁ R₁ - powPt P O₂ R₂ =
      -2 * ⟪P, O₁ - O₂⟫ + (⟪O₁, O₁⟫ - R₁ ^ 2 - (⟪O₂, O₂⟫ - R₂ ^ 2)) := by
  rw [powPt_eq_inner, powPt_eq_inner, inner_sub_right]; ring

/-- The constant of the radical axis: `P` is on it iff `⟪P, O₁ − O₂⟫ = radConst O₁ R₁ O₂ R₂`. -/
noncomputable def radConst (O₁ : V) (R₁ : ℝ) (O₂ : V) (R₂ : ℝ) : ℝ :=
  (⟪O₁, O₁⟫ - R₁ ^ 2 - (⟪O₂, O₂⟫ - R₂ ^ 2)) / 2

theorem mem_radicalAxis_iff {O₁ O₂ P : V} {R₁ R₂ : ℝ} :
    P ∈ radicalAxis O₁ R₁ O₂ R₂ ↔ ⟪P, O₁ - O₂⟫ = radConst O₁ R₁ O₂ R₂ := by
  have h := powPt_sub_powPt P O₁ O₂ R₁ R₂
  simp only [radicalAxis, Set.mem_ofPred_eq, radConst]
  constructor
  · intro e; rw [e, sub_self] at h; linarith
  · intro e; rw [e] at h; linarith

/-- The radical axis is a level set of the linear functional `P ↦ ⟪P, O₁ − O₂⟫`. -/
theorem radicalAxis_eq_inner (O₁ O₂ : V) (R₁ R₂ : ℝ) :
    radicalAxis O₁ R₁ O₂ R₂ = {P | ⟪P, O₁ - O₂⟫ = radConst O₁ R₁ O₂ R₂} := by
  ext P; exact mem_radicalAxis_iff

omit [InnerProductSpace ℝ V] in
/-- The radical axis is symmetric in the two circles. -/
theorem radicalAxis_comm (O₁ O₂ : V) (R₁ R₂ : ℝ) :
    radicalAxis O₁ R₁ O₂ R₂ = radicalAxis O₂ R₂ O₁ R₁ := by
  ext P; simp only [radicalAxis, Set.mem_ofPred_eq]; exact eq_comm

omit [InnerProductSpace ℝ V] in
/-- Common points of two circles lie on their radical axis. -/
theorem mem_radicalAxis_of_mem_circles {O₁ O₂ X : V} {R₁ R₂ : ℝ} (h₁ : dist X O₁ = R₁)
    (h₂ : dist X O₂ = R₂) : X ∈ radicalAxis O₁ R₁ O₂ R₂ := by
  simp only [radicalAxis, Set.mem_ofPred_eq, powPt, h₁, h₂, sub_self]

/-- Two points of the radical axis differ by a vector perpendicular to `O₁ − O₂`. -/
theorem inner_sub_eq_zero_of_mem_radicalAxis {O₁ O₂ P Q : V} {R₁ R₂ : ℝ}
    (hP : P ∈ radicalAxis O₁ R₁ O₂ R₂) (hQ : Q ∈ radicalAxis O₁ R₁ O₂ R₂) :
    ⟪P - Q, O₁ - O₂⟫ = 0 := by
  rw [mem_radicalAxis_iff] at hP hQ
  rw [inner_sub_left, hP, hQ, sub_self]

/-- A point of the radical axis of two circles with distinct centers. -/
noncomputable def radBase (O₁ : V) (R₁ : ℝ) (O₂ : V) (R₂ : ℝ) : V :=
  ((radConst O₁ R₁ O₂ R₂ - ⟪O₂, O₁ - O₂⟫) / ‖O₁ - O₂‖ ^ 2) • (O₁ - O₂) + O₂

theorem radBase_mem {O₁ O₂ : V} (R₁ R₂ : ℝ) (h : O₁ ≠ O₂) :
    radBase O₁ R₁ O₂ R₂ ∈ radicalAxis O₁ R₁ O₂ R₂ := by
  have hn : ‖O₁ - O₂‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 h)
  rw [mem_radicalAxis_iff, radBase, inner_add_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq]
  field_simp
  ring

/-- For distinct centers the radical axis is the affine hyperplane through `radBase` perpendicular
to `O₁ − O₂`. -/
theorem radicalAxis_eq_mk' {O₁ O₂ : V} (R₁ R₂ : ℝ) (h : O₁ ≠ O₂) :
    radicalAxis O₁ R₁ O₂ R₂ =
      (AffineSubspace.mk' (radBase O₁ R₁ O₂ R₂) (ℝ ∙ (O₁ - O₂))ᗮ : Set V) := by
  ext P
  have h0 := radBase_mem R₁ R₂ h
  rw [SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub,
    Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm]
  constructor
  · intro hP; exact inner_sub_eq_zero_of_mem_radicalAxis hP h0
  · intro hP
    rw [mem_radicalAxis_iff] at h0 ⊢
    rw [inner_sub_left, h0, sub_eq_zero] at hP
    exact hP

omit [InnerProductSpace ℝ V] in
/-- If `P` is on two of the three pairwise radical axes, it is on the third. -/
theorem mem_radicalAxis_trans {O₁ O₂ O₃ P : V} {R₁ R₂ R₃ : ℝ}
    (h₁₂ : P ∈ radicalAxis O₁ R₁ O₂ R₂) (h₂₃ : P ∈ radicalAxis O₂ R₂ O₃ R₃) :
    P ∈ radicalAxis O₃ R₃ O₁ R₁ := by
  simp only [radicalAxis, Set.mem_ofPred_eq] at *
  rw [h₁₂, h₂₃]

theorem powPt_coord (b : OrthonormalBasis (Fin 2) ℝ V) (P O : V) (R : ℝ) :
    powPt P O R = (cx b P - cx b O) ^ 2 + (cy b P - cy b O) ^ 2 - R ^ 2 := by
  rw [powPt, dist_sq_coord]

theorem cx_mk (b : OrthonormalBasis (Fin 2) ℝ V) (x y : ℝ) : cx b (x • b 0 + y • b 1) = x := by
  simp [cx_b0, cx_b1]

theorem cy_mk (b : OrthonormalBasis (Fin 2) ℝ V) (x y : ℝ) : cy b (x • b 0 + y • b 1) = y := by
  simp [cy_b0, cy_b1]

/-- **Monge's radical center theorem.** In the plane, if the centers of three circles are not
collinear, there is exactly one point lying on all three pairwise radical axes (the radical
center). -/
theorem radical_center_concurrent [Fact (finrank ℝ V = 2)] {O₁ O₂ O₃ : V} (R₁ R₂ R₃ : ℝ)
    (hO : ¬ Collinear ℝ ({O₁, O₂, O₃} : Set V)) :
    ∃! X : V, X ∈ radicalAxis O₁ R₁ O₂ R₂ ∧ X ∈ radicalAxis O₂ R₂ O₃ R₃ ∧
      X ∈ radicalAxis O₃ R₃ O₁ R₁ := by
  obtain ⟨b⟩ := exists_basis (V := V)
  rw [collinear_iff_cross b] at hO
  have key : ∀ X : V, (X ∈ radicalAxis O₁ R₁ O₂ R₂ ∧ X ∈ radicalAxis O₂ R₂ O₃ R₃) ↔
      (powPt X O₁ R₁ = powPt X O₂ R₂ ∧ powPt X O₁ R₁ = powPt X O₃ R₃) := by
    intro X
    simp only [radicalAxis, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h1.trans h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h1.symm.trans h2⟩
  simp only [cross, cx_sub, cy_sub] at hO
  have hd : (cx b O₂ - cx b O₁) * (cy b O₃ - cy b O₁) - (cy b O₂ - cy b O₁) * (cx b O₃ - cx b O₁)
      ≠ 0 := hO
  set u1 := cx b O₂ - cx b O₁
  set u2 := cy b O₂ - cy b O₁
  set w1 := cx b O₃ - cx b O₁
  set w2 := cy b O₃ - cy b O₁
  set k1 := (cx b O₂ ^ 2 + cy b O₂ ^ 2 - R₂ ^ 2) - (cx b O₁ ^ 2 + cy b O₁ ^ 2 - R₁ ^ 2)
  set k2 := (cx b O₃ ^ 2 + cy b O₃ ^ 2 - R₃ ^ 2) - (cx b O₁ ^ 2 + cy b O₁ ^ 2 - R₁ ^ 2)
  have lin : ∀ X : V, (powPt X O₁ R₁ = powPt X O₂ R₂ ∧ powPt X O₁ R₁ = powPt X O₃ R₃) ↔
      (2 * (u1 * cx b X + u2 * cy b X) = k1 ∧ 2 * (w1 * cx b X + w2 * cy b X) = k2) := by
    intro X
    simp only [powPt_coord b]
    constructor
    · rintro ⟨h1, h2⟩; constructor <;> [linear_combination h1; linear_combination h2]
    · rintro ⟨h1, h2⟩; constructor <;> [linear_combination h1; linear_combination h2]
  have hD : 2 * (u1 * w2 - u2 * w1) ≠ 0 := mul_ne_zero two_ne_zero hd
  set x := (k1 * w2 - k2 * u2) / (2 * (u1 * w2 - u2 * w1))
  set y := (u1 * k2 - w1 * k1) / (2 * (u1 * w2 - u2 * w1))
  have hx : x * (2 * (u1 * w2 - u2 * w1)) = k1 * w2 - k2 * u2 := div_mul_cancel₀ _ hD
  have hy : y * (2 * (u1 * w2 - u2 * w1)) = u1 * k2 - w1 * k1 := div_mul_cancel₀ _ hD
  have sol : 2 * (u1 * x + u2 * y) = k1 ∧ 2 * (w1 * x + w2 * y) = k2 := by
    constructor <;> apply mul_left_cancel₀ hD
    · linear_combination 2 * u1 * hx + 2 * u2 * hy
    · linear_combination 2 * w1 * hx + 2 * w2 * hy
  have hmem := (key (x • b 0 + y • b 1)).2 ((lin _).2 (by rw [cx_mk, cy_mk]; exact sol))
  refine ⟨x • b 0 + y • b 1, ⟨hmem.1, hmem.2, mem_radicalAxis_trans hmem.1 hmem.2⟩, ?_⟩
  rintro X ⟨h1, h2, -⟩
  obtain ⟨e1, e2⟩ := (lin X).1 ((key X).1 ⟨h1, h2⟩)
  apply ext_coord b
  · rw [cx_mk]; apply mul_right_cancel₀ hD
    linear_combination -hx + w2 * e1 - u2 * e2
  · rw [cy_mk]; apply mul_right_cancel₀ hD
    linear_combination -hy + u1 * e2 - w1 * e1

end CircleSystems
