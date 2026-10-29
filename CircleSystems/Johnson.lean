import CircleSystems.Coord

/-!
# Johnson's three-circle theorem

Three circles of the same radius `R` with centers `O₁, O₂, O₃` pass through a common point `H`.
The circles with centers `O₂, O₃` meet again at `A = O₂ + O₃ − H` (the reflection of `H` in the
midpoint of `O₂O₃`), and similarly `B = O₃ + O₁ − H`, `C = O₁ + O₂ − H`.

* `johnson_mem_circles`: `A` lies on the circles about `O₂` and `O₃` (and similarly for `B`, `C`).
* `johnson_circle` (**Johnson's theorem**): `A, B, C` lie on the circle of radius `R` centered at
  `J = O₁ + O₂ + O₃ − 2 H`.
* `johnson_orthocenter`: `⟪A − H, B − C⟫ = ⟪B − H, C − A⟫ = ⟪C − H, A − B⟫ = 0`;
  `johnson_orthocenter_eq`: if `A, B, C` are affinely independent, `H` is the orthocenter of the
  triangle `ABC` (Mathlib's `Affine.Simplex.orthocenter`).
* `johnson_congruent`: the point reflection in `M = (O₁ + O₂ + O₃ − H) / 2` maps `O₁ ↦ A`,
  `O₂ ↦ B`, `O₃ ↦ C` (and `H ↦ J`), so `△O₁O₂O₃` and `△ABC` are congruent (Mathlib's `Congruent`).
-/

open Module
open scoped RealInnerProductSpace

namespace CircleSystems

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

section Johnson

variable {H O₁ O₂ O₃ : V} {R : ℝ}

omit [InnerProductSpace ℝ V] in
/-- The second intersection `O₂ + O₃ − H` lies on both circles. -/
theorem johnson_mem_circles (h₂ : dist H O₂ = R) (h₃ : dist H O₃ = R) :
    dist (O₂ + O₃ - H) O₂ = R ∧ dist (O₂ + O₃ - H) O₃ = R := by
  rw [dist_eq_norm, dist_eq_norm] at *
  constructor
  · rw [show O₂ + O₃ - H - O₂ = -(H - O₃) by abel, norm_neg, h₃]
  · rw [show O₂ + O₃ - H - O₃ = -(H - O₂) by abel, norm_neg, h₂]

/-- **Johnson's three-circle theorem.** The three other pairwise intersections lie on a circle of
the same radius `R`, centered at `O₁ + O₂ + O₃ − 2 H`. -/
theorem johnson_circle (h₁ : dist H O₁ = R) (h₂ : dist H O₂ = R) (h₃ : dist H O₃ = R) :
    dist (O₂ + O₃ - H) (O₁ + O₂ + O₃ - (2 : ℝ) • H) = R ∧
    dist (O₃ + O₁ - H) (O₁ + O₂ + O₃ - (2 : ℝ) • H) = R ∧
    dist (O₁ + O₂ - H) (O₁ + O₂ + O₃ - (2 : ℝ) • H) = R := by
  rw [dist_eq_norm] at h₁ h₂ h₃
  refine ⟨?_, ?_, ?_⟩ <;> rw [dist_eq_norm, two_smul]
  · rw [show O₂ + O₃ - H - (O₁ + O₂ + O₃ - (H + H)) = H - O₁ by abel, h₁]
  · rw [show O₃ + O₁ - H - (O₁ + O₂ + O₃ - (H + H)) = H - O₂ by abel, h₂]
  · rw [show O₁ + O₂ - H - (O₁ + O₂ + O₃ - (H + H)) = H - O₃ by abel, h₃]

/-- `H` lies on the three altitudes of `ABC`: `AH ⟂ BC`, `BH ⟂ CA`, `CH ⟂ AB`. -/
theorem johnson_orthocenter (h₁ : dist H O₁ = R) (h₂ : dist H O₂ = R) (h₃ : dist H O₃ = R) :
    ⟪(O₂ + O₃ - H) - H, (O₃ + O₁ - H) - (O₁ + O₂ - H)⟫ = 0 ∧
    ⟪(O₃ + O₁ - H) - H, (O₁ + O₂ - H) - (O₂ + O₃ - H)⟫ = 0 ∧
    ⟪(O₁ + O₂ - H) - H, (O₂ + O₃ - H) - (O₃ + O₁ - H)⟫ = 0 := by
  have key : ∀ X Y : V, ‖H - X‖ = R → ‖H - Y‖ = R → ⟪(X + Y - H) - H, Y - X⟫ = 0 := by
    intro X Y hX hY
    have e1 : (X + Y - H) - H = -((H - X) + (H - Y)) := by abel
    have e2 : Y - X = (H - X) - (H - Y) := by abel
    rw [e1, e2]
    generalize H - X = u at hX ⊢
    generalize H - Y = v at hY ⊢
    rw [inner_neg_left, inner_add_left, inner_sub_right, inner_sub_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm u v, hX, hY]
    ring
  rw [dist_eq_norm] at h₁ h₂ h₃
  refine ⟨?_, ?_, ?_⟩
  · rw [show (O₃ + O₁ - H) - (O₁ + O₂ - H) = O₃ - O₂ by abel]; exact key _ _ h₂ h₃
  · rw [show (O₁ + O₂ - H) - (O₂ + O₃ - H) = O₁ - O₃ by abel, add_comm O₃ O₁]
    have := key _ _ h₁ h₃
    rw [add_comm O₁ O₃, ← neg_sub O₃ O₁, inner_neg_right, neg_eq_zero] at *
    exact this
  · rw [show (O₂ + O₃ - H) - (O₃ + O₁ - H) = O₂ - O₁ by abel]; exact key _ _ h₁ h₂

/-- In the plane, if `A, B, C` are affinely independent, `H` is the orthocenter of the triangle
`ABC` (Mathlib's `Affine.Simplex.orthocenter`); `J` is its circumcenter. -/
theorem johnson_orthocenter_eq [Fact (finrank ℝ V = 2)] (h₁ : dist H O₁ = R)
    (h₂ : dist H O₂ = R) (h₃ : dist H O₃ = R)
    (hind : AffineIndependent ℝ ![O₂ + O₃ - H, O₃ + O₁ - H, O₁ + O₂ - H]) :
    (⟨_, hind⟩ : Affine.Triangle ℝ V).circumcenter = O₁ + O₂ + O₃ - (2 : ℝ) • H ∧
      Affine.Triangle.orthocenter (⟨_, hind⟩ : Affine.Triangle ℝ V) = H := by
  have : FiniteDimensional ℝ V := .of_fact_finrank_eq_two
  set t : Affine.Triangle ℝ V := ⟨_, hind⟩
  have htop : affineSpan ℝ (Set.range t.points) = ⊤ :=
    t.independent.affineSpan_eq_top_iff_card_eq_finrank_add_one.2
      (by rw [Fintype.card_fin, (Fact.out : finrank ℝ V = 2)])
  obtain ⟨hA, hB, hC⟩ := johnson_circle h₁ h₂ h₃
  have hc : O₁ + O₂ + O₃ - (2 : ℝ) • H = t.circumcenter := by
    refine t.eq_circumcenter_of_dist_eq (by rw [htop]; exact AffineSubspace.mem_top _ _ _)
      (r := R) fun i => ?_
    fin_cases i
    · exact hA
    · exact hB
    · exact hC
  refine ⟨hc.symm, ?_⟩
  have hs := t.orthocenter_vsub_circumcenter_eq_sum_vsub
  rw [← hc, Fin.sum_univ_three, vsub_eq_sub] at hs
  simp only [t, vsub_eq_sub, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hs
  rw [← sub_eq_zero, ← sub_eq_zero.2 hs, two_smul]
  abel

/-- The point reflection in `M = (O₁ + O₂ + O₃ − H) / 2` maps each center `Oᵢ` to the
corresponding vertex of `ABC` and `H` to `J`. -/
theorem johnson_reflection (H O₁ O₂ O₃ : V) :
    let M : V := (1 / 2 : ℝ) • (O₁ + O₂ + O₃ - H)
    (2 : ℝ) • M - O₁ = O₂ + O₃ - H ∧ (2 : ℝ) • M - O₂ = O₃ + O₁ - H ∧
      (2 : ℝ) • M - O₃ = O₁ + O₂ - H ∧ (2 : ℝ) • M - H = O₁ + O₂ + O₃ - (2 : ℝ) • H := by
  intro M
  have hM : (2 : ℝ) • M = O₁ + O₂ + O₃ - H := by
    simp only [M, smul_smul]; norm_num
  rw [hM, two_smul]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> abel

omit [InnerProductSpace ℝ V] in
/-- `△O₁O₂O₃` and `△ABC` are congruent. -/
theorem johnson_congruent (H O₁ O₂ O₃ : V) :
    Congruent ![O₁, O₂, O₃] ![O₂ + O₃ - H, O₃ + O₁ - H, O₁ + O₂ - H] := by
  rw [congruent_iff_dist_eq]
  intro i j
  have key : ∀ X Y : V, dist ((O₁ + O₂ + O₃ - H) - X) ((O₁ + O₂ + O₃ - H) - Y) = dist X Y := by
    intro X Y; rw [dist_sub_left]
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] <;>
  first
  | simp only [dist_self]
  | (rw [← key]; congr 1 <;> abel)

end Johnson

end CircleSystems
