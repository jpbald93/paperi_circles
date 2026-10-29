import Mathlib

/-!
# Orthonormal coordinates in the plane

Points are vectors of a real inner product space `V`. For an orthonormal basis `b` of `V` indexed
by `Fin 2` (so `V` is a plane), `cx b v = ⟪b 0, v⟫` and `cy b v = ⟪b 1, v⟫` are the coordinates of
`v`, and `cross b u v = cx u · cy v − cy u · cx v` is the planar cross product. This file
translates inner products, norms, distances and `Collinear` into these coordinates.
-/

open Module
open scoped RealInnerProductSpace

namespace CircleSystems

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- First coordinate of `v` in the orthonormal basis `b`. -/
noncomputable def cx (b : OrthonormalBasis (Fin 2) ℝ V) (v : V) : ℝ := ⟪b 0, v⟫

/-- Second coordinate of `v` in the orthonormal basis `b`. -/
noncomputable def cy (b : OrthonormalBasis (Fin 2) ℝ V) (v : V) : ℝ := ⟪b 1, v⟫

/-- Cross product of `u` and `v` in the coordinates of `b`. -/
noncomputable def cross (b : OrthonormalBasis (Fin 2) ℝ V) (u v : V) : ℝ :=
  cx b u * cy b v - cy b u * cx b v

/-- A two-dimensional space has an orthonormal basis indexed by `Fin 2`. -/
theorem exists_basis [Fact (finrank ℝ V = 2)] : Nonempty (OrthonormalBasis (Fin 2) ℝ V) := by
  have : FiniteDimensional ℝ V := .of_fact_finrank_eq_two
  exact ⟨(stdOrthonormalBasis ℝ V).reindex (finCongr (Fact.out : finrank ℝ V = 2))⟩

variable (b : OrthonormalBasis (Fin 2) ℝ V)

@[simp] theorem cx_add (u v : V) : cx b (u + v) = cx b u + cx b v := inner_add_right _ _ _
@[simp] theorem cy_add (u v : V) : cy b (u + v) = cy b u + cy b v := inner_add_right _ _ _
@[simp] theorem cx_sub (u v : V) : cx b (u - v) = cx b u - cx b v := inner_sub_right _ _ _
@[simp] theorem cy_sub (u v : V) : cy b (u - v) = cy b u - cy b v := inner_sub_right _ _ _
@[simp] theorem cx_smul (r : ℝ) (u : V) : cx b (r • u) = r * cx b u := real_inner_smul_right _ _ _
@[simp] theorem cy_smul (r : ℝ) (u : V) : cy b (r • u) = r * cy b u := real_inner_smul_right _ _ _

@[simp] theorem cx_zero' : cx b 0 = 0 := inner_zero_right _
@[simp] theorem cy_zero' : cy b 0 = 0 := inner_zero_right _

theorem cx_b0 : cx b (b 0) = 1 := by
  rw [cx, real_inner_self_eq_norm_sq, b.orthonormal.1 0, one_pow]
theorem cy_b0 : cy b (b 0) = 0 := b.orthonormal.2 (by decide)
theorem cx_b1 : cx b (b 1) = 0 := b.orthonormal.2 (by decide)
theorem cy_b1 : cy b (b 1) = 1 := by
  rw [cy, real_inner_self_eq_norm_sq, b.orthonormal.1 1, one_pow]

/-- Every vector is the combination of the basis vectors with its coordinates. -/
theorem eq_coord (v : V) : v = cx b v • b 0 + cy b v • b 1 := by
  have h := b.sum_repr' v
  rw [Fin.sum_univ_two] at h
  exact h.symm

/-- Two vectors with the same coordinates are equal. -/
theorem ext_coord {u v : V} (h0 : cx b u = cx b v) (h1 : cy b u = cy b v) : u = v := by
  rw [eq_coord b u, eq_coord b v, h0, h1]

theorem inner_coord (u v : V) : ⟪u, v⟫ = cx b u * cx b v + cy b u * cy b v := by
  have h := b.sum_inner_mul_inner u v
  rw [Fin.sum_univ_two] at h
  rw [← h, cx, cy, real_inner_comm u (b 0), real_inner_comm u (b 1)]
  rfl

theorem norm_sq_coord (v : V) : ‖v‖ ^ 2 = cx b v ^ 2 + cy b v ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_coord]; ring

theorem dist_sq_coord (X Y : V) : dist X Y ^ 2 = (cx b X - cx b Y) ^ 2 + (cy b X - cy b Y) ^ 2 := by
  rw [dist_eq_norm, norm_sq_coord, cx_sub, cy_sub]

/-- If `u ≠ 0` and `u × v = 0`, then `v` is a multiple of `u`. -/
theorem eq_smul_of_cross_eq_zero {u v : V} (hu : u ≠ 0) (h : cross b u v = 0) :
    ∃ k : ℝ, v = k • u := by
  have hn : ‖u‖ ^ 2 ≠ 0 := by positivity
  have hn' : cx b u ^ 2 + cy b u ^ 2 ≠ 0 := by rwa [norm_sq_coord] at hn
  unfold cross at h
  refine ⟨(cx b u * cx b v + cy b u * cy b v) / (cx b u ^ 2 + cy b u ^ 2), ext_coord b ?_ ?_⟩
  · rw [cx_smul]; field_simp; linear_combination (-(cy b u)) * h
  · rw [cy_smul]; field_simp; linear_combination (cx b u) * h

/-- Points of the form `k • u + X` are collinear with `X`. -/
theorem collinear_of_forall_smul {s : Set V} {X u : V} (hX : X ∈ s)
    (h : ∀ p ∈ s, ∃ k : ℝ, p - X = k • u) : Collinear ℝ s := by
  refine (collinear_iff_of_mem hX).2 ⟨u, fun p hp => ?_⟩
  obtain ⟨k, hk⟩ := h p hp
  exact ⟨k, by rw [vadd_eq_add, ← hk, sub_add_cancel]⟩

/-- Four points `X, Y, Z, W` whose difference vectors from `X` have pairwise zero cross products
are collinear. -/
theorem collinear_four_of_cross {X Y Z W : V} (h1 : cross b (Y - X) (Z - X) = 0)
    (h2 : cross b (Y - X) (W - X) = 0) (h3 : cross b (Z - X) (W - X) = 0) :
    Collinear ℝ ({X, Y, Z, W} : Set V) := by
  have hX : X ∈ ({X, Y, Z, W} : Set V) := Set.mem_insert _ _
  by_cases hY : Y - X = 0
  · by_cases hZ : Z - X = 0
    · refine collinear_of_forall_smul hX (u := W - X) fun p hp => ?_
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨0, by simpa using hY⟩
      · exact ⟨0, by simpa using hZ⟩
      · exact ⟨1, by simp⟩
    · obtain ⟨m, hm⟩ := eq_smul_of_cross_eq_zero b hZ h3
      refine collinear_of_forall_smul hX (u := Z - X) fun p hp => ?_
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨0, by simpa using hY⟩
      · exact ⟨1, by simp⟩
      · exact ⟨m, hm⟩
  · obtain ⟨k, hk⟩ := eq_smul_of_cross_eq_zero b hY h1
    obtain ⟨m, hm⟩ := eq_smul_of_cross_eq_zero b hY h2
    refine collinear_of_forall_smul hX (u := Y - X) fun p hp => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · exact ⟨k, hk⟩
    · exact ⟨m, hm⟩

/-- `Collinear ℝ {X, Y, Z} ↔ (Y − X) × (Z − X) = 0`. -/
theorem collinear_iff_cross {X Y Z : V} :
    Collinear ℝ ({X, Y, Z} : Set V) ↔ cross b (Y - X) (Z - X) = 0 := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := (collinear_iff_of_mem (Set.mem_insert X _)).1 h
    obtain ⟨r, hr⟩ := hv Y (by simp)
    obtain ⟨s, hs⟩ := hv Z (by simp)
    rw [vadd_eq_add] at hr hs
    rw [hr, hs, add_sub_cancel_right, add_sub_cancel_right, cross, cx_smul, cy_smul, cx_smul,
      cy_smul]
    ring
  · intro h
    have e : ({X, Y, Z} : Set V) = {X, Y, Z, Z} := by ext; simp
    rw [e]
    exact collinear_four_of_cross b h h (by rw [cross]; ring)

end CircleSystems
