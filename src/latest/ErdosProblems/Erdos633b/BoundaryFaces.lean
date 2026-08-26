import ErdosProblems.Erdos633b.BoundaryCoordinates

/-! Supporting faces of an arbitrary triangle are the convex hulls of their
zero vertices. In particular a tile meets an outer side in a whole face. -/

namespace Erdos633b.Triangle

theorem reconstruct_sum (T : Triangle) (p : Plane) :
    ∑ i : Fin 3, T.coord i p • T.points i = p :=
  T.affineBasis.linear_combination_coord_eq_self p

theorem affine_scalar_interpolation_sum (T : Triangle) (f : Plane →ᵃ[ℝ] ℝ)
    (p : Plane) : f p = ∑ i : Fin 3, f (T.points i) * T.coord i p := by
  simpa only [Fin.sum_univ_three] using T.affine_scalar_interpolation f p

theorem coord_zero_of_affine_zero (S : Triangle) (f : Plane →ᵃ[ℝ] ℝ)
    (hf : ∀ j, 0 ≤ f (S.points j)) {p : Plane} (hp : p ∈ S.support)
    (hfp : f p = 0) (j : Fin 3) (hj : f (S.points j) ≠ 0) :
    S.coord j p = 0 := by
  have hs : ∑ k : Fin 3, f (S.points k) * S.coord k p = 0 := by
    rw [← S.affine_scalar_interpolation_sum f, hfp]
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun k (_ : k ∈ (Finset.univ : Finset (Fin 3))) =>
      mul_nonneg (hf k) (S.coord_nonneg hp k))).mp hs j (Finset.mem_univ j)
  exact (mul_eq_zero.mp hz).resolve_left hj

theorem support_inter_affine_zero (S : Triangle) (f : Plane →ᵃ[ℝ] ℝ)
    (hf : ∀ j, 0 ≤ f (S.points j)) :
    S.support ∩ {p | f p = 0} =
      convexHull ℝ (S.points '' {j | f (S.points j) = 0}) := by
  classical
  apply Set.Subset.antisymm
  · rintro p ⟨hp, hfp⟩
    let I : Finset (Fin 3) := Finset.univ.filter (fun j => f (S.points j) = 0)
    have hw (j : Fin 3) (hj : j ∉ I) : S.coord j p = 0 := by
      apply S.coord_zero_of_affine_zero f hf hp hfp j
      simpa only [I, Finset.mem_filter, Finset.mem_univ, true_and] using hj
    have hs : ∑ j ∈ I, S.coord j p = 1 := by
      rw [Finset.sum_subset (Finset.subset_univ I) (fun j _ hj => hw j hj)]
      exact S.affineBasis.sum_coord_apply_eq_one p
    have hv : ∑ j ∈ I, S.coord j p • S.points j = p := by
      rw [Finset.sum_subset (Finset.subset_univ I)
        (fun j _ hj => by rw [hw j hj, zero_smul])]
      exact S.reconstruct_sum p
    rw [← hv]
    apply (convex_convexHull ℝ _).sum_mem (fun j _ => S.coord_nonneg hp j) hs
    intro j hj
    apply subset_convexHull ℝ _
    refine ⟨j, ?_, rfl⟩
    exact (Finset.mem_filter.mp hj).2
  · apply convexHull_min
    · rintro _ ⟨j, hj, rfl⟩
      exact ⟨S.vertex_mem_support j, hj⟩
    · exact S.support_convex.inter ((convex_singleton (0 : ℝ)).affine_preimage f)

/-- The closed edge opposite a vertex, defined by its supporting coordinate. -/
def edge (T : Triangle) (i : Fin 3) : Set Plane :=
  T.support ∩ {p | T.coord i p = 0}

theorem edge_eq_convexHull (T : Triangle) (i : Fin 3) :
    T.edge i = convexHull ℝ (T.points '' {j | j ≠ i}) := by
  rw [edge, T.support_inter_affine_zero (T.coord i)
    (fun j => T.coord_nonneg (T.vertex_mem_support j) i)]
  congr 2
  ext j
  simp [coord_vertex, eq_comm]

theorem edge_eq_segment (T : Triangle) (i : Fin 3) :
    T.edge i = segment ℝ (T.points (i + 1)) (T.points (i + 2)) := by
  rw [T.edge_eq_convexHull]
  have he : T.points '' {j | j ≠ i} = {T.points (i + 1), T.points (i + 2)} := by
    ext p
    constructor
    · rintro ⟨j, hj, rfl⟩
      have h : j = i + 1 ∨ j = i + 2 := by
        revert hj
        decide +revert
      rcases h with rfl | rfl <;> simp
    · intro hp
      rcases hp with hp | hp
      · exact ⟨i + 1, (by decide : ∀ i : Fin 3, i + 1 ≠ i) i, hp.symm⟩
      · exact ⟨i + 2, (by decide : ∀ i : Fin 3, i + 2 ≠ i) i, hp.symm⟩
  rw [he, convexHull_pair]

theorem support_inter_edge (T S : Triangle) (hST : S.support ⊆ T.support)
    (i : Fin 3) :
    S.support ∩ T.edge i =
      convexHull ℝ (S.points '' {j | T.coord i (S.points j) = 0}) := by
  have he : S.support ∩ T.edge i = S.support ∩ {p | T.coord i p = 0} := by
    ext p
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hST h.1, h.2⟩⟩
  rw [he]
  exact S.support_inter_affine_zero (T.coord i)
    (fun j => T.coord_nonneg (hST (S.vertex_mem_support j)) i)

theorem exists_vertex_coord_pos_of_subset (T S : Triangle)
    (hST : S.support ⊆ T.support) (i : Fin 3) :
    ∃ j, 0 < T.coord i (S.points j) := by
  by_contra h
  have hz (j : Fin 3) : T.coord i (S.points j) = 0 :=
    le_antisymm (not_lt.mp (fun hj => h ⟨j, hj⟩))
      (T.coord_nonneg (hST (S.vertex_mem_support j)) i)
  have he := S.affine_scalar_interpolation (T.coord i) (T.points i)
  simp only [hz, zero_mul, zero_add, T.coord_vertex, ite_true] at he
  norm_num at he

/-- All possible contacts with an outer side. Each nontrivial contact is a
complete edge of the smaller triangle, not merely a subsegment. -/
theorem support_inter_edge_cases (T S : Triangle) (hST : S.support ⊆ T.support)
    (i : Fin 3) :
    S.support ∩ T.edge i = ∅ ∨
      (∃ j, S.support ∩ T.edge i = {S.points j}) ∨
      ∃ j, S.support ∩ T.edge i = S.edge j := by
  obtain ⟨k, hk⟩ := T.exists_vertex_coord_pos_of_subset S hST i
  have he : S.points '' {j | T.coord i (S.points j) = 0} =
      (if T.coord i (S.points (k + 1)) = 0 then {S.points (k + 1)} else ∅) ∪
      (if T.coord i (S.points (k + 2)) = 0 then {S.points (k + 2)} else ∅) := by
    ext p
    constructor
    · rintro ⟨j, hj, rfl⟩
      change T.coord i (S.points j) = 0 at hj
      have hjk : j ≠ k := by
        intro h
        subst j
        exact hk.ne' hj
      have hj' : j = k + 1 ∨ j = k + 2 :=
        (by decide : ∀ k j : Fin 3, j ≠ k → j = k + 1 ∨ j = k + 2) k j hjk
      rcases hj' with rfl | rfl
      · simp [hj]
      · simp [hj]
    · intro hp
      rcases hp with hp | hp
      · split_ifs at hp with h
        · exact ⟨k + 1, h, (Set.mem_singleton_iff.mp hp).symm⟩
        · exact hp.elim
      · split_ifs at hp with h
        · exact ⟨k + 2, h, (Set.mem_singleton_iff.mp hp).symm⟩
        · exact hp.elim
  have hface := T.support_inter_edge S hST i
  rw [he] at hface
  by_cases h1 : T.coord i (S.points (k + 1)) = 0
  · by_cases h2 : T.coord i (S.points (k + 2)) = 0
    · right; right
      refine ⟨k, ?_⟩
      rw [hface, if_pos h1, if_pos h2, Set.singleton_union, convexHull_pair,
        S.edge_eq_segment]
    · right; left
      exact ⟨k + 1, by simpa only [if_pos h1, if_neg h2, Set.union_empty,
        convexHull_singleton] using hface⟩
  · by_cases h2 : T.coord i (S.points (k + 2)) = 0
    · right; left
      exact ⟨k + 2, by simpa only [if_neg h1, if_pos h2, Set.empty_union,
        convexHull_singleton] using hface⟩
    · left
      simpa only [if_neg h1, if_neg h2, Set.union_empty, convexHull_empty] using hface

end Erdos633b.Triangle
