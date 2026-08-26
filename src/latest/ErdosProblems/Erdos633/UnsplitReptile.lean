import ErdosProblems.Erdos633.ReptileStarMatrix
import ErdosProblems.Erdos633.CornerBoundaryEdges

/-!
# Three unsplit corners exclude a nonsquare reptiling

The negative eigenvalue excludes unchanged adjacent side labels at each
corner. Swapping at all three corners gives a three-cycle of sign reversals,
contradicting the maximum-ratio sign argument. No checkerboard coloring or
global planar-graph theorem is needed.
-/

namespace Erdos633

open scoped BigOperators

theorem natural_matrix_three_corner_obstruction
    (D : Fin 3 → Fin 3 → ℕ) (v : Fin 3 → ℝ) (x : ℝ) (N : ℕ)
    (hv : ∀ i, 0 < v i) (hx : 0 < x) (hsq : x ^ 2 = N) (hN : ¬ IsSquare N)
    (hpos : ∀ i, ∑ j : Fin 3, (D i j : ℝ) * v j = x * v i)
    (hA : (0 < D 1 1 ∧ 0 < D 2 2) ∨ (0 < D 1 2 ∧ 0 < D 2 1))
    (hB : (0 < D 0 0 ∧ 0 < D 2 2) ∨ (0 < D 0 2 ∧ 0 < D 2 0))
    (hC : (0 < D 0 0 ∧ 0 < D 1 1) ∨ (0 < D 0 1 ∧ 0 < D 1 0)) : False := by
  have hvne : v ≠ 0 := by intro h; exact (ne_of_gt (hv 0)) (congrFun h 0)
  obtain ⟨w, hw, hneg⟩ := natural_matrix_three_negative_eigenvector D N x hN hsq v hvne hpos
  have hzero := positive_negative_eigenvectors_two_zero_diagonals D v w x hv hw hx hpos hneg
  have hAswap := hA.resolve_left (fun h =>
    two_zero_diagonals_exclude_two_positive D hzero 1 2 (by decide) h.1 h.2)
  have hBswap := hB.resolve_left (fun h =>
    two_zero_diagonals_exclude_two_positive D hzero 0 2 (by decide) h.1 h.2)
  have hCswap := hC.resolve_left (fun h =>
    two_zero_diagonals_exclude_two_positive D hzero 0 1 (by decide) h.1 h.2)
  have hstar := star_matrix_zeros_of_eigenvectors D v w x hv hw hpos hneg
    hBswap.1 hAswap.1 hBswap.2 hAswap.2
  have hz := hstar.2.1
  omega

theorem CongruentTiling.three_corner_boundary_alternatives
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hcount : ∀ j k : Fin 3, T.cornerCount (P.vertex j) k = if j = k then 1 else 0) :
    ((0 < T.boundarySideCount 1 1 ∧ 0 < T.boundarySideCount 2 2) ∨
      (0 < T.boundarySideCount 1 2 ∧ 0 < T.boundarySideCount 2 1)) ∧
    ((0 < T.boundarySideCount 0 0 ∧ 0 < T.boundarySideCount 2 2) ∨
      (0 < T.boundarySideCount 0 2 ∧ 0 < T.boundarySideCount 2 0)) ∧
    ((0 < T.boundarySideCount 0 0 ∧ 0 < T.boundarySideCount 1 1) ∨
      (0 < T.boundarySideCount 0 1 ∧ 0 < T.boundarySideCount 1 0)) := by
  have hone (j : Fin 3) : T.cornerCount (P.vertex j) j = 1 := by rw [hcount]; simp
  have hzero (j k : Fin 3) (hkj : k ≠ j) : T.cornerCount (P.vertex j) k = 0 := by
    rw [hcount, if_neg hkj.symm]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨u, v, hu, hv, huv, hku, hlv⟩ := T.two_boundary_edges_at_single_corner 0 1 2
      (by decide) (by decide) (by decide) (hone 0) (hzero 0)
    have hcases : (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1) := by omega
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hku, hlv⟩
    · exact Or.inr ⟨hku, hlv⟩
  · obtain ⟨u, v, hu, hv, huv, hku, hlv⟩ := T.two_boundary_edges_at_single_corner 1 0 2
      (by decide) (by decide) (by decide) (hone 1) (hzero 1)
    have hcases : (u = 0 ∧ v = 2) ∨ (u = 2 ∧ v = 0) := by omega
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hku, hlv⟩
    · exact Or.inr ⟨hku, hlv⟩
  · obtain ⟨u, v, hu, hv, huv, hku, hlv⟩ := T.two_boundary_edges_at_single_corner 2 0 1
      (by decide) (by decide) (by decide) (hone 2) (hzero 2)
    have hcases : (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) := by omega
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hku, hlv⟩
    · exact Or.inr ⟨hku, hlv⟩

theorem CongruentTiling.unsplit_aligned_reptile_isSquare
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hA : P.angleA = R.angleA) (hB : P.angleB = R.angleB)
    (hcount : ∀ j k : Fin 3, T.cornerCount (P.vertex j) k = if j = k then 1 else 0) :
    IsSquare N := by
  by_contra hN
  obtain ⟨x, hx, hsq, _, hmatrix⟩ := T.aligned_reptile_scale hA hB
  obtain ⟨hcornerA, hcornerB, hcornerC⟩ := T.three_corner_boundary_alternatives hcount
  exact natural_matrix_three_corner_obstruction T.boundarySideCount R.sideLength x N
    R.sideLength_pos hx hsq hN hmatrix hcornerA hcornerB hcornerC

theorem CongruentTiling.aligned_corner_counts_of_all_outer_types
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hR : Function.Injective R.cornerAngle)
    (hangle : ∀ j : Fin 3, P.cornerAngle j = R.cornerAngle j)
    (hpos : ∀ k : Fin 3, 0 < T.outerCornerCount k) :
    ∀ j k : Fin 3, T.cornerCount (P.vertex j) k = if j = k then 1 else 0 := by
  obtain ⟨e, he⟩ := corner_matrix_is_permutation
    (fun j k => T.cornerCount (P.vertex j) k)
    (T.outer_counts_eq_one_of_all_pos hpos) T.outer_cornerCount_pos
  have heq (j : Fin 3) : e j = j := by
    apply hR
    have h := T.outer_angle_count_identity j
    simp_rw [he] at h
    simpa [ite_mul, hangle j] using h
  intro j k
  rw [he, heq]

theorem CongruentTiling.all_outer_types_aligned_reptile_isSquare
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hR : Function.Injective R.cornerAngle)
    (hangle : ∀ j : Fin 3, P.cornerAngle j = R.cornerAngle j)
    (hpos : ∀ k : Fin 3, 0 < T.outerCornerCount k) : IsSquare N := by
  exact T.unsplit_aligned_reptile_isSquare (hangle 0) (hangle 1)
    (T.aligned_corner_counts_of_all_outer_types hR hangle hpos)

end Erdos633
