import ErdosProblems.Erdos633b.CornerCoordinates
import Mathlib.Tactic.Module

/-! Relative barycentric coordinates at a point in an outer open side.
Every inward ray is a nonnegative transverse combination of the boundary ray. -/

namespace Erdos633b.Triangle

theorem relative_barycentric_sum (T : Triangle) (p q : Plane) :
    (∑ j : Fin 3, T.coord j q • (T.points j - p)) = q - p := by
  have hsum : (∑ j : Fin 3, T.coord j q) = 1 := T.affineBasis.sum_coord_apply_eq_one q
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hsum, one_smul, T.reconstruct_sum]

theorem relative_barycentric_cyclic (T : Triangle) (i : Fin 3) (p q : Plane) :
    q - p = T.coord i q • (T.points i - p) +
      T.coord (i + 1) q • (T.points (i + 1) - p) +
      T.coord (i + 2) q • (T.points (i + 2) - p) := by
  have hc (f : Fin 3 → Plane) (k : Fin 3) :
      (∑ j, f j) = f k + f (k + 1) + f (k + 2) := by
    rw [Fin.sum_univ_three]
    fin_cases k
    · rfl
    · change f 0 + f 1 + f 2 = f 1 + f 2 + f 0
      abel
    · change f 0 + f 1 + f 2 = f 2 + f 0 + f 1
      abel
  rw [← T.relative_barycentric_sum p q, hc (fun j => T.coord j q • (T.points j - p)) i]

theorem boundary_opposite_ray (T : Triangle) (i : Fin 3) {p : Plane}
    (hp : p ∈ T.openEdge i) :
    T.points (i + 2) - p = -(T.coord (i + 1) p / T.coord (i + 2) p) •
      (T.points (i + 1) - p) := by
  have ht := hp.2 (i + 2) ((by decide : ∀ i : Fin 3, i + 2 ≠ i) i)
  have he := T.relative_barycentric_cyclic i p p
  rw [sub_self, hp.1, zero_smul, zero_add] at he
  have hs : T.coord (i + 2) p • (T.points (i + 2) - p) =
      -(T.coord (i + 1) p) • (T.points (i + 1) - p) := by
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_right he.symm
  calc
    T.points (i + 2) - p =
        (T.coord (i + 2) p)⁻¹ • (T.coord (i + 2) p • (T.points (i + 2) - p)) := by
      rw [smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
    _ = _ := by rw [hs, smul_smul]; congr 1; ring

theorem boundary_relative_coordinates (T : Triangle) (i : Fin 3) {p : Plane}
    (hp : p ∈ T.openEdge i) (q : Plane) :
    q - p =
      (T.coord (i + 1) q - T.coord (i + 2) q *
        (T.coord (i + 1) p / T.coord (i + 2) p)) • (T.points (i + 1) - p) +
      T.coord i q • (T.points i - p) := by
  rw [T.relative_barycentric_cyclic i p q, T.boundary_opposite_ray i hp]
  module

theorem boundary_ray_ne_zero (T : Triangle) (i : Fin 3) {p : Plane}
    (hp : p ∈ T.openEdge i) (j : Fin 3) : T.points j - p ≠ 0 := by
  intro hz
  have he : T.points j = p := sub_eq_zero.mp hz
  have hj : T.points j ∈ T.openEdge i := he.symm ▸ hp
  obtain ⟨k, hki, hkj⟩ := (by decide : ∀ i j : Fin 3, ∃ k, k ≠ i ∧ k ≠ j) i j
  have hk := hj.2 k hki
  rw [T.coord_vertex, if_neg hkj] at hk
  exact lt_irrefl _ hk

end Erdos633b.Triangle
