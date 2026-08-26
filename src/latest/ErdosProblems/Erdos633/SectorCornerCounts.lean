import ErdosProblems.Erdos633.LocalConeIsometry
import ErdosProblems.Erdos633.ActualCornerCounts

/-!
# Local sector identities with actual tile-corner counts

At an outer corner every incident tile has a corner there. Isometry
invariance and sector additivity therefore give the weighted corner-count
identity directly from the geometric tiling. The separate identification
of sector area with half the Euclidean angle is not assumed here.
-/

namespace Erdos633

open scoped BigOperators

theorem CongruentTiling.labelledTile_vertexSectorArea {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (i : Fin N) (k : Fin 3) :
    (T.labelledTile i).localSectorArea ((T.labelledTile i).vertex k) =
      R.localSectorArea (R.vertex k) := by
  change (R.mapIsometry (T.tileIsometry i)).localSectorArea
      ((R.mapIsometry (T.tileIsometry i)).vertex k) = _
  rw [R.vertex_mapIsometry]
  exact R.localSectorArea_mapIsometry (T.tileIsometry i) (R.vertex k)
    (R.vertex_mem_carrier k)

open Classical in
theorem CongruentTiling.outer_sector_contribution {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (j : Fin 3) (i : Fin N) :
    (∑ k : Fin 3, if (T.labelledTile i).vertex k = P.vertex j then
      R.localSectorArea (R.vertex k) else 0) =
      if P.vertex j ∈ (T.labelledTile i).carrier then
        (T.labelledTile i).localSectorArea (P.vertex j) else 0 := by
  classical
  by_cases hi : P.vertex j ∈ (T.labelledTile i).carrier
  · rw [if_pos hi]
    obtain ⟨k, hk⟩ := (T.labelledDissection.mem_tile_at_outer_vertex_iff j i).mp hi
    change (T.labelledTile i).vertex k = P.vertex j at hk
    rw [← hk]
    simp only [(T.labelledTile i).vertex_injective.eq_iff]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact (T.labelledTile_vertexSectorArea i k).symm
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro k _
    apply if_neg
    intro hk
    apply hi
    rw [← hk]
    exact (T.labelledTile i).vertex_mem_carrier k

theorem CongruentTiling.outer_sector_count_identity {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (j : Fin 3) :
    P.localSectorArea (P.vertex j) =
      ∑ k : Fin 3, (T.cornerCount (P.vertex j) k : ℝ) *
        R.localSectorArea (R.vertex k) := by
  classical
  let s : Finset (Fin N) := Finset.univ.filter
    (fun i => P.vertex j ∈ (T.labelledTile i).carrier)
  have hs (i : Fin N) : i ∈ s ↔ P.vertex j ∈ (T.labelledTile i).carrier := by
    simp [s]
  calc
    _ = ∑ i : {i : Fin N // P.vertex j ∈ (T.labelledTile i).carrier},
        (T.labelledTile i).localSectorArea (P.vertex j) :=
      T.labelledDissection.localSectorArea_eq_sum (P.vertex j) (P.vertex_mem_carrier j)
    _ = ∑ i ∈ s, (T.labelledTile i).localSectorArea (P.vertex j) :=
      (Finset.sum_subtype s hs
        (fun i : Fin N => (T.labelledTile i).localSectorArea (P.vertex j))).symm
    _ = ∑ i : Fin N, if P.vertex j ∈ (T.labelledTile i).carrier then
        (T.labelledTile i).localSectorArea (P.vertex j) else 0 := by
      exact Finset.sum_filter _ _
    _ = ∑ i : Fin N, ∑ k : Fin 3,
        if (T.labelledTile i).vertex k = P.vertex j then
          R.localSectorArea (R.vertex k) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      exact (T.outer_sector_contribution j i).symm
    _ = _ := (T.sum_cornerCount_mul (P.vertex j)
      (fun k => R.localSectorArea (R.vertex k))).symm

theorem CongruentTiling.outer_sector_total {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) :
    (∑ j : Fin 3, P.localSectorArea (P.vertex j)) =
      ∑ k : Fin 3, (T.outerCornerCount k : ℝ) * R.localSectorArea (R.vertex k) := by
  simp_rw [T.outer_sector_count_identity]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, ← Nat.cast_sum]
  rfl

end Erdos633
