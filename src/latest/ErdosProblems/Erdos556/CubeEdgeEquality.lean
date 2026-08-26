import ErdosProblems.Erdos556.CubeTilings

/-!
# Equality when no face has positive weight
-/

namespace Erdos556

open Finset

theorem IsCubeWeight.tiling_of_only_edges {w : CubeProfile → ℝ} (hw : IsCubeWeight w)
    (hedges : ∀ p, profileDimension p ≠ 1 → w p = 0) : IsCubeTiling w := by
  classical
  have hposdim (p : CubeProfile) (hp : 0 < w p) : profileDimension p = 1 := by
    by_contra h
    rw [hedges p h] at hp
    exact hp.false
  have hsum : (∑ p ∈ positiveEdgeProfiles w, w p) = 4 := by
    calc
      (∑ p ∈ positiveEdgeProfiles w, w p) = ∑ p, w p := by
        apply sum_subset (subset_univ _)
        intro p _ hp
        apply hw.eq_zero_of_not_pos
        intro hpos
        exact hp (mem_filter.mpr ⟨mem_univ p, hposdim p hpos, hpos⟩)
      _ = 4 := hw.sum_four
  obtain ⟨_, hones⟩ := weights_eq_one_of_maximal_sum (positiveEdgeProfiles w) w 4
    hw.positive_edges_card_le_four
    (fun p hp => hw.edge_le_one p (mem_filter.mp hp).2.1) hsum
  constructor
  · intro p hp
    exact Or.inl ⟨hposdim p hp, hones p (mem_filter.mpr ⟨mem_univ p, hposdim p hp, hp⟩)⟩
  · intro p q hpq hp hq
    exact distinct_compatible_edges_disjoint p q (hposdim p hp) (hposdim q hq) hpq
      (hw.compatible p q hp hq)

theorem IsCubeWeight.tiling_of_zero_energy_high_support {w : CubeProfile → ℝ}
    (hw : IsCubeWeight w)
    (hhigh : ∀ p, 2 ≤ profileDimension p → p ≠ wholeCube → w p = 0)
    (hzero : cubeEnergy w = 0) : IsCubeTiling w := by
  have hcube : w wholeCube = 0 := by
    have h := hw.energy_ge_whole_of_high_support hhigh
    rw [hzero] at h
    exact le_antisymm h (hw.nonneg wholeCube)
  apply hw.tiling_of_only_edges
  intro p hp
  by_cases hp0 : profileDimension p = 0
  · exact hw.vertex_zero p hp0
  by_cases hpc : p = wholeCube
  · exact hpc ▸ hcube
  · exact hhigh p (by omega) hpc

#print axioms IsCubeWeight.tiling_of_zero_energy_high_support

end Erdos556
