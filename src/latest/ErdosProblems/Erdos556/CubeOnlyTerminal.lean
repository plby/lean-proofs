import ErdosProblems.Erdos556.CubeEdgeEnergy
import ErdosProblems.Erdos556.CubeFiniteWeights
import ErdosProblems.Erdos556.CubeTerminalArithmetic

/-!
# The terminal case with only cube and edge weights
-/

namespace Erdos556

open Finset

theorem IsCubeWeight.energy_ge_whole_of_high_support {w : CubeProfile → ℝ}
    (hw : IsCubeWeight w)
    (hhigh : ∀ p, 2 ≤ profileDimension p → p ≠ wholeCube → w p = 0) :
    w wholeCube ≤ cubeEnergy w := by
  classical
  let E := positiveEdgeProfiles w
  let x (p : CubeProfile) : ℝ := if p = wholeCube then 0 else w p
  have hx (p : CubeProfile) (hp : p ∈ E) : x p = w p := by
    have hd := (mem_filter.mp hp).2.1
    have hne : p ≠ wholeCube := by intro h; subst p; rw [wholeCube_dimension] at hd; omega
    exact if_neg hne
  have hzero (p : CubeProfile) (hp : p ∉ E) : x p = 0 := by
    by_cases hpc : p = wholeCube
    · exact if_pos hpc
    rw [show x p = w p from if_neg hpc]
    by_cases hd0 : profileDimension p = 0
    · exact hw.vertex_zero p hd0
    by_cases hd1 : profileDimension p = 1
    · have hnot : ¬ 0 < w p := fun h => hp (mem_filter.mpr ⟨mem_univ p, hd1, h⟩)
      exact le_antisymm (le_of_not_gt hnot) (hw.nonneg p)
    · exact hhigh p (by omega) hpc
  have hdecomp : w = x + Pi.single wholeCube (w wholeCube) := by
    funext p
    by_cases hpc : p = wholeCube
    · subst p
      simp [x]
    · simp [x, hpc, Ne.symm hpc]
  have hsum : (∑ p, x p) = ∑ p ∈ E, w p := by
    calc
      (∑ p, x p) = ∑ p ∈ E, x p := by
        symm
        exact sum_subset (subset_univ E) (fun p _ hp => hzero p hp)
      _ = ∑ p ∈ E, w p := sum_congr rfl hx
  have henergy : cubeEnergy x = (∑ p ∈ E, w p ^ 2) - ∑ p ∈ E, w p := by
    rw [cubeEnergy_of_edge_support x E hzero (fun p hp => (mem_filter.mp hp).2.1)
      hw.positive_edges_disjoint]
    congr 1
    · exact sum_congr rfl (fun p hp => congrArg (fun a : ℝ => a ^ 2) (hx p hp))
    · exact sum_congr rfl hx
  have htotal : (∑ p ∈ E, w p) + w wholeCube = 4 := by
    calc
      (∑ p ∈ E, w p) + w wholeCube = (∑ p, x p) + w wholeCube := by rw [hsum]
      _ = ∑ p, ((x + Pi.single wholeCube (w wholeCube)) : CubeProfile → ℝ) p := by
        simp [Pi.add_apply, sum_add_distrib]
      _ = ∑ p, w p := congrArg (fun f : CubeProfile → ℝ => ∑ p, f p) hdecomp.symm
      _ = 4 := hw.sum_four
  have hfull : cubeEnergy w = (∑ p ∈ E, w p ^ 2) - (∑ p ∈ E, w p) +
      w wholeCube * (2 * (∑ p ∈ E, w p) - 3) + (w wholeCube) ^ 2 := by
    calc
      cubeEnergy w = cubeEnergy (x + Pi.single wholeCube (w wholeCube)) := congrArg cubeEnergy hdecomp
      _ = _ := by rw [cubeEnergy_add_single, henergy, cubeGradient_wholeCube, hsum]
  have hbound := cube_terminal_bound (w wholeCube) (∑ p ∈ E, w p) (∑ p ∈ E, w p ^ 2)
    (hw.nonneg wholeCube) (sum_nonneg fun p _ => hw.nonneg p) htotal hw.edge_sum_sq_bound
  rw [hfull]
  nlinarith only [hbound]

#print axioms IsCubeWeight.energy_ge_whole_of_high_support

end Erdos556
