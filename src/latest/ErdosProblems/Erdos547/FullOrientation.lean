import ErdosProblems.Erdos547.BipartiteOrientation
import ErdosProblems.Erdos547.OrientationRate

/-!
# Orienting all fractional mass at the maximal rate for one fixed side
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem exists_full_orientation (μ : FractionalMatching G) (U : Finset V)
    (hcross : μ.Crosses U) (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ σ : SkewMatching G γ, σ.DominatedByFractional μ ∧
      σ.total = orientationRate γ * μ.total ∧ ∀ u ∉ U, σ.outLoad u = 0 := by
  classical
  have hM : 0 < max 1 γ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hden : 0 < 1 + γ := by linarith
  have hL : orientationRate γ + γ * 0 ≤ 1 + γ := by
    rw [mul_zero, add_zero]
    apply (div_le_iff₀ hM).mpr
    nlinarith [le_max_left (1 : ℝ) γ]
  have hR : 0 + γ * orientationRate γ ≤ 1 + γ := by
    rw [zero_add]
    change γ * ((1 + γ) / max 1 γ) ≤ _
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hM).mpr
    nlinarith [le_max_right (1 : ℝ) γ]
  let σ := μ.bipartiteRows U hcross γ (orientationRate γ) 0 hγ
    (orientationRate_pos hγ).le le_rfl hL hR
  refine ⟨σ, SkewMatching.ofDominatedWeight_dominated _ _ _ _ _ _, ?_, ?_⟩
  · change (∑ u, ∑ v, μ.rowWeight U (orientationRate γ) 0 u v) = _
    rw [hcross.rowWeight_total, add_zero]
  · intro u hu
    change (∑ v, μ.rowWeight U (orientationRate γ) 0 u v) / (1 + γ) = 0
    rw [μ.rowWeight_sum, if_neg hu, zero_mul, zero_div]

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_full_orientation
