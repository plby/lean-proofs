import ErdosProblems.Erdos547.ImprovedBalancing

/-!
# Orienting a bipartite fractional matching to prescribed part budgets
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem exists_bipartite_orientation (μ : FractionalMatching G) (U W : Finset V)
    (hdis : Disjoint U W) (hruns : μ.RunsBetween U W) (a b : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hsize : max a b ≤ μ.total) :
    ∃ σ : SkewMatching G (b / a), σ.DominatedByFractional μ ∧
      σ.total = a + b ∧ ∀ u ∉ U, σ.outLoad u = 0 := by
  classical
  have hM : 0 < μ.total := ha.trans_le ((le_max_left _ _).trans hsize)
  have hγ : 0 ≤ b / a := div_nonneg hb ha.le
  have hden : 0 < 1 + b / a := by linarith
  let p := (a + b) / μ.total
  have hp : 0 ≤ p := div_nonneg (by linarith) hM.le
  have hleft : (p + (b / a) * 0) / (1 + b / a) = a / μ.total := by
    simpa only [one_mul, sub_self, zero_mul, zero_div, mul_zero, add_zero] using
      proportional_endpoint a b μ.total 1 ha hb hM
  have hright : (0 + (b / a) * p) / (1 + b / a) = b / μ.total := by
    simpa only [zero_mul, zero_div, sub_zero, one_mul, zero_add] using
      proportional_endpoint a b μ.total 0 ha hb hM
  have hL : p + (b / a) * 0 ≤ 1 + b / a := (div_le_one hden).mp (by
    rw [hleft]
    exact (div_le_one hM).mpr ((le_max_left _ _).trans hsize))
  have hR : 0 + (b / a) * p ≤ 1 + b / a := (div_le_one hden).mp (by
    rw [hright]
    exact (div_le_one hM).mpr ((le_max_right _ _).trans hsize))
  have hcross := hruns.crosses hdis
  let σ := μ.bipartiteRows U hcross (b / a) p 0 hγ hp le_rfl hL hR
  refine ⟨σ, ?_, ?_, ?_⟩
  · exact SkewMatching.ofDominatedWeight_dominated _ _ _ _ _ _
  · change (∑ u, ∑ v, μ.rowWeight U p 0 u v) = _
    rw [hcross.rowWeight_total, add_zero, div_mul_cancel₀ _ (ne_of_gt hM)]
  · intro u hu
    change (∑ v, μ.rowWeight U p 0 u v) / (1 + b / a) = 0
    rw [μ.rowWeight_sum, if_neg hu, zero_mul, zero_div]

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_bipartite_orientation
