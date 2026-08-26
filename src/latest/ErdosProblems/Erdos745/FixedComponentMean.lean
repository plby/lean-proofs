import ErdosProblems.Erdos745.FixedTreeMean
import ErdosProblems.Erdos745.NonTreeComponents

/-! # Fixed-order component density limits, including non-trees -/

open Filter
open scoped BigOperators Topology

namespace Erdos745

noncomputable section

attribute [local instance] Classical.propDecidable

theorem probability_component_tree_partition (lam : ℝ) (n : ℕ) (S : Finset (Fin n)) :
    probability lam n (fun G ↦ IsComponentSet G S) =
      probability lam n (fun G ↦ IsTreeComponentSet G S) +
        probability lam n (fun G ↦ IsNonTreeComponentSet G S) := by
  simp only [probability_eq_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro G _
  by_cases hc : IsComponentSet G S <;>
    by_cases ht : (G.induce (S : Set (Fin n))).IsTree <;>
    simp only [IsTreeComponentSet, IsNonTreeComponentSet, hc, ht, and_self, and_true,
      and_false, not_true_eq_false, not_false_eq_true, if_true, if_false, add_zero, zero_add]

def componentMean (lam : ℝ) (n k : ℕ) : ℝ :=
  ∑ S ∈ Finset.univ.powersetCard k, probability lam n (fun G ↦ IsComponentSet G S)

def nonTreeMean (lam : ℝ) (n k : ℕ) : ℝ :=
  ∑ S ∈ Finset.univ.powersetCard k, probability lam n (fun G ↦ IsNonTreeComponentSet G S)

theorem componentMean_eq_tree_add (lam : ℝ) (n k : ℕ) :
    componentMean lam n k = treeMean lam n k + nonTreeMean lam n k := by
  unfold componentMean nonTreeMean
  simp_rw [probability_component_tree_partition]
  rw [Finset.sum_add_distrib, sum_treeComponentSet_probabilities]

theorem nonTreeMean_nonneg (lam : ℝ) (n k : ℕ) : 0 ≤ nonTreeMean lam n k :=
  Finset.sum_nonneg (fun _ _ ↦ probability_nonneg _ _ _)

theorem tendsto_nonTreeMean_div {lam : ℝ} (hlam : 0 ≤ lam) (k : ℕ) :
    Tendsto (fun n ↦ nonTreeMean lam n k / n) atTop (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall
    (fun n ↦ div_nonneg (nonTreeMean_nonneg lam n k) (Nat.cast_nonneg n)))
    _ (tendsto_const_div_atTop_nhds_zero_nat ((labelledGraphCount k : ℝ) * lam ^ k))
  filter_upwards [eventually_ge_atTop 1,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop lam] with n hn hlamn
  exact div_le_div_of_nonneg_right
    (sum_probability_nonTree_components_le_constant hlam (by omega) hlamn k) (Nat.cast_nonneg _)

/-- The non-tree contribution has zero limiting density for every fixed order. -/
theorem tendsto_componentMean_div {lam : ℝ} (hlam : 0 ≤ lam) {k : ℕ} (hk : 0 < k) :
    Tendsto (fun n ↦ componentMean lam n k / n) atTop (𝓝 (treeDensity lam k)) := by
  simp_rw [componentMean_eq_tree_add, add_div]
  simpa only [add_zero] using (tendsto_treeMean_div hk hlam).add (tendsto_nonTreeMean_div hlam k)

end

end Erdos745
