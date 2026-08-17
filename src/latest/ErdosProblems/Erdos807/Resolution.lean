import ErdosProblems.Erdos807.Probability
import ErdosProblems.Erdos807.WHP

/-!
# The final logical step in the resolution of Erdős Problem 807

This file isolates the implication from a with-high-probability multiplicative
improvement over the star bound to the failure of the proposed equality.
-/

open Filter
open scoped Topology

namespace Erdos807

/-- A positive multiplicative improvement over `n - a` is incompatible with
the equality `f = n - a`.  Consequently, if the improvement holds with high
probability, the equality cannot hold with high probability. -/
theorem not_almostSurely_nat_sub_equality_of_improvement
    (f a : (n : ℕ) → SimpleGraph (Fin n) → ℕ) {c : ℝ}
    (hc : 0 < c)
    (ha_pos : ∀ᶠ n in atTop, ∀ G, 0 < a n G)
    (ha_le : ∀ᶠ n in atTop, ∀ G, a n G ≤ n)
    (himprovement : RandomGraph.AlmostSurely (fun n G ↦
      (f n G : ℝ) ≤ (n : ℝ) - (1 + c) * (a n G : ℝ))) :
    ¬ RandomGraph.AlmostSurely (fun n G ↦ f n G = n - a n G) := by
  let strict : (n : ℕ) → RandomGraph.Event n := fun n G ↦
    (f n G : ℝ) ≤ (n : ℝ) - (1 + c) * (a n G : ℝ)
  let equality : (n : ℕ) → RandomGraph.Event n := fun n G ↦
    f n G = n - a n G
  have hdisjoint : ∀ᶠ n in atTop,
      ∀ G, equality n G → ¬ strict n G := by
    filter_upwards [ha_pos, ha_le] with n hnpos hnle
    intro G heq hstrict
    have hcast : (f n G : ℝ) = (n : ℝ) - (a n G : ℝ) := by
      rw [heq, Nat.cast_sub (hnle G)]
    dsimp [strict] at hstrict
    rw [hcast] at hstrict
    have haR : (0 : ℝ) < a n G := by exact_mod_cast hnpos G
    nlinarith
  have hequality_zero : Tendsto
      (fun n ↦ RandomGraph.probability n (equality n)) atTop (𝓝 0) := by
    exact WHP.event_equality_tendsto_zero RandomGraph.probability
      RandomGraph.probability_nonneg
      (fun h ↦ RandomGraph.probability_mono h)
      RandomGraph.probability_compl himprovement hdisjoint
  intro hequality_one
  have hlimits : (1 : ℝ) = 0 :=
    tendsto_nhds_unique hequality_one hequality_zero
  norm_num at hlimits

end Erdos807
