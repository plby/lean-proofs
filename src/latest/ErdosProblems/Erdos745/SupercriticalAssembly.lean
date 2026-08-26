import ErdosProblems.Erdos745.IntermediateComponents

/-!
# Assembly of the supercritical logarithmic bound

The intermediate-size exclusion is unconditional. This file records the
remaining macroscopic-uniqueness proof obligation precisely; the final KSS
theorem must discharge it and may not export it as an assumption.
-/

open Filter
open scoped Topology

namespace Erdos745

/-- There are asymptotically not two components of positive linear size. -/
def MacroscopicUniqueness (lam : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    Tendsto (fun n ↦ probability lam n (fun G ↦ δ * (n : ℝ) < secondOrder n G)) atTop (𝓝 0)

theorem logarithmic_upper_of_macroscopic_uniqueness {lam : ℝ} (hlam : 1 < lam)
    (hmacro : MacroscopicUniqueness lam) {A : ℝ} (hA : logarithmicConstant lam < A) :
    WithHighProbabilityAt lam (fun n G ↦ secondOrder n G ≤ A * Real.log (n : ℝ)) := by
  obtain ⟨δ, hδ, hmiddle⟩ := exists_no_intermediate_components hlam hA
  have hA0 : 0 < A := (logarithmicConstant_pos hlam).trans hA
  have hbad : Tendsto
      (fun n ↦ probability lam n (fun G ↦ A * Real.log (n : ℝ) < secondOrder n G))
      atTop (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall (fun n ↦ probability_nonneg _ _ _))
      _ (by simpa only [zero_add] using hmiddle.add (hmacro δ hδ))
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hlog : 0 ≤ A * Real.log (n : ℝ) := mul_nonneg hA0.le (Real.log_nonneg hn1)
    apply (probability_mono (fun G hG ↦ ?_)).trans (probability_or_le lam n _ _)
    by_cases hlarge : δ * (n : ℝ) < secondOrder n G
    · exact Or.inr hlarge
    · left
      have hpos : 0 < secondLargestComponentOrder G := by
        have : (0 : ℝ) < secondOrder n G := hlog.trans_lt hG
        unfold secondOrder at this
        exact_mod_cast this
      obtain ⟨C, hC⟩ := exists_component_order_eq_second G hpos
      refine ⟨C, ?_, ?_⟩
      · simpa only [hC, secondOrder] using hG
      · simpa only [hC, secondOrder] using le_of_not_gt hlarge
  have hcompl (n : ℕ) :
      probability lam n (fun G ↦ secondOrder n G ≤ A * Real.log (n : ℝ)) =
        1 - probability lam n (fun G ↦ A * Real.log (n : ℝ) < secondOrder n G) := by
    rw [← probability_not]
    simp only [not_lt]
  unfold WithHighProbabilityAt
  simp_rw [hcompl]
  simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hbad

end Erdos745
