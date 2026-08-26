/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceGridCandidate
import ErdosProblems.Erdos4b.SourceSimplexBoundary

/-!
# Almost-everywhere convergence of the finite simplex grids

No regularity is asserted at a simplex boundary or a grid endpoint.
Both exceptional sets are proved null before dominated convergence is used.
-/

namespace Erdos4b

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

theorem tendsto_sampled_variableProduct {K : ℕ} {A : ℝ} (hA : 0 < A)
    {t : Fin K → ℝ} (ht : ∀ i, 0 ≤ t i) :
    Tendsto (fun n ↦ VariableMaynard.product K A (fun i ↦ sourceGridUpperSample n (t i)))
      atTop (𝓝 (VariableMaynard.product K A t)) := by
  apply tendsto_finsetProd Finset.univ
  intro i hi
  have hdenom : 0 < 1 + A * ((K : ℝ) * t i) := by
    have hh := mul_nonneg hA.le (mul_nonneg (Nat.cast_nonneg K) (ht i))
    linarith
  exact (tendsto_const_nhds.add
    (((tendsto_sourceGridUpperSample (ht i)).const_mul (K : ℝ)).const_mul A)).inv₀ hdenom.ne'

theorem tendsto_sourceGridValue {K : ℕ} {A : ℝ} (hA : 0 < A) (t : Fin K → ℝ)
    (hregular : ∀ i, SourceGridRegular (t i)) (hboundary : (∑ i, t i) ≠ 1) :
    Tendsto (fun n ↦ sourceGridValue K A n t) atTop (𝓝 (VariableMaynard.candidate K A t)) := by
  classical
  by_cases ht : t ∈ BoundedGaps.Maynard.maynardSimplex K
  · have htopen : ∀ i, t i ∈ Set.Ioo (0 : ℝ) 1 := by
      intro i
      have hi := ht.1 i (Set.mem_univ i)
      have hz : t i ≠ 0 := by simpa using hregular i 0 0
      have hone : t i ≠ 1 := by simpa using hregular i 0 1
      exact ⟨lt_of_le_of_ne hi.1 hz.symm, lt_of_le_of_ne hi.2 hone⟩
    have hs : (∑ i, t i) < 1 := lt_of_le_of_ne ht.2 hboundary
    have hevent := eventually_sourceGridIndex_selected htopen hs
    rw [VariableMaynard.candidate, if_pos ht]
    apply (tendsto_sampled_variableProduct hA (fun i ↦ (htopen i).1.le)).congr'
    filter_upwards [hevent] with n hn
    exact (sourceGridValue_eq_sample_of_selected htopen hregular hn).symm
  · rw [VariableMaynard.candidate, if_neg ht]
    have heq : (fun n ↦ sourceGridValue K A n t) = fun _ : ℕ ↦ (0 : ℝ) :=
      funext fun n ↦ sourceGridValue_simplexSupported K A n t ht
    rw [heq]
    exact tendsto_const_nhds

theorem ae_tendsto_sourceGridValue {K : ℕ} {A : ℝ} (hA : 0 < A) :
    ∀ᵐ t : Fin K → ℝ, Tendsto (fun n ↦ sourceGridValue K A n t) atTop
      (𝓝 (VariableMaynard.candidate K A t)) := by
  filter_upwards [ae_sourceGridRegular_coordinates, ae_sum_ne_one] with t ht hsum
  exact tendsto_sourceGridValue hA t ht hsum

theorem measurable_sourceGridValue (K : ℕ) (A : ℝ) (n : ℕ) :
    Measurable (sourceGridValue K A n) := by
  unfold sourceGridValue sourceTensorValue
  apply Finset.measurable_sum _
  intro j hj
  apply Finset.measurable_prod _
  intro i hi
  unfold sourceGridFactors sourceRectangleFactors sourceIntervalIndicator
  exact measurable_const.mul ((measurable_const.indicator measurableSet_Ioo).comp
    (measurable_pi_apply i))

theorem sourceGridValue_norm_le_one {K n : ℕ} {A : ℝ} (hA : 0 < A) (t : Fin K → ℝ) :
    ‖sourceGridValue K A n t‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (sourceGridValue_bounds hA t).1]
  exact (sourceGridValue_bounds hA t).2

theorem sourceGridValue_sq_norm_le_one {K n : ℕ} {A : ℝ} (hA : 0 < A) (t : Fin K → ℝ) :
    ‖sourceGridValue K A n t ^ 2‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hb := sourceGridValue_bounds (n := n) hA t
  nlinarith

theorem tendsto_maynardI_sourceGridValue {K : ℕ} {A : ℝ} (hA : 0 < A) :
    Tendsto (fun n ↦ BoundedGaps.Maynard.maynardI K (sourceGridValue K A n)) atTop
      (𝓝 (BoundedGaps.Maynard.maynardI K (VariableMaynard.candidate K A))) := by
  apply tendsto_integral_of_dominated_convergence (fun _ : Fin K → ℝ ↦ (1 : ℝ))
  · intro n
    exact ((measurable_sourceGridValue K A n).pow_const 2).aestronglyMeasurable
  · exact integrableOn_const (BoundedGaps.Maynard.maynardCube_measure_lt_top K).ne
  · intro n
    exact ae_of_all _ (sourceGridValue_sq_norm_le_one (n := n) hA)
  · filter_upwards [ae_restrict_of_ae (ae_tendsto_sourceGridValue hA)] with t ht
    exact ht.pow 2

end

end Erdos4b
