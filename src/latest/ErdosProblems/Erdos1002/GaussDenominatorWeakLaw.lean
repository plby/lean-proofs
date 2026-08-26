import ErdosProblems.Erdos1002.GaussRoofWeakLaw
import ErdosProblems.Erdos1002.GaussDenominatorTime

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Weak denominator-time law under Gauss measure

The unbounded-roof weak law is transferred to the logarithm of the actual
continued-fraction denominator.  The transfer is deterministic up to the
uniform error `log 2`, and the terminating or endpoint exceptional set is
proved null explicitly.
-/

open Filter MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

namespace Erdos1002

noncomputable section

/-- Under Gauss measure, almost every starting point lies in the open unit
interval and no finite Gauss iterate is zero. -/
theorem ae_nonterminating_gaussMeasure :
    ∀ᵐ x ∂gaussMeasure,
      x ∈ Ioo (0 : ℝ) 1 ∧ ∀ k : ℕ, gaussOrbit k x ≠ 0 := by
  have hnotOne : ∀ᵐ x ∂gaussMeasure, x ≠ (1 : ℝ) := by
    exact (measure_eq_zero_iff_ae_notMem.mp (gaussMeasure_singleton 1)).mono
      fun x hx => by simpa only [mem_singleton_iff] using! hx
  have hnonzero (k : ℕ) :
      ∀ᵐ x ∂gaussMeasure, gaussOrbit k x ≠ 0 := by
    have hnull := gaussMeasure_preimage_iterate_singleton_zero k
    have hnotmem := measure_eq_zero_iff_ae_notMem.mp hnull
    filter_upwards [hnotmem] with x hx
    simpa only [gaussOrbit, mem_preimage, mem_singleton_iff] using! hx
  have hnonzeroAll :
      ∀ᵐ x ∂gaussMeasure, ∀ k : ℕ, gaussOrbit k x ≠ 0 :=
    ae_all_iff.mpr hnonzero
  filter_upwards [gaussMeasure_unit_ae, hnotOne, hnonzeroAll]
    with x hx hxone hxnonzero
  exact ⟨⟨hx.1, lt_of_le_of_ne hx.2 hxone⟩, hxnonzero⟩

/-- Logarithmic actual-prefix denominator divided by the prefix depth. -/
def gaussDenominatorAverage (n : ℕ) (x : ℝ) : ℝ :=
  Real.log (gaussPrefixDenominator n x : ℝ) / (n : ℝ)

theorem gaussRoofAverage_eq_gaussRoofSum_div (n : ℕ) (x : ℝ) :
    gaussRoofAverage n x = gaussRoofSum n x / (n : ℝ) := by
  rfl

/-- Almost-everywhere deterministic comparison of denominator and roof
averages.  The estimate is simultaneous for every positive depth. -/
theorem ae_dist_gaussDenominatorAverage_gaussRoofAverage_le :
    ∀ᵐ x ∂gaussMeasure, ∀ n : ℕ, 0 < n →
      dist (gaussDenominatorAverage n x) (gaussRoofAverage n x) ≤
        Real.log 2 / (n : ℝ) := by
  filter_upwards [ae_nonterminating_gaussMeasure] with x hx
  intro n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbound :=
    abs_gaussRoofSum_sub_log_gaussPrefixDenominator_le_log_two
      (n := n) hx.1 hx.2
  rw [gaussDenominatorAverage, gaussRoofAverage_eq_gaussRoofSum_div,
    Real.dist_eq]
  rw [show Real.log (gaussPrefixDenominator n x : ℝ) / (n : ℝ) -
      gaussRoofSum n x / (n : ℝ) =
      (Real.log (gaussPrefixDenominator n x : ℝ) -
        gaussRoofSum n x) / (n : ℝ) by ring]
  rw [abs_div, abs_of_pos hnR, abs_sub_comm]
  exact div_le_div_of_nonneg_right hbound hnR.le

/-- The actual logarithmic denominator time satisfies the same weak law as
the logarithmic roof average. -/
theorem tendstoInMeasure_gaussDenominatorAverage :
    TendstoInMeasure gaussMeasure
      (fun n => gaussDenominatorAverage n) atTop
      (fun _ => gaussRoofMean) := by
  rw [tendstoInMeasure_iff_measureReal_dist]
  intro epsilon hepsilon
  have hroof : Tendsto
      (fun n => gaussMeasure.real
        {x | epsilon / 2 ≤ dist (gaussRoofAverage n x) gaussRoofMean})
      atTop (𝓝 0) :=
    (tendstoInMeasure_iff_measureReal_dist.mp
      tendstoInMeasure_gaussRoofAverage) (epsilon / 2) (by positivity)
  have herr : Tendsto
      (fun n : ℕ => Real.log 2 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)
  have herrEventually : ∀ᶠ n : ℕ in atTop,
      Real.log 2 / (n : ℝ) < epsilon / 2 :=
    (tendsto_order.1 herr).2 (epsilon / 2) (by positivity)
  have hupper : ∀ᶠ n : ℕ in atTop,
      gaussMeasure.real
          {x | epsilon ≤
            dist (gaussDenominatorAverage n x) gaussRoofMean} ≤
        gaussMeasure.real
          {x | epsilon / 2 ≤
            dist (gaussRoofAverage n x) gaussRoofMean} := by
    filter_upwards [eventually_ge_atTop 1, herrEventually] with n hn herrn
    have hnpos : 0 < n := by omega
    let E : Set ℝ :=
      {x | epsilon ≤
        dist (gaussDenominatorAverage n x) gaussRoofMean}
    let R : Set ℝ :=
      {x | epsilon / 2 ≤
        dist (gaussRoofAverage n x) gaussRoofMean}
    have hsubsetAE : E ≤ᵐ[gaussMeasure] (R : Set ℝ) := by
      filter_upwards
        [ae_dist_gaussDenominatorAverage_gaussRoofAverage_le]
        with x hxerr
      intro hxE
      by_contra hxR
      have hroofSmall :
          dist (gaussRoofAverage n x) gaussRoofMean < epsilon / 2 := by
        change ¬ epsilon / 2 ≤
          dist (gaussRoofAverage n x) gaussRoofMean at hxR
        exact lt_of_not_ge hxR
      have htri := dist_triangle
        (gaussDenominatorAverage n x)
        (gaussRoofAverage n x) gaussRoofMean
      have hdenSmall :
          dist (gaussDenominatorAverage n x) gaussRoofMean < epsilon := by
        calc
          dist (gaussDenominatorAverage n x) gaussRoofMean ≤
              dist (gaussDenominatorAverage n x)
                  (gaussRoofAverage n x) +
                dist (gaussRoofAverage n x) gaussRoofMean := htri
          _ ≤ Real.log 2 / (n : ℝ) +
                dist (gaussRoofAverage n x) gaussRoofMean := by
              gcongr
              exact hxerr n hnpos
          _ < epsilon / 2 + epsilon / 2 :=
              add_lt_add herrn hroofSmall
          _ = epsilon := by ring
      exact (not_lt_of_ge hxE) hdenSmall
    have hmono := measure_mono_ae hsubsetAE
    exact ENNReal.toReal_mono (by finiteness) hmono
  exact squeeze_zero'
    (Eventually.of_forall fun _ => measureReal_nonneg)
    hupper hroof

/-- Explicit form of the denominator-time constant. -/
theorem tendstoInMeasure_gaussDenominatorAverage_explicit :
    TendstoInMeasure gaussMeasure
      (fun n => gaussDenominatorAverage n) atTop
      (fun _ => Real.pi ^ 2 / (12 * Real.log 2)) := by
  simpa only [gaussRoofMean_eq_pi_sq_div_log_two] using!
    tendstoInMeasure_gaussDenominatorAverage

end

end Erdos1002
