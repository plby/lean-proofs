/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import BoundedGaps.Maynard.NormalizedWeightedAbel
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Smooth logarithmic partial summation

The existing quantitative Abel theorem is specialized to a continuously
differentiable test function. Its logarithmic pullback has exactly the
same total variation on the corresponding interval; this avoids any
loss depending on the summation endpoint.
-/

namespace Erdos4b.FGKMT

noncomputable section

open MeasureTheory
open scoped BigOperators

def normalizedLogWeight (G : ℝ → ℝ) (R : ℕ) (t : ℝ) : ℝ :=
  G (Real.log t / Real.log R)

theorem normalizedLogWeight_hasDerivAt {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G)
    (R : ℕ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (normalizedLogWeight G R)
      (deriv G (Real.log t / Real.log R) * (t⁻¹ / Real.log R)) t :=
  (hG.differentiable_one _).hasDerivAt.comp t ((Real.hasDerivAt_log ht).div_const _)

theorem normalizedLogWeight_deriv {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G)
    (R : ℕ) {t : ℝ} (ht : t ≠ 0) :
    deriv (normalizedLogWeight G R) t =
      deriv G (Real.log t / Real.log R) * (t⁻¹ / Real.log R) :=
  (normalizedLogWeight_hasDerivAt hG R ht).deriv

theorem normalizedLogWeight_deriv_continuousOn {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G)
    (R : ℕ) : ContinuousOn (deriv (normalizedLogWeight G R)) (Set.Icc (1 : ℝ) R) := by
  have ht0 : ∀ t ∈ Set.Icc (1 : ℝ) R, t ≠ 0 :=
    fun t ht => (zero_lt_one.trans_le ht.1).ne'
  have hq : ContinuousOn (fun t : ℝ => Real.log t / Real.log R) (Set.Icc (1 : ℝ) R) :=
    (continuousOn_id.log ht0).div_const _
  have hd : ContinuousOn (fun t : ℝ => t⁻¹ / Real.log R) (Set.Icc (1 : ℝ) R) :=
    (continuousOn_id.inv₀ ht0).div_const _
  exact ((hG.continuous_deriv_one.comp_continuousOn hq).mul hd).congr
    (fun t ht => normalizedLogWeight_deriv hG R (ht0 t ht))

theorem normalizedLogWeight_totalVariation {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G)
    {R : ℕ} (hR : 1 < R) :
    (∫ t in Set.Ioc (1 : ℝ) R, |deriv (normalizedLogWeight G R) t|) =
      ∫ x in (0 : ℝ)..1, |deriv G x| := by
  have hRR : (1 : ℝ) < R := by exact_mod_cast hR
  have hlogR : 0 < Real.log (R : ℝ) := Real.log_pos hRR
  rw [← intervalIntegral.integral_of_le hRR.le]
  calc
    _ = (Real.log R)⁻¹ *
        ∫ t in (1 : ℝ)..R, |deriv G (Real.log t / Real.log R)| / t := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hRR.le] at ht
      have htpos : 0 < t := zero_lt_one.trans_le ht.1
      dsimp only
      rw [normalizedLogWeight_deriv hG R htpos.ne', abs_mul, abs_div,
        abs_inv, abs_of_pos htpos, abs_of_pos hlogR]
      ring
    _ = _ := by
      rw [BoundedGaps.Maynard.intervalIntegral_normalizedLog_div hR
        hG.continuous_deriv_one.abs]
      field_simp

theorem normalizedLogWeight_totalVariation_le {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G)
    {R : ℕ} (hR : 1 < R) {V : ℝ}
    (hV : ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv G x| ≤ V) :
    (∫ t in Set.Ioc (1 : ℝ) R, |deriv (normalizedLogWeight G R) t|) ≤ V := by
  rw [normalizedLogWeight_totalVariation hG hR]
  calc
    _ ≤ ∫ _x in (0 : ℝ)..1, V :=
      intervalIntegral.integral_mono_on (by norm_num)
        (hG.continuous_deriv_one.abs.intervalIntegrable 0 1)
        (continuous_const.intervalIntegrable 0 1) hV
    _ = V := by simp

theorem abs_smoothWeightedSum_sub_logIntegral_le
    {R : ℕ} (hR : 1 < R) {c : ℕ → ℝ} (hc : c 0 = 0)
    {S E V : ℝ} (hE : 0 ≤ E) {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G)
    (happrox : ∀ t ∈ Set.Icc (1 : ℝ) R,
      |BoundedGaps.Maynard.abelCumulative c t - S * Real.log t| ≤ E)
    (hV : ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv G x| ≤ V) :
    |(∑ n ∈ Finset.Icc 0 R, G (Real.log n / Real.log R) * c n) -
      S * Real.log R * (∫ x in (0 : ℝ)..1, G x)| ≤ E * (|G 1| + V) := by
  have hRR : (1 : ℝ) ≤ R := by exact_mod_cast hR.le
  have hd := normalizedLogWeight_deriv_continuousOn hG R
  have hdInt : IntegrableOn (deriv (normalizedLogWeight G R)) (Set.Icc (1 : ℝ) R) :=
    hd.integrableOn_Icc
  have hdInterval : IntervalIntegrable (deriv (normalizedLogWeight G R)) volume 1 R := by
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le hRR] using hd
  have hmain : IntegrableOn
      (fun t => deriv (normalizedLogWeight G R) t * (S * Real.log t))
      (Set.Ioc (1 : ℝ) R) := by
    apply (ContinuousOn.integrableOn_Icc _).mono_set Set.Ioc_subset_Icc_self
    exact hd.mul (continuousOn_const.mul
      (continuousOn_id.log (fun t ht => (zero_lt_one.trans_le ht.1).ne')))
  apply BoundedGaps.Maynard.abs_weightedSum_sub_normalizedLogIntegral_le hR hc hE hG.continuous
  · intro t ht
    exact (normalizedLogWeight_hasDerivAt hG R
      (zero_lt_one.trans_le ht.1).ne').differentiableAt.hasDerivAt
  · exact hdInterval
  · exact hdInt
  · exact (hd.abs.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  · exact hmain
  · exact happrox
  · exact normalizedLogWeight_totalVariation_le hG hR hV

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.abs_smoothWeightedSum_sub_logIntegral_le
