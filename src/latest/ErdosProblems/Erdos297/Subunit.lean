/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos297.Riemann

/-!
# The exponent in Erdős Problem 297 is genuinely below one

At a critical parameter `lam`, the defining moment equation rewrites the
free-energy constant as the integral of binary entropy:

`gamma lam = integral x in [0,1], H (selectionProbability lam x)`.

The logistic probability is different from `1 / 2` at every positive
argument when `lam > 0`.  Hence the integrand is strictly below `log 2` at,
for example, `x = 1`; strict comparison of continuous interval integrals
then gives `gamma lam < log 2` and therefore `binaryExponent lam < 1`.
-/

open MeasureTheory Set
open scoped Interval

namespace Erdos297

noncomputable section

/-- The thermodynamic identity between the logistic free-energy summand and
binary entropy, including the endpoint convention at `x = 0`. -/
lemma binaryEntropy_selectionProbability_eq
    {lam x : ℝ} (hlam : 0 < lam) (hx : 0 ≤ x) :
    Real.binEntropy (selectionProbability lam x) =
      lam * momentKernel lam x + freeEnergyKernel lam x := by
  by_cases hx0 : x = 0
  · subst x
    simp [selectionProbability, momentKernel, freeEnergyKernel]
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have htpos : 0 < lam / x := div_pos hlam hxpos
    have hepos : 0 < Real.exp (lam / x) := Real.exp_pos _
    have hdenpos : 0 < 1 + Real.exp (lam / x) := by positivity
    have honeSub : 1 - 1 / (1 + Real.exp (lam / x)) =
        Real.exp (lam / x) / (1 + Real.exp (lam / x)) := by
      field_simp
      ring
    have hinvOne : (1 / (1 + Real.exp (lam / x)))⁻¹ =
        1 + Real.exp (lam / x) := by
      simp only [one_div, inv_inv]
    have hinvExp :
        (Real.exp (lam / x) / (1 + Real.exp (lam / x)))⁻¹ =
          (1 + Real.exp (lam / x)) / Real.exp (lam / x) := by
      field_simp
    have honeAddInv : 1 + (Real.exp (lam / x))⁻¹ =
        (1 + Real.exp (lam / x)) / Real.exp (lam / x) := by
      field_simp
      ring
    simp only [selectionProbability, momentKernel, freeEnergyKernel, hx0,
      if_false, Real.binEntropy]
    rw [honeSub, hinvOne, hinvExp]
    rw [Real.log_div hdenpos.ne' hepos.ne', Real.log_exp]
    have hneg : -lam / x = -(lam / x) := by ring
    rw [hneg, Real.exp_neg]
    rw [honeAddInv]
    rw [Real.log_div hdenpos.ne' hepos.ne', Real.log_exp]
    field_simp
    ring

/-- At a positive parameter, the logistic probability at `x = 1` is not
the entropy-maximizing value `1 / 2`. -/
lemma selectionProbability_one_ne_half {lam : ℝ} (hlam : 0 < lam) :
    selectionProbability lam 1 ≠ (2 : ℝ)⁻¹ := by
  simp only [selectionProbability, one_ne_zero, if_false, div_one]
  intro h
  have hexp : Real.exp lam = 1 := by
    have hden : 1 + Real.exp lam ≠ 0 := by positivity
    field_simp [hden] at h
    linarith
  have hone_lt : 1 < Real.exp lam := Real.one_lt_exp_iff.mpr hlam
  linarith

/-- The critical moment equation converts `gamma` exactly into an interval
integral of the binary entropy of the logistic selector. -/
lemma gamma_eq_intervalIntegral_binaryEntropy
    {lam : ℝ} (hlam : IsCriticalParameter lam) :
    gamma lam =
      ∫ x in (0 : ℝ)..1, Real.binEntropy (selectionProbability lam x) := by
  have hmomentInt : IntervalIntegrable (momentKernel lam) volume 0 1 :=
    (continuousOn_momentKernel hlam.1).intervalIntegrable_of_Icc zero_le_one
  have hfreeInt : IntervalIntegrable (freeEnergyKernel lam) volume 0 1 :=
    (continuousOn_freeEnergyKernel hlam.1).intervalIntegrable_of_Icc zero_le_one
  calc
    gamma lam = lam * moment lam +
        ∫ x in Set.Icc (0 : ℝ) 1, freeEnergyKernel lam x := by
      rw [hlam.2]
      simp [gamma]
    _ = lam * (∫ x in (0 : ℝ)..1, momentKernel lam x) +
        ∫ x in (0 : ℝ)..1, freeEnergyKernel lam x := by
      rw [moment, intervalIntegral.integral_of_le zero_le_one,
        ← integral_Icc_eq_integral_Ioc]
      rw [intervalIntegral.integral_of_le zero_le_one,
        ← integral_Icc_eq_integral_Ioc]
    _ = ∫ x in (0 : ℝ)..1,
        (lam * momentKernel lam x + freeEnergyKernel lam x) := by
      rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_add
        (hmomentInt.const_mul lam) hfreeInt]
    _ = ∫ x in (0 : ℝ)..1,
        Real.binEntropy (selectionProbability lam x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Icc (0 : ℝ) 1 := by
        simpa [uIcc_of_le zero_le_one] using hx
      exact (binaryEntropy_selectionProbability_eq hlam.1 hx'.1).symm

/-- The sharp natural-log growth constant is strictly below `log 2` at any
critical parameter. -/
theorem gamma_lt_log_two_of_isCriticalParameter
    {lam : ℝ} (hlam : IsCriticalParameter lam) :
    gamma lam < Real.log 2 := by
  rw [gamma_eq_intervalIntegral_binaryEntropy hlam]
  have hentcont : ContinuousOn
      (fun x : ℝ ↦ Real.binEntropy (selectionProbability lam x))
      (Icc (0 : ℝ) 1) := by
    have hsumcont : ContinuousOn
        (fun x : ℝ ↦ lam * momentKernel lam x + freeEnergyKernel lam x)
        (Icc (0 : ℝ) 1) :=
      (continuousOn_const.mul (continuousOn_momentKernel hlam.1)).add
        (continuousOn_freeEnergyKernel hlam.1)
    exact hsumcont.congr fun x hx ↦
      binaryEntropy_selectionProbability_eq hlam.1 hx.1
  have hstrict :=
    intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (f := fun x : ℝ ↦ Real.binEntropy (selectionProbability lam x))
      (g := fun _x : ℝ ↦ Real.log 2)
      zero_lt_one hentcont continuousOn_const
      (fun x hx ↦ Real.binEntropy_le_log_two)
      ⟨1, right_mem_Icc.mpr zero_le_one,
        Real.binEntropy_lt_log_two.mpr (selectionProbability_one_ne_half hlam.1)⟩
  simpa using hstrict

/-- The explicit exponent in the base-two formulation of Erdős Problem 297
is genuinely smaller than one. -/
theorem binaryExponent_lt_one_of_isUniqueCriticalParameter
    {lam : ℝ} (hlam : IsUniqueCriticalParameter lam) :
    binaryExponent lam < 1 :=
  (binaryExponent_lt_one_iff lam).2
    (gamma_lt_log_two_of_isCriticalParameter hlam.1)

end

end Erdos297

#print axioms Erdos297.binaryExponent_lt_one_of_isUniqueCriticalParameter
