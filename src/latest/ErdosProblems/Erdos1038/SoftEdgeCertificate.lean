import ErdosProblems.Erdos1038.CertifiedLog
import ErdosProblems.Erdos1038.OneCutElementary
import ErdosProblems.Erdos1038.KernelDecision

set_option maxRecDepth 100000

/-!
# Certified enclosure of the soft edge

The manuscript encloses `qSoft` between two adjacent 15-digit decimals.
Here the endpoint signs are checked in Lean's kernel.  The analytic part is
`CertifiedLog`; the two remaining leaves are exact rational inequalities
proved by `kernel_decide`.
-/

namespace Erdos1038

noncomputable section

def qSoftLowerRat : Rat := 123630684649383 / 1000000000000000

def qSoftUpperRat : Rat := 123630684649384 / 1000000000000000

def softDRat (q : Rat) : Rat := 2 / (1 + q) ^ 2

def atanhParameterRat (r : Rat) : Rat := (r - 1) / (r + 1)

/-- Exact rational leaf proving positivity at the lower endpoint. -/
theorem qSoftLower_rat_certificate :
    (0 : Rat) <
      (1 + qSoftLowerRat) *
          atanhLowerRat 100
            (atanhParameterRat (softDRat qSoftLowerRat)) -
        2 * qSoftLowerRat *
          atanhUpperRat 100
            (atanhParameterRat (1 / qSoftLowerRat)) := by
  kernel_decide

/-- Exact rational leaf proving negativity at the upper endpoint. -/
theorem qSoftUpper_rat_certificate :
    (1 + qSoftUpperRat) *
          atanhUpperRat 100
            (atanhParameterRat (softDRat qSoftUpperRat)) -
        2 * qSoftUpperRat *
          atanhLowerRat 100
            (atanhParameterRat (1 / qSoftUpperRat)) <
      (0 : Rat) := by
  kernel_decide

theorem softFunction_qSoftLower_pos :
    0 < softFunction (qSoftLowerRat : ℝ) := by
  let q : Rat := qSoftLowerRat
  let d : Rat := softDRat q
  let rd : Rat := atanhParameterRat d
  let iq : Rat := 1 / q
  let rq : Rat := atanhParameterRat iq
  have hdlo :
      ((atanhLowerRat 100 rd : Rat) : ℝ) ≤ Real.log (d : ℝ) := by
    apply log_lower_bound_of_rat d rd 100
    · norm_num [rd, atanhParameterRat, d, softDRat, q, qSoftLowerRat]
    · norm_num [rd, atanhParameterRat, d, softDRat, q, qSoftLowerRat]
    · norm_num [rd, atanhParameterRat, d, softDRat, q, qSoftLowerRat]
  have hqhi :
      Real.log (iq : ℝ) ≤ ((atanhUpperRat 100 rq : Rat) : ℝ) := by
    apply log_upper_bound_of_rat iq rq 100
    · norm_num [rq, atanhParameterRat, iq, q, qSoftLowerRat]
    · norm_num [rq, atanhParameterRat, iq, q, qSoftLowerRat]
    · norm_num [rq, atanhParameterRat, iq, q, qSoftLowerRat]
  have hratReal :
      (0 : ℝ) <
        (1 + (q : ℝ)) * ((atanhLowerRat 100 rd : Rat) : ℝ) -
          2 * (q : ℝ) * ((atanhUpperRat 100 rq : Rat) : ℝ) := by
    exact_mod_cast qSoftLower_rat_certificate
  have hcomb :
      0 < (1 + (q : ℝ)) * Real.log (d : ℝ) -
        2 * (q : ℝ) * Real.log (iq : ℝ) := by
    nlinarith [show (0 : ℝ) < (q : ℝ) by
      norm_num [q, qSoftLowerRat]]
  have hrewrite :
      softFunction (q : ℝ) =
        (1 + (q : ℝ)) * Real.log (d : ℝ) -
          2 * (q : ℝ) * Real.log (iq : ℝ) := by
    rw [softFunction]
    have hd : (d : ℝ) = 2 / (1 + (q : ℝ)) ^ 2 := by
      norm_num [d, softDRat]
    rw [hd]
    have hiq : (iq : ℝ) = (q : ℝ)⁻¹ := by
      norm_num [iq]
    rw [hiq, Real.log_inv]
    ring
  change 0 < softFunction (q : ℝ)
  rwa [hrewrite]

theorem softFunction_qSoftUpper_neg :
    softFunction (qSoftUpperRat : ℝ) < 0 := by
  let q : Rat := qSoftUpperRat
  let d : Rat := softDRat q
  let rd : Rat := atanhParameterRat d
  let iq : Rat := 1 / q
  let rq : Rat := atanhParameterRat iq
  have hdhi :
      Real.log (d : ℝ) ≤ ((atanhUpperRat 100 rd : Rat) : ℝ) := by
    apply log_upper_bound_of_rat d rd 100
    · norm_num [rd, atanhParameterRat, d, softDRat, q, qSoftUpperRat]
    · norm_num [rd, atanhParameterRat, d, softDRat, q, qSoftUpperRat]
    · norm_num [rd, atanhParameterRat, d, softDRat, q, qSoftUpperRat]
  have hqlo :
      ((atanhLowerRat 100 rq : Rat) : ℝ) ≤ Real.log (iq : ℝ) := by
    apply log_lower_bound_of_rat iq rq 100
    · norm_num [rq, atanhParameterRat, iq, q, qSoftUpperRat]
    · norm_num [rq, atanhParameterRat, iq, q, qSoftUpperRat]
    · norm_num [rq, atanhParameterRat, iq, q, qSoftUpperRat]
  have hratReal :
      (1 + (q : ℝ)) * ((atanhUpperRat 100 rd : Rat) : ℝ) -
          2 * (q : ℝ) * ((atanhLowerRat 100 rq : Rat) : ℝ) <
        (0 : ℝ) := by
    exact_mod_cast qSoftUpper_rat_certificate
  have hcomb :
      (1 + (q : ℝ)) * Real.log (d : ℝ) -
          2 * (q : ℝ) * Real.log (iq : ℝ) <
        0 := by
    nlinarith [show (0 : ℝ) < (q : ℝ) by
      norm_num [q, qSoftUpperRat]]
  have hrewrite :
      softFunction (q : ℝ) =
        (1 + (q : ℝ)) * Real.log (d : ℝ) -
          2 * (q : ℝ) * Real.log (iq : ℝ) := by
    rw [softFunction]
    have hd : (d : ℝ) = 2 / (1 + (q : ℝ)) ^ 2 := by
      norm_num [d, softDRat]
    rw [hd]
    have hiq : (iq : ℝ) = (q : ℝ)⁻¹ := by
      norm_num [iq]
    rw [hiq, Real.log_inv]
    ring
  change softFunction (q : ℝ) < 0
  rwa [hrewrite]

theorem qSoftLower_mem_domain :
    (qSoftLowerRat : ℝ) ∈ Set.Ioo 0 qCeiling := by
  constructor
  · norm_num [qSoftLowerRat]
  · exact (by norm_num [qSoftLowerRat] :
      (qSoftLowerRat : ℝ) < 1 / 7).trans one_seventh_lt_qCeiling

theorem qSoftUpper_mem_domain :
    (qSoftUpperRat : ℝ) ∈ Set.Ioo 0 qCeiling := by
  constructor
  · norm_num [qSoftUpperRat]
  · exact (by norm_num [qSoftUpperRat] :
      (qSoftUpperRat : ℝ) < 1 / 7).trans one_seventh_lt_qCeiling

theorem qSoftLower_lt_qSoft : (qSoftLowerRat : ℝ) < qSoft := by
  by_contra h
  have hle : qSoft ≤ (qSoftLowerRat : ℝ) := le_of_not_gt h
  rcases hle.eq_or_lt with heq | hlt
  · have hpos := softFunction_qSoftLower_pos
    rw [← heq] at hpos
    linarith [softFunction_qSoft_eq_zero]
  · have hanti := softFunction_strictAntiOn_Ioo_zero_qCeiling
      qSoft_mem_Ioo qSoftLower_mem_domain hlt
    linarith [softFunction_qSoft_eq_zero, softFunction_qSoftLower_pos]

theorem qSoft_lt_qSoftUpper : qSoft < (qSoftUpperRat : ℝ) := by
  by_contra h
  have hle : (qSoftUpperRat : ℝ) ≤ qSoft := le_of_not_gt h
  rcases hle.eq_or_lt with heq | hlt
  · have hneg := softFunction_qSoftUpper_neg
    rw [heq] at hneg
    linarith [softFunction_qSoft_eq_zero]
  · have hanti := softFunction_strictAntiOn_Ioo_zero_qCeiling
      qSoftUpper_mem_domain qSoft_mem_Ioo hlt
    linarith [softFunction_qSoft_eq_zero, softFunction_qSoftUpper_neg]

/-- The precise outward enclosure printed in the manuscript. -/
theorem qSoft_decimal_enclosure :
    (123630684649383 / 10 ^ 15 : ℝ) < qSoft ∧
      qSoft < (123630684649384 / 10 ^ 15 : ℝ) := by
  constructor
  · convert! qSoftLower_lt_qSoft using 1
    norm_num [qSoftLowerRat]
  · convert! qSoft_lt_qSoftUpper using 1
    norm_num [qSoftUpperRat]

end

end Erdos1038
