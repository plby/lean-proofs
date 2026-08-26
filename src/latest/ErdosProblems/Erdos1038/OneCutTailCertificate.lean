import ErdosProblems.Erdos1038.OneCutTailExpr
import ErdosProblems.Erdos1038.KernelDecision

set_option maxRecDepth 100000

namespace Erdos1038

noncomputable section

open Set
open IntervalExpr

namespace OneCutTailCertificate

def tailQ : Rat := 1 / 10 ^ 22
def tailQr : Rat := 1 / 10 ^ 9

def tailVars : Fin 5 → RatInterval :=
  ![⟨0, 1 / 50⟩,
    ⟨0, tailQ⟩,
    ⟨0, tailQr⟩,
    ⟨499 / 1000, 501 / 1000⟩,
    ⟨149 / 100, 15001 / 10000⟩]

def innerLowerVars : Fin 5 → RatInterval :=
  ![tailVars 0, tailVars 1, tailVars 2,
    RatInterval.point (499 / 1000), tailVars 4]

def innerUpperVars : Fin 5 → RatInterval :=
  ![tailVars 0, tailVars 1, tailVars 2,
    RatInterval.point (501 / 1000), tailVars 4]

def outerLowerVars : Fin 5 → RatInterval :=
  ![tailVars 0, tailVars 1, tailVars 2, tailVars 3,
    RatInterval.point (149 / 100)]

def outerUpperVars : Fin 5 → RatInterval :=
  ![tailVars 0, tailVars 1, tailVars 2, tailVars 3,
    RatInterval.point (15001 / 10000)]

theorem innerLower_certified :
    EvalNegative innerLowerVars (tailInnerGExpr 80) := by
  kernel_decide

theorem innerUpper_certified :
    EvalPositive innerUpperVars (tailInnerGExpr 80) := by
  kernel_decide

theorem outerLower_certified :
    EvalPositive outerLowerVars (tailOuterGExpr 80) := by
  kernel_decide

theorem outerUpper_certified :
    EvalNegative outerUpperVars (tailOuterGExpr 80) := by
  kernel_decide

theorem lambdaR_certified :
    EvalNegative tailVars (tailLambdaRExpr 80) := by
  kernel_decide

theorem tailVars_ordered : ∀ i, (tailVars i).Ordered := by
  intro i
  fin_cases i <;>
    simp [tailVars, tailQ, tailQr, RatInterval.Ordered] <;> norm_num

theorem innerLowerVars_ordered : ∀ i, (innerLowerVars i).Ordered := by
  intro i
  fin_cases i
  all_goals simp [innerLowerVars, tailVars, tailQ, tailQr,
    RatInterval.Ordered, RatInterval.point]
  all_goals norm_num

theorem innerUpperVars_ordered : ∀ i, (innerUpperVars i).Ordered := by
  intro i
  fin_cases i
  all_goals simp [innerUpperVars, tailVars, tailQ, tailQr,
    RatInterval.Ordered, RatInterval.point]
  all_goals norm_num

theorem outerLowerVars_ordered : ∀ i, (outerLowerVars i).Ordered := by
  intro i
  fin_cases i
  all_goals simp [outerLowerVars, tailVars, tailQ, tailQr,
    RatInterval.Ordered, RatInterval.point]
  all_goals norm_num

theorem outerUpperVars_ordered : ∀ i, (outerUpperVars i).Ordered := by
  intro i
  fin_cases i
  all_goals simp [outerUpperVars, tailVars, tailQ, tailQr,
    RatInterval.Ordered, RatInterval.point]
  all_goals norm_num

def tailRReal (q : ℝ) : ℝ := -1 / Real.log q

def tailQrReal (q : ℝ) : ℝ := q * (Real.log q) ^ 2

theorem log_tailQ_eq :
    Real.log (tailQ : ℝ) = -22 * Real.log 10 := by
  have hcast : (tailQ : ℝ) = (1 : ℝ) / 10 ^ 22 := by
    norm_num [tailQ]
  rw [hcast]
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
    (pow_ne_zero 22 (by norm_num : (10 : ℝ) ≠ 0)), Real.log_one,
    Real.log_pow]
  ring

theorem log_ten_lower : (23 / 10 : ℝ) < Real.log 10 := by
  have hcert : (23 : Rat) < 10 * logLowerRat 80 10 := by
    kernel_decide
  have hcast : (23 : ℝ) < 10 * ((logLowerRat 80 10 : Rat) : ℝ) := by
    exact_mod_cast hcert
  have hbound := logLowerRat_le_log (n := 80)
    (r := 10) (by norm_num)
  norm_num at hcast hbound ⊢
  nlinarith

theorem log_ten_upper : Real.log 10 < (3 : ℝ) := by
  have hcert : logUpperRat 80 10 < (3 : Rat) := by
    kernel_decide
  have hcast : ((logUpperRat 80 10 : Rat) : ℝ) < (3 : ℝ) := by
    exact_mod_cast hcert
  exact (log_le_logUpperRat (n := 80) (r := 10) (by norm_num)).trans_lt
    hcast

theorem log_tailQ_lt : Real.log (tailQ : ℝ) < -50 := by
  rw [log_tailQ_eq]
  nlinarith [log_ten_lower]

theorem neg_sixty_six_lt_log_tailQ :
    (-66 : ℝ) < Real.log (tailQ : ℝ) := by
  rw [log_tailQ_eq]
  nlinarith [log_ten_upper]

theorem hasDerivAt_tailQrReal {q : ℝ} (hq : 0 < q) :
    HasDerivAt tailQrReal
      (Real.log q * (Real.log q + 2)) q := by
  have hlog := Real.hasDerivAt_log hq.ne'
  have h := (hasDerivAt_id q).mul (hlog.pow 2)
  change HasDerivAt (fun x : ℝ ↦ x * (Real.log x) ^ 2)
    (Real.log q * (Real.log q + 2)) q
  convert! h using 1
  simp only [id_eq, Pi.pow_apply]
  field_simp [hq.ne']
  ring

theorem tailQrReal_le_tailQr {q : ℝ}
    (hq : 0 < q) (hqTail : q ≤ (tailQ : ℝ)) :
    tailQrReal q ≤ (tailQr : ℝ) := by
  have hlogq : Real.log q < -50 :=
    (Real.log_le_log hq hqTail).trans_lt log_tailQ_lt
  have hmono : StrictMonoOn tailQrReal (Icc q (tailQ : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc q (tailQ : ℝ))
    · intro x hx
      have hx0 : 0 < x := hq.trans_le hx.1
      exact (hasDerivAt_tailQrReal hx0).continuousAt.continuousWithinAt
    · rw [interior_Icc]
      intro x hx
      have hx0 : 0 < x := hq.trans hx.1
      have hlogx : Real.log x < -50 :=
        (Real.log_le_log hx0 hx.2.le).trans_lt log_tailQ_lt
      rw [(hasDerivAt_tailQrReal hx0).deriv]
      exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
  have hfun : tailQrReal q ≤ tailQrReal (tailQ : ℝ) :=
    hmono.monotoneOn ⟨le_rfl, hqTail⟩ ⟨hqTail, le_rfl⟩ hqTail
  have hlog0 : Real.log (tailQ : ℝ) < 0 := log_tailQ_lt.trans (by norm_num)
  have hsquare : (Real.log (tailQ : ℝ)) ^ 2 < 66 ^ 2 := by
    nlinarith [neg_sixty_six_lt_log_tailQ]
  have hend : tailQrReal (tailQ : ℝ) ≤ (tailQr : ℝ) := by
    have hqcast : (tailQ : ℝ) = (1 : ℝ) / 10 ^ 22 := by
      norm_num [tailQ]
    have hqrcast : (tailQr : ℝ) = (1 : ℝ) / 10 ^ 9 := by
      norm_num [tailQr]
    rw [tailQrReal]
    rw [hqcast, hqrcast]
    rw [hqcast] at hsquare
    norm_num at hsquare ⊢
    nlinarith
  exact hfun.trans hend

theorem tailRReal_pos {q : ℝ}
    (hq : 0 < q) (hqTail : q ≤ (tailQ : ℝ)) :
    0 < tailRReal q := by
  have hlog : Real.log q < -50 :=
    (Real.log_le_log hq hqTail).trans_lt log_tailQ_lt
  rw [tailRReal]
  exact div_pos_of_neg_of_neg (by norm_num) (by linarith)

theorem tailRReal_le_fiftieth {q : ℝ}
    (hq : 0 < q) (hqTail : q ≤ (tailQ : ℝ)) :
    tailRReal q ≤ ((1 / 50 : Rat) : ℝ) := by
  have hlog : Real.log q < -50 :=
    (Real.log_le_log hq hqTail).trans_lt log_tailQ_lt
  have hden : 0 < -Real.log q := by linarith
  rw [tailRReal]
  have heq : -1 / Real.log q = 1 / (-Real.log q) := by ring
  rw [heq, div_le_iff₀ hden]
  norm_num
  linarith

theorem tailQrReal_pos {q : ℝ}
    (hq : 0 < q) (hqTail : q ≤ (tailQ : ℝ)) :
    0 < tailQrReal q := by
  have hlog : Real.log q < -50 :=
    (Real.log_le_log hq hqTail).trans_lt log_tailQ_lt
  rw [tailQrReal]
  exact mul_pos hq (sq_pos_of_ne_zero (by linarith))

theorem tailDReal_eq_scaledD {q : ℝ} (hq : 0 < q) :
    tailDReal q = scaledD q := by
  have hden : (1 + q) ^ 2 ≠ 0 := by positivity
  rw [tailDReal, scaledD, Real.log_div (by norm_num) hden,
    Real.log_pow]
  ring

theorem tailAReal_eq_A {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    tailAReal (tailRReal q) q = A q := by
  have hlog : Real.log q ≠ 0 := log_q_ne_zero hq hq1
  rw [tailAReal, tailRReal, tailDReal_eq_scaledD hq,
    scaledD_eq_log_H_sub_log_q hq, A]
  field_simp [hlog]
  ring

theorem Hprime_div_H_eq {q : ℝ} (hq : 0 < q) :
    Hprime q / H q = 1 / q - 2 / (1 + q) := by
  have hq0 : q ≠ 0 := hq.ne'
  have hq1 : 1 + q ≠ 0 := by linarith
  rw [Hprime, H]
  field_simp [hq0, hq1]
  ring

theorem tailArReal_eq_Aprime_mul {q : ℝ}
    (hq : 0 < q) (hq1 : q < 1) :
    tailArReal (tailRReal q) q (tailQrReal q) =
      Aprime q * tailQrReal q := by
  have hlog : Real.log q ≠ 0 := log_q_ne_zero hq hq1
  have hq0 : q ≠ 0 := hq.ne'
  have hqOne : 1 + q ≠ 0 := by linarith
  rw [tailArReal, tailRReal, tailQrReal, tailDReal_eq_scaledD hq,
    scaledD_eq_log_H_sub_log_q hq, Aprime, Hprime_div_H_eq hq]
  field_simp [hlog, hq0, hqOne]
  ring

theorem tailInnerGReal_eq_scaledInnerResidual {q z : ℝ}
    (hq : 0 < q) (hq1 : q < 1) :
    tailInnerGReal (tailRReal q) q z = scaledInnerResidual (q, z) := by
  rw [tailInnerGReal, scaledInnerResidual, tailAReal_eq_A hq hq1,
    tailDReal_eq_scaledD hq]

theorem tailOuterGReal_eq_scaledOuterResidual {q z : ℝ}
    (hq : 0 < q) (hq1 : q < 1) :
    tailOuterGReal (tailRReal q) q z = scaledOuterResidual (q, z) := by
  rw [tailOuterGReal, scaledOuterResidual, tailAReal_eq_A hq hq1,
    tailDReal_eq_scaledD hq]

theorem tailInnerGzReal_eq_scaledInnerPartialZ {q z : ℝ}
    (hq : 0 < q) (hq1 : q < 1) :
    tailInnerGzReal (tailRReal q) q z = scaledInnerPartialZ q z := by
  rw [tailInnerGzReal, scaledInnerPartialZ, tailAReal_eq_A hq hq1]

theorem tailOuterGzReal_eq_scaledOuterPartialZ {q z : ℝ}
    (hq : 0 < q) (hq1 : q < 1) :
    tailOuterGzReal (tailRReal q) q z = scaledOuterPartialZ q z := by
  rw [tailOuterGzReal, scaledOuterPartialZ, tailAReal_eq_A hq hq1]

theorem tailInnerGrReal_eq_scaledInnerPartialQ_mul {q z : ℝ}
    (hq : 0 < q) (hq1 : q < 1) :
    tailInnerGrReal (tailRReal q) q (tailQrReal q) z =
      scaledInnerPartialQ q z * tailQrReal q := by
  rw [tailInnerGrReal, scaledInnerPartialQ,
    tailArReal_eq_Aprime_mul hq hq1, tailAReal_eq_A hq hq1,
    scaledDprime]
  ring

theorem tailOuterGrReal_eq_scaledOuterPartialQ_mul {q z : ℝ}
    (hq : 0 < q) (hq1 : q < 1) :
    tailOuterGrReal (tailRReal q) q (tailQrReal q) z =
      scaledOuterPartialQ q z * tailQrReal q := by
  rw [tailOuterGrReal, scaledOuterPartialQ,
    tailArReal_eq_Aprime_mul hq hq1, tailAReal_eq_A hq hq1,
    scaledDprime]
  ring

theorem tailZpSlopeReal_eq_scaled_mul {q z : ℝ}
    (hq : 0 < q) (hq1 : q < 1) :
    tailZpSlopeReal (tailRReal q) q (tailQrReal q) z =
      scaledZPlusSlopeAt q z * tailQrReal q := by
  rw [tailZpSlopeReal, scaledZPlusSlopeAt,
    tailInnerGrReal_eq_scaledInnerPartialQ_mul hq hq1,
    tailInnerGzReal_eq_scaledInnerPartialZ hq hq1]
  ring

theorem tailZmSlopeReal_eq_scaled_mul {q z : ℝ}
    (hq : 0 < q) (hq1 : q < 1) :
    tailZmSlopeReal (tailRReal q) q (tailQrReal q) z =
      scaledZMinusSlopeAt q z * tailQrReal q := by
  rw [tailZmSlopeReal, scaledZMinusSlopeAt,
    tailOuterGrReal_eq_scaledOuterPartialQ_mul hq hq1,
    tailOuterGzReal_eq_scaledOuterPartialZ hq hq1]
  ring

theorem tailLambdaRReal_eq_scaled_mul {q zp zm : ℝ}
    (hq : 0 < q) (hq1 : q < 1) :
    tailLambdaRReal (tailRReal q) q (tailQrReal q) zp zm =
      scaledLambdaDerivativeAt q zp zm * tailQrReal q := by
  rw [tailLambdaRReal, scaledLambdaDerivativeAt,
    tailZpSlopeReal_eq_scaled_mul hq hq1,
    tailZmSlopeReal_eq_scaled_mul hq hq1, scaledHprime, scaledH,
    scaledKprime, scaledK]
  ring

end OneCutTailCertificate

end

end Erdos1038
