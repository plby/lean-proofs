import ErdosProblems.Erdos327.Analytic.ThreeFormBoxAllCutoffs

/-!
# Power forms of the explicit three-form product envelopes

The finite sieve stores its Mertens estimates in exponential logarithmic
form.  This file converts them to the power forms used in the dyadic
summations, with explicit cutoff-independent constants.
-/

namespace Erdos327.Analytic

open Real

noncomputable section

/-- Uniform constant in the large-cutoff source product estimate. -/
def sourceLargeProductConstant : ℝ :=
  exp (-(5 / 2 : ℝ) *
      Mertens.Weight.M (f := Mertens.Weight.prime) +
    (5 / 2 : ℝ) * ((log 4 + 3) / log 2) +
    11 / 4 + 3 / 8)

/-- Uniform constant in the small-cutoff source product estimate. -/
def sourceSmallProductConstant : ℝ :=
  exp (-(5 / 2 : ℝ) *
      Mertens.Weight.M (f := Mertens.Weight.prime) +
    (5 / 2 : ℝ) * ((log 4 + 3) / log 2) +
    11 / 4)

theorem sourceLargeProductConstant_pos :
    0 < sourceLargeProductConstant := by
  unfold sourceLargeProductConstant
  positivity

theorem sourceSmallProductConstant_pos :
    0 < sourceSmallProductConstant := by
  unfold sourceSmallProductConstant
  positivity

private theorem inv_log_nat_le_inv_log_two
    {n : ℕ} (hn : 2 ≤ n) :
    1 / log (n : ℝ) ≤ 1 / log 2 := by
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hmono : log (2 : ℝ) ≤ log (n : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by norm_num)
      (by
        simpa only [Set.mem_Ioi]
          using (show (0 : ℝ) < (n : ℕ) by positivity))
      (by exact_mod_cast hn)
  exact one_div_le_one_div_of_le hlog2 hmono

/-- The large-cutoff source Mertens envelope has the advertised
`-7/4,-3/4` power form. -/
theorem exp_sourceMertensEnvelope_le_powers
    {L z : ℕ} (hL : 2 ≤ L) (hz : 2 ≤ z) :
    exp (sourceMertensEnvelope L z) ≤
      sourceLargeProductConstant *
        log (z : ℝ) ^ (-(7 / 4 : ℝ)) *
        log (L : ℝ) ^ (-(3 / 4 : ℝ)) := by
  have hlogL : 0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  have hlogz : 0 < log (z : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < z by omega))
  have hinvL := inv_log_nat_le_inv_log_two hL
  have hinvz := inv_log_nat_le_inv_log_two hz
  have hLcast : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hexponent :
      sourceMertensEnvelope L z ≤
        -(7 / 4 : ℝ) * log (log (z : ℝ)) -
          (3 / 4 : ℝ) * log (log (L : ℝ)) +
          (-(5 / 2 : ℝ) *
              Mertens.Weight.M (f := Mertens.Weight.prime) +
            (5 / 2 : ℝ) * ((log 4 + 3) / log 2) +
            11 / 4 + 3 / 8) := by
    unfold sourceMertensEnvelope primeInvMertensCenter
      primeInvMertensError
    have hcoef : 0 ≤ log (4 : ℝ) + 3 := by positivity
    have herrz :
        (log 4 + 3) / log (z : ℝ) ≤
          (log 4 + 3) / log 2 := by
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_left hinvz hcoef
    have herrL :
        (log 4 + 3) / log (L : ℝ) ≤
          (log 4 + 3) / log 2 := by
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_left hinvL hcoef
    have hlast : 3 / (4 * (L : ℝ)) ≤ 3 / 8 := by
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * L)
        (by norm_num : (0 : ℝ) < 8)).2
      nlinarith
    nlinarith
  refine (exp_le_exp.mpr hexponent).trans_eq ?_
  unfold sourceLargeProductConstant
  rw [Real.rpow_def_of_pos hlogz, Real.rpow_def_of_pos hlogL]
  rw [← exp_add, ← exp_add]
  congr 1
  ring

/-- The small-cutoff source Mertens envelope has power `-5/2`. -/
theorem exp_sourceSmallCutoffMertensEnvelope_le_power
    {z : ℕ} (hz : 2 ≤ z) :
    exp (sourceSmallCutoffMertensEnvelope z) ≤
      sourceSmallProductConstant *
        log (z : ℝ) ^ (-(5 / 2 : ℝ)) := by
  have hlogz : 0 < log (z : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < z by omega))
  have hinvz := inv_log_nat_le_inv_log_two hz
  have hexponent :
      sourceSmallCutoffMertensEnvelope z ≤
        -(5 / 2 : ℝ) * log (log (z : ℝ)) +
          (-(5 / 2 : ℝ) *
              Mertens.Weight.M (f := Mertens.Weight.prime) +
            (5 / 2 : ℝ) * ((log 4 + 3) / log 2) +
            11 / 4) := by
    unfold sourceSmallCutoffMertensEnvelope primeInvMertensCenter
      primeInvMertensError
    have hcoef : 0 ≤ log (4 : ℝ) + 3 := by positivity
    have herrz :
        (log 4 + 3) / log (z : ℝ) ≤
          (log 4 + 3) / log 2 := by
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_left hinvz hcoef
    nlinarith
  refine (exp_le_exp.mpr hexponent).trans_eq ?_
  unfold sourceSmallProductConstant
  rw [Real.rpow_def_of_pos hlogz, ← exp_add]
  congr 1
  ring

/-- Uniform mixed-product constant for the `L ≤ z` branch. -/
def mixedLargeProductConstant (alpha beta s : ℝ) : ℝ :=
  let a := alpha + beta + s - 3
  let b := 1 - alpha - beta - s
  exp ((a + b) * Mertens.Weight.M (f := Mertens.Weight.prime) +
    (|a| + |b|) * ((log 4 + 3) / log 2) +
    3 + |b| / 2)

/-- Uniform mixed-product constant for the `z < L` branch. -/
def mixedSmallProductConstant : ℝ :=
  exp (-2 * Mertens.Weight.M (f := Mertens.Weight.prime) +
    2 * ((log 4 + 3) / log 2) + 3)

theorem mixedLargeProductConstant_pos (alpha beta s : ℝ) :
    0 < mixedLargeProductConstant alpha beta s := by
  unfold mixedLargeProductConstant
  positivity

theorem mixedSmallProductConstant_pos :
    0 < mixedSmallProductConstant := by
  unfold mixedSmallProductConstant
  positivity

/-- Power form of the large-cutoff mixed Mertens envelope. -/
theorem exp_mixedMertensEnvelope_le_powers
    {L z : ℕ} {alpha beta s : ℝ}
    (hL : 2 ≤ L) (hz : 2 ≤ z) :
    exp (mixedMertensEnvelope L z alpha beta s) ≤
      mixedLargeProductConstant alpha beta s *
        log (z : ℝ) ^ (alpha + beta + s - 3) *
        log (L : ℝ) ^ (1 - alpha - beta - s) := by
  let a := alpha + beta + s - 3
  let b := 1 - alpha - beta - s
  have hlogL : 0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  have hlogz : 0 < log (z : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < z by omega))
  have hinvL := inv_log_nat_le_inv_log_two hL
  have hinvz := inv_log_nat_le_inv_log_two hz
  have hexponent :
      mixedMertensEnvelope L z alpha beta s ≤
        a * log (log (z : ℝ)) +
          b * log (log (L : ℝ)) +
          ((a + b) * Mertens.Weight.M (f := Mertens.Weight.prime) +
            (|a| + |b|) * ((log 4 + 3) / log 2) +
            3 + |b| / 2) := by
    unfold mixedMertensEnvelope primeInvMertensCenter
      primeInvMertensError
    dsimp [a, b]
    have hcoef : 0 ≤ log (4 : ℝ) + 3 := by positivity
    have herrz :
        (log 4 + 3) / log (z : ℝ) ≤
          (log 4 + 3) / log 2 := by
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_left hinvz hcoef
    have herrL :
        (log 4 + 3) / log (L : ℝ) ≤
          (log 4 + 3) / log 2 := by
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_left hinvL hcoef
    have hlast :
        |1 - alpha - beta - s| / (L : ℝ) ≤
          |1 - alpha - beta - s| / 2 := by
      exact div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num)
        (by exact_mod_cast hL)
    nlinarith [mul_le_mul_of_nonneg_left herrz
      (abs_nonneg (alpha + beta + s - 3)),
      mul_le_mul_of_nonneg_left herrL
        (abs_nonneg (1 - alpha - beta - s))]
  refine (exp_le_exp.mpr hexponent).trans_eq ?_
  unfold mixedLargeProductConstant
  dsimp [a, b]
  rw [Real.rpow_def_of_pos hlogz, Real.rpow_def_of_pos hlogL]
  rw [← exp_add, ← exp_add]
  congr 1
  ring

/-- Power form of the small-cutoff mixed Mertens envelope. -/
theorem exp_mixedSmallCutoffMertensEnvelope_le_power
    {z : ℕ} (hz : 2 ≤ z) :
    exp (mixedSmallCutoffMertensEnvelope z) ≤
      mixedSmallProductConstant *
        log (z : ℝ) ^ (-2 : ℝ) := by
  have hlogz : 0 < log (z : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < z by omega))
  have hinvz := inv_log_nat_le_inv_log_two hz
  have hexponent :
      mixedSmallCutoffMertensEnvelope z ≤
        -2 * log (log (z : ℝ)) +
          (-2 * Mertens.Weight.M (f := Mertens.Weight.prime) +
            2 * ((log 4 + 3) / log 2) + 3) := by
    unfold mixedSmallCutoffMertensEnvelope primeInvMertensCenter
      primeInvMertensError
    have hcoef : 0 ≤ log (4 : ℝ) + 3 := by positivity
    have herrz :
        (log 4 + 3) / log (z : ℝ) ≤
          (log 4 + 3) / log 2 := by
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_left hinvz hcoef
    nlinarith
  refine (exp_le_exp.mpr hexponent).trans_eq ?_
  unfold mixedSmallProductConstant
  rw [Real.rpow_def_of_pos hlogz, ← exp_add]
  congr 1
  ring

end

end Erdos327.Analytic
