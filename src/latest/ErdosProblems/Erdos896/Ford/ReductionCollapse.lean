/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos896.Ford.Reduction
import ErdosProblems.Erdos896.Ford.Denominator
import ErdosProblems.Erdos896.Ford.SumTk
import ErdosProblems.Erdos896.Ford.SquarefullDivisorTail
import ErdosProblems.Erdos896.Scale

/-!
# Collapsing Ford's finite reduction

This file is the analytic last step of the upper bound.  It first turns the
sharp estimate for `fordWeightSum` into the corresponding estimate for
`fordDenominatorSum`.  The remainder of the file collapses the squarefull
`q`, divisor `f`, and dyadic shell sums in `fordHReductionDenominatorWeight`.

The first section is deliberately stated with the weight estimate as an
explicit hypothesis.  This keeps the elementary `rpow` calculation usable
independently of the combinatorial proof of the estimate in `SumTk.lean`.
-/

namespace Erdos896.Ford

open Filter Asymptotics
open scoped BigOperators

/-- The logarithmic denominator is eventually bounded by the identity.  This
very coarse estimate is useful for absorbing finite initial ranges in later
uniform estimates. -/
theorem eventually_logDenom896_le_nat :
    ∀ᶠ n : ℕ in atTop, Erdos896.logDenom896 n ≤ (n : ℝ) := by
  have hreal := (Real.isLittleO_pow_log_id_atTop (n := 3)).bound
    (by norm_num : (0 : ℝ) < 1)
  have hnat := tendsto_natCast_atTop_atTop.eventually hreal
  filter_upwards [hnat, eventually_ge_atTop 3] with n hn hn3
  have hnpos : (0 : ℝ) < n := by positivity
  have hlog1 : 1 < Real.log (n : ℝ) := by
    rw [Real.lt_log_iff_exp_lt hnpos]
    exact Real.exp_one_lt_three.trans_le (by exact_mod_cast hn3)
  have hllpos : 0 < Real.log (Real.log (n : ℝ)) := Real.log_pos hlog1
  have hll_le_log : Real.log (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) := by
    exact Real.log_le_sub_one_of_pos
      (by linarith : 0 < Real.log (n : ℝ)) |>.trans (by linarith)
  have hfirst :
      (Real.log (n : ℝ)) ^ Erdos896.delta896 ≤ Real.log n := by
    simpa using Real.rpow_le_self_of_one_le hlog1.le
      Erdos896.delta896_le_one
  have hsecond :
      (Real.log (Real.log (n : ℝ))) ^ (3 / 2 : ℝ) ≤
        (Real.log (n : ℝ)) ^ (2 : ℕ) := by
    calc
      (Real.log (Real.log (n : ℝ))) ^ (3 / 2 : ℝ) ≤
          (Real.log (n : ℝ)) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow hllpos.le hll_le_log (by norm_num)
      _ ≤ (Real.log (n : ℝ)) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hlog1.le (by norm_num)
      _ = (Real.log (n : ℝ)) ^ (2 : ℕ) := Real.rpow_two _
  have hlogcube0 : 0 ≤ Real.log (n : ℝ) ^ (3 : ℕ) :=
    pow_nonneg (le_of_lt (zero_lt_one.trans hlog1)) 3
  have hncast0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [Real.norm_eq_abs, abs_of_nonneg hlogcube0, id_eq] at hn
  rw [Real.norm_eq_abs, abs_of_nonneg hncast0, one_mul] at hn
  unfold Erdos896.logDenom896 Erdos896.logDenom896R
  calc
    (Real.log (n : ℝ)) ^ Erdos896.delta896 *
        (Real.log (Real.log (n : ℝ))) ^ (3 / 2 : ℝ) ≤
      Real.log n * Real.log n ^ 2 :=
        mul_le_mul hfirst hsecond (Real.rpow_nonneg hllpos.le _)
          (le_of_lt (zero_lt_one.trans hlog1))
    _ = Real.log (n : ℝ) ^ 3 := by ring
    _ ≤ (n : ℝ) := hn

/-! ## Slow variation of the logarithmic denominator -/

private lemma logDenom896_le_log_rpow_five_halves
    {N : ℕ} (hN : 3 ≤ N) :
    Erdos896.logDenom896 N ≤ (Real.log (N : ℝ)) ^ (5 / 2 : ℝ) := by
  have hNreal : Real.exp 1 < (N : ℝ) :=
    Real.exp_one_lt_three.trans_le (by exact_mod_cast hN)
  have hNpos : (0 : ℝ) < N := (Real.exp_pos 1).trans hNreal
  have hlog_one : 1 < Real.log (N : ℝ) := by
    rw [Real.lt_log_iff_exp_lt hNpos]
    simpa using hNreal
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_one
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_one
  have hloglog_le :
      Real.log (Real.log (N : ℝ)) ≤ Real.log (N : ℝ) := by
    linarith [Real.log_le_sub_one_of_pos hlog_pos]
  have hfirst :
      (Real.log (N : ℝ)) ^ Erdos896.delta896 ≤ Real.log (N : ℝ) := by
    simpa [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hlog_one.le
        Erdos896.delta896_le_one)
  have hsecond :
      (Real.log (Real.log (N : ℝ))) ^ (3 / 2 : ℝ) ≤
        (Real.log (N : ℝ)) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hloglog_pos.le hloglog_le (by norm_num)
  unfold Erdos896.logDenom896 Erdos896.logDenom896R
  calc
    (Real.log (N : ℝ)) ^ Erdos896.delta896 *
          (Real.log (Real.log (N : ℝ))) ^ (3 / 2 : ℝ) ≤
        Real.log (N : ℝ) *
          (Real.log (N : ℝ)) ^ (3 / 2 : ℝ) := by
      exact mul_le_mul hfirst hsecond
        (Real.rpow_nonneg hloglog_pos.le _) hlog_pos.le
    _ = (Real.log (N : ℝ)) ^ (5 / 2 : ℝ) := by
      calc
        Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ (3 / 2 : ℝ) =
            (Real.log (N : ℝ)) ^ (1 : ℝ) *
              (Real.log (N : ℝ)) ^ (3 / 2 : ℝ) := by
          rw [Real.rpow_one]
        _ = (Real.log (N : ℝ)) ^ ((1 : ℝ) + 3 / 2) := by
          rw [Real.rpow_add hlog_pos]
        _ = (Real.log (N : ℝ)) ^ (5 / 2 : ℝ) := by norm_num

/-- The logarithmic denominator is smaller than every fixed positive power;
the exponent `1/8` is the one used in the squarefull-divisor moment. -/
theorem eventually_logDenom896_le_eighth_rpow :
    ∀ᶠ N : ℕ in atTop,
      Erdos896.logDenom896 N ≤ (N : ℝ) ^ (1 / 8 : ℝ) := by
  have hsmallReal :=
    (isLittleO_log_rpow_rpow_atTop (5 / 2 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 8)).bound one_pos
  have hsmallNat :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hsmallReal
  filter_upwards [hsmallNat, eventually_ge_atTop 3] with N hsmall hN
  have hlogpow_nonneg :
      0 ≤ (Real.log (N : ℝ)) ^ (5 / 2 : ℝ) := by positivity
  have hNpow_nonneg : 0 ≤ (N : ℝ) ^ (1 / 8 : ℝ) := by positivity
  have hpow :
      (Real.log (N : ℝ)) ^ (5 / 2 : ℝ) ≤
        (N : ℝ) ^ (1 / 8 : ℝ) := by
    simpa only [one_mul, Real.norm_eq_abs, abs_of_nonneg hlogpow_nonneg,
      abs_of_nonneg hNpow_nonneg] using hsmall
  exact (logDenom896_le_log_rpow_five_halves hN).trans hpow

private lemma eventually_logDenom896_le_sixteenth_rpow :
    ∀ᶠ N : ℕ in atTop,
      Erdos896.logDenom896 N ≤ (N : ℝ) ^ (1 / 16 : ℝ) := by
  have hsmallReal :=
    (isLittleO_log_rpow_rpow_atTop (5 / 2 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 16)).bound one_pos
  have hsmallNat :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hsmallReal
  filter_upwards [hsmallNat, eventually_ge_atTop 3] with N hsmall hN
  have hlogpow_nonneg :
      0 ≤ (Real.log (N : ℝ)) ^ (5 / 2 : ℝ) := by positivity
  have hNpow_nonneg : 0 ≤ (N : ℝ) ^ (1 / 16 : ℝ) := by positivity
  have hpow :
      (Real.log (N : ℝ)) ^ (5 / 2 : ℝ) ≤
        (N : ℝ) ^ (1 / 16 : ℝ) := by
    simpa only [one_mul, Real.norm_eq_abs, abs_of_nonneg hlogpow_nonneg,
      abs_of_nonneg hNpow_nonneg] using hsmall
  exact (logDenom896_le_log_rpow_five_halves hN).trans hpow

private lemma one_le_logDenom896_of_27_le {N : ℕ} (hN : 27 ≤ N) :
    1 ≤ Erdos896.logDenom896 N := by
  have hexp3 : Real.exp 3 < 27 := by
    calc
      Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
        rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add,
          Real.exp_add]
      _ < 27 := by
        nlinarith [Real.exp_pos 1, Real.exp_one_lt_three]
  have hexpexp : Real.exp (Real.exp 1) < (N : ℝ) := by
    exact (Real.exp_lt_exp.mpr Real.exp_one_lt_three).trans
      (hexp3.trans_le (by exact_mod_cast hN))
  have hNpos : (0 : ℝ) < N := by positivity
  have hlog_exp : Real.exp 1 < Real.log (N : ℝ) := by
    rw [Real.lt_log_iff_exp_lt hNpos]
    exact hexpexp
  have hlog_one : 1 ≤ Real.log (N : ℝ) :=
    (show (1 : ℝ) < Real.exp 1 from
      Real.one_lt_exp_iff.mpr zero_lt_one).le.trans hlog_exp.le
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog_one
  have hloglog_one : 1 ≤ Real.log (Real.log (N : ℝ)) := by
    apply (Real.le_log_iff_exp_le hlog_pos).2
    exact hlog_exp.le
  unfold Erdos896.logDenom896 Erdos896.logDenom896R
  exact one_le_mul_of_one_le_of_one_le
    (Real.one_le_rpow hlog_one Erdos896.delta896_nonneg)
    (Real.one_le_rpow hloglog_one (by norm_num))

private lemma sixteenth_rpow_le_div_eighth_rpow
    {y t : ℕ} (ht : 0 < t) (hsq : t ^ 2 ≤ y) :
    (y : ℝ) ^ (1 / 16 : ℝ) ≤
      ((y : ℝ) / (t : ℝ)) ^ (1 / 8 : ℝ) := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hyR : (0 : ℝ) < y := by
    exact_mod_cast (lt_of_lt_of_le (pow_pos ht 2) hsq)
  have hsqR : (t : ℝ) ^ 2 ≤ (y : ℝ) := by exact_mod_cast hsq
  have hlogsq : Real.log ((t : ℝ) ^ 2) ≤ Real.log (y : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (pow_pos htR 2)) (Set.mem_Ioi.mpr hyR) hsqR
  have htwolog : 2 * Real.log (t : ℝ) ≤ Real.log (y : ℝ) := by
    simpa [Real.log_pow] using hlogsq
  have hratio : 0 < (y : ℝ) / (t : ℝ) := div_pos hyR htR
  rw [← Real.log_le_log_iff
    (Real.rpow_pos_of_pos hyR _) (Real.rpow_pos_of_pos hratio _),
    Real.log_rpow hyR, Real.log_rpow hratio,
    Real.log_div hyR.ne' htR.ne']
  nlinarith

/-- A concrete Potter bound for the logarithmic denominator. -/
theorem exists_logDenom896_potter_eighth :
    ∃ T : ℕ, 27 ≤ T ∧ ∀ y t : ℕ, T ≤ y → T ≤ t →
      Erdos896.logDenom896 y ≤
        8 * max 1 (((y : ℝ) / (t : ℝ)) ^ (1 / 8 : ℝ)) *
          Erdos896.logDenom896 t := by
  have hsubpower := eventually_logDenom896_le_sixteenth_rpow
  rw [eventually_atTop] at hsubpower
  obtain ⟨T₀, hT₀⟩ := hsubpower
  refine ⟨max 27 T₀, le_max_left _ _, ?_⟩
  intro y t hy ht
  have hy27 : 27 ≤ y := (le_max_left 27 T₀).trans hy
  have ht27 : 27 ≤ t := (le_max_left 27 T₀).trans ht
  have hyT₀ : T₀ ≤ y := (le_max_right 27 T₀).trans hy
  have hden_y_nonneg : 0 ≤ Erdos896.logDenom896 y :=
    (Erdos896.logDenom896_pos (by omega)).le
  have hden_t_one : 1 ≤ Erdos896.logDenom896 t :=
    one_le_logDenom896_of_27_le ht27
  let M : ℝ := max 1 (((y : ℝ) / (t : ℝ)) ^ (1 / 8 : ℝ))
  have hM_one : 1 ≤ M := le_max_left _ _
  have hM_nonneg : 0 ≤ M := zero_le_one.trans hM_one
  by_cases hyt : y ≤ t ^ 2
  · have hmono :
        Erdos896.logDenom896 y ≤ Erdos896.logDenom896 (t ^ 2) :=
      Erdos896.logDenom896_mono (by omega) hyt
    have hsquare :
        Erdos896.logDenom896 (t ^ 2) ≤
          8 * Erdos896.logDenom896 t :=
      Erdos896.logDenom896_sq_le t (by omega)
    have h8M : (8 : ℝ) ≤ 8 * M := by nlinarith
    calc
      Erdos896.logDenom896 y ≤
          8 * Erdos896.logDenom896 t := hmono.trans hsquare
      _ ≤ 8 * M * Erdos896.logDenom896 t := by
        exact mul_le_mul_of_nonneg_right h8M
          (zero_le_one.trans hden_t_one)
  · have hsq : t ^ 2 ≤ y := by omega
    have hsub :
        Erdos896.logDenom896 y ≤ (y : ℝ) ^ (1 / 16 : ℝ) :=
      hT₀ y hyT₀
    have hratio :
        (y : ℝ) ^ (1 / 16 : ℝ) ≤
          ((y : ℝ) / (t : ℝ)) ^ (1 / 8 : ℝ) :=
      sixteenth_rpow_le_div_eighth_rpow (by omega) hsq
    have hratio_M :
        ((y : ℝ) / (t : ℝ)) ^ (1 / 8 : ℝ) ≤ M :=
      le_max_right _ _
    have hM_mul : M ≤ M * Erdos896.logDenom896 t :=
      le_mul_of_one_le_right hM_nonneg hden_t_one
    calc
      Erdos896.logDenom896 y ≤ (y : ℝ) ^ (1 / 16 : ℝ) := hsub
      _ ≤ ((y : ℝ) / (t : ℝ)) ^ (1 / 8 : ℝ) := hratio
      _ ≤ M := hratio_M
      _ ≤ M * Erdos896.logDenom896 t := hM_mul
      _ ≤ 8 * M * Erdos896.logDenom896 t := by
        exact mul_le_mul_of_nonneg_right
          (by nlinarith : M ≤ 8 * M) (zero_le_one.trans hden_t_one)

/-- Positive-constant packaging of the Potter bound. -/
theorem exists_pos_logDenom896_potter_eighth :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, ∀ y t : ℕ, T ≤ y → T ≤ t →
      Erdos896.logDenom896 y ≤
        C * max 1 (((y : ℝ) / (t : ℝ)) ^ (1 / 8 : ℝ)) *
          Erdos896.logDenom896 t := by
  obtain ⟨T, -, hT⟩ := exists_logDenom896_potter_eighth
  exact ⟨8, by norm_num, T, hT⟩

/-- The scale which occurs on the right side of Ford's sharp weighted-sum
estimate. -/
noncomputable def fordWeightScale (t : ℕ) : ℝ :=
  (Real.log t) ^ (2 - Erdos896.delta896) /
    (Real.log (Real.log t)) ^ (3 / 2 : ℝ)

/-- Removing the two powers of `log t` from Ford's weight scale leaves the
reciprocal Erdős--Tenenbaum--Ford denominator. -/
theorem inv_log_sq_mul_fordWeightScale {t : ℕ} (ht : 3 ≤ t) :
    (1 / Real.log t ^ 2) * fordWeightScale t =
      1 / Erdos896.logDenom896 t := by
  have hlog : 0 < Real.log t :=
    Real.log_pos (by exact_mod_cast (show 1 < t by omega))
  have hloglog : 0 < Real.log (Real.log t) := by
    exact Real.log_pos (by
      rw [Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < t)]
      exact Real.exp_one_lt_three.trans_le (by exact_mod_cast ht))
  have hpow :
      (Real.log t) ^ (2 - Erdos896.delta896) =
        Real.log t ^ 2 * (Real.log t) ^ (-Erdos896.delta896) := by
    calc
      (Real.log t) ^ (2 - Erdos896.delta896) =
          (Real.log t) ^ ((2 : ℝ) + (-Erdos896.delta896)) := by ring_nf
      _ = (Real.log t) ^ (2 : ℝ) *
          (Real.log t) ^ (-Erdos896.delta896) := by
        rw [Real.rpow_add hlog]
      _ = Real.log t ^ 2 *
          (Real.log t) ^ (-Erdos896.delta896) := by
        rw [Real.rpow_two]
  rw [fordWeightScale, hpow, Real.rpow_neg hlog.le]
  unfold Erdos896.logDenom896 Erdos896.logDenom896R
  field_simp [hlog.ne', ne_of_gt (Real.rpow_pos_of_pos hlog _),
    ne_of_gt (Real.rpow_pos_of_pos hloglog _)]

/-- Pointwise form of denominator removal followed by the elementary scale
calculation. -/
theorem fordDenominatorSum_le_inv_logDenom_of_weight_le
    {t : ℕ} (ht : 3 ≤ t) {Cden Cweight : ℝ}
    (hCden : 0 ≤ Cden)
    (hden : fordDenominatorSum t ≤
      Cden / Real.log t ^ 2 * fordWeightSum t)
    (hweight : fordWeightSum t ≤ Cweight * fordWeightScale t) :
    fordDenominatorSum t ≤
      (Cden * Cweight) / Erdos896.logDenom896 t := by
  calc
    fordDenominatorSum t ≤
        Cden / Real.log t ^ 2 * fordWeightSum t := hden
    _ ≤ Cden / Real.log t ^ 2 *
        (Cweight * fordWeightScale t) := by
      exact mul_le_mul_of_nonneg_left hweight
        (div_nonneg hCden (sq_nonneg _))
    _ = (Cden * Cweight) *
        ((1 / Real.log t ^ 2) * fordWeightScale t) := by ring
    _ = (Cden * Cweight) / Erdos896.logDenom896 t := by
      rw [inv_log_sq_mul_fordWeightScale ht]
      ring

/-- A sharp eventual bound for `fordWeightSum` implies the expected
reciprocal-`logDenom896` bound for `fordDenominatorSum`.  This is the exact
interface consumed by the `q/f` and dyadic collapse below. -/
theorem exists_fordDenominatorSum_le_inv_logDenom_of_weight_bound
    {T : ℕ} {Cweight : ℝ} (hT : 3 ≤ T) (_hCweight : 0 ≤ Cweight)
    (hweight : ∀ t : ℕ, T ≤ t →
      fordWeightSum t ≤ Cweight * fordWeightScale t) :
    ∃ Cden : ℝ, 0 ≤ Cden ∧ ∀ t : ℕ, T ≤ t →
      fordDenominatorSum t ≤
        (Cden * Cweight) / Erdos896.logDenom896 t := by
  obtain ⟨Cden, hCden, hden⟩ :=
    exists_fordDenominatorSum_le_const_div_log_sq
  refine ⟨Cden, hCden, fun t ht ↦ ?_⟩
  exact fordDenominatorSum_le_inv_logDenom_of_weight_le
    (hT.trans ht) hCden (hden t (by omega)) (hweight t ht)

/-- Positive-constant packaging of the preceding pointwise estimate. -/
theorem exists_pos_fordDenominatorSum_le_inv_logDenom_of_weight_bound
    {T : ℕ} {Cweight : ℝ} (hT : 3 ≤ T) (hCweight : 0 < Cweight)
    (hweight : ∀ t : ℕ, T ≤ t →
      fordWeightSum t ≤ Cweight * fordWeightScale t) :
    ∃ A : ℝ, 0 < A ∧ ∃ K : ℕ, ∀ {t : ℕ}, K ≤ t →
      fordDenominatorSum t ≤ A / Erdos896.logDenom896 t := by
  obtain ⟨Cden, hCden, hden⟩ :=
    exists_fordDenominatorSum_le_inv_logDenom_of_weight_bound
      hT hCweight.le hweight
  let A := Cden * Cweight + 1
  have hA : 0 < A := by
    dsimp [A]
    positivity
  refine ⟨A, hA, T, ?_⟩
  intro t ht
  have ht3 := hT.trans ht
  have hL : 0 < Erdos896.logDenom896 t :=
    Erdos896.logDenom896_pos ht3
  calc
    fordDenominatorSum t ≤
        (Cden * Cweight) / Erdos896.logDenom896 t := hden t ht
    _ ≤ A / Erdos896.logDenom896 t := by
      exact div_le_div_of_nonneg_right (by dsimp [A]; linarith) hL.le

/-- The slow-variation loss used in the uniform denominator envelope. -/
private noncomputable def fordDenominatorEnvelopeRatio (y T : ℕ) : ℝ :=
  (max 1 ((y : ℝ) / (T : ℝ))) ^ (1 / 8 : ℝ)

/-- An eventual reciprocal-denominator estimate can be made uniform in a
second, larger scale `y`.  The finite initial range of `T` is absorbed into
the constant, while the Potter bound handles all later `T`. -/
theorem exists_fordDenominatorSum_uniform_envelope
    (hpotter : ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ,
      ∀ {y T : ℕ}, K ≤ y → K ≤ T →
        Erdos896.logDenom896 y ≤
          C * fordDenominatorEnvelopeRatio y T *
            Erdos896.logDenom896 T)
    (hgrowth : ∃ G : ℝ, 0 < G ∧ ∃ Y : ℕ,
      ∀ {y : ℕ}, Y ≤ y →
        Erdos896.logDenom896 y ≤ G * (y : ℝ) ^ (1 / 8 : ℝ))
    (hpoint : ∃ A : ℝ, 0 < A ∧ ∃ K : ℕ,
      ∀ {T : ℕ}, K ≤ T →
        fordDenominatorSum T ≤ A / Erdos896.logDenom896 T) :
    ∃ B : ℝ, 0 < B ∧ ∃ Y₀ : ℕ, ∀ {y T : ℕ}, Y₀ ≤ y → 2 ≤ T →
      fordDenominatorSum T ≤
        B * (max 1 ((y : ℝ) / (T : ℝ))) ^ (1 / 8 : ℝ) /
          Erdos896.logDenom896 y := by
  obtain ⟨C, hC, KC, hpotter⟩ := hpotter
  obtain ⟨G, hG, YG, hgrowth⟩ := hgrowth
  obtain ⟨A, hA, KA, hpoint⟩ := hpoint
  let K : ℕ := max 3 (max KC KA)
  let S : ℝ := Finset.sum (Finset.range K) fun t ↦
    fordDenominatorSum t * (t : ℝ) ^ (1 / 8 : ℝ)
  let B : ℝ := 1 + A * C + G * S
  let Y₀ : ℕ := max K YG
  have hK3 : 3 ≤ K := le_max_left _ _
  have hK_C : KC ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have hK_A : KA ≤ K := le_trans (le_max_right _ _) (le_max_right _ _)
  have hS0 : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun t _ ↦
      mul_nonneg (fordDenominatorSum_nonneg t)
        (Real.rpow_nonneg (Nat.cast_nonneg t) _)
  have hB : 0 < B := by
    dsimp [B]
    positivity
  refine ⟨B, hB, Y₀, ?_⟩
  intro y T hy hT2
  have hyK : K ≤ y := le_trans (le_max_left _ _) hy
  have hyG : YG ≤ y := le_trans (le_max_right _ _) hy
  have hy3 : 3 ≤ y := hK3.trans hyK
  have hLy : 0 < Erdos896.logDenom896 y :=
    Erdos896.logDenom896_pos hy3
  have hR : 0 < fordDenominatorEnvelopeRatio y T := by
    exact Real.rpow_pos_of_pos
      (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _
  change fordDenominatorSum T ≤
    B * fordDenominatorEnvelopeRatio y T / Erdos896.logDenom896 y
  by_cases hTK : K ≤ T
  · have hT3 : 3 ≤ T := hK3.trans hTK
    have hLT : 0 < Erdos896.logDenom896 T :=
      Erdos896.logDenom896_pos hT3
    have hp := hpotter (hK_C.trans hyK) (hK_C.trans hTK)
    have hd := hpoint (hK_A.trans hTK)
    have hACB : A * C ≤ B := by
      dsimp [B]
      nlinarith [mul_nonneg hG.le hS0]
    calc
      fordDenominatorSum T ≤ A / Erdos896.logDenom896 T := hd
      _ ≤ (A * C) * fordDenominatorEnvelopeRatio y T /
          Erdos896.logDenom896 y := by
        rw [div_le_div_iff₀ hLT hLy]
        have := mul_le_mul_of_nonneg_left hp hA.le
        nlinarith
      _ ≤ B * fordDenominatorEnvelopeRatio y T /
          Erdos896.logDenom896 y := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hACB hR.le) hLy.le
  · have hTlt : T < K := Nat.lt_of_not_ge hTK
    have hTy : T ≤ y := hTlt.le.trans hyK
    have hTposR : (0 : ℝ) < T := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hT2)
    have hyR0 : (0 : ℝ) ≤ y := Nat.cast_nonneg y
    have hdiv1 : (1 : ℝ) ≤ (y : ℝ) / (T : ℝ) := by
      rw [le_div_iff₀ hTposR]
      simpa using (by exact_mod_cast hTy : (T : ℝ) ≤ y)
    have hratio : fordDenominatorEnvelopeRatio y T =
        ((y : ℝ) / (T : ℝ)) ^ (1 / 8 : ℝ) := by
      rw [fordDenominatorEnvelopeRatio, max_eq_right hdiv1]
    have hpowT : 0 < (T : ℝ) ^ (1 / 8 : ℝ) :=
      Real.rpow_pos_of_pos hTposR _
    have hpowY : 0 < (y : ℝ) ^ (1 / 8 : ℝ) := by
      have : (0 : ℝ) < y :=
        lt_of_lt_of_le hTposR (by exact_mod_cast hTy)
      exact Real.rpow_pos_of_pos this _
    have hratio' : fordDenominatorEnvelopeRatio y T =
        (y : ℝ) ^ (1 / 8 : ℝ) / (T : ℝ) ^ (1 / 8 : ℝ) := by
      rw [hratio, Real.div_rpow hyR0 hTposR.le]
    have hterm :
        fordDenominatorSum T * (T : ℝ) ^ (1 / 8 : ℝ) ≤ S := by
      dsimp [S]
      refine Finset.single_le_sum (s := Finset.range K)
        (f := fun i : ℕ ↦
          fordDenominatorSum i * (i : ℝ) ^ (1 / 8 : ℝ)) ?_ ?_
      · intro i hi
        exact mul_nonneg (fordDenominatorSum_nonneg i)
          (Real.rpow_nonneg (Nat.cast_nonneg i) _)
      · exact Finset.mem_range.mpr hTlt
    have hGBterm :
        G * (fordDenominatorSum T * (T : ℝ) ^ (1 / 8 : ℝ)) ≤ B := by
      have hGS : G * S ≤ B := by
        dsimp [B]
        nlinarith [mul_pos hA hC]
      exact (mul_le_mul_of_nonneg_left hterm hG.le).trans hGS
    have hgy := hgrowth hyG
    rw [hratio']
    have hdivform :
        B * ((y : ℝ) ^ (1 / 8 : ℝ) / (T : ℝ) ^ (1 / 8 : ℝ)) /
            Erdos896.logDenom896 y =
          B * (y : ℝ) ^ (1 / 8 : ℝ) /
            ((T : ℝ) ^ (1 / 8 : ℝ) * Erdos896.logDenom896 y) := by
      ring
    rw [hdivform]
    rw [le_div_iff₀ (mul_pos hpowT hLy)]
    have hf0 : 0 ≤ fordDenominatorSum T := fordDenominatorSum_nonneg T
    have hleft :
        fordDenominatorSum T *
            ((T : ℝ) ^ (1 / 8 : ℝ) * Erdos896.logDenom896 y) ≤
          (G * (fordDenominatorSum T * (T : ℝ) ^ (1 / 8 : ℝ))) *
            (y : ℝ) ^ (1 / 8 : ℝ) := by
      have := mul_le_mul_of_nonneg_left hgy (mul_nonneg hf0 hpowT.le)
      nlinarith
    calc
      fordDenominatorSum T *
          ((T : ℝ) ^ (1 / 8 : ℝ) * Erdos896.logDenom896 y) ≤
        (G * (fordDenominatorSum T * (T : ℝ) ^ (1 / 8 : ℝ))) *
          (y : ℝ) ^ (1 / 8 : ℝ) := hleft
      _ ≤ B * (y : ℝ) ^ (1 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_right hGBterm hpowY.le

/-- The actual Potter and subpower estimates proved above turn any eventual
pointwise denominator estimate into the uniform envelope needed by the
dyadic reduction. -/
theorem exists_fordDenominatorSum_uniform_envelope_of_pointwise
    (hpoint : ∃ A : ℝ, 0 < A ∧ ∃ K : ℕ,
      ∀ {T : ℕ}, K ≤ T →
        fordDenominatorSum T ≤ A / Erdos896.logDenom896 T) :
    ∃ B : ℝ, 0 < B ∧ ∃ Y₀ : ℕ, ∀ {y T : ℕ}, Y₀ ≤ y → 2 ≤ T →
      fordDenominatorSum T ≤
        B * (max 1 ((y : ℝ) / (T : ℝ))) ^ (1 / 8 : ℝ) /
          Erdos896.logDenom896 y := by
  have hpotter : ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ,
      ∀ {y T : ℕ}, K ≤ y → K ≤ T →
        Erdos896.logDenom896 y ≤
          C * fordDenominatorEnvelopeRatio y T *
            Erdos896.logDenom896 T := by
    obtain ⟨C, hC, K, hK⟩ := exists_pos_logDenom896_potter_eighth
    exact ⟨C, hC, K, fun hy hT ↦ by
      rw [fordDenominatorEnvelopeRatio,
        Real.rpow_max (by norm_num) (by positivity) (by norm_num)]
      simpa using hK _ _ hy hT⟩
  have hgrowth : ∃ G : ℝ, 0 < G ∧ ∃ Y : ℕ,
      ∀ {y : ℕ}, Y ≤ y →
        Erdos896.logDenom896 y ≤ G * (y : ℝ) ^ (1 / 8 : ℝ) := by
    have hg := eventually_logDenom896_le_eighth_rpow
    rw [eventually_atTop] at hg
    obtain ⟨Y, hY⟩ := hg
    exact ⟨1, by norm_num, Y, fun hy ↦ by simpa using hY _ hy⟩
  exact exists_fordDenominatorSum_uniform_envelope hpotter hgrowth hpoint

/-- Direct consumer interface from Ford's sharp weighted-sum estimate to a
uniform denominator envelope at every dyadic argument. -/
theorem exists_fordDenominatorSum_uniform_envelope_of_weight_bound
    {T : ℕ} {Cweight : ℝ} (hT : 3 ≤ T) (hCweight : 0 < Cweight)
    (hweight : ∀ t : ℕ, T ≤ t →
      fordWeightSum t ≤ Cweight * fordWeightScale t) :
    ∃ B : ℝ, 0 < B ∧ ∃ Y₀ : ℕ, ∀ {y t : ℕ}, Y₀ ≤ y → 2 ≤ t →
      fordDenominatorSum t ≤
        B * (max 1 ((y : ℝ) / (t : ℝ))) ^ (1 / 8 : ℝ) /
          Erdos896.logDenom896 y := by
  apply exists_fordDenominatorSum_uniform_envelope_of_pointwise
  exact exists_pos_fordDenominatorSum_le_inv_logDenom_of_weight_bound
    hT hCweight hweight

/-- Existential form matching the final output of `SumTk.lean`. -/
theorem exists_fordDenominatorSum_uniform_envelope_of_weight_estimate
    (hweight : ∃ Cweight : ℝ, 0 < Cweight ∧ ∃ T : ℕ,
      ∀ t : ℕ, T ≤ t → fordWeightSum t ≤ Cweight * fordWeightScale t) :
    ∃ B : ℝ, 0 < B ∧ ∃ Y₀ : ℕ, ∀ {y t : ℕ}, Y₀ ≤ y → 2 ≤ t →
      fordDenominatorSum t ≤
        B * (max 1 ((y : ℝ) / (t : ℝ))) ^ (1 / 8 : ℝ) /
          Erdos896.logDenom896 y := by
  obtain ⟨Cweight, hCweight, T, hweight⟩ := hweight
  apply exists_fordDenominatorSum_uniform_envelope_of_weight_bound
    (T := max T 3) (Cweight := Cweight) (le_max_right _ _) hCweight
  intro t ht
  exact hweight t ((le_max_left T 3).trans ht)

/-! ## Dyadic geometric sums -/

theorem sum_inv_two_pow_le_two (s : Finset ℕ) :
    (∑ k ∈ s, ((2 ^ k : ℕ) : ℝ)⁻¹) ≤ 2 := by
  have hterm (k : ℕ) :
      ((2 ^ k : ℕ) : ℝ)⁻¹ = ((1 : ℝ) / 2) ^ k := by
    norm_num [Nat.cast_pow, inv_pow, div_pow]
  simp_rw [hterm]
  exact (summable_geometric_two.sum_le_tsum s fun _ _ ↦ by positivity).trans_eq
    tsum_geometric_two

theorem cast_div_ratio_le_inv_pow_two (X k : ℕ) (hX : 0 < X) :
    ((X / 2 ^ k : ℕ) : ℝ) / (X : ℝ) ≤
      ((2 ^ k : ℕ) : ℝ)⁻¹ := by
  rw [div_le_iff₀ (Nat.cast_pos.mpr hX)]
  simpa [div_eq_mul_inv, mul_comm] using
    (Nat.cast_div_le (α := ℝ) (m := X) (n := 2 ^ k))

/-- Ratio of the geometric series left after paying the `1/8` Potter loss. -/
noncomputable def fordDyadicEighthRatio : ℝ :=
  (2 : ℝ)⁻¹ * (2 : ℝ) ^ ((1 : ℝ) / 8)

private lemma fordDyadicEighthRatio_nonneg : 0 ≤ fordDyadicEighthRatio := by
  unfold fordDyadicEighthRatio
  positivity

private lemma fordDyadicEighthRatio_lt_one : fordDyadicEighthRatio < 1 := by
  have hpow : (2 : ℝ) ^ ((1 : ℝ) / 8) < 2 :=
    Real.rpow_lt_self_of_one_lt (by norm_num) (by norm_num)
  unfold fordDyadicEighthRatio
  calc
    (2 : ℝ)⁻¹ * 2 ^ ((1 : ℝ) / 8) =
        2 ^ ((1 : ℝ) / 8) / 2 := by ring
    _ < 2 / 2 := (div_lt_div_iff_of_pos_right (by norm_num)).2 hpow
    _ = 1 := by norm_num

private lemma ford_weighted_eighth_term_eq (k : ℕ) :
    ((2 ^ k : ℕ) : ℝ)⁻¹ *
        ((2 ^ k : ℕ) : ℝ) ^ ((1 : ℝ) / 8) =
      fordDyadicEighthRatio ^ k := by
  unfold fordDyadicEighthRatio
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [← inv_pow]
  rw [← Real.rpow_natCast_mul (by positivity : (0 : ℝ) ≤ 2)
    k ((1 : ℝ) / 8)]
  rw [mul_comm (k : ℝ) ((1 : ℝ) / 8)]
  rw [Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ 2)
    ((1 : ℝ) / 8) k]
  rw [mul_pow]

theorem sum_weighted_eighth_le (s : Finset ℕ) :
    (∑ k ∈ s, ((2 ^ k : ℕ) : ℝ)⁻¹ *
      ((2 ^ k : ℕ) : ℝ) ^ ((1 : ℝ) / 8)) ≤
        (1 - fordDyadicEighthRatio)⁻¹ := by
  simp_rw [ford_weighted_eighth_term_eq]
  exact ((summable_geometric_of_lt_one fordDyadicEighthRatio_nonneg
    fordDyadicEighthRatio_lt_one).sum_le_tsum s
      fun _ _ ↦ pow_nonneg fordDyadicEighthRatio_nonneg _).trans_eq
        (tsum_geometric_of_lt_one fordDyadicEighthRatio_nonneg
          fordDyadicEighthRatio_lt_one)

theorem fordDyadicEighthConstant_pos :
    0 < (1 - fordDyadicEighthRatio)⁻¹ := by
  exact inv_pos.mpr (sub_pos.mpr fordDyadicEighthRatio_lt_one)

/-! ## The active local dyadic estimate -/

private lemma active_div_le_div_rpow_one_eighth {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    a / b ≤ a ^ (1 / 8 : ℝ) / b ^ (1 / 8 : ℝ) := by
  have hb : 0 < b := ha.trans_le hab
  have ht0 : 0 < a / b := div_pos ha hb
  have ht1 : a / b ≤ 1 := (div_le_one hb).2 hab
  have ht := Real.rpow_le_rpow_of_exponent_ge ht0 ht1
    (by norm_num : (1 / 8 : ℝ) ≤ 1)
  rw [Real.rpow_one] at ht
  simpa [Real.div_rpow ha.le hb.le] using ht

private lemma active_base_bound
    {x y q f : ℕ} {G : ℝ}
    (hy : 3 ≤ y) (hxy : y ^ 2 ≤ x)
    (hq : q ∈ squarefullSet x) (hfmem : f ∈ q.divisors)
    (hG : 0 ≤ G)
    (hgrowth : Erdos896.logDenom896 y ≤
      G * (y : ℝ) ^ (1 / 8 : ℝ))
    (hactive : 3 ≤ y / f ∧ 8 * (y / f) ≤ x / q) :
    (((8 * (y / f) : ℕ) : ℝ) / ((x / q : ℕ) : ℝ)) ≤
      (16 * G) *
        (max (f : ℝ) ((q / f : ℕ) : ℝ)) ^ (1 / 8 : ℝ) /
          Erdos896.logDenom896 y := by
  have hqData := mem_squarefullSet.mp hq
  have hqPos : 0 < q := by omega
  have hfDvd : f ∣ q := Nat.dvd_of_mem_divisors hfmem
  have hfPos : 0 < f := Nat.pos_of_dvd_of_pos hfDvd hqPos
  have hrPos : 0 < q / f :=
    Nat.div_pos (Nat.le_of_dvd hqPos hfDvd) hfPos
  have hfactor : f * (q / f) = q := by
    simpa [mul_comm] using Nat.div_mul_cancel hfDvd
  have hYPos : 0 < y / f := by omega
  have hXPos : 0 < x / q := by omega
  have hyPos : 0 < y := by omega
  have hL : 0 < Erdos896.logDenom896 y := Erdos896.logDenom896_pos hy
  have hrM : ((q / f : ℕ) : ℝ) ≤
      max (f : ℝ) ((q / f : ℕ) : ℝ) := le_max_right _ _
  have hrPowM : ((q / f : ℕ) : ℝ) ^ (1 / 8 : ℝ) ≤
      (max (f : ℝ) ((q / f : ℕ) : ℝ)) ^ (1 / 8 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hrM (by norm_num)
  have hbaseOne :
      (((8 * (y / f) : ℕ) : ℝ) / ((x / q : ℕ) : ℝ)) ≤ 1 := by
    exact (div_le_one (by positivity)).2 (by exact_mod_cast hactive.2)
  have hxlt : x < q * (x / q + 1) := Nat.lt_mul_div_succ x hqPos
  have hsucc : x / q + 1 ≤ 2 * (x / q) := by omega
  have hfY : f * (y / f) ≤ y := by
    simpa [mul_comm] using Nat.div_mul_le_self y f
  have hbaseRatio :
      (((8 * (y / f) : ℕ) : ℝ) / ((x / q : ℕ) : ℝ)) ≤
        16 * ((q / f : ℕ) : ℝ) / (y : ℝ) := by
    have hxlt' : x < 2 * q * (x / q) := by
      calc
        x < q * (x / q + 1) := hxlt
        _ ≤ q * (2 * (x / q)) := Nat.mul_le_mul_left q hsucc
        _ = 2 * q * (x / q) := by ring
    have hsquare : y * y ≤ x := by simpa [pow_two] using hxy
    have hcore : f * (y / f) * y ≤
        2 * f * (q / f) * (x / q) := by
      calc
        f * (y / f) * y ≤ y * y := Nat.mul_le_mul_right y hfY
        _ ≤ x := hsquare
        _ ≤ 2 * q * (x / q) := hxlt'.le
        _ = 2 * (f * (q / f)) * (x / q) := by
          exact congrArg (fun z : ℕ ↦ 2 * z * (x / q)) hfactor.symm
        _ = 2 * f * (q / f) * (x / q) := by ring
    have hcoreCancel : (y / f) * y ≤ 2 * (q / f) * (x / q) := by
      apply Nat.le_of_mul_le_mul_left _ hfPos
      simpa [mul_assoc, mul_left_comm, mul_comm] using hcore
    have hXR : (0 : ℝ) < ((x / q : ℕ) : ℝ) := by exact_mod_cast hXPos
    have hyR : (0 : ℝ) < y := by exact_mod_cast hyPos
    rw [div_le_div_iff₀ hXR hyR]
    exact_mod_cast (show 8 * (y / f) * y ≤
      16 * (q / f) * (x / q) by nlinarith [hcoreCancel])
  rw [le_div_iff₀ hL]
  by_cases hry : q / f ≤ y
  · have hrR : (0 : ℝ) < ((q / f : ℕ) : ℝ) := by exact_mod_cast hrPos
    have hryR : ((q / f : ℕ) : ℝ) ≤ (y : ℝ) := by exact_mod_cast hry
    have hratio := active_div_le_div_rpow_one_eighth hrR hryR
    have hyPow : 0 < (y : ℝ) ^ (1 / 8 : ℝ) := by positivity
    calc
      (((8 * (y / f) : ℕ) : ℝ) / ((x / q : ℕ) : ℝ)) *
          Erdos896.logDenom896 y ≤
          (16 * ((q / f : ℕ) : ℝ) / (y : ℝ)) *
            Erdos896.logDenom896 y :=
        mul_le_mul_of_nonneg_right hbaseRatio hL.le
      _ ≤ (16 * ((q / f : ℕ) : ℝ) / (y : ℝ)) *
          (G * (y : ℝ) ^ (1 / 8 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hgrowth (by positivity)
      _ ≤ 16 * G * ((q / f : ℕ) : ℝ) ^ (1 / 8 : ℝ) := by
        calc
          (16 * ((q / f : ℕ) : ℝ) / (y : ℝ)) *
              (G * (y : ℝ) ^ (1 / 8 : ℝ)) =
              (16 * G) * (((q / f : ℕ) : ℝ) / (y : ℝ)) *
                (y : ℝ) ^ (1 / 8 : ℝ) := by ring
          _ ≤ (16 * G) *
              (((q / f : ℕ) : ℝ) ^ (1 / 8 : ℝ) /
                (y : ℝ) ^ (1 / 8 : ℝ)) *
                (y : ℝ) ^ (1 / 8 : ℝ) := by gcongr
          _ = 16 * G * ((q / f : ℕ) : ℝ) ^ (1 / 8 : ℝ) := by
            field_simp [hyPow.ne']
      _ ≤ (16 * G) *
          (max (f : ℝ) ((q / f : ℕ) : ℝ)) ^ (1 / 8 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hrPowM (by positivity)
  · have hyr : y < q / f := by omega
    have hyPowR : (y : ℝ) ^ (1 / 8 : ℝ) ≤
        ((q / f : ℕ) : ℝ) ^ (1 / 8 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hyr.le) (by norm_num)
    calc
      (((8 * (y / f) : ℕ) : ℝ) / ((x / q : ℕ) : ℝ)) *
          Erdos896.logDenom896 y ≤ Erdos896.logDenom896 y := by
        simpa using mul_le_mul_of_nonneg_right hbaseOne hL.le
      _ ≤ G * (y : ℝ) ^ (1 / 8 : ℝ) := hgrowth
      _ ≤ G * ((q / f : ℕ) : ℝ) ^ (1 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_left hyPowR hG
      _ ≤ (16 * G) *
          (max (f : ℝ) ((q / f : ℕ) : ℝ)) ^ (1 / 8 : ℝ) := by
        have hMPow : 0 ≤
            (max (f : ℝ) ((q / f : ℕ) : ℝ)) ^ (1 / 8 : ℝ) := by positivity
        nlinarith

private lemma active_shell_ratio_bound
    {x y q f k : ℕ}
    (hxy : y ^ 2 ≤ x)
    (hq : q ∈ squarefullSet x) (hfmem : f ∈ q.divisors)
    (hY : 3 ≤ y / f)
    (hk : 8 * (y / f) ≤ (x / q) / 2 ^ k) :
    max 1 ((y : ℝ) /
        ((((x / q) / 2 ^ k) / (y / f) : ℕ) : ℝ)) ≤
      8 * ((q / f : ℕ) : ℝ) * (2 : ℝ) ^ k := by
  have hqData := mem_squarefullSet.mp hq
  have hqPos : 0 < q := by omega
  have hfDvd : f ∣ q := Nat.dvd_of_mem_divisors hfmem
  have hfPos : 0 < f := Nat.pos_of_dvd_of_pos hfDvd hqPos
  have hrPos : 0 < q / f :=
    Nat.div_pos (Nat.le_of_dvd hqPos hfDvd) hfPos
  have hfactor : f * (q / f) = q := by
    simpa [mul_comm] using Nat.div_mul_cancel hfDvd
  let X := x / q
  let Y := y / f
  let Xk := X / 2 ^ k
  let T := Xk / Y
  have hYPos : 0 < Y := by dsimp [Y]; omega
  have hXk8 : 8 * Y ≤ Xk := by simpa [Xk, X, Y] using hk
  have hXkPos : 0 < Xk := by omega
  have hXPos : 0 < X := by
    dsimp [Xk] at hXkPos
    exact Nat.pos_of_div_pos hXkPos
  have hT8 : 8 ≤ T := by
    apply (Nat.le_div_iff_mul_le hYPos).mpr
    exact hXk8
  have hTPos : 0 < T := by omega
  have hpowPos : 0 < 2 ^ k := pow_pos (by omega) k
  have hxlt : x < q * (X + 1) := by
    dsimp [X]
    exact Nat.lt_mul_div_succ x hqPos
  have hXsucc : X + 1 ≤ 2 * X := by omega
  have hXlt : X < 2 ^ k * (Xk + 1) := by
    dsimp [Xk]
    exact Nat.lt_mul_div_succ X hpowPos
  have hXksucc : Xk + 1 ≤ 2 * Xk := by omega
  have hTklt : Xk < Y * (T + 1) := by
    dsimp [T]
    exact Nat.lt_mul_div_succ Xk hYPos
  have hTsucc : T + 1 ≤ 2 * T := by omega
  have hfY : f * Y ≤ y := by
    dsimp [Y]
    simpa [mul_comm] using Nat.div_mul_le_self y f
  have hyPos : 0 < y :=
    lt_of_lt_of_le (mul_pos hfPos hYPos) hfY
  have hbig : x < 8 * (q / f) * (2 ^ k) * y * T := by
    calc
      x < q * (X + 1) := hxlt
      _ ≤ q * (2 * X) := Nat.mul_le_mul_left q hXsucc
      _ < q * (2 * (2 ^ k * (Xk + 1))) := by
        exact Nat.mul_lt_mul_of_pos_left
          (Nat.mul_lt_mul_of_pos_left hXlt (by omega)) hqPos
      _ ≤ q * (2 * (2 ^ k * (2 * Xk))) := by gcongr
      _ < q * (2 * (2 ^ k * (2 * (Y * (T + 1))))) := by gcongr
      _ ≤ q * (2 * (2 ^ k * (2 * (Y * (2 * T))))) := by gcongr
      _ = 8 * q * (2 ^ k) * Y * T := by ring
      _ = 8 * (f * (q / f)) * (2 ^ k) * Y * T := by
        exact congrArg (fun z : ℕ ↦ 8 * z * (2 ^ k) * Y * T) hfactor.symm
      _ = 8 * (q / f) * (2 ^ k) * (f * Y) * T := by ring
      _ ≤ 8 * (q / f) * (2 ^ k) * y * T := by gcongr
  have hsquare : y * y ≤ x := by simpa [pow_two] using hxy
  have hyBound : y ≤ 8 * (q / f) * (2 ^ k) * T := by
    apply Nat.le_of_mul_le_mul_left _ hyPos
    calc
      y * y ≤ x := hsquare
      _ ≤ 8 * (q / f) * (2 ^ k) * y * T := hbig.le
      _ = y * (8 * (q / f) * (2 ^ k) * T) := by ring
  have hTR : (0 : ℝ) < T := by exact_mod_cast hTPos
  have hyDiv : (y : ℝ) / (T : ℝ) ≤
      8 * ((q / f : ℕ) : ℝ) * (2 : ℝ) ^ k := by
    rw [div_le_iff₀ hTR]
    exact_mod_cast hyBound
  have hone : (1 : ℝ) ≤
      8 * ((q / f : ℕ) : ℝ) * (2 : ℝ) ^ k := by
    have : (1 : ℕ) ≤ 8 * (q / f) * 2 ^ k :=
      (mul_pos (mul_pos (by omega) hrPos) hpowPos)
    exact_mod_cast this
  dsimp [T, Xk, X, Y] at hyDiv
  exact max_le hone hyDiv

private lemma active_first_ratio_bound
    {y f : ℕ} (hf : 0 < f) (hY : 3 ≤ y / f) :
    max 1 ((y : ℝ) / ((2 * (y / f) : ℕ) : ℝ)) ≤ (f : ℝ) := by
  have hYpos : 0 < y / f := by omega
  have hflt : y < f * (y / f + 1) := Nat.lt_mul_div_succ y hf
  have hylt : y < f * (2 * (y / f)) := by
    calc
      y < f * (y / f + 1) := hflt
      _ ≤ f * (2 * (y / f)) := by gcongr; omega
  have hden : (0 : ℝ) < ((2 * (y / f) : ℕ) : ℝ) := by positivity
  apply max_le
  · exact_mod_cast hf
  · rw [div_le_iff₀ hden]
    exact_mod_cast hylt.le

private lemma active_rpow_product (a : ℝ) (k : ℕ)
    (ha : 0 ≤ a) :
    (8 * a * (2 : ℝ) ^ k) ^ (1 / 8 : ℝ) =
      8 ^ (1 / 8 : ℝ) * a ^ (1 / 8 : ℝ) *
        (((2 ^ k : ℕ) : ℝ) ^ (1 / 8 : ℝ)) := by
  rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 8 * a)
      (by positivity : 0 ≤ (2 : ℝ) ^ k),
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) ha]
  norm_num

/-- Active branch of the local `HStar` denominator collapse. -/
theorem active_fordHStarDenominatorWeight_le
    {Y₀ x y q f : ℕ} {B G : ℝ}
    (hy₀ : Y₀ ≤ y) (hy : 3 ≤ y) (hxy : y ^ 2 ≤ x)
    (hq : q ∈ squarefullSet x) (hfmem : f ∈ q.divisors)
    (hB : 0 ≤ B) (hG : 0 ≤ G)
    (henvelope : ∀ {y T : ℕ}, Y₀ ≤ y → 2 ≤ T →
      fordDenominatorSum T ≤
        B * (max 1 ((y : ℝ) / (T : ℝ))) ^ (1 / 8 : ℝ) /
          Erdos896.logDenom896 y)
    (hgrowth : Erdos896.logDenom896 y ≤
      G * (y : ℝ) ^ (1 / 8 : ℝ))
    (hactive : 3 ≤ y / f ∧ 8 * (y / f) ≤ x / q) :
    fordHStarDenominatorWeight (x / q) (y / f) ≤
      (16 * G + 2 * B +
          2 * B * 8 ^ (1 / 8 : ℝ) *
            (1 - fordDyadicEighthRatio)⁻¹) *
        (max (f : ℝ) ((q / f : ℕ) : ℝ)) ^ (1 / 8 : ℝ) /
          Erdos896.logDenom896 y := by
  classical
  have hqPos : 0 < q := (mem_squarefullSet.mp hq).1
  have hfDvd : f ∣ q := Nat.dvd_of_mem_divisors hfmem
  have hfPos : 0 < f := Nat.pos_of_dvd_of_pos hfDvd hqPos
  have hrPos : 0 < q / f :=
    Nat.div_pos (Nat.le_of_dvd hqPos hfDvd) hfPos
  let X := x / q
  let Y := y / f
  let M : ℝ := max (f : ℝ) ((q / f : ℕ) : ℝ)
  let L : ℝ := Erdos896.logDenom896 y
  let S : Finset ℕ :=
    (Finset.range (X + 1)).filter (fun k ↦ 8 * Y ≤ X / 2 ^ k)
  have hL : 0 < L := by
    dsimp [L]
    exact Erdos896.logDenom896_pos hy
  have hXPos : 0 < X := by dsimp [X]; omega
  have hMnonneg : 0 ≤ M := by dsimp [M]; positivity
  have hfM : (f : ℝ) ≤ M := by dsimp [M]; exact le_max_left _ _
  have hrM : ((q / f : ℕ) : ℝ) ≤ M := by
    dsimp [M]; exact le_max_right _ _
  have hfPowM : (f : ℝ) ^ (1 / 8 : ℝ) ≤ M ^ (1 / 8 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hfM (by norm_num)
  have hrPowM : ((q / f : ℕ) : ℝ) ^ (1 / 8 : ℝ) ≤ M ^ (1 / 8 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hrM (by norm_num)
  have hDfirst : fordDenominatorSum (2 * Y) ≤ B * M ^ (1 / 8 : ℝ) / L := by
    have hratio := active_first_ratio_bound hfPos hactive.1
    have hpow := Real.rpow_le_rpow (by positivity) hratio
      (by norm_num : (0 : ℝ) ≤ 1 / 8)
    calc
      fordDenominatorSum (2 * Y) ≤
          B * (max 1 ((y : ℝ) / ((2 * Y : ℕ) : ℝ))) ^
              (1 / 8 : ℝ) / L := by
        apply henvelope hy₀
        dsimp [Y]
        omega
      _ ≤ B * (f : ℝ) ^ (1 / 8 : ℝ) / L := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow hB) hL.le
      _ ≤ B * M ^ (1 / 8 : ℝ) / L := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfPowM hB) hL.le
  have hDshell (k : ℕ) (hk : k ∈ S) :
      fordDenominatorSum ((X / 2 ^ k) / Y) ≤
        B * (8 ^ (1 / 8 : ℝ) *
          ((q / f : ℕ) : ℝ) ^ (1 / 8 : ℝ) *
          (((2 ^ k : ℕ) : ℝ) ^ (1 / 8 : ℝ))) / L := by
    have hk' : 8 * Y ≤ X / 2 ^ k := (Finset.mem_filter.mp hk).2
    have hT : 2 ≤ (X / 2 ^ k) / Y := by
      have hYpos : 0 < Y := by dsimp [Y]; omega
      apply (Nat.le_div_iff_mul_le hYpos).mpr
      omega
    have hratio := active_shell_ratio_bound hxy hq hfmem hactive.1 (by
      simpa [X, Y] using hk')
    have hpow := Real.rpow_le_rpow (by positivity) hratio
      (by norm_num : (0 : ℝ) ≤ 1 / 8)
    have hsplit := active_rpow_product ((q / f : ℕ) : ℝ) k
      (by positivity)
    calc
      fordDenominatorSum ((X / 2 ^ k) / Y) ≤
          B * (max 1 ((y : ℝ) / (((X / 2 ^ k) / Y : ℕ) : ℝ))) ^
            (1 / 8 : ℝ) / L := henvelope hy₀ hT
      _ ≤ B * (8 * ((q / f : ℕ) : ℝ) * (2 : ℝ) ^ k) ^
            (1 / 8 : ℝ) / L := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow hB) hL.le
      _ = B * (8 ^ (1 / 8 : ℝ) *
          ((q / f : ℕ) : ℝ) ^ (1 / 8 : ℝ) *
          (((2 ^ k : ℕ) : ℝ) ^ (1 / 8 : ℝ))) / L := by
        rw [hsplit]
  have hcoeff (k : ℕ) :
      (((X / 2 ^ k : ℕ) : ℝ) / (X : ℝ)) ≤
        (((2 ^ k : ℕ) : ℝ))⁻¹ :=
    cast_div_ratio_le_inv_pow_two X k hXPos
  have hsumCoeff :
      ∑ k ∈ S, (((X / 2 ^ k : ℕ) : ℝ) / (X : ℝ)) ≤ 2 := by
    calc
      ∑ k ∈ S, (((X / 2 ^ k : ℕ) : ℝ) / (X : ℝ)) ≤
          ∑ k ∈ S, (((2 ^ k : ℕ) : ℝ))⁻¹ := by
        exact Finset.sum_le_sum fun k _ ↦ hcoeff k
      _ ≤ 2 := sum_inv_two_pow_le_two S
  have hsumWeighted :
      ∑ k ∈ S, (((X / 2 ^ k : ℕ) : ℝ) / (X : ℝ)) *
          (((2 ^ k : ℕ) : ℝ) ^ (1 / 8 : ℝ)) ≤
        (1 - fordDyadicEighthRatio)⁻¹ := by
    calc
      ∑ k ∈ S, (((X / 2 ^ k : ℕ) : ℝ) / (X : ℝ)) *
          (((2 ^ k : ℕ) : ℝ) ^ (1 / 8 : ℝ)) ≤
        ∑ k ∈ S, (((2 ^ k : ℕ) : ℝ))⁻¹ *
          (((2 ^ k : ℕ) : ℝ) ^ (1 / 8 : ℝ)) := by
          apply Finset.sum_le_sum
          intro k hk
          exact mul_le_mul_of_nonneg_right (hcoeff k) (by positivity)
      _ ≤ (1 - fordDyadicEighthRatio)⁻¹ := sum_weighted_eighth_le S
  have hbase : (((8 * Y : ℕ) : ℝ) / (X : ℝ)) ≤
      (16 * G) * M ^ (1 / 8 : ℝ) / L := by
    simpa [X, Y, M, L] using
      active_base_bound hy hxy hq hfmem hG hgrowth hactive
  rw [fordHStarDenominatorWeight, if_pos hactive]
  change (((8 * Y : ℕ) : ℝ) / (X : ℝ)) +
      ∑ k ∈ S, (((X / 2 ^ k : ℕ) : ℝ) / (X : ℝ)) *
        fordDyadicDenominatorWeight (X / 2 ^ k) Y ≤ _
  have hsum :
      ∑ k ∈ S, (((X / 2 ^ k : ℕ) : ℝ) / (X : ℝ)) *
        fordDyadicDenominatorWeight (X / 2 ^ k) Y ≤
      (2 * B + 2 * B * 8 ^ (1 / 8 : ℝ) *
          (1 - fordDyadicEighthRatio)⁻¹) * M ^ (1 / 8 : ℝ) / L := by
    simp_rw [fordDyadicDenominatorWeight]
    calc
      ∑ k ∈ S, (((X / 2 ^ k : ℕ) : ℝ) / (X : ℝ)) *
          (fordDenominatorSum (2 * Y) +
            2 * fordDenominatorSum ((X / 2 ^ k) / Y)) ≤
        ∑ k ∈ S, (((X / 2 ^ k : ℕ) : ℝ) / (X : ℝ)) *
          ((B * M ^ (1 / 8 : ℝ) / L) +
            2 * (B * (8 ^ (1 / 8 : ℝ) *
              ((q / f : ℕ) : ℝ) ^ (1 / 8 : ℝ) *
              (((2 ^ k : ℕ) : ℝ) ^ (1 / 8 : ℝ))) / L)) := by
          apply Finset.sum_le_sum
          intro k hk
          have hc : 0 ≤ (((X / 2 ^ k : ℕ) : ℝ) / (X : ℝ)) := by positivity
          exact mul_le_mul_of_nonneg_left
            (add_le_add hDfirst (mul_le_mul_of_nonneg_left (hDshell k hk)
              (by norm_num))) hc
      _ = (B * M ^ (1 / 8 : ℝ) / L) *
            (∑ k ∈ S, (((X / 2 ^ k : ℕ) : ℝ) / (X : ℝ))) +
          (2 * B * 8 ^ (1 / 8 : ℝ) *
              ((q / f : ℕ) : ℝ) ^ (1 / 8 : ℝ) / L) *
            (∑ k ∈ S, (((X / 2 ^ k : ℕ) : ℝ) / (X : ℝ)) *
              (((2 ^ k : ℕ) : ℝ) ^ (1 / 8 : ℝ))) := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib]
          congr 1
          · rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k hk
            ring
          · rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k hk
            ring
      _ ≤ (B * M ^ (1 / 8 : ℝ) / L) * 2 +
          (2 * B * 8 ^ (1 / 8 : ℝ) *
              ((q / f : ℕ) : ℝ) ^ (1 / 8 : ℝ) / L) *
            (1 - fordDyadicEighthRatio)⁻¹ := by
          gcongr
      _ ≤ (2 * B + 2 * B * 8 ^ (1 / 8 : ℝ) *
          (1 - fordDyadicEighthRatio)⁻¹) * M ^ (1 / 8 : ℝ) / L := by
        have hC : 0 ≤ (1 - fordDyadicEighthRatio)⁻¹ :=
          fordDyadicEighthConstant_pos.le
        have hcoef : 0 ≤ 2 * B * 8 ^ (1 / 8 : ℝ) := by positivity
        have hsecond :
            (2 * B * 8 ^ (1 / 8 : ℝ) *
                ((q / f : ℕ) : ℝ) ^ (1 / 8 : ℝ) / L) *
              (1 - fordDyadicEighthRatio)⁻¹ ≤
            (2 * B * 8 ^ (1 / 8 : ℝ) * M ^ (1 / 8 : ℝ) / L) *
              (1 - fordDyadicEighthRatio)⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ hC
          apply div_le_div_of_nonneg_right _ hL.le
          exact mul_le_mul_of_nonneg_left hrPowM hcoef
        calc
          (B * M ^ (1 / 8 : ℝ) / L) * 2 +
              (2 * B * 8 ^ (1 / 8 : ℝ) *
                ((q / f : ℕ) : ℝ) ^ (1 / 8 : ℝ) / L) *
                (1 - fordDyadicEighthRatio)⁻¹ ≤
            (B * M ^ (1 / 8 : ℝ) / L) * 2 +
              (2 * B * 8 ^ (1 / 8 : ℝ) * M ^ (1 / 8 : ℝ) / L) *
                (1 - fordDyadicEighthRatio)⁻¹ := add_le_add le_rfl hsecond
          _ = (2 * B + 2 * B * 8 ^ (1 / 8 : ℝ) *
              (1 - fordDyadicEighthRatio)⁻¹) * M ^ (1 / 8 : ℝ) / L := by
            ring
  calc
    (((8 * Y : ℕ) : ℝ) / (X : ℝ)) +
        ∑ k ∈ S, (((X / 2 ^ k : ℕ) : ℝ) / (X : ℝ)) *
          fordDyadicDenominatorWeight (X / 2 ^ k) Y ≤
      (16 * G) * M ^ (1 / 8 : ℝ) / L +
        (2 * B + 2 * B * 8 ^ (1 / 8 : ℝ) *
          (1 - fordDyadicEighthRatio)⁻¹) * M ^ (1 / 8 : ℝ) / L :=
      add_le_add hbase hsum
    _ = (16 * G + 2 * B + 2 * B * 8 ^ (1 / 8 : ℝ) *
          (1 - fordDyadicEighthRatio)⁻¹) * M ^ (1 / 8 : ℝ) / L := by ring

private lemma endpoint_denominatorWeight_le
    {y q f : ℕ} {G : ℝ}
    (hy : 3 ≤ y) (hf : 0 < f) (hG : 0 ≤ G)
    (hgrowth : Erdos896.logDenom896 y ≤
      G * (y : ℝ) ^ (1 / 8 : ℝ)) :
    (((2 * (y / f) + 1 : ℕ) : ℝ))⁻¹ ≤
      (2 * G) *
        (max (f : ℝ) ((q / f : ℕ) : ℝ)) ^ (1 / 8 : ℝ) /
          Erdos896.logDenom896 y := by
  have hL : 0 < Erdos896.logDenom896 y := Erdos896.logDenom896_pos hy
  have hyR : (0 : ℝ) < y := by positivity
  have hfR : (0 : ℝ) < f := by exact_mod_cast hf
  have hfM : (f : ℝ) ≤ max (f : ℝ) ((q / f : ℕ) : ℝ) := le_max_left _ _
  have hfPowM : (f : ℝ) ^ (1 / 8 : ℝ) ≤
      (max (f : ℝ) ((q / f : ℕ) : ℝ)) ^ (1 / 8 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hfM (by norm_num)
  rw [le_div_iff₀ hL]
  by_cases hfy : f ≤ y
  · have hYpos : 0 < y / f := Nat.div_pos hfy hf
    have hylt : y < f * (y / f + 1) := Nat.lt_mul_div_succ y hf
    have hylt2 : y < 2 * f * (y / f) := by
      have : y / f + 1 ≤ 2 * (y / f) := by omega
      nlinarith
    have hendpoint : (((2 * (y / f) + 1 : ℕ) : ℝ))⁻¹ ≤
        2 * (f : ℝ) / (y : ℝ) := by
      have hden : (0 : ℝ) < (2 * (y / f) + 1 : ℕ) := by positivity
      rw [inv_le_iff_one_le_mul₀' hden]
      have hylt2R : (y : ℝ) < 2 * (f : ℝ) * (y / f : ℕ) := by
        exact_mod_cast hylt2
      have hYcast : ((y / f : ℕ) : ℝ) <
          ((2 * (y / f) + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
      field_simp [hyR.ne']
      nlinarith
    have hratio : (f : ℝ) / (y : ℝ) ≤
        (f : ℝ) ^ (1 / 8 : ℝ) / (y : ℝ) ^ (1 / 8 : ℝ) :=
      active_div_le_div_rpow_one_eighth hfR (by exact_mod_cast hfy)
    have hyPow : 0 < (y : ℝ) ^ (1 / 8 : ℝ) := by positivity
    calc
      (((2 * (y / f) + 1 : ℕ) : ℝ))⁻¹ * Erdos896.logDenom896 y ≤
          (2 * (f : ℝ) / (y : ℝ)) * Erdos896.logDenom896 y :=
        mul_le_mul_of_nonneg_right hendpoint hL.le
      _ ≤ (2 * (f : ℝ) / (y : ℝ)) *
          (G * (y : ℝ) ^ (1 / 8 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hgrowth (by positivity)
      _ ≤ 2 * G * (f : ℝ) ^ (1 / 8 : ℝ) := by
        calc
          (2 * (f : ℝ) / (y : ℝ)) *
              (G * (y : ℝ) ^ (1 / 8 : ℝ)) =
              (2 * G) * ((f : ℝ) / (y : ℝ)) *
                (y : ℝ) ^ (1 / 8 : ℝ) := by ring
          _ ≤ (2 * G) *
              ((f : ℝ) ^ (1 / 8 : ℝ) /
                (y : ℝ) ^ (1 / 8 : ℝ)) *
                (y : ℝ) ^ (1 / 8 : ℝ) := by gcongr
          _ = 2 * G * (f : ℝ) ^ (1 / 8 : ℝ) := by
            field_simp [hyPow.ne']
      _ ≤ (2 * G) *
          (max (f : ℝ) ((q / f : ℕ) : ℝ)) ^ (1 / 8 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hfPowM (by positivity)
  · have hyf : y < f := by omega
    have hyPowLe : (y : ℝ) ^ (1 / 8 : ℝ) ≤
        (f : ℝ) ^ (1 / 8 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hyf.le) (by norm_num)
    have hendOne : (((2 * (y / f) + 1 : ℕ) : ℝ))⁻¹ ≤ 1 := by
      have hden : (0 : ℝ) < ((2 * (y / f) + 1 : ℕ) : ℝ) := by positivity
      have hone : (1 : ℝ) ≤ ((2 * (y / f) + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show 1 ≤ 2 * (y / f) + 1 by omega)
      exact (inv_le_one₀ hden).2 hone
    calc
      (((2 * (y / f) + 1 : ℕ) : ℝ))⁻¹ * Erdos896.logDenom896 y ≤
          Erdos896.logDenom896 y := by
        simpa using mul_le_mul_of_nonneg_right hendOne hL.le
      _ ≤ G * (y : ℝ) ^ (1 / 8 : ℝ) := hgrowth
      _ ≤ G * (f : ℝ) ^ (1 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_left hyPowLe hG
      _ ≤ (2 * G) *
          (max (f : ℝ) ((q / f : ℕ) : ℝ)) ^ (1 / 8 : ℝ) := by
        have hpM : 0 ≤ (max (f : ℝ) ((q / f : ℕ) : ℝ)) ^
            (1 / 8 : ℝ) := by positivity
        nlinarith

private lemma inactive_unit_le
    {x y q f : ℕ} {G : ℝ}
    (hy : 3 ≤ y) (hxy : y ^ 2 ≤ x)
    (hq : q ∈ squarefullSet x) (hfmem : f ∈ q.divisors)
    (hG : 0 ≤ G)
    (hgrowth : Erdos896.logDenom896 y ≤
      G * (y : ℝ) ^ (1 / 8 : ℝ))
    (hinactive : ¬ (3 ≤ y / f ∧ 8 * (y / f) ≤ x / q)) :
    1 ≤
      (8 ^ (1 / 8 : ℝ) * G) *
        (max (f : ℝ) ((q / f : ℕ) : ℝ)) ^ (1 / 8 : ℝ) /
          Erdos896.logDenom896 y := by
  have hqData := mem_squarefullSet.mp hq
  have hqPos : 0 < q := by omega
  have hfDvd : f ∣ q := Nat.dvd_of_mem_divisors hfmem
  have hfPos : 0 < f := Nat.pos_of_dvd_of_pos hfDvd hqPos
  have hrPos : 0 < q / f := Nat.div_pos (Nat.le_of_dvd hqPos hfDvd) hfPos
  have hfactor : f * (q / f) = q := by
    simpa [mul_comm] using Nat.div_mul_cancel hfDvd
  have hMpos : (0 : ℝ) < max (f : ℝ) ((q / f : ℕ) : ℝ) :=
    lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hL : 0 < Erdos896.logDenom896 y := Erdos896.logDenom896_pos hy
  have hyM : (y : ℝ) ≤
      8 * max (f : ℝ) ((q / f : ℕ) : ℝ) := by
    by_cases hY : 3 ≤ y / f
    · have hXlt : x / q < 8 * (y / f) := by omega
      have hxlt : x < q * (x / q + 1) := Nat.lt_mul_div_succ x hqPos
      have hsucc : x / q + 1 ≤ 8 * (y / f) := by omega
      have hfY : f * (y / f) ≤ y := by
        simpa [mul_comm] using Nat.div_mul_le_self y f
      have hxlt' : x < 8 * (q / f) * y := by
        calc
          x < q * (x / q + 1) := hxlt
          _ ≤ q * (8 * (y / f)) := Nat.mul_le_mul_left q hsucc
          _ = 8 * q * (y / f) := by ring
          _ = 8 * (f * (q / f)) * (y / f) := by rw [hfactor]
          _ = 8 * (q / f) * (f * (y / f)) := by ring
          _ ≤ 8 * (q / f) * y := Nat.mul_le_mul_left _ hfY
      have hylt : y < 8 * (q / f) := by nlinarith
      exact (by
        exact_mod_cast (hylt.le.trans (Nat.mul_le_mul_left 8
          (show q / f ≤ max f (q / f) by exact le_max_right _ _))))
    · have hYlt : y / f < 3 := by omega
      have hylt : y < f * (y / f + 1) := Nat.lt_mul_div_succ y hfPos
      have hylt' : y < 8 * f := by
        have : y / f + 1 ≤ 3 := by omega
        calc
          y < f * (y / f + 1) := hylt
          _ ≤ f * 3 := Nat.mul_le_mul_left f this
          _ ≤ 8 * f := by omega
      exact (by
        exact_mod_cast (hylt'.le.trans (Nat.mul_le_mul_left 8
          (show f ≤ max f (q / f) by exact le_max_left _ _))))
  have hyPowM : (y : ℝ) ^ (1 / 8 : ℝ) ≤
      (8 * max (f : ℝ) ((q / f : ℕ) : ℝ)) ^ (1 / 8 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hyM (by norm_num)
  have hsplit :
      (8 * max (f : ℝ) ((q / f : ℕ) : ℝ)) ^ (1 / 8 : ℝ) =
        8 ^ (1 / 8 : ℝ) *
          (max (f : ℝ) ((q / f : ℕ) : ℝ)) ^ (1 / 8 : ℝ) := by
    exact Real.mul_rpow (by norm_num) hMpos.le
  rw [le_div_iff₀ hL]
  calc
    1 * Erdos896.logDenom896 y = Erdos896.logDenom896 y := one_mul _
    _ ≤ G * (y : ℝ) ^ (1 / 8 : ℝ) := hgrowth
    _ ≤ G * (8 * max (f : ℝ) ((q / f : ℕ) : ℝ)) ^ (1 / 8 : ℝ) :=
      mul_le_mul_of_nonneg_left hyPowM hG
    _ = (8 ^ (1 / 8 : ℝ) * G) *
        (max (f : ℝ) ((q / f : ℕ) : ℝ)) ^ (1 / 8 : ℝ) := by
      rw [hsplit]
      ring

/-- The active dyadic estimate, endpoint term, and inactive fallback combine
into the local estimate consumed by the squarefull-divisor moment. -/
theorem exists_fordHStarDenominatorWeight_add_endpoint_le
    {Y₀ : ℕ} {B G : ℝ}
    (hY₀ : 3 ≤ Y₀) (hB : 0 ≤ B) (hG : 0 ≤ G)
    (henvelope : ∀ {y T : ℕ}, Y₀ ≤ y → 2 ≤ T →
      fordDenominatorSum T ≤
        B * (max 1 ((y : ℝ) / (T : ℝ))) ^ (1 / 8 : ℝ) /
          Erdos896.logDenom896 y)
    (hgrowth : ∀ {y : ℕ}, Y₀ ≤ y →
      Erdos896.logDenom896 y ≤ G * (y : ℝ) ^ (1 / 8 : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y q f : ℕ, Y₀ ≤ y → y ^ 2 ≤ x →
      q ∈ squarefullSet x → f ∈ q.divisors →
      fordHStarDenominatorWeight (x / q) (y / f) +
          ((2 * (y / f) + 1 : ℕ) : ℝ)⁻¹ ≤
        C * (((max f (q / f) : ℕ) : ℝ) ^ (1 / 8 : ℝ)) /
          Erdos896.logDenom896 y := by
  let Ka : ℝ := 16 * G + 2 * B +
    2 * B * 8 ^ (1 / 8 : ℝ) * (1 - fordDyadicEighthRatio)⁻¹
  let Ki : ℝ := 8 ^ (1 / 8 : ℝ) * G
  let C : ℝ := 1 + Ka + 2 * G + Ki
  have hKa0 : 0 ≤ Ka := by
    dsimp [Ka]
    have := fordDyadicEighthConstant_pos.le
    positivity
  have hKi0 : 0 ≤ Ki := by dsimp [Ki]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro x y q f hy₀ hxy hq hfmem
  have hy : 3 ≤ y := hY₀.trans hy₀
  have hqPos : 0 < q := (mem_squarefullSet.mp hq).1
  have hfDvd : f ∣ q := Nat.dvd_of_mem_divisors hfmem
  have hfPos : 0 < f := Nat.pos_of_dvd_of_pos hfDvd hqPos
  have hL : 0 < Erdos896.logDenom896 y := Erdos896.logDenom896_pos hy
  have hMcast : (((max f (q / f) : ℕ) : ℝ)) =
      max (f : ℝ) ((q / f : ℕ) : ℝ) := by simp
  rw [hMcast]
  let M : ℝ := max (f : ℝ) ((q / f : ℕ) : ℝ)
  have hscale0 : 0 ≤ M ^ (1 / 8 : ℝ) /
      Erdos896.logDenom896 y := div_nonneg (by positivity) hL.le
  have hend := endpoint_denominatorWeight_le (q := q) hy hfPos hG (hgrowth hy₀)
  change fordHStarDenominatorWeight (x / q) (y / f) +
      ((2 * (y / f) + 1 : ℕ) : ℝ)⁻¹ ≤
        C * M ^ (1 / 8 : ℝ) / Erdos896.logDenom896 y
  by_cases hactive : 3 ≤ y / f ∧ 8 * (y / f) ≤ x / q
  · have hstar := active_fordHStarDenominatorWeight_le hy₀ hy hxy hq hfmem
      hB hG henvelope (hgrowth hy₀) hactive
    have hsum : fordHStarDenominatorWeight (x / q) (y / f) +
        ((2 * (y / f) + 1 : ℕ) : ℝ)⁻¹ ≤
          (Ka + 2 * G) * M ^ (1 / 8 : ℝ) /
            Erdos896.logDenom896 y := by
      calc
        fordHStarDenominatorWeight (x / q) (y / f) +
            ((2 * (y / f) + 1 : ℕ) : ℝ)⁻¹ ≤
          Ka * M ^ (1 / 8 : ℝ) / Erdos896.logDenom896 y +
            (2 * G) * M ^ (1 / 8 : ℝ) /
              Erdos896.logDenom896 y := by
            exact add_le_add (by simpa [Ka, M] using hstar)
              (by simpa [M] using hend)
        _ = (Ka + 2 * G) * M ^ (1 / 8 : ℝ) /
              Erdos896.logDenom896 y := by ring
    calc
      fordHStarDenominatorWeight (x / q) (y / f) +
          ((2 * (y / f) + 1 : ℕ) : ℝ)⁻¹ ≤
        (Ka + 2 * G) * M ^ (1 / 8 : ℝ) /
          Erdos896.logDenom896 y := hsum
      _ ≤ C * M ^ (1 / 8 : ℝ) / Erdos896.logDenom896 y := by
        have hKC : Ka + 2 * G ≤ C := by dsimp [C]; linarith
        calc
          (Ka + 2 * G) * M ^ (1 / 8 : ℝ) /
              Erdos896.logDenom896 y =
            (Ka + 2 * G) *
              (M ^ (1 / 8 : ℝ) / Erdos896.logDenom896 y) := by ring
          _ ≤ C * (M ^ (1 / 8 : ℝ) / Erdos896.logDenom896 y) :=
            mul_le_mul_of_nonneg_right hKC hscale0
          _ = C * M ^ (1 / 8 : ℝ) / Erdos896.logDenom896 y := by ring
  · have hone := inactive_unit_le hy hxy hq hfmem hG (hgrowth hy₀) hactive
    have hstarEq : fordHStarDenominatorWeight (x / q) (y / f) = 1 := by
      rw [fordHStarDenominatorWeight, if_neg hactive]
    have hsum : fordHStarDenominatorWeight (x / q) (y / f) +
        ((2 * (y / f) + 1 : ℕ) : ℝ)⁻¹ ≤
          (Ki + 2 * G) * M ^ (1 / 8 : ℝ) /
            Erdos896.logDenom896 y := by
      rw [hstarEq]
      calc
        1 + ((2 * (y / f) + 1 : ℕ) : ℝ)⁻¹ ≤
          Ki * M ^ (1 / 8 : ℝ) / Erdos896.logDenom896 y +
            (2 * G) * M ^ (1 / 8 : ℝ) /
              Erdos896.logDenom896 y := by
            exact add_le_add (by simpa [Ki, M] using hone)
              (by simpa [M] using hend)
        _ = (Ki + 2 * G) * M ^ (1 / 8 : ℝ) /
              Erdos896.logDenom896 y := by ring
    calc
      fordHStarDenominatorWeight (x / q) (y / f) +
          ((2 * (y / f) + 1 : ℕ) : ℝ)⁻¹ ≤
        (Ki + 2 * G) * M ^ (1 / 8 : ℝ) /
          Erdos896.logDenom896 y := hsum
      _ ≤ C * M ^ (1 / 8 : ℝ) / Erdos896.logDenom896 y := by
        have hKC : Ki + 2 * G ≤ C := by dsimp [C]; linarith
        calc
          (Ki + 2 * G) * M ^ (1 / 8 : ℝ) /
              Erdos896.logDenom896 y =
            (Ki + 2 * G) *
              (M ^ (1 / 8 : ℝ) / Erdos896.logDenom896 y) := by ring
          _ ≤ C * (M ^ (1 / 8 : ℝ) / Erdos896.logDenom896 y) :=
            mul_le_mul_of_nonneg_right hKC hscale0
          _ = C * M ^ (1 / 8 : ℝ) / Erdos896.logDenom896 y := by ring

/-- Ford's sharp weighted-sum estimate supplies all hypotheses of the local
dyadic collapse after enlarging the common threshold. -/
theorem exists_fordHStarDenominatorWeight_add_endpoint_le_of_weight_estimate
    (hweight : ∃ Cweight : ℝ, 0 < Cweight ∧ ∃ T : ℕ,
      ∀ t : ℕ, T ≤ t → fordWeightSum t ≤ Cweight * fordWeightScale t) :
    ∃ C : ℝ, 0 < C ∧ ∃ Y₀ : ℕ,
      ∀ x y q f : ℕ, Y₀ ≤ y → y ^ 2 ≤ x →
        q ∈ squarefullSet x → f ∈ q.divisors →
        fordHStarDenominatorWeight (x / q) (y / f) +
            ((2 * (y / f) + 1 : ℕ) : ℝ)⁻¹ ≤
          C * (((max f (q / f) : ℕ) : ℝ) ^ (1 / 8 : ℝ)) /
            Erdos896.logDenom896 y := by
  obtain ⟨B, hB, YB, henvelope⟩ :=
    exists_fordDenominatorSum_uniform_envelope_of_weight_estimate hweight
  have hgrowthEventually := eventually_logDenom896_le_eighth_rpow
  rw [eventually_atTop] at hgrowthEventually
  obtain ⟨YG, hgrowth⟩ := hgrowthEventually
  let Y₀ : ℕ := max 3 (max YB YG)
  have hY₀ : 3 ≤ Y₀ := le_max_left _ _
  have hYB : YB ≤ Y₀ :=
    (le_max_left YB YG).trans (le_max_right 3 (max YB YG))
  have hYG : YG ≤ Y₀ :=
    (le_max_right YB YG).trans (le_max_right 3 (max YB YG))
  have henvelope' : ∀ {y T : ℕ}, Y₀ ≤ y → 2 ≤ T →
      fordDenominatorSum T ≤
        B * (max 1 ((y : ℝ) / (T : ℝ))) ^ (1 / 8 : ℝ) /
          Erdos896.logDenom896 y := by
    intro y T hy hT
    exact henvelope (hYB.trans hy) hT
  have hgrowth' : ∀ {y : ℕ}, Y₀ ≤ y →
      Erdos896.logDenom896 y ≤ (1 : ℝ) * (y : ℝ) ^ (1 / 8 : ℝ) := by
    intro y hy
    simpa using hgrowth y (hYG.trans hy)
  obtain ⟨C, hC, hlocal⟩ :=
    exists_fordHStarDenominatorWeight_add_endpoint_le hY₀ hB.le
      (by norm_num : (0 : ℝ) ≤ 1) henvelope' hgrowth'
  exact ⟨C, hC, Y₀, hlocal⟩


/-! ## The squarefull-divisor moment and finite assembly -/

/-- The positive moment which absorbs both the divisor variable and its
complement inside the squarefull part.  The exponent `1/8 < 1/2` leaves a
convergent squarefull series. -/
noncomputable def fordSquarefullDivisorEighthMoment (R : ℕ) : ℝ :=
  ∑ q ∈ squarefullSet R, ∑ f ∈ q.divisors,
    (q : ℝ)⁻¹ * (((max f (q / f) : ℕ) : ℝ) ^ (1 / 8 : ℝ))

theorem fordSquarefullDivisorEighthMoment_nonneg (R : ℕ) :
    0 ≤ fordSquarefullDivisorEighthMoment R := by
  unfold fordSquarefullDivisorEighthMoment
  exact Finset.sum_nonneg fun q _ ↦ Finset.sum_nonneg fun f _ ↦
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- The squarefull moment is uniformly bounded. -/
theorem exists_fordSquarefullDivisorEighthMoment_le :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℕ,
      fordSquarefullDivisorEighthMoment R ≤ C := by
  simpa [fordSquarefullDivisorEighthMoment] using
    exists_uniform_squarefull_max_divisor_moment

/-- Purely finite assembly of the `q/f` collapse.  Its two hypotheses are
the exact independent inputs proved by the local dyadic estimate and the
squarefull moment estimate. -/
theorem exists_fordHReductionDenominatorWeight_le_of_local_and_moment
    (hmoment : ∃ Cmoment : ℝ, 0 < Cmoment ∧ ∀ R : ℕ,
      fordSquarefullDivisorEighthMoment R ≤ Cmoment)
    (hlocal : ∃ Clocal : ℝ, 0 < Clocal ∧ ∃ Y₀ : ℕ,
      ∀ x y q f : ℕ, Y₀ ≤ y → y ^ 2 ≤ x →
        q ∈ squarefullSet x → f ∈ q.divisors →
        fordHStarDenominatorWeight (x / q) (y / f) +
            ((2 * (y / f) + 1 : ℕ) : ℝ)⁻¹ ≤
          Clocal * (((max f (q / f) : ℕ) : ℝ) ^ (1 / 8 : ℝ)) /
            Erdos896.logDenom896 y) :
    ∃ C : ℝ, 0 < C ∧ ∃ Y₀ : ℕ, ∀ x y : ℕ,
      Y₀ ≤ y → y ^ 2 ≤ x →
        fordHReductionDenominatorWeight x y ≤
          C / Erdos896.logDenom896 y := by
  obtain ⟨Cmoment, hCmoment, hmoment⟩ := hmoment
  obtain ⟨Clocal, hClocal, Y₀, hlocal⟩ := hlocal
  refine ⟨Clocal * Cmoment, mul_pos hClocal hCmoment,
    max Y₀ 3, ?_⟩
  intro x y hy hxy
  have hyY₀ : Y₀ ≤ y := (le_max_left Y₀ 3).trans hy
  have hy3 : 3 ≤ y := (le_max_right Y₀ 3).trans hy
  have hdenPos : 0 < Erdos896.logDenom896 y :=
    Erdos896.logDenom896_pos hy3
  rw [fordHReductionDenominatorWeight]
  calc
    (∑ q ∈ squarefullSet x, ∑ f ∈ q.divisors,
        (q : ℝ)⁻¹ *
          (fordHStarDenominatorWeight (x / q) (y / f) +
            ((2 * (y / f) + 1 : ℕ) : ℝ)⁻¹)) ≤
      ∑ q ∈ squarefullSet x, ∑ f ∈ q.divisors,
        (q : ℝ)⁻¹ *
          (Clocal * (((max f (q / f) : ℕ) : ℝ) ^ (1 / 8 : ℝ)) /
            Erdos896.logDenom896 y) := by
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro f hf
      exact mul_le_mul_of_nonneg_left
        (hlocal x y q f hyY₀ hxy hq hf)
        (inv_nonneg.mpr (Nat.cast_nonneg q))
    _ = (Clocal / Erdos896.logDenom896 y) *
        fordSquarefullDivisorEighthMoment x := by
      unfold fordSquarefullDivisorEighthMoment
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f hf
      ring
    _ ≤ (Clocal / Erdos896.logDenom896 y) * Cmoment := by
      exact mul_le_mul_of_nonneg_left (hmoment x)
        (div_nonneg hClocal.le hdenPos.le)
    _ = (Clocal * Cmoment) / Erdos896.logDenom896 y := by ring

/-! ## Consumer-facing assembly -/

/-- Once the finite `q/f` expression has been collapsed, the weighted
reduction of `Reduction.lean` immediately gives Ford's upper bound for
`H(x,y,2y)`. -/
theorem exists_H_le_inv_logDenom_of_reduction_bound
    (hcollapse : ∃ Creduce : ℝ, 0 < Creduce ∧ ∃ Y₀ : ℕ,
      ∀ x y : ℕ, Y₀ ≤ y → y ^ 2 ≤ x →
        fordHReductionDenominatorWeight x y ≤
          Creduce / Erdos896.logDenom896 y) :
    ∃ C : ℝ, 0 < C ∧ ∃ Y₀ : ℕ, ∀ x y : ℕ,
      Y₀ ≤ y → y ^ 2 ≤ x →
        (H x y (2 * y) : ℝ) ≤
          C * (x : ℝ) / Erdos896.logDenom896 y := by
  obtain ⟨Cbase, hCbase, hbase⟩ :=
    exists_H_le_fordHReductionDenominatorWeight
  obtain ⟨Creduce, hCreduce, Y₀, hcollapse⟩ := hcollapse
  refine ⟨Cbase * Creduce, mul_pos hCbase hCreduce, max Y₀ 3, ?_⟩
  intro x y hy hxy
  have hyY₀ : Y₀ ≤ y := (le_max_left Y₀ 3).trans hy
  have hy3 : 3 ≤ y := (le_max_right Y₀ 3).trans hy
  have hdenPos := Erdos896.logDenom896_pos hy3
  have hx0 : 0 ≤ (x : ℝ) := Nat.cast_nonneg x
  calc
    (H x y (2 * y) : ℝ) ≤
        Cbase * (x : ℝ) * fordHReductionDenominatorWeight x y :=
      hbase x y
    _ ≤ Cbase * (x : ℝ) *
        (Creduce / Erdos896.logDenom896 y) := by
      exact mul_le_mul_of_nonneg_left (hcollapse x y hyY₀ hxy)
        (mul_nonneg hCbase.le hx0)
    _ = (Cbase * Creduce) * (x : ℝ) /
        Erdos896.logDenom896 y := by ring

/-- Ford's sharp weight-sum estimate implies the complete collapse of the
squarefull, divisor, and dyadic parts of the reduction. -/
theorem exists_fordHReductionDenominatorWeight_le_of_weight_estimate
    (hweight : ∃ Cweight : ℝ, 0 < Cweight ∧ ∃ T : ℕ,
      ∀ t : ℕ, T ≤ t → fordWeightSum t ≤ Cweight * fordWeightScale t) :
    ∃ C : ℝ, 0 < C ∧ ∃ Y₀ : ℕ, ∀ x y : ℕ,
      Y₀ ≤ y → y ^ 2 ≤ x →
        fordHReductionDenominatorWeight x y ≤
          C / Erdos896.logDenom896 y := by
  exact exists_fordHReductionDenominatorWeight_le_of_local_and_moment
    exists_fordSquarefullDivisorEighthMoment_le
    (exists_fordHStarDenominatorWeight_add_endpoint_le_of_weight_estimate
      hweight)

/-- Conditional consumer form of Ford's upper bound for `H(x,y,2y)`. -/
theorem exists_H_le_inv_logDenom_of_weight_estimate
    (hweight : ∃ Cweight : ℝ, 0 < Cweight ∧ ∃ T : ℕ,
      ∀ t : ℕ, T ≤ t → fordWeightSum t ≤ Cweight * fordWeightScale t) :
    ∃ C : ℝ, 0 < C ∧ ∃ Y₀ : ℕ, ∀ x y : ℕ,
      Y₀ ≤ y → y ^ 2 ≤ x →
        (H x y (2 * y) : ℝ) ≤
          C * (x : ℝ) / Erdos896.logDenom896 y :=
  exists_H_le_inv_logDenom_of_reduction_bound
    (exists_fordHReductionDenominatorWeight_le_of_weight_estimate hweight)

/-- Big-O form at the Ford scale, specialized to the square ambient range.
This is the upper-bound interface used by the final `IsTheta` assembly. -/
theorem H_square_isBigO_scale896_of_weight_estimate
    (hweight : ∃ Cweight : ℝ, 0 < Cweight ∧ ∃ T : ℕ,
      ∀ t : ℕ, T ≤ t → fordWeightSum t ≤ Cweight * fordWeightScale t) :
    (fun N : ℕ ↦ (H (N ^ 2) N (2 * N) : ℝ)) =O[atTop]
      Erdos896.scale896 := by
  obtain ⟨C, hC, Y₀, hH⟩ :=
    exists_H_le_inv_logDenom_of_weight_estimate hweight
  apply IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (max Y₀ 3)] with N hN
  have hNY₀ : Y₀ ≤ N := (le_max_left Y₀ 3).trans hN
  have hN3 : 3 ≤ N := (le_max_right Y₀ 3).trans hN
  have hHN : (H (N ^ 2) N (2 * N) : ℝ) ≤
      C * ((N ^ 2 : ℕ) : ℝ) / Erdos896.logDenom896 N :=
    hH (N ^ 2) N hNY₀ le_rfl
  have hHnonneg : 0 ≤ (H (N ^ 2) N (2 * N) : ℝ) := Nat.cast_nonneg _
  have hscaleNonneg : 0 ≤ Erdos896.scale896 N :=
    (Erdos896.scale896_pos hN3).le
  rw [Real.norm_of_nonneg hHnonneg, Real.norm_of_nonneg hscaleNonneg]
  calc
    (H (N ^ 2) N (2 * N) : ℝ) ≤
        C * ((N ^ 2 : ℕ) : ℝ) / Erdos896.logDenom896 N := hHN
    _ = C * Erdos896.scale896 N := by
      rw [Erdos896.scale896, Nat.cast_pow]
      ring

/-! ## Assumption-free upper bounds -/

/-- The fully assembled collapse of Ford's squarefull/divisor/dyadic
reduction.  Its only analytic input is the unconditional sharp weight-sum
estimate proved in `SumTk.lean`. -/
theorem exists_fordHReductionDenominatorWeight_le :
    ∃ C : ℝ, 0 < C ∧ ∃ Y₀ : ℕ, ∀ x y : ℕ,
      Y₀ ≤ y → y ^ 2 ≤ x →
        fordHReductionDenominatorWeight x y ≤
          C / Erdos896.logDenom896 y :=
  exists_fordHReductionDenominatorWeight_le_of_weight_estimate (by
    simpa only [fordWeightScale] using exists_fordWeightSum_le_scale)

/-- Ford's unconditional local upper estimate for divisors in `(y,2y]`. -/
theorem exists_H_le_inv_logDenom :
    ∃ C : ℝ, 0 < C ∧ ∃ Y₀ : ℕ, ∀ x y : ℕ,
      Y₀ ≤ y → y ^ 2 ≤ x →
        (H x y (2 * y) : ℝ) ≤
          C * (x : ℝ) / Erdos896.logDenom896 y :=
  exists_H_le_inv_logDenom_of_reduction_bound
    exists_fordHReductionDenominatorWeight_le

/-- Assumption-free Big-O form of the square-range local estimate. -/
theorem H_square_isBigO_scale896 :
    (fun N : ℕ ↦ (H (N ^ 2) N (2 * N) : ℝ)) =O[atTop]
      Erdos896.scale896 :=
  H_square_isBigO_scale896_of_weight_estimate (by
    simpa only [fordWeightScale] using exists_fordWeightSum_le_scale)

end Erdos896.Ford
