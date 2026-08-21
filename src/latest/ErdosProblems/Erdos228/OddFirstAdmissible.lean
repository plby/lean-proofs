import ErdosProblems.Erdos228.OddSine
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-!
# The first odd-sine colouring parameters

This file verifies the numerical hypotheses for the first full-colouring
argument in the odd-sine construction.  If the interval family has `N`
members, the common discrepancy parameter is

`14 * sqrt (log (16 * n / N))`.

The smallness assumption `N ≤ 2⁻⁴⁰ n` is just strong enough for the unit-error
estimate.  The proof retains the rational margin in the published constants.
-/

namespace Erdos228.OddSine

open scoped BigOperators

noncomputable section

/-- The common parameter in the first discrepancy colouring. -/
def firstColoringParameter (n N : ℕ) : ℝ :=
  14 * Real.sqrt (Real.log ((16 * n : ℕ) / (N : ℝ)))

private lemma firstColoring_ratio_ge
    {n N : ℕ} {gamma : ℝ} (hn : 0 < n) (hN : 0 < N)
    (hgamma : gamma ≤ 1 / (2 : ℝ) ^ 40)
    (hcard : (N : ℝ) ≤ gamma * n) :
    (2 : ℝ) ^ 44 ≤ (16 * n : ℕ) / (N : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsmall : (N : ℝ) ≤ (n : ℝ) / 2 ^ 40 := by
    calc
      (N : ℝ) ≤ gamma * n := hcard
      _ ≤ (1 / (2 : ℝ) ^ 40) * n :=
        mul_le_mul_of_nonneg_right hgamma hnR.le
      _ = (n : ℝ) / 2 ^ 40 := by ring
  apply (le_div_iff₀ hNR).2
  push_cast
  norm_num at hsmall ⊢
  nlinarith

private lemma firstColoring_log_ratio_nonneg
    {n N : ℕ} {gamma : ℝ} (hn : 0 < n) (hN : 0 < N)
    (hgamma : gamma ≤ 1 / (2 : ℝ) ^ 40)
    (hcard : (N : ℝ) ≤ gamma * n) :
    0 ≤ Real.log ((16 * n : ℕ) / (N : ℝ)) := by
  apply Real.log_nonneg
  exact (by norm_num : (1 : ℝ) ≤ 2 ^ 44).trans
    (firstColoring_ratio_ge hn hN hgamma hcard)

private lemma log_ratio_div_ratio_le
    {n N : ℕ} {gamma : ℝ} (hn : 0 < n) (hN : 0 < N)
    (hgamma : gamma ≤ 1 / (2 : ℝ) ^ 40)
    (hcard : (N : ℝ) ≤ gamma * n) :
    Real.log ((16 * n : ℕ) / (N : ℝ)) /
        ((16 * n : ℕ) / (N : ℝ)) ≤
      (28 / 5 : ℝ) ^ 2 / 2 ^ 44 := by
  let q : ℝ := (16 * n : ℕ) / (N : ℝ)
  have hq : (2 : ℝ) ^ 44 ≤ q := firstColoring_ratio_ge hn hN hgamma hcard
  have hexp : Real.exp 1 ≤ (2 : ℝ) ^ 44 := by
    exact Real.exp_one_lt_d9.le.trans (by norm_num)
  have hmono : Real.log q / q ≤ Real.log ((2 : ℝ) ^ 44) / (2 : ℝ) ^ 44 :=
    Real.log_div_self_antitoneOn hexp (hexp.trans hq) hq
  have hlog2 : Real.log 2 ≤ (7 / 10 : ℝ) :=
    Real.log_two_lt_d9.le.trans (by norm_num)
  have hlogpow : Real.log ((2 : ℝ) ^ 44) ≤ 44 * (7 / 10 : ℝ) := by
    rw [Real.log_pow]
    nlinarith
  dsimp only [q] at hmono
  calc
    Real.log ((16 * n : ℕ) / (N : ℝ)) /
          ((16 * n : ℕ) / (N : ℝ)) ≤
        Real.log ((2 : ℝ) ^ 44) / (2 : ℝ) ^ 44 := hmono
    _ ≤ (28 / 5 : ℝ) ^ 2 / 2 ^ 44 := by
      apply div_le_div_of_nonneg_right (hlogpow.trans (by norm_num)) (by positivity)

private lemma sqrt_card_scale_le
    {n N : ℕ} {gamma : ℝ} (hn : 0 < n) (hN : 0 < N)
    (hgamma : gamma ≤ 1 / (2 : ℝ) ^ 40)
    (hcard : (N : ℝ) ≤ gamma * n) :
    Real.sqrt N * Real.sqrt n / n ≤ (1 : ℝ) / 2 ^ 20 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNR : (0 : ℝ) ≤ N := by positivity
  have hsmall : (N : ℝ) ≤ (n : ℝ) / 2 ^ 40 := by
    calc
      (N : ℝ) ≤ gamma * n := hcard
      _ ≤ (1 / (2 : ℝ) ^ 40) * n :=
        mul_le_mul_of_nonneg_right hgamma hnR.le
      _ = (n : ℝ) / 2 ^ 40 := by ring
  have hsqrtn_sq : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
  have hsqrtN_sq : (Real.sqrt N) ^ 2 = (N : ℝ) := Real.sq_sqrt hNR
  have hscale_nonneg : 0 ≤ Real.sqrt N * Real.sqrt n / (n : ℝ) := by positivity
  have hsquare :
      (Real.sqrt N * Real.sqrt n / (n : ℝ)) ^ 2 = (N : ℝ) / n := by
    rw [div_pow, mul_pow, hsqrtN_sq, hsqrtn_sq]
    field_simp
  have htarget_nonneg : (0 : ℝ) ≤ 1 / 2 ^ 20 := by positivity
  have hratio : (N : ℝ) / n ≤ (1 : ℝ) / 2 ^ 40 := by
    apply (div_le_iff₀ hnR).2
    calc
      (N : ℝ) ≤ (n : ℝ) / 2 ^ 40 := hsmall
      _ = ((1 : ℝ) / 2 ^ 40) * n := by ring
  nlinarith [sq_nonneg
    (Real.sqrt N * Real.sqrt n / (n : ℝ) + (1 : ℝ) / 2 ^ 20)]

private lemma sqrt_log_mul_sqrt_card_scale_le
    {n N : ℕ} {gamma : ℝ} (hn : 0 < n) (hN : 0 < N)
    (hgamma : gamma ≤ 1 / (2 : ℝ) ^ 40)
    (hcard : (N : ℝ) ≤ gamma * n) :
    Real.sqrt (Real.log ((16 * n : ℕ) / (N : ℝ))) *
        (Real.sqrt N * Real.sqrt n / n) ≤
      (28 / 5 : ℝ) / 2 ^ 20 := by
  let q : ℝ := (16 * n : ℕ) / (N : ℝ)
  let a : ℝ := Real.sqrt N * Real.sqrt n / n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hqpos : 0 < q := by
    dsimp [q]
    positivity
  have hlog : 0 ≤ Real.log q := by
    dsimp only [q]
    exact firstColoring_log_ratio_nonneg hn hN hgamma hcard
  have ha_nonneg : 0 ≤ a := by dsimp [a]; positivity
  have hsqrta : a ^ 2 = 16 / q := by
    have hsqrtn_sq : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
    have hsqrtN_sq : (Real.sqrt N) ^ 2 = (N : ℝ) := Real.sq_sqrt hNR.le
    dsimp [a, q]
    rw [div_pow, mul_pow, hsqrtN_sq, hsqrtn_sq]
    push_cast
    field_simp
  have hquot := log_ratio_div_ratio_le hn hN hgamma hcard
  change Real.log q / q ≤ (28 / 5 : ℝ) ^ 2 / 2 ^ 44 at hquot
  have hsqrtlog_sq : (Real.sqrt (Real.log q)) ^ 2 = Real.log q :=
    Real.sq_sqrt hlog
  have hleft_nonneg : 0 ≤ Real.sqrt (Real.log q) * a := by positivity
  have hright_nonneg : (0 : ℝ) ≤ (28 / 5 : ℝ) / 2 ^ 20 := by positivity
  have hsquare :
      (Real.sqrt (Real.log q) * a) ^ 2 = 16 * (Real.log q / q) := by
    rw [mul_pow, hsqrtlog_sq, hsqrta]
    field_simp
  nlinarith

/-- The common parameter has exactly the exponential weight needed by the
first full-colouring budget. -/
theorem exp_neg_firstColoringParameter_sq
    {n N : ℕ} {gamma : ℝ} (hn : 0 < n) (hN : 0 < N)
    (hgamma : gamma ≤ 1 / (2 : ℝ) ^ 40)
    (hcard : (N : ℝ) ≤ gamma * n) :
    Real.exp (-(firstColoringParameter n N) ^ 2 / 196) =
      (N : ℝ) / (16 * n) := by
  have hlog := firstColoring_log_ratio_nonneg hn hN hgamma hcard
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  rw [firstColoringParameter, mul_pow, Real.sq_sqrt hlog]
  have hqpos : (0 : ℝ) < (16 * n : ℕ) / (N : ℝ) := by positivity
  rw [show -((14 : ℝ) ^ 2 * Real.log ((16 * n : ℕ) / (N : ℝ))) / 196 =
      -Real.log ((16 * n : ℕ) / (N : ℝ)) by ring]
  rw [Real.exp_neg, Real.exp_log hqpos]
  push_cast
  field_simp

/-- Under the BBMST density bound, the common first-colouring parameter is
admissible.  Positivity of `F.base.card` is necessary here: when `n > 0`, the
budget condition itself rules out an empty base family. -/
theorem firstColoringAdmissible_of_card_le
    {n : ℕ} (hn : 0 < n) (F : SuitableIntervalFamily n) {gamma : ℝ}
    (hgamma : gamma ≤ 1 / (2 : ℝ) ^ 40)
    (hbase : 0 < F.base.card)
    (hcard : (F.base.card : ℝ) ≤ gamma * n) :
    FirstColoringAdmissible F
      (fun _ ↦ firstColoringParameter n F.base.card) := by
  classical
  apply firstColoringAdmissible_of_numeric hn
  · intro j
    exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  · simp_rw [exp_neg_firstColoringParameter_sq hn hbase hgamma hcard]
    simp
    field_simp
    norm_num
  · intro j
    have hscale := sqrt_card_scale_le hn hbase hgamma hcard
    have hlogscale :=
      sqrt_log_mul_sqrt_card_scale_le hn hbase hgamma hcard
    have hpi : Real.pi ≤ (22 / 7 : ℝ) :=
      Real.pi_lt_d4.le.trans (by norm_num)
    rw [firstColoringParameter]
    simp only [K_eq]
    have hnonneg :
        0 ≤ (14 * Real.sqrt (Real.log ((16 * n : ℕ) / (F.base.card : ℝ))) + 30) *
          (Real.sqrt F.base.card * Real.sqrt n / n) := by
      have hlog := firstColoring_log_ratio_nonneg hn hbase hgamma hcard
      positivity
    calc
      (14 * Real.sqrt (Real.log ((16 * n : ℕ) / (F.base.card : ℝ))) + 30) *
          Real.sqrt (Fintype.card (↑F.base : Type)) *
          (24 * 128 * Real.pi * Real.sqrt n / n) =
        (24 * 128 * Real.pi) *
          ((14 * Real.sqrt (Real.log ((16 * n : ℕ) / (F.base.card : ℝ))) + 30) *
            (Real.sqrt F.base.card * Real.sqrt n / n)) := by
          simp only [Fintype.card_coe]
          ring
      _ ≤ (24 * 128 * (22 / 7 : ℝ)) *
          ((14 * Real.sqrt (Real.log ((16 * n : ℕ) / (F.base.card : ℝ))) + 30) *
            (Real.sqrt F.base.card * Real.sqrt n / n)) := by
          gcongr
      _ ≤ (24 * 128 * (22 / 7 : ℝ)) *
          (14 * ((28 / 5 : ℝ) / 2 ^ 20) + 30 * ((1 : ℝ) / 2 ^ 20)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc
            (14 * Real.sqrt (Real.log ((16 * n : ℕ) / (F.base.card : ℝ))) + 30) *
                (Real.sqrt F.base.card * Real.sqrt n / n) =
              14 * (Real.sqrt (Real.log ((16 * n : ℕ) / (F.base.card : ℝ))) *
                (Real.sqrt F.base.card * Real.sqrt n / n)) +
              30 * (Real.sqrt F.base.card * Real.sqrt n / n) := by ring
            _ ≤ 14 * ((28 / 5 : ℝ) / 2 ^ 20) +
                30 * ((1 : ℝ) / 2 ^ 20) := by gcongr
      _ ≤ 1 := by norm_num

/-- If the interval family is empty, the first colouring step is unnecessary:
the unique empty collection of interval signs has all Fourier targets equal to
zero.  This is the correct replacement for admissibility in the zero-cardinal
branch (the admissibility budget itself is impossible when `n > 0`). -/
theorem exists_intervalColoring_of_base_card_eq_zero
    {n : ℕ} (F : SuitableIntervalFamily n) (hbase : F.base.card = 0) :
    ∃ alpha : (↑F.base : Type) → ℝ,
      Erdos228.Discrepancy.IsSign alpha ∧
        ∀ j < n, |fourierTarget F alpha j| ≤ 1 := by
  classical
  have hempty : F.base = ∅ := Finset.card_eq_zero.mp hbase
  have hisEmpty : IsEmpty (↑F.base : Type) := Finset.isEmpty_coe_sort.mpr hempty
  let alpha : (↑F.base : Type) → ℝ := fun _ ↦ 1
  refine ⟨alpha, fun I ↦ Or.inl rfl, ?_⟩
  intro j hj
  simp [fourierTarget, hj]

end

end Erdos228.OddSine
