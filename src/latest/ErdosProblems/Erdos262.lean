/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of the resolution of Erdős Problem 262.
https://www.erdosproblems.com/262

The mathematical argument is due to Jaroslav Hančl:
J. Hančl, Expression of real numbers with the help of infinite series,
Acta Arith. 59 (1991), 97--104.
-/

import Mathlib

namespace Erdos262

open Filter Finset Real Topology
open scoped BigOperators Topology

noncomputable section

/-- The summand occurring in the definition of an irrationality sequence. -/
def seriesTerm (a t : ℕ → ℕ) (n : ℕ) : ℝ :=
  1 / ((t n : ℝ) * (a n : ℝ))

/-- A positive, strictly increasing sequence of integers is an irrationality sequence when
every positive integral choice of the extra factors gives an irrational reciprocal sum. -/
def IrrationalitySequence (a : ℕ → ℕ) : Prop :=
  (∀ n, 0 < a n) ∧ StrictMono a ∧
    ∀ t : ℕ → ℕ, (∀ n, 0 < t n) → Irrational (∑' n, seriesTerm a t n)

/-- The strictly-underestimating greedy denominator.  Adding one to the floor (rather than
using the ceiling) ensures that the new remainder is strictly positive. -/
def greedyDenom (a : ℕ) (r : ℝ) : ℕ :=
  ⌊1 / ((a : ℝ) * r)⌋₊ + 1

@[simp]
lemma greedyDenom_pos (a : ℕ) (r : ℝ) : 0 < greedyDenom a r := by
  simp [greedyDenom]

/-- One step of Hančl's greedy construction. -/
lemma greedy_step {a : ℕ} (ha : 0 < a) {r : ℝ} (hr : 0 < r) :
    0 < r - 1 / ((a : ℝ) * greedyDenom a r) ∧
      r - 1 / ((a : ℝ) * greedyDenom a r) ≤ (a : ℝ) * r ^ 2 := by
  let A : ℝ := a
  let x : ℝ := 1 / (A * r)
  let T : ℝ := greedyDenom a r
  have hA : 0 < A := by
    dsimp [A]
    exact_mod_cast ha
  have hAr : 0 < A * r := mul_pos hA hr
  have hT : 0 < T := by
    dsimp [T]
    exact_mod_cast greedyDenom_pos a r
  have hx0 : 0 ≤ x := (one_div_pos.mpr hAr).le
  have hxT : x < T := by
    dsimp [x, T, greedyDenom]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one (1 / (A * r)))
  have hTle : T ≤ x + 1 := by
    have hf := Nat.floor_le hx0
    dsimp [T, greedyDenom]
    rw [Nat.cast_add, Nat.cast_one]
    simpa [x, add_comm] using add_le_add_right hf 1
  have hterm : 1 / (A * T) < r := by
    have h := (div_lt_iff₀ hAr).mp hxT
    apply (div_lt_iff₀ (mul_pos hA hT)).2
    nlinarith [h]
  constructor
  · exact sub_pos.mpr hterm
  · have hrem : r - 1 / (A * T) = r * (T - x) / T := by
      dsimp [x]
      field_simp [ne_of_gt hA, ne_of_gt hr, ne_of_gt hT]
    have hTx0 : 0 ≤ T - x := sub_nonneg.mpr hxT.le
    have hTx1 : T - x ≤ 1 := by linarith
    have hrem_le : r * (T - x) / T ≤ r / T := by
      apply div_le_div_of_nonneg_right _ hT.le
      simpa using mul_le_mul_of_nonneg_left hTx1 hr.le
    have hinv : 1 / T < A * r := by
      apply (div_lt_iff₀ hT).2
      have h := (div_lt_iff₀ hAr).mp hxT
      nlinarith [h]
    rw [hrem]
    calc
      r * (T - x) / T ≤ r / T := hrem_le
      _ = r * (1 / T) := by ring
      _ ≤ r * (A * r) := mul_le_mul_of_nonneg_left hinv.le hr.le
      _ = A * r ^ 2 := by ring

/-- Remainders in the greedy expansion of the dyadic number `2⁻ᴹ`. -/
def remainder (a : ℕ → ℕ) (M : ℕ) : ℕ → ℝ
  | 0 => (1 / 2 : ℝ) ^ M
  | n + 1 => remainder a M n -
      1 / ((a n : ℝ) * greedyDenom (a n) (remainder a M n))

/-- The positive integral multipliers supplied by the greedy construction. -/
def coefficients (a : ℕ → ℕ) (M : ℕ) (n : ℕ) : ℕ :=
  greedyDenom (a n) (remainder a M n)

@[simp]
lemma coefficients_pos (a : ℕ → ℕ) (M n : ℕ) : 0 < coefficients a M n := by
  simp [coefficients]

@[simp]
lemma remainder_zero (a : ℕ → ℕ) (M : ℕ) :
    remainder a M 0 = (1 / 2 : ℝ) ^ M := rfl

lemma remainder_succ (a : ℕ → ℕ) (M n : ℕ) :
    remainder a M (n + 1) = remainder a M n - seriesTerm a (coefficients a M) n := by
  simp [remainder, seriesTerm, coefficients, mul_comm]

lemma remainder_pos (a : ℕ → ℕ) (M : ℕ) (ha : ∀ n, 0 < a n) :
    ∀ n, 0 < remainder a M n := by
  intro n
  induction n with
  | zero => simp [remainder]
  | succ n ih =>
      rw [remainder_succ]
      simpa [seriesTerm, coefficients, mul_comm] using (greedy_step (ha n) ih).1

lemma remainder_quadratic (a : ℕ → ℕ) (M n : ℕ) (ha : ∀ n, 0 < a n) :
    remainder a M (n + 1) ≤ (a n : ℝ) * remainder a M n ^ 2 := by
  rw [remainder_succ]
  simpa [seriesTerm, coefficients, mul_comm] using
    (greedy_step (ha n) (remainder_pos a M ha n)).2

/-- The defining finite sums telescope exactly. -/
lemma sum_range_seriesTerm (a : ℕ → ℕ) (M N : ℕ) :
    ∑ n ∈ range N, seriesTerm a (coefficients a M) n =
      (1 / 2 : ℝ) ^ M - remainder a M N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [sum_range_succ, ih, remainder_succ]
      ring

/-- The logarithmic cost of the `n`th entry, with the paper's one-based weight `2⁻⁽ⁿ⁺¹⁾`. -/
def logBudgetTerm (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  Real.log (a n : ℝ) / (2 : ℝ) ^ (n + 1)

lemma logBudgetTerm_nonneg (a : ℕ → ℕ) (ha : ∀ n, 0 < a n) (n : ℕ) :
    0 ≤ logBudgetTerm a n := by
  apply div_nonneg
  · apply Real.log_nonneg
    exact_mod_cast ha n
  · positivity

/-- Iterating the quadratic remainder estimate gives the normalized logarithmic bound. -/
lemma log_remainder_le (a : ℕ → ℕ) (M N : ℕ) (ha : ∀ n, 0 < a n) :
    Real.log (remainder a M N) ≤
      (2 : ℝ) ^ N *
        (-((M : ℝ) * Real.log 2) + ∑ n ∈ range N, logBudgetTerm a n) := by
  induction N with
  | zero =>
      simp only [remainder_zero, pow_zero, range_zero, sum_empty, add_zero, one_mul]
      rw [Real.log_pow, Real.log_div one_ne_zero (by norm_num : (2 : ℝ) ≠ 0)]
      simp
  | succ N ih =>
      have hr := remainder_pos a M ha N
      have hrs := remainder_pos a M ha (N + 1)
      have hA : 0 < (a N : ℝ) := by exact_mod_cast ha N
      have hquad := remainder_quadratic a M N ha
      have hlog : Real.log (remainder a M (N + 1)) ≤
          Real.log ((a N : ℝ) * remainder a M N ^ 2) :=
        Real.log_le_log hrs hquad
      rw [Real.log_mul hA.ne' (pow_ne_zero 2 hr.ne'), Real.log_pow] at hlog
      calc
        Real.log (remainder a M (N + 1))
            ≤ Real.log (a N : ℝ) + (2 : ℝ) * Real.log (remainder a M N) := hlog
        _ ≤ Real.log (a N : ℝ) + (2 : ℝ) *
              ((2 : ℝ) ^ N *
                (-((M : ℝ) * Real.log 2) + ∑ n ∈ range N, logBudgetTerm a n)) := by
              gcongr
        _ = (2 : ℝ) ^ (N + 1) *
              (-((M : ℝ) * Real.log 2) +
                ∑ n ∈ range (N + 1), logBudgetTerm a n) := by
              rw [sum_range_succ, pow_succ]
              simp only [logBudgetTerm]
              field_simp
              ring

/-- If the initial dyadic exponent exceeds the full logarithmic budget, the greedy
remainders converge to zero. -/
lemma remainder_tendsto_zero (a : ℕ → ℕ) (M : ℕ) (ha : ∀ n, 0 < a n)
    (hs : Summable (logBudgetTerm a))
    (hM : ∑' n, logBudgetTerm a n < (M : ℝ) * Real.log 2) :
    Tendsto (remainder a M) atTop (𝓝 0) := by
  let δ : ℝ := (M : ℝ) * Real.log 2 - ∑' n, logBudgetTerm a n
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  have hupper : ∀ N : ℕ, remainder a M N ≤ Real.exp (-δ * (N : ℝ)) := by
    intro N
    have hpartial : ∑ n ∈ range N, logBudgetTerm a n ≤ ∑' n, logBudgetTerm a n :=
      hs.sum_le_tsum (range N) (fun n _ ↦ logBudgetTerm_nonneg a ha n)
    have hlog : Real.log (remainder a M N) ≤ -δ * (N : ℝ) := by
      calc
        Real.log (remainder a M N) ≤
            (2 : ℝ) ^ N *
              (-((M : ℝ) * Real.log 2) + ∑ n ∈ range N, logBudgetTerm a n) :=
          log_remainder_le a M N ha
        _ ≤ (2 : ℝ) ^ N * (-δ) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          dsimp [δ]
          linarith
        _ ≤ -δ * (N : ℝ) := by
          have hpowNat : N ≤ 2 ^ N := Nat.le_of_lt N.lt_two_pow_self
          have hpow : (N : ℝ) ≤ (2 : ℝ) ^ N := by exact_mod_cast hpowNat
          nlinarith
    calc
      remainder a M N = Real.exp (Real.log (remainder a M N)) :=
        (Real.exp_log (remainder_pos a M ha N)).symm
      _ ≤ Real.exp (-δ * (N : ℝ)) := Real.exp_le_exp.mpr hlog
  have hgeom : Tendsto (fun N : ℕ ↦ Real.exp (-δ * (N : ℝ))) atTop (𝓝 0) := by
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
      (show 0 ≤ Real.exp (-δ) by positivity)
      (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hδ))
    convert hpow using 1
    ext N
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hgeom
    (Eventually.of_forall fun N ↦ (remainder_pos a M ha N).le)
    (Eventually.of_forall hupper)

lemma seriesTerm_nonneg (a t : ℕ → ℕ) (n : ℕ) : 0 ≤ seriesTerm a t n := by
  unfold seriesTerm
  exact one_div_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-- Hančl's master criterion: a finite weighted logarithmic budget produces positive
integral multipliers for which the reciprocal series has a rational sum. -/
theorem exists_rational_sum_of_summable_logBudget (a : ℕ → ℕ) (ha : ∀ n, 0 < a n)
    (hs : Summable (logBudgetTerm a)) :
    ∃ t : ℕ → ℕ, (∀ n, 0 < t n) ∧
      ∃ q : ℚ, HasSum (seriesTerm a t) (q : ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨M, hM⟩ := exists_nat_gt ((∑' n, logBudgetTerm a n) / Real.log 2)
  have hM' : ∑' n, logBudgetTerm a n < (M : ℝ) * Real.log 2 := by
    have := (div_lt_iff₀ hlog2).mp hM
    simpa [mul_comm] using this
  let t : ℕ → ℕ := coefficients a M
  have ht : ∀ n, 0 < t n := fun n ↦ coefficients_pos a M n
  have hsum : HasSum (seriesTerm a t) ((1 / 2 : ℝ) ^ M) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg (seriesTerm_nonneg a t)]
    have hrem := remainder_tendsto_zero a M ha hs hM'
    have hlim : Tendsto (fun N ↦ (1 / 2 : ℝ) ^ M - remainder a M N)
        atTop (𝓝 ((1 / 2 : ℝ) ^ M)) := by
      simpa using tendsto_const_nhds.sub hrem
    simpa [t, sum_range_seriesTerm] using hlim
  refine ⟨t, ht, (1 / 2 : ℚ) ^ M, ?_⟩
  simpa using hsum

theorem not_irrationalitySequence_of_summable_logBudget (a : ℕ → ℕ)
    (hs : Summable (logBudgetTerm a)) : ¬IrrationalitySequence a := by
  intro h
  obtain ⟨t, ht, q, hq⟩ :=
    exists_rational_sum_of_summable_logBudget a h.1 hs
  have hirr := h.2.2 t ht
  rw [hq.tsum_eq] at hirr
  exact q.not_irrational hirr

private lemma rpow_sub_div_natPow (n : ℕ) (x : ℝ) :
    (2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) - x) / (2 : ℝ) ^ (n + 1) =
      (2 : ℝ) ^ (-x) := by
  rw [← Real.rpow_natCast, Real.rpow_sub (by norm_num),
    Real.rpow_neg (by norm_num)]
  field_simp

private lemma summable_logC_geometric (C : ℝ) :
    Summable (fun n : ℕ ↦ Real.log C / (2 : ℝ) ^ (n + 1)) := by
  simpa [pow_succ, div_eq_mul_inv, mul_assoc] using
    (summable_geometric_two.mul_left (Real.log C / 2))

/-- The analytic comparison underlying the general `F`-growth form of Hančl's theorem. -/
theorem summable_logBudget_of_rpow_bound
    (a : ℕ → ℕ) (F : ℕ → ℝ) (C : ℝ)
    (ha : ∀ n, 0 < a n) (hC : 1 ≤ C)
    (hF : Summable (fun n ↦ (2 : ℝ) ^ (-F n)))
    (hgrowth : ∀ᶠ n in atTop,
      (a n : ℝ) ≤ C * (2 : ℝ) ^ ((2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) - F n))) :
    Summable (logBudgetTerm a) := by
  have hmajorant : Summable (fun n : ℕ ↦
      Real.log C / (2 : ℝ) ^ (n + 1) +
        Real.log 2 * (2 : ℝ) ^ (-F n)) :=
    (summable_logC_geometric C).add (hF.mul_left (Real.log 2))
  apply hmajorant.of_norm_bounded_eventually_nat
  filter_upwards [hgrowth] with n hn
  have ha1 : 1 ≤ a n := ha n
  have haRpos : 0 < (a n : ℝ) := by exact_mod_cast ha n
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have houterpos : 0 < (2 : ℝ) ^ ((2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) - F n)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hlognonneg : 0 ≤ Real.log (a n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast ha1)
  simp only [logBudgetTerm]
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hlognonneg (by positivity))]
  calc
    logBudgetTerm a n ≤
        Real.log (C * (2 : ℝ) ^ ((2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) - F n))) /
          (2 : ℝ) ^ (n + 1) := by
      exact div_le_div_of_nonneg_right (Real.log_le_log haRpos hn) (by positivity)
    _ = (Real.log C +
          ((2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) - F n)) * Real.log 2) /
          (2 : ℝ) ^ (n + 1) := by
      rw [Real.log_mul hCpos.ne' houterpos.ne', Real.log_rpow (by norm_num)]
    _ = Real.log C / (2 : ℝ) ^ (n + 1) +
          Real.log 2 * (2 : ℝ) ^ (-F n) := by
      rw [add_div]
      congr 1
      calc
        (2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) - F n) *
              Real.log 2 / (2 : ℝ) ^ (n + 1) =
            Real.log 2 *
              ((2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) - F n) /
                (2 : ℝ) ^ (n + 1)) := by ring
        _ = Real.log 2 * (2 : ℝ) ^ (-F n) := by
          rw [rpow_sub_div_natPow]

/-- The same comparison with an arbitrary positive big-O constant. -/
theorem summable_logBudget_of_rpow_bound_pos
    (a : ℕ → ℕ) (F : ℕ → ℝ) (C : ℝ)
    (ha : ∀ n, 0 < a n) (_hC : 0 < C)
    (hF : Summable (fun n ↦ (2 : ℝ) ^ (-F n)))
    (hgrowth : ∀ᶠ n in atTop,
      (a n : ℝ) ≤ C * (2 : ℝ) ^ ((2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) - F n))) :
    Summable (logBudgetTerm a) := by
  apply summable_logBudget_of_rpow_bound a F (max C 1) ha
    (le_max_right C 1) hF
  filter_upwards [hgrowth] with n hn
  refine hn.trans ?_
  exact mul_le_mul_of_nonneg_right (le_max_left C 1)
    (Real.rpow_nonneg (by norm_num) _)

/-- The general resolution stated on the Erdős Problems page.  Lean indices start at zero,
so `a n` represents the paper's `a_(n+1)`. -/
theorem erdos_262_general_growth
    (a : ℕ → ℕ) (ha : ∀ n, 0 < a n) (F : ℕ → ℝ)
    (_hFlt : ∀ n, F n < (n + 1 : ℕ))
    (hF : Summable (fun n ↦ (2 : ℝ) ^ (-F n)))
    (hgrowth : ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
      (a n : ℝ) ≤ C * (2 : ℝ) ^ ((2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) - F n))) :
    ∃ t : ℕ → ℕ, (∀ n, 0 < t n) ∧
      ∃ q : ℚ, HasSum (seriesTerm a t) (q : ℝ) := by
  obtain ⟨C, hC, hgrowth⟩ := hgrowth
  exact exists_rational_sum_of_summable_logBudget a ha
    (summable_logBudget_of_rpow_bound_pos a F C ha hC hF hgrowth)

theorem not_irrationalitySequence_of_general_growth
    (a : ℕ → ℕ) (F : ℕ → ℝ)
    (hFlt : ∀ n, F n < (n + 1 : ℕ))
    (hF : Summable (fun n ↦ (2 : ℝ) ^ (-F n)))
    (hgrowth : ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
      (a n : ℝ) ≤ C * (2 : ℝ) ^ ((2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) - F n))) :
    ¬IrrationalitySequence a := by
  intro h
  obtain ⟨t, ht, q, hq⟩ := erdos_262_general_growth a h.1 F hFlt hF hgrowth
  have hirr := h.2.2 t ht
  rw [hq.tsum_eq] at hirr
  exact q.not_irrational hirr

private lemma summable_rpow_linear_gap (c : ℝ) (hc : c < 1) :
    Summable (fun n : ℕ ↦
      (2 : ℝ) ^ (-((1 - c) * ((n + 1 : ℕ) : ℝ)))) := by
  let r : ℝ := (2 : ℝ) ^ (-(1 - c))
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hgeom : Summable (fun n : ℕ ↦ r ^ n) :=
    summable_geometric_of_lt_one hr0 hr1
  have hshift : Summable (fun n : ℕ ↦ r ^ (n + 1)) :=
    hgeom.comp_injective Nat.succ_injective
  apply hshift.congr
  intro n
  dsimp [r]
  calc
    ((2 : ℝ) ^ (-(1 - c))) ^ (n + 1) =
        ((2 : ℝ) ^ (-(1 - c))) ^ ((n + 1 : ℕ) : ℝ) :=
      (Real.rpow_natCast _ _).symm
    _ = (2 : ℝ) ^ ((-(1 - c)) * ((n + 1 : ℕ) : ℝ)) :=
      (Real.rpow_mul (by norm_num) _ _).symm
    _ = (2 : ℝ) ^ (-((1 - c) * ((n + 1 : ℕ) : ℝ))) := by ring_nf

/-- Positivity and strict increase imply the elementary lower bound `n + 1 ≤ a n`. -/
private lemma index_succ_le_of_strictMono
    (a : ℕ → ℕ) (ha : ∀ n, 0 < a n) (hmono : StrictMono a) (n : ℕ) :
    n + 1 ≤ a n := by
  calc
    n + 1 ≤ n + a 0 := Nat.add_le_add_left (ha 0) n
    _ ≤ a (n + 0) := hmono.add_le_nat n 0
    _ = a n := by simp

/-- The double-logarithmic quotient, with the one-based index represented by `n + 1`. -/
def doubleLogRatio (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  Real.logb 2 (Real.logb 2 (a n : ℝ)) / ((n + 1 : ℕ) : ℝ)

private theorem summable_logBudget_of_eventually_doubleLogRatio_lt
    (a : ℕ → ℕ) (ha : ∀ n, 0 < a n) (hmono : StrictMono a)
    (c : ℝ) (hc : c < 1)
    (hub : ∀ᶠ n in atTop, doubleLogRatio a n < c) :
    Summable (logBudgetTerm a) := by
  apply summable_logBudget_of_rpow_bound a
    (fun n ↦ (1 - c) * ((n + 1 : ℕ) : ℝ)) 1 ha (by norm_num)
    (summable_rpow_linear_gap c hc)
  filter_upwards [hub, eventually_ge_atTop 1] with n hn hn1
  have hanLower : n + 1 ≤ a n := index_succ_le_of_strictMono a ha hmono n
  have haTwo : 1 < (a n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 1 < n + 1) hanLower)
  have haRpos : 0 < (a n : ℝ) := lt_trans zero_lt_one haTwo
  have hlogbpos : 0 < Real.logb 2 (a n : ℝ) :=
    Real.logb_pos (by norm_num) haTwo
  have hnpos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hdouble :
      Real.logb 2 (Real.logb 2 (a n : ℝ)) <
        c * ((n + 1 : ℕ) : ℝ) := by
    exact (div_lt_iff₀ hnpos).mp hn
  have hsingle :
      Real.logb 2 (a n : ℝ) <
        (2 : ℝ) ^ (c * ((n + 1 : ℕ) : ℝ)) :=
    (Real.logb_lt_iff_lt_rpow (by norm_num) hlogbpos).mp hdouble
  have haBound :
      (a n : ℝ) <
        (2 : ℝ) ^ ((2 : ℝ) ^ (c * ((n + 1 : ℕ) : ℝ))) :=
    (Real.logb_lt_iff_lt_rpow (by norm_num) haRpos).mp hsingle
  simpa only [one_mul, show
      ((n + 1 : ℕ) : ℝ) - (1 - c) * ((n + 1 : ℕ) : ℝ) =
        c * ((n + 1 : ℕ) : ℝ) by ring] using haBound.le

/-- Equivalent order-theoretic form of the sharp lower-limsup bound: every level below one
is attained infinitely often. -/
theorem frequently_le_doubleLogRatio (a : ℕ → ℕ) (h : IrrationalitySequence a)
    {c : ℝ} (hc : c < 1) : ∃ᶠ n in atTop, c ≤ doubleLogRatio a n := by
  by_contra hfreq
  have hub : ∀ᶠ n in atTop, doubleLogRatio a n < c := by
    change ¬¬(∀ᶠ n in atTop, ¬c ≤ doubleLogRatio a n) at hfreq
    exact Classical.not_not.mp (by simpa only [not_le] using hfreq)
  exact not_irrationalitySequence_of_summable_logBudget a
    (summable_logBudget_of_eventually_doubleLogRatio_lt a h.1 h.2.1 c hc hub) h

/-- **Erdős Problem 262 (Hančl).**  Every irrationality sequence obeys
`limsup log₂(log₂(aₙ))/n ≥ 1`.  The limsup is taken in `EReal`, so the statement also has
the mathematically correct meaning when the quotient is unbounded above. -/
theorem erdos_262 (a : ℕ → ℕ) (h : IrrationalitySequence a) :
    (1 : EReal) ≤ limsup (fun n ↦ (doubleLogRatio a n : EReal)) atTop := by
  apply le_of_forall_lt
  intro x hx
  obtain ⟨c, hxc, hc1⟩ := EReal.exists_between_coe_real hx
  have hc : c < 1 := EReal.coe_lt_coe_iff.mp (by simpa using hc1)
  have hfreqReal := frequently_le_doubleLogRatio a h hc
  have hfreq : ∃ᶠ n in atTop, (c : EReal) ≤ (doubleLogRatio a n : EReal) :=
    hfreqReal.mono fun n hn ↦ EReal.coe_le_coe_iff.mpr hn
  have hbounded : IsBoundedUnder (· ≤ ·) atTop
      (fun n ↦ (doubleLogRatio a n : EReal)) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun _ ↦ le_top)
  exact hxc.trans_le (le_limsup_of_frequently_le hfreq hbounded)

#print axioms Erdos262.erdos_262

end

end Erdos262
