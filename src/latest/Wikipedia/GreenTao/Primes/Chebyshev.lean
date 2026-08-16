import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Wikipedia.SzemeredisTheorem

open Finset Real
open Filter Asymptotics

/-- The natural primes in the quarter interval `(X / 4, X]`. -/
def primesInQuarterInterval (X : ℕ) : Finset ℕ :=
  {p ∈ Finset.range (X + 1) | p.Prime ∧ X / 4 < p}

@[simp]
theorem mem_primesInQuarterInterval {X p : ℕ} :
    p ∈ primesInQuarterInterval X ↔
      p.Prime ∧ X / 4 < p ∧ p ≤ X := by
  simp [primesInQuarterInterval, and_left_comm, and_comm]

/-- The interval finset is the difference of the two standard prime
finsets supplied by `Mathlib.NumberTheory.PrimeCounting`. -/
theorem primesInQuarterInterval_eq_sdiff (X : ℕ) :
    primesInQuarterInterval X =
      Nat.primesLE X \ Nat.primesLE (X / 4) := by
  ext p
  rw [mem_primesInQuarterInterval, Finset.mem_sdiff,
    Nat.mem_primesLE, Nat.mem_primesLE]
  constructor
  · rintro ⟨hp, hqp, hpX⟩
    exact ⟨⟨hpX, hp⟩, fun h ↦ by omega⟩
  · rintro ⟨⟨hpX, hp⟩, hnot⟩
    refine ⟨hp, ?_, hpX⟩
    by_contra! hpq
    exact hnot ⟨hpq, hp⟩

/-- Exact cardinality bridge to the prime-counting function. -/
theorem card_primesInQuarterInterval (X : ℕ) :
    #(primesInQuarterInterval X) =
      Nat.primeCounting X - Nat.primeCounting (X / 4) := by
  rw [primesInQuarterInterval_eq_sdiff,
    Finset.card_sdiff_of_subset
      (Nat.primesLE_mono (Nat.div_le_self X 4))]
  simp

/-- The same bridge with the literal filtered range appearing in the
statement. -/
theorem card_filter_range_prime_and_quarter_lt (X : ℕ) :
    #{p ∈ Finset.range (X + 1) | p.Prime ∧ X / 4 < p} =
      Nat.primeCounting X - Nat.primeCounting (X / 4) := by
  exact card_primesInQuarterInterval X

/-- Real-valued form of the cardinality bridge, with natural subtraction
converted to subtraction in `ℝ`. -/
theorem cast_card_primesInQuarterInterval (X : ℕ) :
    (#(primesInQuarterInterval X) : ℝ) =
      (Nat.primeCounting X : ℝ) -
        (Nat.primeCounting (X / 4) : ℝ) := by
  rw [card_primesInQuarterInterval, Nat.cast_sub]
  exact Nat.monotone_primeCounting (Nat.div_le_self X 4)

/-- The theta mass in `(X / 4, X]` is the sum of `log p` over the interval
finset. -/
theorem theta_sub_theta_quarter_eq_sum (X : ℕ) :
    Chebyshev.theta X -
        Chebyshev.theta ((X / 4 : ℕ) : ℝ) =
      ∑ p ∈ primesInQuarterInterval X, log p := by
  rw [Chebyshev.theta_eq_sum_primesLE_log,
    Chebyshev.theta_eq_sum_primesLE_log,
    primesInQuarterInterval_eq_sdiff]
  rw [sub_eq_iff_eq_add]
  exact (Finset.sum_sdiff (f := fun p : ℕ ↦ log p)
    (Nat.primesLE_mono (Nat.div_le_self X 4))).symm

/-- Each logarithmic prime weight in `(X / 4, X]` is at most `log X`. -/
theorem theta_sub_theta_quarter_le_card_mul_log (X : ℕ) :
    Chebyshev.theta X -
        Chebyshev.theta ((X / 4 : ℕ) : ℝ) ≤
      (#(primesInQuarterInterval X) : ℝ) * log X := by
  rw [theta_sub_theta_quarter_eq_sum]
  calc
    (∑ p ∈ primesInQuarterInterval X, log p)
        ≤ ∑ _p ∈ primesInQuarterInterval X, log X := by
      apply Finset.sum_le_sum
      intro p hp
      exact Real.log_le_log
        (by exact_mod_cast (mem_primesInQuarterInterval.mp hp).1.pos)
        (by exact_mod_cast (mem_primesInQuarterInterval.mp hp).2.2)
    _ = (#(primesInQuarterInterval X) : ℝ) * log X := by simp

/-- An explicit Chebyshev-expression lower bound for the number of primes in
`(X / 4, X]`.  The numerator has positive linear main term; its other terms
are elementary logarithmic and square-root errors. -/
theorem chebyshev_expression_le_card_primesInQuarterInterval
    {X : ℕ} (hX : 2 ≤ X) :
    (((X : ℝ) * log 2 - log (X + 1) -
          2 * √(X : ℝ) * log X) -
        log 4 * (X / 4 : ℕ)) /
      log X ≤
        (#(primesInQuarterInterval X) : ℝ) := by
  have hlogX : 0 < log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hX))
  rw [div_le_iff₀ hlogX]
  calc
    ((X : ℝ) * log 2 - log (X + 1) -
          2 * √(X : ℝ) * log X) -
        log 4 * (X / 4 : ℕ)
        ≤ Chebyshev.theta X -
            Chebyshev.theta ((X / 4 : ℕ) : ℝ) := by
      have hlo := Chebyshev.theta_ge X
      have hup := Chebyshev.theta_le_log4_mul_x
        (x := ((X / 4 : ℕ) : ℝ)) (by positivity)
      linarith
    _ ≤ (#(primesInQuarterInterval X) : ℝ) * log X :=
      theta_sub_theta_quarter_le_card_mul_log X

/-- A convenient conditional `1/10`-bound.  Its extra hypothesis is exactly
the remaining elementary estimate on the lower-order Chebyshev terms. -/
theorem one_tenth_mul_div_log_le_card_primesInQuarterInterval
    {X : ℕ} (hX : 2 ≤ X)
    (herror :
      log (X + 1 : ℕ) + 2 * √(X : ℝ) * log X ≤
        (log 2 / 2 - (1 / 10 : ℝ)) * X) :
    (1 / 10 : ℝ) * X / log X ≤
      (#(primesInQuarterInterval X) : ℝ) := by
  have hlogX : 0 < log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hX))
  rw [div_le_iff₀ hlogX]
  have hquarter :
      log 4 * ((X / 4 : ℕ) : ℝ) ≤
        log 2 / 2 * X := by
    have hdiv :
        ((X / 4 : ℕ) : ℝ) ≤ (X : ℝ) / 4 :=
      Nat.cast_div_le
    have hlog4 : log (4 : ℝ) = 2 * log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [hlog4]
    have hlog2 : 0 ≤ log (2 : ℝ) := (Real.log_pos one_lt_two).le
    nlinarith [mul_le_mul_of_nonneg_left hdiv hlog2]
  have hexplicit :=
    chebyshev_expression_le_card_primesInQuarterInterval hX
  rw [div_le_iff₀ hlogX] at hexplicit
  calc
    (1 / 10 : ℝ) * X
        ≤ ((X : ℝ) * log 2 - log (X + 1) -
              2 * √(X : ℝ) * log X) -
            log 4 * (X / 4 : ℕ) := by
      simp only [Nat.cast_add, Nat.cast_one] at herror
      ring_nf at herror hquarter ⊢
      linarith
    _ ≤ (#(primesInQuarterInterval X) : ℝ) * log X :=
      hexplicit

private theorem log_add_one_isLittleO_id :
    (fun x : ℝ ↦ log (x + 1)) =o[atTop]
      (fun x : ℝ ↦ x) := by
  have hlog :
      (fun x : ℝ ↦ log (x + 1)) =o[atTop]
        (fun x : ℝ ↦ x + 1) := by
    simpa only [Function.comp_def, id] using
      Real.isLittleO_log_id_atTop.comp_tendsto
        (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id)
  apply hlog.trans_isBigO
  apply IsBigO.of_bound 2
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith),
    Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  linarith

private theorem sqrt_mul_log_isLittleO_id :
    (fun x : ℝ ↦ √x * log x) =o[atTop]
      (fun x : ℝ ↦ x) := by
  have hlog :
      log =o[atTop] (fun x : ℝ ↦ √x) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop
        (r := (1 / 2 : ℝ)) (by norm_num))
  have hmul :=
    (isBigO_refl (fun x : ℝ ↦ √x) atTop).mul_isLittleO hlog
  refine hmul.congr' EventuallyEq.rfl ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  exact Real.mul_self_sqrt hx

private theorem quarter_interval_chebyshev_error_isLittleO :
    (fun X : ℕ ↦
      log (X + 1 : ℕ) + 2 * √(X : ℝ) * log X) =o[atTop]
        (fun X : ℕ ↦ (X : ℝ)) := by
  have hlog := log_add_one_isLittleO_id.natCast_atTop
  have hsqrtlog := sqrt_mul_log_isLittleO_id.natCast_atTop
  simpa only [Nat.cast_add, Nat.cast_one, mul_assoc] using
    hlog.add (hsqrtlog.const_mul_left 2)

theorem log_two_div_four_pos : 0 < log (2 : ℝ) / 4 :=
  div_pos (Real.log_pos one_lt_two) (by norm_num)

private theorem eventually_quarter_interval_chebyshev_error :
    ∀ᶠ X : ℕ in atTop,
      log (X + 1 : ℕ) + 2 * √(X : ℝ) * log X ≤
        log 2 / 4 * X := by
  have hbound :=
    quarter_interval_chebyshev_error_isLittleO.bound log_two_div_four_pos
  filter_upwards [hbound, eventually_ge_atTop 1] with X hbound hX
  have hlogSucc : 0 ≤ log ((X + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X + 1 by omega))
  have hlogX : 0 ≤ log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hX)
  have herrorNonneg :
      0 ≤ log ((X + 1 : ℕ) : ℝ) +
        2 * √(X : ℝ) * log X := by positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg herrorNonneg,
    abs_of_nonneg (show (0 : ℝ) ≤ (X : ℝ) by positivity)] using hbound

/-- Quantitative Chebyshev lower bound for all sufficiently large natural
`X`.  The explicit constant `log 2 / 4` is positive. -/
theorem eventually_log_two_div_four_mul_div_log_le_card :
    ∀ᶠ X : ℕ in atTop,
      log 2 / 4 * X / log X ≤
        (#(primesInQuarterInterval X) : ℝ) := by
  filter_upwards [eventually_ge_atTop 2,
    eventually_quarter_interval_chebyshev_error] with X hX herror
  have hlogX : 0 < log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hX))
  rw [div_le_iff₀ hlogX]
  have hquarter :
      log 4 * ((X / 4 : ℕ) : ℝ) ≤
        log 2 / 2 * X := by
    have hdiv :
        ((X / 4 : ℕ) : ℝ) ≤ (X : ℝ) / 4 :=
      Nat.cast_div_le
    have hlog4 : log (4 : ℝ) = 2 * log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [hlog4]
    have hlog2 : 0 ≤ log (2 : ℝ) := (Real.log_pos one_lt_two).le
    nlinarith [mul_le_mul_of_nonneg_left hdiv hlog2]
  have hexplicit :=
    chebyshev_expression_le_card_primesInQuarterInterval hX
  rw [div_le_iff₀ hlogX] at hexplicit
  calc
    log 2 / 4 * X
        ≤ ((X : ℝ) * log 2 - log (X + 1) -
              2 * √(X : ℝ) * log X) -
            log 4 * (X / 4 : ℕ) := by
      simp only [Nat.cast_add, Nat.cast_one] at herror
      ring_nf at herror hquarter ⊢
      linarith
    _ ≤ (#(primesInQuarterInterval X) : ℝ) * log X :=
      hexplicit

end Wikipedia.SzemeredisTheorem
