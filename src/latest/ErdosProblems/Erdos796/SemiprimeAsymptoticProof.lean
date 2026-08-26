import ErdosProblems.Erdos796.SemiprimeSummatory
import ErdosProblems.Erdos796.MeisselMertensProof
import ErdosProblems.Erdos796.PrimeHarmonicSqrt
import ErdosProblems.Erdos796.PrimeLogCorrection
import ErdosProblems.Erdos796.SemiprimeBoundaryError
import ErdosProblems.Erdos796.External.PNTBigO

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The second-order semiprime asymptotic

This file derives the semiprime asymptotic from the quantitative prime number
theorem in `PrimeNumberTheoremAnd`.  The quantitative estimate is needed to
sum the prime-counting error uniformly over all primes up to `sqrt n`.
-/

namespace Erdos796

open Filter Topology Asymptotics MeasureTheory intervalIntegral
open scoped BigOperators Nat.Prime

/-- A logarithmic-rate form of the PNT for Chebyshev's theta function. -/
theorem theta_sub_id_isBigO_log_sq :
    (Chebyshev.theta - id) =O[atTop]
      (fun x : ℝ => x / Real.log x ^ 2) :=
  External.pntBigO

/-- Quantitative PNT in the exact real-variable form needed below. -/
theorem primeCounting_sub_main_isBigO :
    (fun x : ℝ =>
      (Nat.primeCounting ⌊x⌋₊ : ℝ) - x / Real.log x) =O[atTop]
      (fun x : ℝ => x / Real.log x ^ 2) := by
  have hinvLog :
      (fun x : ℝ => (Real.log x)⁻¹) =O[atTop]
        (fun _x : ℝ => (1 : ℝ)) := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
    have hxpos : 0 < x := (Real.exp_pos 1).trans_le hx
    have hlog : 1 ≤ Real.log x := by
      exact (Real.le_log_iff_exp_le hxpos).2 hx
    have hlog0 : 0 ≤ Real.log x := by linarith
    simp only [Real.norm_eq_abs, norm_one, mul_one, abs_inv]
    rw [abs_of_nonneg hlog0]
    exact (inv_le_one₀ (by linarith)).2 hlog
  have hfirst :
      (fun x : ℝ =>
        (Chebyshev.theta x - x) / Real.log x) =O[atTop]
        (fun x : ℝ => x / Real.log x ^ 2) := by
    have hmul := theta_sub_id_isBigO_log_sq.mul hinvLog
    apply hmul.congr'
    · filter_upwards with x
      simp only [Pi.sub_apply, id_eq]
      rw [div_eq_mul_inv]
    · filter_upwards with x
      simp only [mul_one]
  have hsum := hfirst.add Chebyshev.integral_theta_div_log_sq_isBigO
  apply hsum.congr'
  · filter_upwards [eventually_ge_atTop 2] with x hx
    rw [Chebyshev.primeCounting_eq_theta_div_log_add_integral hx]
    ring
  · exact Eventually.of_forall fun _ => rfl

/-- The accumulated error made by replacing each `pi(n / p)` by its
logarithmic main term.  The latter is evaluated at the real quotient; the
natural floor of that quotient is exactly `n / p`. -/
noncomputable def semiprimePNTError (n : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE n.sqrt,
    ((Nat.primeCounting (n / p) : ℝ) -
      ((n : ℝ) / (p : ℝ)) /
        Real.log ((n : ℝ) / (p : ℝ)))

theorem floor_natCast_div_natCast (n p : ℕ) :
    ⌊(n : ℝ) / (p : ℝ)⌋₊ = n / p := by
  rw [Nat.floor_div_natCast, Nat.floor_natCast]

/-- The quantitative PNT error summed over all primes up to `sqrt n`. -/
theorem semiprimePNTError_eventually_le :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      |semiprimePNTError n| ≤
        C * (n : ℝ) * primeHarmonic n.sqrt /
          Real.log (n.sqrt : ℝ) ^ 2 := by
  obtain ⟨C, hCpos, hC⟩ :=
    (isBigO_iff').mp primeCounting_sub_main_isBigO
  rcases Filter.eventually_atTop.mp hC with ⟨X, hX⟩
  refine ⟨C, hCpos, ?_⟩
  have hsqrtTop : Tendsto (fun n : ℕ => (n.sqrt : ℝ)) atTop atTop :=
    tendsto_natSqrtCast_atTop
  filter_upwards [hsqrtTop.eventually (Ici_mem_atTop (max X 3))] with n hn
  have hsqrtThree : (3 : ℝ) ≤ (n.sqrt : ℝ) := hn.trans' (le_max_right X 3)
  have hlogS : 0 < Real.log (n.sqrt : ℝ) :=
    Real.log_pos (by linarith)
  have hterm : ∀ p ∈ Nat.primesLE n.sqrt,
      |(Nat.primeCounting (n / p) : ℝ) -
          ((n : ℝ) / (p : ℝ)) /
            Real.log ((n : ℝ) / (p : ℝ))| ≤
        C * ((n : ℝ) / (p : ℝ)) /
          Real.log (n.sqrt : ℝ) ^ 2 := by
    intro p hp
    have hp' := Nat.mem_primesLE.mp hp
    have hpPos : 0 < p := hp'.2.pos
    have hpCastPos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpPos
    have hsquare : n.sqrt * p ≤ n := by
      exact (Nat.mul_le_mul_left n.sqrt hp'.1).trans (Nat.sqrt_le n)
    have hquot : (n.sqrt : ℝ) ≤ (n : ℝ) / (p : ℝ) := by
      rw [le_div_iff₀ hpCastPos]
      exact_mod_cast hsquare
    have hquotX : X ≤ (n : ℝ) / (p : ℝ) :=
      (le_max_left X 3).trans hn |>.trans hquot
    have hraw := hX _ hquotX
    rw [floor_natCast_div_natCast] at hraw
    have hlogQ : Real.log (n.sqrt : ℝ) ≤
        Real.log ((n : ℝ) / (p : ℝ)) :=
      Real.log_le_log (by positivity) hquot
    have hquotNonneg : 0 ≤ (n : ℝ) / (p : ℝ) := by positivity
    have hmainNonneg : 0 ≤
        ((n : ℝ) / (p : ℝ)) /
          Real.log ((n : ℝ) / (p : ℝ)) ^ 2 := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hmainNonneg] at hraw
    calc
      |(Nat.primeCounting (n / p) : ℝ) -
          ((n : ℝ) / (p : ℝ)) /
            Real.log ((n : ℝ) / (p : ℝ))| ≤
          C * (((n : ℝ) / (p : ℝ)) /
            Real.log ((n : ℝ) / (p : ℝ)) ^ 2) := hraw
      _ ≤ C * ((n : ℝ) / (p : ℝ)) /
          Real.log (n.sqrt : ℝ) ^ 2 := by
        have hsq : Real.log (n.sqrt : ℝ) ^ 2 ≤
            Real.log ((n : ℝ) / (p : ℝ)) ^ 2 := by nlinarith
        rw [mul_div_assoc]
        gcongr
  calc
    |semiprimePNTError n| ≤
        ∑ p ∈ Nat.primesLE n.sqrt,
          |(Nat.primeCounting (n / p) : ℝ) -
            ((n : ℝ) / (p : ℝ)) /
              Real.log ((n : ℝ) / (p : ℝ))| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ Nat.primesLE n.sqrt,
        C * ((n : ℝ) / (p : ℝ)) /
          Real.log (n.sqrt : ℝ) ^ 2 := by
      exact Finset.sum_le_sum hterm
    _ = C * (n : ℝ) * primeHarmonic n.sqrt /
          Real.log (n.sqrt : ℝ) ^ 2 := by
      unfold primeHarmonic
      simp_rw [div_eq_mul_inv]
      rw [show
        C * (n : ℝ) * (∑ p ∈ Nat.primesLE n.sqrt, (p : ℝ)⁻¹) *
            (Real.log (n.sqrt : ℝ) ^ 2)⁻¹ =
          (C * (n : ℝ) * (Real.log (n.sqrt : ℝ) ^ 2)⁻¹) *
            (∑ p ∈ Nat.primesLE n.sqrt, (p : ℝ)⁻¹) by ring,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring

/-- The accumulated quantitative PNT error is negligible on the
`n / log n` scale. -/
theorem semiprimePNTError_negligible :
    Tendsto
      (fun n : ℕ => semiprimePNTError n / secondOrderScale n)
      atTop (nhds 0) := by
  obtain ⟨C, hCpos, hbound⟩ := semiprimePNTError_eventually_le
  have hupper : Tendsto
      (fun n : ℕ =>
        (3 * C) *
          (primeHarmonic n.sqrt / Real.log (n.sqrt : ℝ)))
      atTop (nhds 0) := by
    simpa using!
      primeHarmonic_sqrt_div_log_sqrt_tendsto_zero.const_mul (3 * C)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (g := fun n : ℕ =>
    (3 * C) *
      (primeHarmonic n.sqrt / Real.log (n.sqrt : ℝ)))
  · filter_upwards with n
    positivity
  · filter_upwards [hbound, eventually_ge_atTop 9,
      eventually_log_le_three_log_sqrt] with n hb hn hlog
    have hnPos : (0 : ℝ) < (n : ℝ) := by positivity
    have hlogN : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hsqrt : 3 ≤ n.sqrt := by
      rw [Nat.le_sqrt]
      omega
    have hlogS : 0 < Real.log (n.sqrt : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n.sqrt by omega))
    have hH : 0 ≤ primeHarmonic n.sqrt := by
      unfold primeHarmonic
      positivity
    rw [Real.norm_eq_abs]
    calc
      |semiprimePNTError n / secondOrderScale n| =
          |semiprimePNTError n| / secondOrderScale n := by
        have hscale : 0 < secondOrderScale n := by
          unfold secondOrderScale
          positivity
        rw [abs_div, abs_of_pos hscale]
      _ ≤
          (C * (n : ℝ) * primeHarmonic n.sqrt /
            Real.log (n.sqrt : ℝ) ^ 2) /
            secondOrderScale n := by
        apply div_le_div_of_nonneg_right hb
        unfold secondOrderScale
        positivity
      _ = C * primeHarmonic n.sqrt * Real.log (n : ℝ) /
          Real.log (n.sqrt : ℝ) ^ 2 := by
        unfold secondOrderScale
        field_simp
      _ ≤ 3 * C * primeHarmonic n.sqrt /
          Real.log (n.sqrt : ℝ) := by
        rw [div_le_div_iff₀ (sq_pos_of_pos hlogS) hlogS]
        have hfac : 0 ≤
            C * primeHarmonic n.sqrt * Real.log (n.sqrt : ℝ) := by
          positivity
        calc
          C * primeHarmonic n.sqrt * Real.log (n : ℝ) *
                Real.log (n.sqrt : ℝ) =
              (C * primeHarmonic n.sqrt * Real.log (n.sqrt : ℝ)) *
                Real.log (n : ℝ) := by ring
          _ ≤ (C * primeHarmonic n.sqrt * Real.log (n.sqrt : ℝ)) *
                (3 * Real.log (n.sqrt : ℝ)) :=
            mul_le_mul_of_nonneg_left hlog hfac
          _ = 3 * C * primeHarmonic n.sqrt *
                Real.log (n.sqrt : ℝ) ^ 2 := by ring
      _ = (3 * C) *
          (primeHarmonic n.sqrt / Real.log (n.sqrt : ℝ)) := by ring
  · exact hupper

/-- Exact normalized decomposition of the unrestricted quotient sum into
the analytic main sum and the accumulated PNT error. -/
theorem eventually_normalized_primeQuotientSum_eq_main_add_error :
    ∀ᶠ n : ℕ in atTop,
      (primeQuotientSum n : ℝ) / secondOrderScale n =
        primeQuotientMainSum n +
          semiprimePNTError n / secondOrderScale n := by
  filter_upwards [eventually_ge_atTop 4] with n hn
  have hnPos : 0 < n := by omega
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hlogN : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).ne'
  rw [primeQuotientSum, Nat.cast_sum]
  unfold primeQuotientMainSum semiprimePNTError
  rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := Nat.mem_primesLE.mp hp
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp'.2.ne_zero
  have hpn : p < n := hp'.1.trans_lt (Nat.sqrt_lt_self (by omega))
  have hloglt : Real.log (p : ℝ) < Real.log (n : ℝ) :=
    Real.strictMonoOn_log
      (show (p : ℝ) ∈ Set.Ioi 0 by
        simp only [Set.mem_Ioi]
        exact_mod_cast hp'.2.pos)
      (show (n : ℝ) ∈ Set.Ioi 0 by
        simp only [Set.mem_Ioi]
        exact_mod_cast hnPos)
      (by exact_mod_cast hpn)
  have hlogQ : Real.log ((n : ℝ) / (p : ℝ)) ≠ 0 := by
    rw [Real.log_div hn0 hp0]
    linarith
  unfold secondOrderScale
  field_simp
  ring

/-- The unrestricted quotient sum has the same second-order constant as its
normalized PNT main sum. -/
theorem normalized_primeQuotientSum_sub_loglog_tendsto :
    Tendsto
      (fun n : ℕ =>
        (primeQuotientSum n : ℝ) / secondOrderScale n -
          Real.log (Real.log (n : ℝ)))
      atTop (nhds Mertens.M) := by
  have hsum := primeQuotientMainSum_sub_loglog_tendsto.add
    semiprimePNTError_negligible
  have heq : ∀ᶠ n : ℕ in atTop,
      (primeQuotientMainSum n - Real.log (Real.log (n : ℝ))) +
          semiprimePNTError n / secondOrderScale n =
        (primeQuotientSum n : ℝ) / secondOrderScale n -
          Real.log (Real.log (n : ℝ)) := by
    filter_upwards [eventually_normalized_primeQuotientSum_eq_main_add_error]
      with n hn
    rw [hn]
    ring
  simpa only [add_zero] using! hsum.congr' heq

/-- The complete unconditional second-order semiprime asymptotic. -/
theorem semiprimeAsymptotic : SemiprimeAsymptotic Mertens.M := by
  have h := normalized_primeQuotientSum_sub_loglog_tendsto.sub
    normalized_primeQuotientSum_sub_semiprime_tendsto_zero
  rw [SemiprimeAsymptotic]
  have heq :
      (fun n : ℕ =>
        (primeQuotientSum n : ℝ) / secondOrderScale n -
            Real.log (Real.log (n : ℝ)) -
          ((primeQuotientSum n : ℝ) - (semiprimeCount n : ℝ)) /
            secondOrderScale n) =ᶠ[atTop]
      (fun n : ℕ =>
        ((semiprimeCount n : ℝ) - leadingTerm n) /
          secondOrderScale n) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hlogN : Real.log (n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).ne'
    unfold leadingTerm secondOrderScale
    field_simp
    ring
  have ht := h.congr' heq
  simpa only [sub_zero] using! ht

end Erdos796
