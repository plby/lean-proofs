import ErdosProblems.Erdos49.PNT.MediumPNT
import ErdosProblems.Erdos49.PNT.IEANTN.Mertens

/-!
# Quantitative prime-number input for Erdős Problem 49

Tao's proof only needs an error which beats every fixed power of
`exp (log (log x) ^ 3)`.  The medium-strength prime number theorem is more
than sufficient: it gives an error `x * exp (-c * log(x)^(1/10))` for
Chebyshev's second function.  This file puts that theorem into a pointwise,
nonnegative form convenient for the interval-counting argument.
-/

open Filter Set
open scoped BigOperators

namespace Erdos49.Analytic

/-- A pointwise, nonnegative version of the medium-strength prime
number theorem. -/
theorem exists_mediumPsi_error :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
      |Chebyshev.psi x - x| ≤
        C * (x * Real.exp
          (-c * Real.log x ^ ((1 : ℝ) / 10))) := by
  obtain ⟨c, hc, hO⟩ := MediumPNT
  obtain ⟨C, hC⟩ := hO.bound
  refine ⟨c, |C|, hc, abs_nonneg C, ?_⟩
  filter_upwards [hC, eventually_ge_atTop 0] with x hxO hx
  rw [Real.norm_eq_abs, Real.norm_of_nonneg] at hxO
  · exact hxO.trans
      (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  · positivity

/-- Every fixed power of `log x` is dominated by the exponential decay in
`MediumPNT`. -/
lemma tendsto_log_pow_mul_mediumDecay (c : ℝ) (hc : 0 < c) (k : ℕ) :
    Tendsto (fun x : ℝ ↦ Real.log x ^ k *
      Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) atTop (nhds 0) := by
  have ht : Tendsto (fun x : ℝ ↦ Real.log x ^ ((1 : ℝ) / 10))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 10)).comp
      Real.tendsto_log_atTop
  have hdecay :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      ((10 * k : ℕ) : ℝ) c hc).comp ht
  apply hdecay.congr'
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  change (Real.log x ^ ((1 : ℝ) / 10)) ^ ((10 * k : ℕ) : ℝ) *
      Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)) =
    Real.log x ^ k * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hlog]
  congr 1
  push_cast
  ring

/-- The medium PNT error is eventually smaller than `δ x / log(x)^k`, for
every fixed logarithmic power and positive `δ`. -/
theorem eventually_mediumPsi_error_div_log_pow (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) : ∀ᶠ x : ℝ in atTop,
      |Chebyshev.psi x - x| ≤ δ * x / Real.log x ^ k := by
  obtain ⟨c, C, hc, hC, hpsi⟩ := exists_mediumPsi_error
  have hlim := (tendsto_log_pow_mul_mediumDecay c hc k).const_mul C
  have hlim' : Tendsto (fun x : ℝ ↦ C * (Real.log x ^ k *
      Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)))) atTop (nhds 0) := by
    simpa using hlim
  have hsmall : ∀ᶠ x : ℝ in atTop,
      C * (Real.log x ^ k *
        Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) < δ :=
    (Filter.Eventually.and
      (NormedAddGroup.tendsto_nhds_zero.mp hlim' δ hδ)
      (eventually_ge_atTop 1)).mono fun x hx ↦ by
      rw [Real.norm_of_nonneg] at hx
      · exact hx.1
      · exact mul_nonneg hC (mul_nonneg (pow_nonneg (Real.log_nonneg hx.2) k)
          (Real.exp_pos _).le)
  filter_upwards [hpsi, hsmall, eventually_gt_atTop 1] with x hxpsi hxsmall hx
  have hx0 : 0 ≤ x := (by norm_num : (0 : ℝ) ≤ 1).trans hx.le
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hlogpow : 0 < Real.log x ^ k := pow_pos hlog k
  apply hxpsi.trans
  apply (le_div_iff₀ hlogpow).2
  calc
    C * (x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) *
        Real.log x ^ k =
        x * (C * (Real.log x ^ k *
          Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)))) := by ring
    _ ≤ x * δ := mul_le_mul_of_nonneg_left hxsmall.le hx0
    _ = δ * x := by ring

/-- A fixed logarithmic power divided by `sqrt x` tends to zero. -/
lemma tendsto_log_pow_div_sqrt (k : ℕ) :
    Tendsto (fun x : ℝ ↦ Real.log x ^ k / Real.sqrt x) atTop (nhds 0) := by
  have h := Real.tendsto_pow_log_div_pow_atTop
    ((1 : ℝ) / 2) (k : ℝ) (by norm_num)
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with x hx
  rw [Real.rpow_natCast, ← Real.sqrt_eq_rpow]

/-- Prime powers contribute less than `δ x / log(x)^k` to `ψ-θ`
eventually. -/
theorem eventually_psi_sub_theta_div_log_pow (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) : ∀ᶠ x : ℝ in atTop,
      Chebyshev.psi x - Chebyshev.theta x ≤
        δ * x / Real.log x ^ k := by
  have hlim := (tendsto_log_pow_div_sqrt (k + 1)).const_mul 2
  have hlim' : Tendsto (fun x : ℝ ↦
      2 * (Real.log x ^ (k + 1) / Real.sqrt x)) atTop (nhds 0) := by
    simpa using hlim
  have hsmall : ∀ᶠ x : ℝ in atTop,
      2 * (Real.log x ^ (k + 1) / Real.sqrt x) < δ := by
    have hnorm := NormedAddGroup.tendsto_nhds_zero.mp hlim' δ hδ
    filter_upwards [hnorm, eventually_gt_atTop 1] with x hxnorm hx
    rw [Real.norm_of_nonneg] at hxnorm
    · exact hxnorm
    · exact mul_nonneg (by norm_num) (div_nonneg
        (pow_nonneg (Real.log_nonneg hx.le) (k + 1)) (Real.sqrt_nonneg x))
  filter_upwards [hsmall, eventually_gt_atTop 1] with x hxsmall hx
  have hx0 : 0 ≤ x := (by norm_num : (0 : ℝ) ≤ 1).trans hx.le
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hlogpow : 0 < Real.log x ^ k := pow_pos hlog k
  have hsqrt : 0 < Real.sqrt x := Real.sqrt_pos.2 (by positivity)
  apply (Chebyshev.psi_sub_theta_le hx.le).trans
  apply (le_div_iff₀ hlogpow).2
  have hsmall' : 2 * Real.log x ^ (k + 1) < δ * Real.sqrt x := by
    rw [← mul_div_assoc] at hxsmall
    exact (div_lt_iff₀ hsqrt).mp hxsmall
  have hmul := mul_le_mul_of_nonneg_left hsmall'.le (Real.sqrt_nonneg x)
  calc
    2 * Real.sqrt x * Real.log x * Real.log x ^ k =
        Real.sqrt x * (2 * Real.log x ^ (k + 1)) := by
      rw [pow_succ]
      ring
    _ ≤ Real.sqrt x * (δ * Real.sqrt x) := hmul
    _ = δ * Real.sqrt x ^ 2 := by ring
    _ = δ * x := by rw [Real.sq_sqrt hx0]

/-- Quantitative theta form of `MediumPNT`, at every fixed logarithmic
power. -/
theorem eventually_mediumTheta_error_div_log_pow (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) : ∀ᶠ x : ℝ in atTop,
      |Chebyshev.theta x - x| ≤ δ * x / Real.log x ^ k := by
  have hhalf : 0 < δ / 2 := by positivity
  have hpsi := eventually_mediumPsi_error_div_log_pow k hhalf
  have hcorr := eventually_psi_sub_theta_div_log_pow k hhalf
  filter_upwards [hpsi, hcorr, eventually_gt_atTop 1] with x hpsi hcorr hx
  have hx0 : 0 ≤ x := (by norm_num : (0 : ℝ) ≤ 1).trans hx.le
  have hlog0 : 0 ≤ Real.log x := (Real.log_pos hx).le
  have hscale : 0 ≤ (δ / 2) * x / Real.log x ^ k :=
    div_nonneg (mul_nonneg hhalf.le hx0) (pow_nonneg hlog0 k)
  have hdouble : δ * x / Real.log x ^ k =
      2 * ((δ / 2) * x / Real.log x ^ k) := by ring
  rw [abs_le]
  constructor
  · have hleft := (abs_le.mp hpsi).1
    rw [hdouble]
    linarith
  · have hright := (abs_le.mp hpsi).2
    have hthetaPsi := Chebyshev.theta_le_psi x
    rw [hdouble]
    linarith

/-- The exact set of primes in a closed natural interval. -/
def primeInterval (u v : ℕ) : Finset ℕ :=
  (Finset.Icc u v).filter Nat.Prime

/-- The sum defining a theta difference is bounded below by the number of
interval primes times the logarithm of the lower endpoint. -/
lemma primeInterval_card_mul_log_le_theta_sub {u v : ℕ}
    (hu : 1 ≤ u) (huv : u ≤ v) :
    ((primeInterval u v).card : ℝ) * Real.log u ≤
      Chebyshev.theta v - Chebyshev.theta ((u - 1 : ℕ) : ℝ) := by
  have hsub : Nat.primesLE (u - 1) ⊆ Nat.primesLE v :=
    Nat.primesLE_mono ((Nat.sub_le u 1).trans huv)
  have hsum :
      ∑ p ∈ Nat.primesLE v \ Nat.primesLE (u - 1), Real.log p =
        Chebyshev.theta v - Chebyshev.theta ((u - 1 : ℕ) : ℝ) := by
    have hadd := Finset.sum_sdiff (f := fun p : ℕ ↦ Real.log p) hsub
    rw [← Chebyshev.theta_eq_sum_primesLE_log,
      ← Chebyshev.theta_eq_sum_primesLE_log] at hadd
    linarith
  rw [← hsum]
  have hset : primeInterval u v =
      Nat.primesLE v \ Nat.primesLE (u - 1) := by
    ext p
    simp only [primeInterval, Finset.mem_filter, Finset.mem_Icc,
      Finset.mem_sdiff, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hpu, hpv⟩, hp⟩
      exact ⟨⟨hpv, hp⟩, fun h ↦ by omega⟩
    · rintro ⟨⟨hpv, hp⟩, hnot⟩
      refine ⟨⟨?_, hpv⟩, hp⟩
      by_contra h
      exact hnot ⟨by omega, hp⟩
  rw [hset]
  calc
    ((Nat.primesLE v \ Nat.primesLE (u - 1)).card : ℝ) * Real.log u =
        ∑ _p ∈ Nat.primesLE v \ Nat.primesLE (u - 1), Real.log u := by
          simp
    _ ≤ ∑ p ∈ Nat.primesLE v \ Nat.primesLE (u - 1), Real.log p := by
      apply Finset.sum_le_sum
      intro p hp
      apply Real.log_le_log
      · exact_mod_cast (Nat.zero_lt_of_lt hu)
      · have hpLE := (Finset.mem_sdiff.mp hp).1
        have hpnot := (Finset.mem_sdiff.mp hp).2
        have hpPrime := Nat.prime_of_mem_primesLE hpLE
        have hlt : u - 1 < p := by
          by_contra h
          exact hpnot (Nat.mem_primesLE.mpr ⟨by omega, hpPrime⟩)
        exact_mod_cast (by omega : u ≤ p)

/-- A pointwise interval-prime upper bound obtained from two theta errors. -/
lemma primeInterval_card_real_upper {u v : ℕ} {Eu Ev : ℝ}
    (hu : 1 < u) (huv : u ≤ v)
    (hEu : |Chebyshev.theta ((u - 1 : ℕ) : ℝ) - (u - 1 : ℕ)| ≤ Eu)
    (hEv : |Chebyshev.theta v - v| ≤ Ev) :
    ((primeInterval u v).card : ℝ) ≤
      ((v : ℝ) - (u - 1 : ℕ) + Eu + Ev) / Real.log u := by
  have hlog : 0 < Real.log (u : ℝ) := Real.log_pos (by exact_mod_cast hu)
  apply (le_div_iff₀ hlog).2
  apply (primeInterval_card_mul_log_le_theta_sub hu.le huv).trans
  have hEu' := (abs_le.mp hEu).1
  have hEv' := (abs_le.mp hEv).2
  linarith

#print axioms exists_mediumPsi_error
#print axioms Mertens.sum_prime_div_eq_log_log

end Erdos49.Analytic
