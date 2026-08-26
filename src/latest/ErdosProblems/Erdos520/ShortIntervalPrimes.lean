import ErdosProblems.Erdos520.ThinScheduleChebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory Set
open scoped BigOperators Nat.Prime Interval Topology

namespace Erdos
namespace Problem520

/-!
# Reciprocal primes in very short multiplicative intervals

Caich's smoothing argument needs an estimate of the shape

`sum_{t / (1 + 1 / X) < p <= t} 1 / p << 1 / (X * log y)`.

Here `X` is a power of `log y`, so the interval has relative length about
`1 / X`.  Mathlib currently has Chebyshev's global upper bound for the prime
counting function, but no Brun--Titchmarsh theorem and no effective prime
number theorem.  A global `O(x / log x)` bound cannot be subtracted at two
nearby endpoints.  Likewise, a qualitative `pi(x) ~ x / log x` leaves an
endpoint error which need not be smaller than `x / (X log x)` when `X` tends
to infinity.

Mathlib also has `Nat.primeCounting'_add_le`, a one-modulus residue-class
bound of size `phi(q) * (h / q + 1)`.  Making `phi(q) / q` as small as
`1 / log h` requires a modulus whose additive `phi(q)` error is too large.
Removing that error is precisely the missing Brun-sieve content, so this
lemma does not supply the required estimate either.

This file formalizes every remaining elementary step from the classical
de la Vallee Poussin error term for the prime number theorem.  No instance of
that deep input is asserted: `EffectivePrimeCountingError` is a proposition,
not an axiom.  The final theorem shows exactly that this is the sole missing
number-theoretic input for the reciprocal-prime estimate.
-/

/-! ## The effective prime-number-theorem interface -/

/-- The logarithmic integral, normalized to vanish at `2`.  Its additive
normalization is immaterial because only differences occur below. -/
noncomputable def logarithmicIntegralFromTwo (x : ℝ) : ℝ :=
  ∫ u in (2 : ℝ)..x, 1 / Real.log u

/-- The standard de la Vallee Poussin strength of the prime number theorem,
at natural endpoints:

`|pi(n) - Li(n)| <= C n exp (-c sqrt(log n))`.

The constants are kept explicit so that the later absorption calculation is
fully transparent. -/
def EffectivePrimeCountingError (C c : ℝ) (N : ℕ) : Prop :=
  ∀ n : ℕ, N ≤ n →
    |(Nat.primeCounting n : ℝ) -
        logarithmicIntegralFromTwo (n : ℝ)| ≤
      C * (n : ℝ) *
        Real.exp (-c * Real.sqrt (Real.log (n : ℝ)))

/-- The exact analytic theorem missing from the current Mathlib snapshot.
This is a proposition packaging the classical effective PNT, not an axiom or
an unproved theorem declaration. -/
def EffectivePrimeCountingStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, 2 ≤ N ∧
    EffectivePrimeCountingError C c N

private theorem intervalIntegrable_one_div_log
    {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable (fun u : ℝ ↦ 1 / Real.log u) volume a b := by
  refine ContinuousOn.intervalIntegrable fun u hu ↦
    ContinuousAt.continuousWithinAt ?_
  have hu1 : 1 < u := by
    rw [Set.mem_uIcc] at hu
    rcases hu with hu | hu <;> linarith
  exact continuousAt_const.div (Real.continuousAt_log (by positivity))
    (Real.log_ne_zero_of_pos_of_ne_one (by positivity) (by linarith))

/-- The difference of the normalized logarithmic integral is the integral
over the intervening interval. -/
theorem logarithmicIntegralFromTwo_sub
    {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    logarithmicIntegralFromTwo b - logarithmicIntegralFromTwo a =
      ∫ u in a..b, 1 / Real.log u := by
  have h2a := intervalIntegrable_one_div_log
    (by norm_num : (1 : ℝ) < 2) (by linarith : 1 < a)
  have habInt := intervalIntegrable_one_div_log
    (by linarith : 1 < a) (by linarith : 1 < b)
  have hadd := intervalIntegral.integral_add_adjacent_intervals h2a habInt
  unfold logarithmicIntegralFromTwo
  linarith

/-- On `[a,b]`, the logarithmic-integral main term is at most the interval
length divided by `log a`. -/
theorem logarithmicIntegralFromTwo_sub_le
    {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    logarithmicIntegralFromTwo b - logarithmicIntegralFromTwo a ≤
      (b - a) / Real.log a := by
  rw [logarithmicIntegralFromTwo_sub ha hab]
  have hlogA : 0 < Real.log a := Real.log_pos (by linarith)
  have hleft := intervalIntegrable_one_div_log
    (by linarith : 1 < a) (by linarith : 1 < b)
  have hright : IntervalIntegrable
      (fun _ : ℝ ↦ 1 / Real.log a) volume a b :=
    intervalIntegrable_const
  calc
    (∫ u in a..b, 1 / Real.log u) ≤
        ∫ _u in a..b, 1 / Real.log a := by
      apply intervalIntegral.integral_mono_on hab hleft hright
      intro u hu
      have hau : a ≤ u := hu.1
      have hlogU : Real.log a ≤ Real.log u :=
        Real.log_le_log (by positivity) hau
      exact one_div_le_one_div_of_le hlogA hlogU
    _ = (b - a) / Real.log a := by
      rw [intervalIntegral.integral_const]
      simp [div_eq_mul_inv]

/-! ## Finite prime blocks and endpoint subtraction -/

/-- The number of primes in `(a,b]` is the difference of the two prime
counting functions. -/
theorem card_freshPrimes_eq_primeCounting_sub
    {a b : ℕ} (hab : a ≤ b) :
    #(freshPrimes a b) = Nat.primeCounting b - Nat.primeCounting a := by
  have hunion := primesBelow_succ_eq_union_freshPrimes hab
  have hdisj := primesBelow_succ_disjoint_freshPrimes a b
  have hcard := congrArg Finset.card hunion
  rw [Finset.card_union_of_disjoint hdisj] at hcard
  simp only [Nat.primeCounting, Nat.primesBelow_card_eq_primeCounting'] at hcard ⊢
  omega

/-- Every prime in `(a,b]` has reciprocal at most `1/a`. -/
theorem freshReciprocalSum_le_card_div
    {a b : ℕ} (ha : 1 ≤ a) :
    freshReciprocalSum a b ≤ (#(freshPrimes a b) : ℝ) / (a : ℝ) := by
  classical
  rw [freshReciprocalSum]
  calc
    (∑ p ∈ freshPrimes a b, (p : ℝ)⁻¹) ≤
        ∑ _p ∈ freshPrimes a b, ((a : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro p hp
      have hap : a < p := (mem_freshPrimes.mp hp).2.1
      exact (inv_le_inv₀
        (by exact_mod_cast (mem_freshPrimes.mp hp).1.pos : (0 : ℝ) < (p : ℝ))
        (by positivity : (0 : ℝ) < (a : ℝ))).2
          (by exact_mod_cast hap.le : (a : ℝ) ≤ (p : ℝ))
    _ = (#(freshPrimes a b) : ℝ) / (a : ℝ) := by
      simp [div_eq_mul_inv]

/-- Sharp endpoint form of the effective-PNT reduction.  It retains both
PNT errors separately and therefore loses no schedule information. -/
theorem freshReciprocalSum_le_of_effectivePrimeCountingError_exact
    {C c : ℝ} {N a b : ℕ}
    (hPNT : EffectivePrimeCountingError C c N)
    (hNa : N ≤ a) (ha : 2 ≤ a) (hab : a ≤ b) :
    freshReciprocalSum a b ≤
      ((b : ℝ) - (a : ℝ)) / ((a : ℝ) * Real.log (a : ℝ)) +
      C * Real.exp (-c * Real.sqrt (Real.log (a : ℝ))) +
      C * ((b : ℝ) / (a : ℝ)) *
        Real.exp (-c * Real.sqrt (Real.log (b : ℝ))) := by
  have hpiMono : Nat.primeCounting a ≤ Nat.primeCounting b :=
    Nat.monotone_primeCounting hab
  have hcardCast :
      (#(freshPrimes a b) : ℝ) =
        (Nat.primeCounting b : ℝ) - (Nat.primeCounting a : ℝ) := by
    rw [card_freshPrimes_eq_primeCounting_sub hab, Nat.cast_sub hpiMono]
  have hEa := hPNT a hNa
  have hEb := hPNT b (hNa.trans hab)
  have hli :
      logarithmicIntegralFromTwo (b : ℝ) -
          logarithmicIntegralFromTwo (a : ℝ) ≤
        ((b : ℝ) - (a : ℝ)) / Real.log (a : ℝ) :=
    logarithmicIntegralFromTwo_sub_le (by exact_mod_cast ha)
      (by exact_mod_cast hab)
  have hcount :
      (Nat.primeCounting b : ℝ) - (Nat.primeCounting a : ℝ) ≤
        ((b : ℝ) - (a : ℝ)) / Real.log (a : ℝ) +
        C * (a : ℝ) *
          Real.exp (-c * Real.sqrt (Real.log (a : ℝ))) +
        C * (b : ℝ) *
          Real.exp (-c * Real.sqrt (Real.log (b : ℝ))) := by
    have hEaLower := neg_le_of_abs_le hEa
    have hEbUpper := le_of_abs_le hEb
    linarith
  have haR : 0 < (a : ℝ) := by positivity
  calc
    freshReciprocalSum a b ≤
        (#(freshPrimes a b) : ℝ) / (a : ℝ) :=
      freshReciprocalSum_le_card_div (by omega)
    _ = ((Nat.primeCounting b : ℝ) -
          (Nat.primeCounting a : ℝ)) / (a : ℝ) := by rw [hcardCast]
    _ ≤ (((b : ℝ) - (a : ℝ)) / Real.log (a : ℝ) +
          C * (a : ℝ) *
            Real.exp (-c * Real.sqrt (Real.log (a : ℝ))) +
          C * (b : ℝ) *
            Real.exp (-c * Real.sqrt (Real.log (b : ℝ)))) /
          (a : ℝ) :=
      div_le_div_of_nonneg_right hcount haR.le
    _ = _ := by field_simp

/-- If `b <= 2a`, both endpoint errors are controlled by the lower endpoint.
This is the form used for a multiplicative interval of relative width at
most one. -/
theorem freshReciprocalSum_le_of_effectivePrimeCountingError
    {C c : ℝ} {N a b : ℕ}
    (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hPNT : EffectivePrimeCountingError C c N)
    (hNa : N ≤ a) (ha : 2 ≤ a) (hab : a ≤ b)
    (hba : b ≤ 2 * a) :
    freshReciprocalSum a b ≤
      ((b : ℝ) - (a : ℝ)) / ((a : ℝ) * Real.log (a : ℝ)) +
      3 * C * Real.exp (-c * Real.sqrt (Real.log (a : ℝ))) := by
  have haPos : 0 < (a : ℝ) := by positivity
  have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hbaR : (b : ℝ) ≤ 2 * (a : ℝ) := by exact_mod_cast hba
  have hlogMono : Real.log (a : ℝ) ≤ Real.log (b : ℝ) :=
    Real.log_le_log haPos habR
  have hsqrtMono :
      Real.sqrt (Real.log (a : ℝ)) ≤
        Real.sqrt (Real.log (b : ℝ)) :=
    Real.sqrt_le_sqrt hlogMono
  have hexpMono :
      Real.exp (-c * Real.sqrt (Real.log (b : ℝ))) ≤
        Real.exp (-c * Real.sqrt (Real.log (a : ℝ))) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hsqrtMono hc]
  have hratio : (b : ℝ) / (a : ℝ) ≤ 2 := by
    exact (div_le_iff₀ haPos).2 (by nlinarith)
  have herror :
      C * ((b : ℝ) / (a : ℝ)) *
          Real.exp (-c * Real.sqrt (Real.log (b : ℝ))) ≤
        2 * C * Real.exp (-c * Real.sqrt (Real.log (a : ℝ))) := by
    calc
      C * ((b : ℝ) / (a : ℝ)) *
          Real.exp (-c * Real.sqrt (Real.log (b : ℝ))) ≤
          C * 2 * Real.exp (-c * Real.sqrt (Real.log (b : ℝ))) := by
        gcongr
      _ ≤ C * 2 * Real.exp (-c * Real.sqrt (Real.log (a : ℝ))) := by
        gcongr
      _ = 2 * C * Real.exp (-c * Real.sqrt (Real.log (a : ℝ))) := by ring
  calc
    freshReciprocalSum a b ≤
        ((b : ℝ) - (a : ℝ)) / ((a : ℝ) * Real.log (a : ℝ)) +
        C * Real.exp (-c * Real.sqrt (Real.log (a : ℝ))) +
        C * ((b : ℝ) / (a : ℝ)) *
          Real.exp (-c * Real.sqrt (Real.log (b : ℝ))) :=
      freshReciprocalSum_le_of_effectivePrimeCountingError_exact
        hPNT hNa ha hab
    _ ≤ ((b : ℝ) - (a : ℝ)) /
          ((a : ℝ) * Real.log (a : ℝ)) +
        C * Real.exp (-c * Real.sqrt (Real.log (a : ℝ))) +
        2 * C * Real.exp (-c * Real.sqrt (Real.log (a : ℝ))) := by
      gcongr
    _ = _ := by ring

/-! ## Caich's multiplicative interval -/

/-- The effective-PNT error is harmless whenever the exponential on the
right dominates `3 C X log y`. -/
theorem effectivePrimeCountingError_le_reciprocalScale
    {C c : ℝ} {X y a : ℕ}
    (hX : 1 ≤ X) (hy : 2 ≤ y)
    (hdom : 3 * C * (X : ℝ) * Real.log (y : ℝ) ≤
      Real.exp (c * Real.sqrt (Real.log (a : ℝ)))) :
    3 * C * Real.exp (-c * Real.sqrt (Real.log (a : ℝ))) ≤
      1 / ((X : ℝ) * Real.log (y : ℝ)) := by
  have hden : 0 < (X : ℝ) * Real.log (y : ℝ) :=
    mul_pos (by exact_mod_cast (show 0 < X by omega))
      (Real.log_pos (by exact_mod_cast (show 1 < y by omega)))
  apply (le_div_iff₀ hden).2
  calc
    3 * C * Real.exp (-c * Real.sqrt (Real.log (a : ℝ))) *
        ((X : ℝ) * Real.log (y : ℝ)) =
        (3 * C * (X : ℝ) * Real.log (y : ℝ)) *
          Real.exp (-c * Real.sqrt (Real.log (a : ℝ))) := by ring
    _ ≤ Real.exp (c * Real.sqrt (Real.log (a : ℝ))) *
          Real.exp (-c * Real.sqrt (Real.log (a : ℝ))) :=
      mul_le_mul_of_nonneg_right hdom (Real.exp_pos _).le
    _ = 1 := by
      rw [← Real.exp_add, ← Real.exp_zero]
      congr 1
      ring

/-- The exact reciprocal-prime estimate used in Caich's smoothing.  The
natural endpoints satisfy `b-a <= a/X`; `y <= a` records that the interval is
above the current prime cutoff. -/
theorem freshReciprocalSum_le_two_div_X_log_of_effectivePNT
    {C c : ℝ} {N X y a b : ℕ}
    (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hPNT : EffectivePrimeCountingError C c N)
    (hNa : N ≤ a) (ha : 2 ≤ a) (hab : a ≤ b)
    (hX : 1 ≤ X) (hy : 2 ≤ y) (hya : y ≤ a)
    (hwidth : ((b : ℝ) - (a : ℝ)) ≤ (a : ℝ) / (X : ℝ))
    (hdom : 3 * C * (X : ℝ) * Real.log (y : ℝ) ≤
      Real.exp (c * Real.sqrt (Real.log (a : ℝ)))) :
    freshReciprocalSum a b ≤
      2 / ((X : ℝ) * Real.log (y : ℝ)) := by
  have haPos : 0 < (a : ℝ) := by positivity
  have hXR : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hlogY : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogA : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have hlogMono : Real.log (y : ℝ) ≤ Real.log (a : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hya)
  have hbaR : (b : ℝ) ≤ 2 * (a : ℝ) := by
    have hxa : (a : ℝ) / (X : ℝ) ≤ (a : ℝ) := by
      exact (div_le_iff₀ hXR).2 (by
        nlinarith [show (1 : ℝ) ≤ (X : ℝ) by exact_mod_cast hX])
    nlinarith
  have hba : b ≤ 2 * a := by exact_mod_cast hbaR
  have hmain :
      ((b : ℝ) - (a : ℝ)) /
          ((a : ℝ) * Real.log (a : ℝ)) ≤
        1 / ((X : ℝ) * Real.log (y : ℝ)) := by
    calc
      ((b : ℝ) - (a : ℝ)) /
          ((a : ℝ) * Real.log (a : ℝ)) ≤
          ((a : ℝ) / (X : ℝ)) /
            ((a : ℝ) * Real.log (a : ℝ)) := by
        gcongr
      _ = 1 / ((X : ℝ) * Real.log (a : ℝ)) := by field_simp
      _ ≤ 1 / ((X : ℝ) * Real.log (y : ℝ)) := by
        exact one_div_le_one_div_of_le (mul_pos hXR hlogY)
          (mul_le_mul_of_nonneg_left hlogMono hXR.le)
  have herr := effectivePrimeCountingError_le_reciprocalScale
    hX hy hdom
  calc
    freshReciprocalSum a b ≤
        ((b : ℝ) - (a : ℝ)) /
            ((a : ℝ) * Real.log (a : ℝ)) +
          3 * C * Real.exp (-c * Real.sqrt (Real.log (a : ℝ))) :=
      freshReciprocalSum_le_of_effectivePrimeCountingError
        hC hc hPNT hNa ha hab hba
    _ ≤ 1 / ((X : ℝ) * Real.log (y : ℝ)) +
          1 / ((X : ℝ) * Real.log (y : ℝ)) := add_le_add hmain herr
    _ = 2 / ((X : ℝ) * Real.log (y : ℝ)) := by ring

/-! ## Polylogarithmic smoothing parameters -/

/-- Exponential PNT decay eventually beats any fixed power of `log y` after
the substitution `u = sqrt(log y)`.  This is the schedule fact behind
Caich's choice `log X = O(log log y)`. -/
theorem eventually_polylog_le_exp_sqrt_log
    {D c : ℝ} (hD : 0 ≤ D) (hc : 0 < c) (A : ℕ) :
    ∀ᶠ y : ℕ in atTop,
      D * Real.log (y : ℝ) ^ (A + 1) ≤
        Real.exp (c * Real.sqrt (Real.log (y : ℝ))) := by
  by_cases hDz : D = 0
  · filter_upwards with y
    simp [hDz, (Real.exp_pos _).le]
  have hDpos : 0 < D := lt_of_le_of_ne hD (Ne.symm hDz)
  have hsmall :=
    (isLittleO_pow_exp_pos_mul_atTop (2 * (A + 1)) hc).bound
      (show 0 < 1 / D by positivity)
  have htend : Tendsto
      (fun y : ℕ ↦ Real.sqrt (Real.log (y : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hcomp := htend.eventually hsmall
  filter_upwards [hcomp, eventually_gt_atTop (1 : ℕ)] with y hbound hy
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast hy)
  have hsqrt : 0 ≤ Real.sqrt (Real.log (y : ℝ)) := Real.sqrt_nonneg _
  have hsqrtSq : Real.sqrt (Real.log (y : ℝ)) ^ 2 =
      Real.log (y : ℝ) := Real.sq_sqrt hlog.le
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hsqrt _),
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hbound
  have hpow :
      Real.sqrt (Real.log (y : ℝ)) ^ (2 * (A + 1)) =
        Real.log (y : ℝ) ^ (A + 1) := by
    rw [pow_mul, hsqrtSq]
  rw [hpow] at hbound
  have := mul_le_mul_of_nonneg_left hbound hD
  convert! this using 1
  all_goals field_simp

/-- Concrete Caich-regime absorption: if `X <= (log y)^A`, then the effective
PNT error is eventually at most the main reciprocal scale, uniformly for all
`a >= y`. -/
theorem eventually_effectivePNT_error_dominated_polylog
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (A : ℕ) :
    ∀ᶠ y : ℕ in atTop, ∀ {X a : ℕ},
      1 ≤ X → y ≤ a →
      (X : ℝ) ≤ Real.log (y : ℝ) ^ A →
      3 * C * (X : ℝ) * Real.log (y : ℝ) ≤
        Real.exp (c * Real.sqrt (Real.log (a : ℝ))) := by
  have hev := eventually_polylog_le_exp_sqrt_log
    (D := 3 * C) (by positivity) hc A
  filter_upwards [hev, eventually_ge_atTop (2 : ℕ)] with y hpoly hy X a hX hya hXpoly
  have hlogNonneg : 0 ≤ Real.log (y : ℝ) :=
    (Real.log_pos (by exact_mod_cast (show 1 < y by omega))).le
  have hpoly' :
      3 * C * (X : ℝ) * Real.log (y : ℝ) ≤
        3 * C * Real.log (y : ℝ) ^ (A + 1) := by
    calc
      3 * C * (X : ℝ) * Real.log (y : ℝ) ≤
          3 * C * Real.log (y : ℝ) ^ A * Real.log (y : ℝ) := by
        gcongr
      _ = 3 * C * Real.log (y : ℝ) ^ (A + 1) := by
        rw [pow_succ]
        ring
  have hlogMono : Real.log (y : ℝ) ≤ Real.log (a : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hya)
  have hsqrtMono : Real.sqrt (Real.log (y : ℝ)) ≤
      Real.sqrt (Real.log (a : ℝ)) := Real.sqrt_le_sqrt hlogMono
  have hexpMono :
      Real.exp (c * Real.sqrt (Real.log (y : ℝ))) ≤
        Real.exp (c * Real.sqrt (Real.log (a : ℝ))) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hsqrtMono hc.le
  exact hpoly'.trans (hpoly.trans hexpMono)

/-- Complete schedule-facing version.  For every fixed polylogarithmic
exponent `A`, the reciprocal-prime estimate holds eventually and uniformly
for all intervals above `y` whose relative width is at most `1/X` and whose
smoothing parameter satisfies `X <= (log y)^A`. -/
theorem eventually_freshReciprocalSum_le_two_div_X_log_of_effectivePNT_polylog
    {C c : ℝ} {N : ℕ}
    (hC : 0 ≤ C) (hc : 0 < c)
    (hPNT : EffectivePrimeCountingError C c N) (A : ℕ) :
    ∀ᶠ y : ℕ in atTop, ∀ {X a b : ℕ},
      N ≤ a → 2 ≤ a → a ≤ b → 1 ≤ X → y ≤ a →
      (X : ℝ) ≤ Real.log (y : ℝ) ^ A →
      ((b : ℝ) - (a : ℝ)) ≤ (a : ℝ) / (X : ℝ) →
      freshReciprocalSum a b ≤
        2 / ((X : ℝ) * Real.log (y : ℝ)) := by
  have hdom := eventually_effectivePNT_error_dominated_polylog hC hc A
  filter_upwards [hdom, eventually_ge_atTop (2 : ℕ)] with
    y hdomY hy X a b hNa ha hab hX hya hXpoly hwidth
  exact freshReciprocalSum_le_two_div_X_log_of_effectivePNT
    hC hc.le hPNT hNa ha hab hX hy hya hwidth
      (hdomY hX hya hXpoly)

end Problem520
end Erdos
