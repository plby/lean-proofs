import ErdosProblems.Erdos520.CaichMainBlockComparison
import ErdosProblems.Erdos520.LargestPrimeDecomposition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory Set
open scoped BigOperators Interval

namespace Erdos
namespace Problem520

/-!
# The first deterministic smoothing step for the quadratic variation

This file formalizes the initial inequality in Caich's smoothing argument:
each summand of the predictable quadratic variation is averaged over the
short interval `p < t ≤ p(1 + 1/X)`, and the error is retained explicitly.
The result is the exact inequality `V ≤ 2 L + 2 W`, before any prime-number
estimate or probabilistic bound is used.
-/

/-- Real-cutoff version of the strict smooth sum `Ψ'`. -/
noncomputable def caichStrictSmoothReal
    (omega : Omega) (z : ℝ) (p : ℕ) : ℝ :=
  ΨReal omega z (p - 1)

/-- At a natural quotient the real-cutoff strict sum is exactly `Ψ'`. -/
theorem caichStrictSmoothReal_nat_div
    (omega : Omega) (x : ℕ) {p : ℕ} (hp : 0 < p) :
    caichStrictSmoothReal omega ((x : ℝ) / (p : ℝ)) p =
      Ψ' omega (x / p) p := by
  rw [Ψ'_eq_Ψ_pred omega (x / p) hp]
  unfold caichStrictSmoothReal ΨReal
  rw [Nat.floor_div_natCast, Nat.floor_natCast]

theorem measurable_caichStrictSmoothReal_cutoff
    (omega : Omega) (p : ℕ) :
    Measurable fun z : ℝ ↦ caichStrictSmoothReal omega z p :=
  measurable_ΨReal_cutoff omega (p - 1)

/-- A convenient uniform bound; it is deliberately crude, since it is used
only to discharge finite-interval integrability. -/
theorem abs_caichStrictSmoothReal_le
    (omega : Omega) (z : ℝ) (p : ℕ) :
    |caichStrictSmoothReal omega z p| ≤
      ((((p - 1 + 1).primesBelow.powerset.card : ℕ) : ℝ)) := by
  exact abs_ΨReal_le_powerset_card omega z (p - 1)

/-- Weighted average over Caich's short interval attached to a prime. -/
noncomputable def caichShortPrimeAverage
    (X : ℝ) (p : ℕ) (F : ℝ → ℝ) : ℝ :=
  (X / (p : ℝ)) *
    ∫ t in (p : ℝ)..(p : ℝ) * (1 + 1 / X), F t

/-- A short-prime average of a nonnegative integrand is nonnegative. -/
theorem caichShortPrimeAverage_nonneg
    {X : ℝ} (hX : 0 < X) {p : ℕ} (hp : 0 < p)
    (F : ℝ → ℝ) (hF : ∀ t, 0 ≤ F t) :
    0 ≤ caichShortPrimeAverage X p F := by
  unfold caichShortPrimeAverage
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hpq : (p : ℝ) ≤ (p : ℝ) * (1 + 1 / X) := by
    have hinv : 0 ≤ 1 / X := by positivity
    nlinarith
  exact mul_nonneg (div_nonneg hX.le hpR.le)
    (intervalIntegral.integral_nonneg hpq fun t _ht ↦ hF t)

/-- Elementary inequality underlying the smoothing step. -/
theorem sq_le_two_sq_add_two_sq_sub (A B : ℝ) :
    A ^ 2 ≤ 2 * B ^ 2 + 2 * (A - B) ^ 2 := by
  nlinarith [sq_nonneg (A - 2 * B)]

/-- Averaging the preceding pointwise inequality over an interval of length
`p/X` leaves its constant left side unchanged. -/
theorem sq_le_shortPrimeAverage
    {X p : ℝ} (hX : 0 < X) (hp : 0 < p)
    (A : ℝ) (B : ℝ → ℝ)
    (hB : IntervalIntegrable (fun t ↦ B t ^ 2) volume
      p (p * (1 + 1 / X)))
    (hD : IntervalIntegrable (fun t ↦ (A - B t) ^ 2) volume
      p (p * (1 + 1 / X))) :
    A ^ 2 ≤
      2 * ((X / p) * ∫ t in p..p * (1 + 1 / X), B t ^ 2) +
      2 * ((X / p) * ∫ t in p..p * (1 + 1 / X), (A - B t) ^ 2) := by
  let q : ℝ := p * (1 + 1 / X)
  have hpq : p ≤ q := by
    dsimp only [q]
    have : 0 ≤ 1 / X := by positivity
    nlinarith
  have hconst : IntervalIntegrable (fun _t : ℝ ↦ A ^ 2) volume p q :=
    intervalIntegrable_const
  have hsum : IntervalIntegrable
      (fun t ↦ 2 * B t ^ 2 + 2 * (A - B t) ^ 2) volume p q := by
    exact hB.const_mul 2 |>.add (hD.const_mul 2)
  have hmono :
      (∫ _t in p..q, A ^ 2) ≤
        ∫ t in p..q, 2 * B t ^ 2 + 2 * (A - B t) ^ 2 := by
    apply intervalIntegral.integral_mono_on hpq hconst hsum
    intro t ht
    exact sq_le_two_sq_add_two_sq_sub A (B t)
  have hdelta : 0 < p / X := div_pos hp hX
  have hlength : q - p = p / X := by
    dsimp only [q]
    field_simp
    <;> ring
  have hmono' :
      (p / X) * A ^ 2 ≤
        ∫ t in p..q, 2 * B t ^ 2 + 2 * (A - B t) ^ 2 := by
    simpa only [intervalIntegral.integral_const, hlength] using! hmono
  have hdivide : A ^ 2 ≤
      (∫ t in p..q, 2 * B t ^ 2 + 2 * (A - B t) ^ 2) / (p / X) := by
    apply (le_div_iff₀ hdelta).2
    simpa only [mul_comm] using! hmono'
  calc
    A ^ 2 ≤
        (∫ t in p..q, 2 * B t ^ 2 + 2 * (A - B t) ^ 2) /
          (p / X) := hdivide
    _ = 2 * ((X / p) * ∫ t in p..q, B t ^ 2) +
        2 * ((X / p) * ∫ t in p..q, (A - B t) ^ 2) := by
      rw [intervalIntegral.integral_add (hB.const_mul 2) (hD.const_mul 2),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
      have hinv : (p / X)⁻¹ = X / p := by
        field_simp <;> ring
      rw [div_eq_mul_inv, hinv]
      ring
    _ = _ := by rfl

/-- The main averaged piece `L` in the first smoothing step. -/
noncomputable def caichInitialSmoothedMain
    (X : ℝ) (omega : Omega) (x a b : ℕ) : ℝ :=
  ∑ p ∈ freshPrimes a b,
    caichShortPrimeAverage X p
      (fun t ↦ |caichStrictSmoothReal omega ((x : ℝ) / t) p| ^ 2)

/-- The short-interval error `W` in the first smoothing step. -/
noncomputable def caichInitialSmoothingError
    (X : ℝ) (omega : Omega) (x a b : ℕ) : ℝ :=
  ∑ p ∈ freshPrimes a b,
    caichShortPrimeAverage X p
      (fun t ↦
        |Ψ' omega (x / p) p -
          caichStrictSmoothReal omega ((x : ℝ) / t) p| ^ 2)

theorem caichInitialSmoothedMain_nonneg
    {X : ℝ} (hX : 0 < X) (omega : Omega) (x a b : ℕ) :
    0 ≤ caichInitialSmoothedMain X omega x a b := by
  unfold caichInitialSmoothedMain
  exact Finset.sum_nonneg fun p hp ↦
    caichShortPrimeAverage_nonneg hX
      (mem_freshPrimes.mp hp).1.pos _ (fun t ↦ sq_nonneg _)

theorem caichInitialSmoothingError_nonneg
    {X : ℝ} (hX : 0 < X) (omega : Omega) (x a b : ℕ) :
    0 ≤ caichInitialSmoothingError X omega x a b := by
  unfold caichInitialSmoothingError
  exact Finset.sum_nonneg fun p hp ↦
    caichShortPrimeAverage_nonneg hX
      (mem_freshPrimes.mp hp).1.pos _ (fun t ↦ sq_nonneg _)

/-- The squared main and error integrands are interval-integrable. -/
theorem intervalIntegrable_caichInitialSmoothingIntegrands
    {X : ℝ} (hX : 0 < X) (omega : Omega) (x : ℕ)
    {p : ℕ} (hp : p.Prime) :
    IntervalIntegrable
        (fun t : ℝ ↦
          |caichStrictSmoothReal omega ((x : ℝ) / t) p| ^ 2)
        volume (p : ℝ) ((p : ℝ) * (1 + 1 / X)) ∧
      IntervalIntegrable
        (fun t : ℝ ↦
          |Ψ' omega (x / p) p -
            caichStrictSmoothReal omega ((x : ℝ) / t) p| ^ 2)
        volume (p : ℝ) ((p : ℝ) * (1 + 1 / X)) := by
  let C : ℝ := ((((p - 1 + 1).primesBelow.powerset.card : ℕ) : ℝ))
  let A : ℝ := Ψ' omega (x / p) p
  let B : ℝ → ℝ := fun t ↦
    caichStrictSmoothReal omega ((x : ℝ) / t) p
  have hBmeas : Measurable B :=
    (measurable_caichStrictSmoothReal_cutoff omega p).comp
      (measurable_const.div measurable_id)
  have hBbound : ∀ t, |B t| ≤ C := by
    intro t
    exact abs_caichStrictSmoothReal_le omega ((x : ℝ) / t) p
  have finiteIntegral (F : ℝ → ℝ) (hFmeas : Measurable F)
      (D : ℝ) (hFbound : ∀ t, ‖F t‖ ≤ D) :
      IntervalIntegrable F volume (p : ℝ)
        ((p : ℝ) * (1 + 1 / X)) := by
    have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
    have hpq : (p : ℝ) ≤ (p : ℝ) * (1 + 1 / X) := by
      have : 0 ≤ 1 / X := by positivity
      nlinarith
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hpq]
    apply IntegrableOn.of_bound measure_Ioc_lt_top hFmeas.aestronglyMeasurable D
    exact ae_of_all _ hFbound
  constructor
  · apply finiteIntegral (fun t ↦ |B t| ^ 2)
      (hBmeas.abs.pow_const 2) (C ^ 2)
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hBbound t) 2
  · apply finiteIntegral (fun t ↦ |A - B t| ^ 2)
      ((measurable_const.sub hBmeas).abs.pow_const 2) ((|A| + C) ^ 2)
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    apply pow_le_pow_left₀ (abs_nonneg _)
    calc
      |A - B t| ≤ |A| + |B t| := abs_sub A (B t)
      _ ≤ |A| + C := add_le_add le_rfl (hBbound t)

/-- Exact formalization of Caich's first smoothing inequality
`V ≤ 2 L + 2 W`. -/
theorem largestPrimeQuadraticVariation_le_initialSmoothing
    {X : ℝ} (hX : 0 < X) (omega : Omega) (x a b : ℕ) :
    largestPrimeQuadraticVariation omega x a b ≤
      2 * caichInitialSmoothedMain X omega x a b +
        2 * caichInitialSmoothingError X omega x a b := by
  classical
  unfold largestPrimeQuadraticVariation caichInitialSmoothedMain
    caichInitialSmoothingError
  calc
    (∑ p ∈ freshPrimes a b, |Ψ' omega (x / p) p| ^ 2) ≤
        ∑ p ∈ freshPrimes a b,
          (2 * caichShortPrimeAverage X p
              (fun t ↦ |caichStrictSmoothReal omega ((x : ℝ) / t) p| ^ 2) +
            2 * caichShortPrimeAverage X p
              (fun t ↦ |Ψ' omega (x / p) p -
                caichStrictSmoothReal omega ((x : ℝ) / t) p| ^ 2)) := by
      apply Finset.sum_le_sum
      intro p hpBlock
      have hpPrime : p.Prime := (mem_freshPrimes.mp hpBlock).1
      have hp0R : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.pos
      let B : ℝ → ℝ := fun t ↦
        caichStrictSmoothReal omega ((x : ℝ) / t) p
      have hInt := intervalIntegrable_caichInitialSmoothingIntegrands
        hX omega x hpPrime
      have havg := sq_le_shortPrimeAverage hX hp0R
        (Ψ' omega (x / p) p) B
        (by simpa only [sq_abs] using! hInt.1)
        (by simpa only [sq_abs] using! hInt.2)
      simpa only [caichShortPrimeAverage, B, sq_abs] using! havg
    _ =
        2 * ∑ p ∈ freshPrimes a b,
          caichShortPrimeAverage X p
            (fun t ↦ |caichStrictSmoothReal omega ((x : ℝ) / t) p| ^ 2) +
        2 * ∑ p ∈ freshPrimes a b,
          caichShortPrimeAverage X p
            (fun t ↦ |Ψ' omega (x / p) p -
              caichStrictSmoothReal omega ((x : ℝ) / t) p| ^ 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

end Problem520
end Erdos
