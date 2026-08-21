import ErdosProblems.Erdos239.External.Erdos67.Pretentious
import ErdosProblems.Erdos239.External.Erdos67.PrimeEstimates
import ErdosProblems.Erdos239.External.Erdos67.PrimeEulerTail
import ErdosProblems.Erdos239.External.Erdos67.Section4Probability
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.ZetaValues
import BoundedGaps.BombieriVinogradov.Analytic.SquareNonprincipalZeroFreeRegion
import BoundedGaps.BombieriVinogradov.Analytic.SiegelWalfisz
import BoundedGaps.Maynard.PrimeMertens

/-!
# Separation of bounded-conductor character twists

This file isolates the finite analytic statement used in the frequency-reduction step of
Tao's proof of the Erdős discrepancy theorem.  Everything below is a finite sum.  In
particular, no infinite Euler product is hidden in the definitions.

For characters `χ` and `χ'` and a real frequency difference `v`, the relevant correlation is

`sum_{p ≤ Y} Re (χ(p) * conj (χ'(p)) * p^(-i v)) / p`.

The corresponding squared pretentious distance is exactly the reciprocal-prime mass minus
this correlation.  The lemmas in this file prove that identity, its compatibility with the
twists defined in `Pretentious.lean`, and the complete finite deduction of twist separation
from a uniform upper bound for the correlation.

The imported BoundedGaps development supplies de la Vallée Poussin zero-free regions,
Dirichlet explicit formulas, and Siegel--Walfisz.  Tao's polynomial-height range additionally
requires the Vinogradov--Korobov-strength upper bound recorded by
`PolynomialHeightPrimeCorrelationBound` below.  We deliberately define that proposition but
do not claim it as a theorem here: the point of the interface is to identify the exact analytic
statement still requiring proof, without introducing an assumption into any declaration.
-/

open scoped BigOperators ComplexConjugate

namespace Erdos67

noncomputable section

/-! ## The finite correlation and distance -/

/-- The phase `χ(p) * conj (χ'(p)) * p^(-i v)` occurring when two
Dirichlet--Archimedean twists have frequency difference `v`. -/
def characterTwistPhase {q q' : ℕ}
    (χ : DirichletCharacter ℂ q) (χ' : DirichletCharacter ℂ q')
    (v : ℝ) (n : ℕ) : ℂ :=
  χ n * conj (χ' n) * (n : ℂ) ^ (-(Complex.I * (v : ℂ)))

/-- The real prime correlation between two characters at frequency difference `v`. -/
def characterTwistPrimeCorrelation {q q' : ℕ}
    (χ : DirichletCharacter ℂ q) (χ' : DirichletCharacter ℂ q')
    (v : ℝ) (Y : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo Y, (characterTwistPhase χ χ' v p).re / (p : ℝ)

/-- Reciprocal mass of all primes at most `Y`, in the notation of this file. -/
def characterTwistPrimeMass (Y : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo Y, (p : ℝ)⁻¹

/-- The finite squared distance between `χ` and `χ' n^(iv)` at the primes at most `Y`. -/
def characterTwistDistSq {q q' : ℕ}
    (χ : DirichletCharacter ℂ q) (χ' : DirichletCharacter ℂ q')
    (v : ℝ) (Y : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo Y,
    (1 - (characterTwistPhase χ χ' v p).re) / (p : ℝ)

/-! ## Putting two characters at a common level -/

/-- The quotient character `χ * ̅χ'`, put at the common (not necessarily minimal)
level `q * q'`.  At integers coprime to `q * q'`, its value is exactly
`χ(n) * conj (χ'(n))`; this is the character whose `L`-function controls the
prime correlation below. -/
def quotientCharacter {q q' : ℕ}
    (χ : DirichletCharacter ℂ q) (χ' : DirichletCharacter ℂ q') :
    DirichletCharacter ℂ (q * q') :=
  DirichletCharacter.changeLevel (dvd_mul_right q q') χ *
    (DirichletCharacter.changeLevel (dvd_mul_left q' q) χ')⁻¹

theorem quotientCharacter_apply_of_isCoprime {q q' n : ℕ}
    (χ : DirichletCharacter ℂ q) (χ' : DirichletCharacter ℂ q')
    (hn : IsCoprime (n : ℤ) (q * q' : ℕ)) :
    quotientCharacter χ χ' n = χ n * conj (χ' n) := by
  have hnprod : IsCoprime (n : ℤ) ((q : ℤ) * (q' : ℤ)) := by
    simpa only [Nat.cast_mul] using hn
  have hnq : IsCoprime (n : ℤ) (q : ℤ) := by
    exact hnprod.of_mul_right_left
  have hnq' : IsCoprime (n : ℤ) (q' : ℤ) := by
    exact hnprod.of_mul_right_right
  have hunit : IsUnit ((n : ℤ) : ZMod q') := by
    rw [ZMod.coe_int_isUnit_iff_isCoprime]
    exact hnq'.symm
  have hnorm : ‖χ' n‖ = 1 := by
    have hnormInt : ‖χ' ((n : ℤ) : ZMod q')‖ = 1 := by
      rw [← hunit.unit_spec]
      exact χ'.unit_norm_eq_one hunit.unit
    simpa only [Int.cast_natCast] using hnormInt
  have hchange :
      DirichletCharacter.changeLevel (dvd_mul_right q q') χ n = χ n := by
    simpa only [Int.cast_natCast] using
      DirichletCharacter.changeLevel_eq_cast_of_dvd' χ
        (dvd_mul_right q q') (a := (n : ℤ)) hn
  have hchange' :
      DirichletCharacter.changeLevel (dvd_mul_left q' q) χ' n = χ' n := by
    simpa only [Int.cast_natCast] using
      DirichletCharacter.changeLevel_eq_cast_of_dvd' χ'
        (dvd_mul_left q' q) (a := (n : ℤ)) hn
  simp only [quotientCharacter, MulChar.mul_apply]
  rw [hchange]
  rw [MulChar.inv_apply_eq_inv']
  rw [hchange', Complex.inv_eq_conj hnorm]

/-- At a prime the common-level quotient character agrees with
`χ(p) * conj (χ'(p))` even at the conductor primes: both sides vanish
there. -/
theorem quotientCharacter_apply_prime {q q' p : ℕ}
    (χ : DirichletCharacter ℂ q) (χ' : DirichletCharacter ℂ q')
    (hp : p.Prime) :
    quotientCharacter χ χ' p = χ p * conj (χ' p) := by
  by_cases hpdvd : p ∣ q * q'
  · have hnonunit : ¬IsUnit (p : ZMod (q * q')) := by
      rwa [ZMod.isUnit_prime_iff_not_dvd hp, not_not]
    rw [MulChar.map_nonunit _ hnonunit]
    rcases (hp.dvd_mul.mp hpdvd) with hpq | hpq'
    · have hnonunitq : ¬IsUnit (p : ZMod q) := by
        rwa [ZMod.isUnit_prime_iff_not_dvd hp, not_not]
      rw [MulChar.map_nonunit χ hnonunitq, zero_mul]
    · have hnonunitq' : ¬IsUnit (p : ZMod q') := by
        rwa [ZMod.isUnit_prime_iff_not_dvd hp, not_not]
      rw [MulChar.map_nonunit χ' hnonunitq', map_zero, mul_zero]
  · apply quotientCharacter_apply_of_isCoprime
    exact_mod_cast (hp.coprime_iff_not_dvd.mpr hpdvd)

/-! ## Removing the higher prime powers from an Euler factor -/

/-- The first term in a logarithmic Euler factor is bounded above by the real
part of the full factor, with a summable quadratic error.  The numerical
radius `1/2` is exactly what is available at every prime when `re s > 1`.

This is the local estimate needed to pass from the logarithm of a Dirichlet
`L`-function to its prime correlation; unlike a formal power-series argument,
it uses Mathlib's analytic logarithm on the slit plane. -/
theorem re_le_neg_log_one_sub_add_norm_sq {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    z.re ≤ (-Complex.log (1 - z)).re + ‖z‖ ^ 2 := by
  have hzlt : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
  have herr := Complex.norm_log_one_sub_inv_sub_self_le hzlt
  have hinv : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    calc
      1 / (1 - ‖z‖) ≤ 1 / (1 / 2 : ℝ) :=
        one_div_le_one_div_of_le (by norm_num) (by linarith)
      _ = 2 := by norm_num
  have herr' : ‖Complex.log (1 - z)⁻¹ - z‖ ≤ ‖z‖ ^ 2 := by
    calc
      ‖Complex.log (1 - z)⁻¹ - z‖ ≤
          ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 := herr
      _ ≤ ‖z‖ ^ 2 * 2 / 2 := by
        gcongr
      _ = ‖z‖ ^ 2 := by ring
  have hre := Complex.re_le_norm (z - Complex.log (1 - z)⁻¹)
  simp only [Complex.sub_re] at hre
  rw [norm_sub_rev] at hre
  have hre' : z.re - (Complex.log (1 - z)⁻¹).re ≤ ‖z‖ ^ 2 :=
    hre.trans herr'
  have hloginv :
      Complex.log (1 - z)⁻¹ = -Complex.log (1 - z) := by
    apply Complex.log_inv
    exact Complex.slitPlane_arg_ne_pi
      (Complex.mem_slitPlane_of_norm_lt_one (z := -z) (by simpa using hzlt))
  rw [hloginv] at hre'
  simp only [Complex.neg_re] at hre'
  rw [Complex.neg_re]
  linarith

/-- The damped first-prime term at a complex point `s`. -/
def dampedCharacterPrimeCorrelation {q : ℕ}
    (χ : DirichletCharacter ℂ q) (s : ℂ) (Y : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo Y, (χ p * (p : ℂ) ^ (-s)).re

/-- The logarithm of the Euler product truncated at the primes at most `Y`.
It is defined as a sum of principal logarithms, not as a logarithm of a
finite product, so no branch choice is suppressed. -/
def truncatedCharacterEulerLog {q : ℕ}
    (χ : DirichletCharacter ℂ q) (s : ℂ) (Y : ℕ) : ℂ :=
  ∑ p ∈ primesUpTo Y,
    -Complex.log (1 - χ p * (p : ℂ) ^ (-s))

/-- Removing all higher prime powers from a truncated logarithmic Euler
product costs at most `3`, uniformly in the character, endpoint, and height.
This makes the prime-power error in the VK reduction completely explicit. -/
theorem dampedCharacterPrimeCorrelation_le_eulerLog_add_three
    {q Y : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) :
    dampedCharacterPrimeCorrelation χ s Y ≤
      (truncatedCharacterEulerLog χ s Y).re + 3 := by
  have hlocal : ∀ p ∈ primesUpTo Y,
      (χ p * (p : ℂ) ^ (-s)).re ≤
        (-Complex.log (1 - χ p * (p : ℂ) ^ (-s))).re +
          1 / (p : ℝ) ^ 2 := by
    intro p hp
    have hpPrime := (mem_primesUpTo.mp hp).1
    have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast hpPrime.one_le
    have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hpPrime.two_le
    have hpPos : (0 : ℝ) < p := by positivity
    let z : ℂ := χ p * (p : ℂ) ^ (-s)
    have hpow : ‖(p : ℂ) ^ (-s)‖ ≤ (p : ℝ)⁻¹ := by
      rw [← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_pos hpPos]
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hpOne (by simp; linarith)
    have hzInv : ‖z‖ ≤ (p : ℝ)⁻¹ := by
      change ‖χ p * (p : ℂ) ^ (-s)‖ ≤ (p : ℝ)⁻¹
      rw [norm_mul]
      calc
        ‖χ p‖ * ‖(p : ℂ) ^ (-s)‖ ≤ 1 * (p : ℝ)⁻¹ :=
          mul_le_mul (χ.norm_le_one p) hpow (norm_nonneg _) zero_le_one
        _ = (p : ℝ)⁻¹ := one_mul _
    have hzHalf : ‖z‖ ≤ 1 / 2 := by
      exact hzInv.trans (by
        rw [inv_eq_one_div]
        exact one_div_le_one_div_of_le (by norm_num) hpTwo)
    have hlog := re_le_neg_log_one_sub_add_norm_sq hzHalf
    have hzSq : ‖z‖ ^ 2 ≤ 1 / (p : ℝ) ^ 2 := by
      calc
        ‖z‖ ^ 2 ≤ ((p : ℝ)⁻¹) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg z) hzInv 2
        _ = 1 / (p : ℝ) ^ 2 := by simp only [one_div, inv_pow]
    dsimp only [z] at hlog hzSq ⊢
    linarith
  unfold dampedCharacterPrimeCorrelation truncatedCharacterEulerLog
  calc
    (∑ p ∈ primesUpTo Y, (χ p * (p : ℂ) ^ (-s)).re) ≤
        ∑ p ∈ primesUpTo Y,
          ((-Complex.log (1 - χ p * (p : ℂ) ^ (-s))).re +
            1 / (p : ℝ) ^ 2) := Finset.sum_le_sum hlocal
    _ = (∑ p ∈ primesUpTo Y,
          -Complex.log (1 - χ p * (p : ℂ) ^ (-s))).re +
        ∑ p ∈ primesUpTo Y, 1 / (p : ℝ) ^ 2 := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Complex.re_sum]
    _ ≤ (∑ p ∈ primesUpTo Y,
          -Complex.log (1 - χ p * (p : ℂ) ^ (-s))).re +
        ∑' n : ℕ, 1 / (n : ℝ) ^ 2 := by
      gcongr
      exact (Real.summable_one_div_nat_pow.mpr (by norm_num)).sum_le_tsum
        (primesUpTo Y) (fun _ _ ↦ by positivity)
    _ = (∑ p ∈ primesUpTo Y,
          -Complex.log (1 - χ p * (p : ℂ) ^ (-s))).re +
        Real.pi ^ 2 / 6 := by rw [hasSum_zeta_two.tsum_eq]
    _ ≤ (∑ p ∈ primesUpTo Y,
          -Complex.log (1 - χ p * (p : ℂ) ^ (-s))).re + 3 := by
      gcongr
      nlinarith [Real.pi_nonneg, Real.pi_le_four]

/-! ## Removing the harmless real damping -/

open BoundedGaps.Maynard

/-- A fixed absolute constant in the bounded-error prime-log Mertens
estimate.  Its numerical value is irrelevant; only its uniformity matters. -/
noncomputable def primeLogMertensConstant : ℝ :=
  Classical.choose exists_uniform_abs_primeLogHarmonicSum_sub_log

theorem primeLogMertensConstant_spec (n : ℕ) :
    |primeLogHarmonicSum n - Real.log n| ≤ primeLogMertensConstant :=
  Classical.choose_spec exists_uniform_abs_primeLogHarmonicSum_sub_log n

theorem primeLogMertensConstant_nonneg : 0 ≤ primeLogMertensConstant := by
  have h := primeLogMertensConstant_spec 1
  simpa [primeLogHarmonicSum] using h

/-- Moving from the line `re s = 1` to the absolutely convergent point
`re s = 1 + 1 / log Y` changes the prime correlation by at most an absolute
constant.  This is the precise finite smoothing estimate used before
invoking a high-frequency `L`-function bound. -/
theorem reciprocalLog_smoothingLoss_le (Y : ℕ) (hY : 4 ≤ Y) :
    (∑ p ∈ primesUpTo Y,
      (1 - (p : ℝ) ^ (-(Real.log (Y : ℝ))⁻¹)) / (p : ℝ)) ≤
      1 + primeLogMertensConstant := by
  have hlogTwo : (1 / 2 : ℝ) < Real.log 2 :=
    (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
  have hlogOne : 1 ≤ Real.log (Y : ℝ) := by
    calc
      (1 : ℝ) ≤ 2 * Real.log 2 := by linarith
      _ = Real.log 4 := Real.log_four_eq.symm
      _ ≤ Real.log (Y : ℝ) := by
        apply Real.log_le_log (by norm_num)
        exact_mod_cast hY
  have hlogPos : 0 < Real.log (Y : ℝ) := zero_lt_one.trans_le hlogOne
  have hpoint : ∀ p ∈ primesUpTo Y,
      (1 - (p : ℝ) ^ (-(Real.log (Y : ℝ))⁻¹)) / (p : ℝ) ≤
        (Real.log (Y : ℝ))⁻¹ * (Real.log p / (p : ℝ)) := by
    intro p hp
    have hpPrime := (mem_primesUpTo.mp hp).1
    have hpPos : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
    have hexp :
        (p : ℝ) ^ (-(Real.log (Y : ℝ))⁻¹) =
          Real.exp (-((Real.log (Y : ℝ))⁻¹ * Real.log p)) := by
      rw [Real.rpow_def_of_pos hpPos]
      congr 1
      ring
    have hone := Real.one_sub_le_exp_neg
      ((Real.log (Y : ℝ))⁻¹ * Real.log p)
    have hdamp :
        1 - Real.exp (-((Real.log (Y : ℝ))⁻¹ * Real.log p)) ≤
          (Real.log (Y : ℝ))⁻¹ * Real.log p := by linarith
    rw [hexp]
    calc
      (1 - Real.exp (-((Real.log (Y : ℝ))⁻¹ * Real.log p))) / (p : ℝ) ≤
          ((Real.log (Y : ℝ))⁻¹ * Real.log p) / (p : ℝ) :=
        div_le_div_of_nonneg_right hdamp hpPos.le
      _ = (Real.log (Y : ℝ))⁻¹ * (Real.log p / (p : ℝ)) := by ring
  calc
    (∑ p ∈ primesUpTo Y,
      (1 - (p : ℝ) ^ (-(Real.log (Y : ℝ))⁻¹)) / (p : ℝ)) ≤
        ∑ p ∈ primesUpTo Y,
          (Real.log (Y : ℝ))⁻¹ * (Real.log p / (p : ℝ)) :=
      Finset.sum_le_sum hpoint
    _ = (Real.log (Y : ℝ))⁻¹ * primeLogHarmonicSum Y := by
      rw [← Finset.mul_sum]
      unfold primeLogHarmonicSum primesUpTo
      rw [Nat.primesLE_eq_filter_range]
    _ ≤ (Real.log (Y : ℝ))⁻¹ *
        (Real.log (Y : ℝ) + primeLogMertensConstant) := by
      gcongr
      have h := primeLogMertensConstant_spec Y
      linarith [le_abs_self (primeLogHarmonicSum Y - Real.log Y)]
    _ ≤ 1 + primeLogMertensConstant := by
      rw [inv_mul_eq_div]
      field_simp
      nlinarith [primeLogMertensConstant_nonneg]

/-- The absolutely convergent point used to smooth a height-`v` prime
correlation. -/
def reciprocalLogSmoothingPoint (Y : ℕ) (v : ℝ) : ℂ :=
  ((1 + (Real.log (Y : ℝ))⁻¹ : ℝ) : ℂ) + Complex.I * (v : ℂ)

theorem reciprocalLogSmoothingPoint_re (Y : ℕ) (v : ℝ) :
    (reciprocalLogSmoothingPoint Y v).re =
      1 + (Real.log (Y : ℝ))⁻¹ := by
  rw [reciprocalLogSmoothingPoint]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero,
    sub_zero, add_zero]

theorem cpow_neg_reciprocalLogSmoothingPoint {Y p : ℕ} (v : ℝ)
    (hp : 0 < p) :
    (p : ℂ) ^ (-reciprocalLogSmoothingPoint Y v) =
      (p : ℂ) ^ (-(Complex.I * (v : ℂ))) *
        ((p : ℝ) ^ (-(Real.log (Y : ℝ))⁻¹) / (p : ℝ) : ℝ) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [reciprocalLogSmoothingPoint]
  have hexponent :
      -(((1 + (Real.log (Y : ℝ))⁻¹ : ℝ) : ℂ) + Complex.I * (v : ℂ)) =
        -(Complex.I * (v : ℂ)) +
          ((-(Real.log (Y : ℝ))⁻¹ : ℝ) : ℂ) + (-1 : ℂ) := by
    push_cast
    ring
  rw [hexponent, Complex.cpow_add _ _ hpC, Complex.cpow_add _ _ hpC,
    Complex.cpow_neg_one]
  have hrealpow :
      (p : ℂ) ^ (((-(Real.log (Y : ℝ))⁻¹ : ℝ) : ℂ)) =
        (((p : ℝ) ^ (-(Real.log (Y : ℝ))⁻¹) : ℝ) : ℂ) :=
    (Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ p)
      (-(Real.log (Y : ℝ))⁻¹)).symm
  rw [hrealpow]
  push_cast
  ring

/-- The original character correlation is bounded by the damped quotient-
character correlation plus the absolute smoothing error.  The equality of
characters at conductor primes is supplied by `quotientCharacter_apply_prime`,
so this reduction has no coprimality gap. -/
theorem characterTwistPrimeCorrelation_le_damped_add_smoothing
    {q q' Y : ℕ} (χ : DirichletCharacter ℂ q)
    (χ' : DirichletCharacter ℂ q') (v : ℝ) (hY : 4 ≤ Y) :
    characterTwistPrimeCorrelation χ χ' v Y ≤
      dampedCharacterPrimeCorrelation (quotientCharacter χ χ')
        (reciprocalLogSmoothingPoint Y v) Y +
          1 + primeLogMertensConstant := by
  have hsmoothing := reciprocalLog_smoothingLoss_le Y hY
  have hpoint : ∀ p ∈ primesUpTo Y,
      (characterTwistPhase χ χ' v p).re / (p : ℝ) ≤
        (quotientCharacter χ χ' p *
          (p : ℂ) ^ (-reciprocalLogSmoothingPoint Y v)).re +
          (1 - (p : ℝ) ^ (-(Real.log (Y : ℝ))⁻¹)) / (p : ℝ) := by
    intro p hp
    have hpPrime := (mem_primesUpTo.mp hp).1
    have hpPosR : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
    have hnorm : ‖characterTwistPhase χ χ' v p‖ ≤ 1 := by
      rw [characterTwistPhase, norm_mul, norm_mul, Complex.norm_conj]
      have hpow : ‖(p : ℂ) ^ (-(Complex.I * (v : ℂ)))‖ = 1 := by
        rw [← Complex.ofReal_natCast,
          Complex.norm_cpow_eq_rpow_re_of_pos hpPosR]
        simp
      rw [hpow, mul_one]
      have hχ := χ.norm_le_one p
      have hχ' := χ'.norm_le_one p
      nlinarith [norm_nonneg (χ p), norm_nonneg (χ' p)]
    have hre : (characterTwistPhase χ χ' v p).re ≤ 1 :=
      (Complex.re_le_norm _).trans hnorm
    rw [quotientCharacter_apply_prime χ χ' hpPrime,
      cpow_neg_reciprocalLogSmoothingPoint v hpPrime.pos]
    have hdampNonneg :
        0 ≤ (p : ℝ) ^ (-(Real.log (Y : ℝ))⁻¹) := Real.rpow_nonneg hpPosR.le _
    have hlogPos : 0 < Real.log (Y : ℝ) :=
      Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 4) hY))
    have hdampLe : (p : ℝ) ^ (-(Real.log (Y : ℝ))⁻¹) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos
        (by exact_mod_cast hpPrime.one_le)
        (neg_nonpos.mpr (inv_nonneg.mpr hlogPos.le))
    rw [show χ p * conj (χ' p) *
          ((p : ℂ) ^ (-(Complex.I * (v : ℂ))) *
            (((p : ℝ) ^ (-(Real.log (Y : ℝ))⁻¹) / (p : ℝ) : ℝ) : ℂ)) =
        characterTwistPhase χ χ' v p *
          (((p : ℝ) ^ (-(Real.log (Y : ℝ))⁻¹) / (p : ℝ) : ℝ) : ℂ) by
        rw [characterTwistPhase]
        ring]
    have hcore :
        (characterTwistPhase χ χ' v p).re ≤
          (characterTwistPhase χ χ' v p).re *
              (p : ℝ) ^ (-(Real.log (Y : ℝ))⁻¹) +
            (1 - (p : ℝ) ^ (-(Real.log (Y : ℝ))⁻¹)) := by
      calc
        (characterTwistPhase χ χ' v p).re =
            (characterTwistPhase χ χ' v p).re *
                (p : ℝ) ^ (-(Real.log (Y : ℝ))⁻¹) +
              (characterTwistPhase χ χ' v p).re *
                (1 - (p : ℝ) ^ (-(Real.log (Y : ℝ))⁻¹)) := by ring
        _ ≤ (characterTwistPhase χ χ' v p).re *
                (p : ℝ) ^ (-(Real.log (Y : ℝ))⁻¹) +
              1 * (1 - (p : ℝ) ^ (-(Real.log (Y : ℝ))⁻¹)) := by
          gcongr
        _ = _ := by ring
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    field_simp
    simpa only [one_div] using hcore
  unfold characterTwistPrimeCorrelation dampedCharacterPrimeCorrelation
  calc
    (∑ p ∈ primesUpTo Y, (characterTwistPhase χ χ' v p).re / (p : ℝ)) ≤
        ∑ p ∈ primesUpTo Y,
          ((quotientCharacter χ χ' p *
            (p : ℂ) ^ (-reciprocalLogSmoothingPoint Y v)).re +
            (1 - (p : ℝ) ^ (-(Real.log (Y : ℝ))⁻¹)) / (p : ℝ)) :=
      Finset.sum_le_sum hpoint
    _ = (∑ p ∈ primesUpTo Y,
          (quotientCharacter χ χ' p *
            (p : ℂ) ^ (-reciprocalLogSmoothingPoint Y v)).re) +
        ∑ p ∈ primesUpTo Y,
          (1 - (p : ℝ) ^ (-(Real.log (Y : ℝ))⁻¹)) / (p : ℝ) := by
      rw [Finset.sum_add_distrib]
    _ ≤ (∑ p ∈ primesUpTo Y,
          (quotientCharacter χ χ' p *
            (p : ℂ) ^ (-reciprocalLogSmoothingPoint Y v)).re) +
        (1 + primeLogMertensConstant) := by gcongr
    _ = (∑ p ∈ primesUpTo Y,
          (quotientCharacter χ χ' p *
            (p : ℂ) ^ (-reciprocalLogSmoothingPoint Y v)).re) +
        1 + primeLogMertensConstant := by ring

/-- Fully finite reduction from the original character-twist prime
correlation to the real part of the truncated Euler logarithm.  All
comparison losses are explicit and independent of the two conductors, the
height, and the endpoint. -/
theorem characterTwistPrimeCorrelation_le_truncatedEulerLog
    {q q' Y : ℕ} (χ : DirichletCharacter ℂ q)
    (χ' : DirichletCharacter ℂ q') (v : ℝ) (hY : 4 ≤ Y) :
    characterTwistPrimeCorrelation χ χ' v Y ≤
      (truncatedCharacterEulerLog (quotientCharacter χ χ')
        (reciprocalLogSmoothingPoint Y v) Y).re +
          4 + primeLogMertensConstant := by
  have hlogPos : 0 < Real.log (Y : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 4) hY))
  have hs : 1 < (reciprocalLogSmoothingPoint Y v).re := by
    rw [reciprocalLogSmoothingPoint_re]
    linarith [inv_pos.mpr hlogPos]
  have hcorr := characterTwistPrimeCorrelation_le_damped_add_smoothing
    χ χ' v hY
  have heuler := dampedCharacterPrimeCorrelation_le_eulerLog_add_three
    (Y := Y) (quotientCharacter χ χ') hs
  linarith

/-! ## A unit-disk triangle inequality -/

/-- The squared pretentious triangle inequality only needs the middle
function to be unit-valued; the other two functions may take values in the
closed unit disk.  This strengthening is important for Dirichlet characters:
their values vanish at primes dividing the modulus, so a unit-sphere lemma
cannot be applied without modification. -/
theorem pretentiousTerm_triangle_sq_left_unit {f g h : ℕ → ℂ} {p : ℕ}
    (hf : ‖f p‖ = 1) (hg : ‖g p‖ ≤ 1) (hh : ‖h p‖ ≤ 1) :
    pretentiousTerm g h p ≤
      2 * (pretentiousTerm f g p + pretentiousTerm f h p) := by
  have hfg :
      ‖f p - g p‖ ^ 2 = 1 + ‖g p‖ ^ 2 -
          2 * (f p * conj (g p)).re := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub,
      Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hf]
    ring
  have hfh :
      ‖f p - h p‖ ^ 2 = 1 + ‖h p‖ ^ 2 -
          2 * (f p * conj (h p)).re := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub,
      Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hf]
    ring
  have hgh :
      ‖g p - h p‖ ^ 2 = ‖g p‖ ^ 2 + ‖h p‖ ^ 2 -
          2 * (g p * conj (h p)).re := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub,
      Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have htri :
      ‖g p - h p‖ ≤ ‖f p - g p‖ + ‖f p - h p‖ := by
    calc
      ‖g p - h p‖ = ‖-(f p - g p) + (f p - h p)‖ := by ring_nf
      _ ≤ ‖-(f p - g p)‖ + ‖f p - h p‖ := norm_add_le _ _
      _ = ‖f p - g p‖ + ‖f p - h p‖ := by rw [norm_neg]
  have htriSq :
      ‖g p - h p‖ ^ 2 ≤
        ‖f p - g p‖ ^ 2 + ‖f p - h p‖ ^ 2 +
          2 * ‖f p - g p‖ * ‖f p - h p‖ := by
    nlinarith [norm_nonneg (g p - h p), norm_nonneg (f p - g p),
      norm_nonneg (f p - h p)]
  have hfgUpper :
      ‖f p - g p‖ ^ 2 ≤ 2 * (1 - (f p * conj (g p)).re) := by
    nlinarith [norm_nonneg (g p), sq_nonneg (1 - ‖g p‖)]
  have hfhUpper :
      ‖f p - h p‖ ^ 2 ≤ 2 * (1 - (f p * conj (h p)).re) := by
    nlinarith [norm_nonneg (h p), sq_nonneg (1 - ‖h p‖)]
  have hab :
      2 * ‖f p - g p‖ * ‖f p - h p‖ ≤
        ‖f p - g p‖ ^ 2 + ‖f p - h p‖ ^ 2 := by
    nlinarith [sq_nonneg (‖f p - g p‖ - ‖f p - h p‖)]
  have hnumerator :
      1 - (g p * conj (h p)).re ≤
        2 * ((1 - (f p * conj (g p)).re) +
          (1 - (f p * conj (h p)).re)) := by
    nlinarith
  unfold pretentiousTerm
  have hpnonneg : (0 : ℝ) ≤ p := by positivity
  calc
    (1 - (g p * conj (h p)).re) / (p : ℝ) ≤
        (2 * ((1 - (f p * conj (g p)).re) +
          (1 - (f p * conj (h p)).re))) / (p : ℝ) :=
      div_le_div_of_nonneg_right hnumerator hpnonneg
    _ = 2 * ((1 - (f p * conj (g p)).re) / (p : ℝ) +
        (1 - (f p * conj (h p)).re) / (p : ℝ)) := by ring

theorem pretentiousDistSq_triangle_sq_left_unit {f g h : ℕ → ℂ} {x : ℕ}
    (hf : ∀ p, p.Prime → ‖f p‖ = 1)
    (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    (hh : ∀ p, p.Prime → ‖h p‖ ≤ 1) :
    pretentiousDistSq g h x ≤
      2 * (pretentiousDistSq f g x + pretentiousDistSq f h x) := by
  calc
    pretentiousDistSq g h x ≤
        ∑ p ∈ primesUpTo x,
          2 * (pretentiousTerm f g p + pretentiousTerm f h p) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' := (mem_primesUpTo.mp hp).1
      exact pretentiousTerm_triangle_sq_left_unit
        (hf p hp') (hg p hp') (hh p hp')
    _ = 2 * (pretentiousDistSq f g x + pretentiousDistSq f h x) := by
      simp only [pretentiousDistSq]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

theorem norm_characterTwistPhase_le_one {q q' n : ℕ}
    (χ : DirichletCharacter ℂ q) (χ' : DirichletCharacter ℂ q')
    (v : ℝ) (hn : 0 < n) :
    ‖characterTwistPhase χ χ' v n‖ ≤ 1 := by
  rw [characterTwistPhase, norm_mul, norm_mul, Complex.norm_conj]
  have hpow : ‖(n : ℂ) ^ (-(Complex.I * (v : ℂ)))‖ = 1 := by
    rw [← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr hn)]
    simp
  rw [hpow, mul_one]
  have hχ := χ.norm_le_one n
  have hχ' := χ'.norm_le_one n
  nlinarith [norm_nonneg (χ n), norm_nonneg (χ' n)]

theorem characterTwistDistSq_nonneg {q q' : ℕ}
    (χ : DirichletCharacter ℂ q) (χ' : DirichletCharacter ℂ q')
    (v : ℝ) (Y : ℕ) :
    0 ≤ characterTwistDistSq χ χ' v Y := by
  apply Finset.sum_nonneg
  intro p hp
  have hpPrime := (mem_primesUpTo.mp hp).1
  have hnorm := norm_characterTwistPhase_le_one χ χ' v hpPrime.pos
  have hre : (characterTwistPhase χ χ' v p).re ≤ 1 :=
    (Complex.re_le_norm _).trans hnorm
  exact div_nonneg (sub_nonneg.mpr hre) (Nat.cast_nonneg p)

/-- The finite distance is exactly mass minus correlation. -/
theorem characterTwistDistSq_eq_mass_sub_correlation {q q' : ℕ}
    (χ : DirichletCharacter ℂ q) (χ' : DirichletCharacter ℂ q')
    (v : ℝ) (Y : ℕ) :
    characterTwistDistSq χ χ' v Y =
      characterTwistPrimeMass Y - characterTwistPrimeCorrelation χ χ' v Y := by
  simp only [characterTwistDistSq, characterTwistPrimeMass,
    characterTwistPrimeCorrelation]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast (mem_primesUpTo.mp hp).1.ne_zero
  rw [inv_eq_one_div]
  field_simp [hp0]

/-- Any finite upper estimate for the prime correlation immediately gives a lower estimate for
the squared twist distance. -/
theorem characterTwistDistSq_lower_of_correlation_upper {q q' : ℕ}
    (χ : DirichletCharacter ℂ q) (χ' : DirichletCharacter ℂ q')
    (v : ℝ) (Y : ℕ) (R : ℝ)
    (hcorr : characterTwistPrimeCorrelation χ χ' v Y ≤
      characterTwistPrimeMass Y - R) :
    R ≤ characterTwistDistSq χ χ' v Y := by
  rw [characterTwistDistSq_eq_mass_sub_correlation]
  linarith

/-! ## Compatibility with the pretentious-distance definitions -/

theorem characterTwistPhase_eq_twist_mul_conj_twist {q q' n : ℕ}
    (χ : DirichletCharacter ℂ q) (χ' : DirichletCharacter ℂ q')
    (t t' : ℝ) (hn : 0 < n) :
    characterTwistPhase χ χ' (t' - t) n =
      dirichletArchimedeanTwist χ t n *
        conj (dirichletArchimedeanTwist χ' t' n) := by
  rw [characterTwistPhase, dirichletArchimedeanTwist,
    dirichletArchimedeanTwist, map_mul, conj_archimedeanTwist]
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hpow :
      (n : ℂ) ^ (-(Complex.I * ((t' - t : ℝ) : ℂ))) =
        archimedeanTwist t n *
          (n : ℂ) ^ (-(Complex.I * (t' : ℂ))) := by
    unfold archimedeanTwist
    rw [← Complex.cpow_add (Complex.I * (t : ℂ))
      (-(Complex.I * (t' : ℂ))) hn0]
    congr 1
    push_cast
    ring
  rw [hpow]
  ring

theorem characterTwistDistSq_eq_pretentiousDistSq {q q' : ℕ}
    (χ : DirichletCharacter ℂ q) (χ' : DirichletCharacter ℂ q')
    (t t' : ℝ) (Y : ℕ) :
    characterTwistDistSq χ χ' (t' - t) Y =
      pretentiousDistSq
        (dirichletArchimedeanTwist χ t)
        (dirichletArchimedeanTwist χ' t') Y := by
  simp only [characterTwistDistSq, pretentiousDistSq, pretentiousTerm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [characterTwistPhase_eq_twist_mul_conj_twist χ χ' t t'
    (mem_primesUpTo.mp hp).1.pos]

theorem characterTwistDistSq_eq_pretentiousDistSqToTwist {q q' : ℕ}
    (χ : DirichletCharacter ℂ q) (χ' : DirichletCharacter ℂ q')
    (t t' : ℝ) (Y : ℕ) :
    characterTwistDistSq χ χ' (t' - t) Y =
      pretentiousDistSqToTwist (dirichletArchimedeanTwist χ t) χ' t' Y :=
  characterTwistDistSq_eq_pretentiousDistSq χ χ' t t' Y

/-! ## Mertens normalization -/

theorem characterTwistPrimeMass_eq_primeReciprocals (Y : ℕ) :
    characterTwistPrimeMass Y = PrimeEstimates.primeReciprocals Y := by
  unfold characterTwistPrimeMass PrimeEstimates.primeReciprocals
    Erdos784.Analytic.primeReciprocals primesUpTo
  rw [Nat.primesLE_eq_filter_range]

theorem characterTwistPrimeMass_mertens_lower {Y : ℕ} (hY : 2 ≤ Y) :
    Real.log (Real.log (Y : ℝ)) - PrimeEstimates.mertensBound ≤
      characterTwistPrimeMass Y := by
  rw [characterTwistPrimeMass_eq_primeReciprocals]
  have h := PrimeEstimates.abs_primeReciprocals_sub_log_log_le hY
  rw [abs_le] at h
  linarith

/-- A correlation upper bound with coefficient `11/12` gives the positive `1/12` Mertens
separation, with the two bounded Mertens errors displayed explicitly. -/
theorem characterTwistDistSq_lower_of_correlation_loglog {q q' Y : ℕ}
    (χ : DirichletCharacter ℂ q) (χ' : DirichletCharacter ℂ q')
    (v : ℝ) (hY : 2 ≤ Y)
    (hcorr : characterTwistPrimeCorrelation χ χ' v Y ≤
      (11 / 12 : ℝ) * Real.log (Real.log (Y : ℝ)) +
        PrimeEstimates.mertensBound) :
    (1 / 12 : ℝ) * Real.log (Real.log (Y : ℝ)) -
        2 * PrimeEstimates.mertensBound ≤
      characterTwistDistSq χ χ' v Y := by
  rw [characterTwistDistSq_eq_mass_sub_correlation]
  have hmass := characterTwistPrimeMass_mertens_lower hY
  linarith

/-! ## The exact two-scale deterministic consumer -/

/-- A uniform lower bound `4 A` for separated character twists implies the
two-scale frequency conclusion used by `Section4Probability`.  The
unit-disk triangle inequality above handles the conductor primes directly;
there is no hidden assumption that a Dirichlet character has unit norm at
those primes. -/
theorem twoScaleTwistSeparationConclusion_of_characterTwistDistSq_lower
    {A Y D : ℕ} (hY : 2 ≤ Y) (hD : 0 < D)
    (hsep : ∀ (q : ℕ), 0 < q → q ≤ A →
      ∀ (χ : DirichletCharacter ℂ q),
      ∀ (q' : ℕ), 0 < q' → q' ≤ A →
      ∀ (χ' : DirichletCharacter ℂ q') (v : ℝ),
        (Y : ℝ) ≤ |v| →
        |v| ≤ (2 * A : ℕ) * (Y ^ D : ℕ) →
        (4 * A : ℕ) ≤ characterTwistDistSq χ χ' v Y) :
    TwoScaleTwistSeparationConclusion A Y D := by
  have hYone : 1 ≤ Y := one_le_two.trans hY
  have hYpow : Y ≤ Y ^ D := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hD.ne'
    rw [pow_succ]
    calc
      Y = 1 * Y := by simp
      _ ≤ Y ^ d * Y := Nat.mul_le_mul_right Y (one_le_pow₀ hYone)
  intro g q hq hqA χ t ht hdist q' hq' hq'A χ' t' ht' hdist'
  by_contra hv
  have hvLower : (Y : ℝ) ≤ |t' - t| := le_of_not_gt hv
  have hvUpper : |t' - t| ≤ (2 * A : ℕ) * (Y ^ D : ℕ) := by
    calc
      |t' - t| ≤ |t'| + |t| := abs_sub t' t
      _ ≤ (A : ℝ) * Y + (A : ℝ) * (Y ^ D : ℕ) :=
        add_le_add ht' ht
      _ ≤ (A : ℝ) * (Y ^ D : ℕ) +
          (A : ℝ) * (Y ^ D : ℕ) := by
        gcongr
      _ = (2 * A : ℕ) * (Y ^ D : ℕ) := by
        push_cast
        ring
  have hfUnit : ∀ p : ℕ, p.Prime →
      ‖compactCharacterNatValue g p‖ = 1 :=
    fun p hp ↦ norm_compactCharacterNatValue g hp.pos
  have hfDisk : ∀ p : ℕ, p.Prime →
      ‖compactCharacterNatValue g p‖ ≤ 1 :=
    fun p hp ↦ (hfUnit p hp).le
  have hlargeAtY :
      pretentiousDistSqToTwist (compactCharacterNatValue g) χ t Y < A :=
    (pretentiousDistSqToTwist_mono χ t hYpow hfDisk).trans_lt hdist
  have htriangle :
      pretentiousDistSq (dirichletArchimedeanTwist χ t)
          (dirichletArchimedeanTwist χ' t') Y < (4 : ℝ) * A := by
    have hle := pretentiousDistSq_triangle_sq_left_unit
      (f := compactCharacterNatValue g)
      (g := dirichletArchimedeanTwist χ t)
      (h := dirichletArchimedeanTwist χ' t')
      (x := Y)
      hfUnit
      (fun p hp ↦ norm_dirichletArchimedeanTwist_le_one χ t hp.pos)
      (fun p hp ↦ norm_dirichletArchimedeanTwist_le_one χ' t' hp.pos)
    dsimp only [pretentiousDistSqToTwist] at hlargeAtY hdist'
    calc
      pretentiousDistSq (dirichletArchimedeanTwist χ t)
          (dirichletArchimedeanTwist χ' t') Y ≤
          2 * (pretentiousDistSq (compactCharacterNatValue g)
            (dirichletArchimedeanTwist χ t) Y +
            pretentiousDistSq (compactCharacterNatValue g)
              (dirichletArchimedeanTwist χ' t') Y) := hle
      _ < (4 : ℝ) * A := by nlinarith
  have hlower := hsep q hq hqA χ q' hq' hq'A χ'
    (t' - t) hvLower hvUpper
  rw [characterTwistDistSq_eq_pretentiousDistSq χ χ' t t'] at hlower
  push_cast at hlower
  exact (not_lt_of_ge hlower) htriangle

/-! ## Exact polynomial-height analytic interface -/

/-- The uniform, fully finite prime-correlation estimate needed to separate two bounded-
conductor character twists in Tao's Lemma 4.1.

The quantifier order is important: `Y₀` may depend on `Q`, `D`, and `T`, but not on either
modulus, either character, the endpoint `Y`, or the frequency `v`.  The use of natural powers
in the upper range keeps the statement free of rounding conventions.

This is a definition of the missing analytic proposition, not an assumption and not a theorem.
Its expected proof is the logarithmic-derivative argument in the Vinogradov--Korobov zero-free
region, followed by removal of prime powers. -/
def PolynomialHeightPrimeCorrelationBound (Q D : ℕ) (T : ℝ) : Prop :=
  ∃ Y₀ : ℕ, 2 ≤ Y₀ ∧
    ∀ (Y q q' : ℕ), Y₀ ≤ Y → 0 < q → q ≤ Q → 0 < q' → q' ≤ Q →
      ∀ (χ : DirichletCharacter ℂ q) (χ' : DirichletCharacter ℂ q') (v : ℝ),
        (Y : ℝ) ≤ |v| → |v| ≤ T * (Y : ℝ) ^ D →
          characterTwistPrimeCorrelation χ χ' v Y ≤
            (11 / 12 : ℝ) * Real.log (Real.log (Y : ℝ)) +
              PrimeEstimates.mertensBound

/-- Once the finite polynomial-height prime-correlation estimate is supplied, the bounded-
conductor twist separation has no further analytic content. -/
theorem polynomialHeight_characterTwistDistSq_lower
    {Q D : ℕ} {T : ℝ} (hVK : PolynomialHeightPrimeCorrelationBound Q D T) :
    ∃ Y₀ : ℕ, 2 ≤ Y₀ ∧
      ∀ (Y q q' : ℕ), Y₀ ≤ Y → 0 < q → q ≤ Q → 0 < q' → q' ≤ Q →
        ∀ (χ : DirichletCharacter ℂ q) (χ' : DirichletCharacter ℂ q') (v : ℝ),
          (Y : ℝ) ≤ |v| → |v| ≤ T * (Y : ℝ) ^ D →
            (1 / 12 : ℝ) * Real.log (Real.log (Y : ℝ)) -
                2 * PrimeEstimates.mertensBound ≤
              characterTwistDistSq χ χ' v Y := by
  rcases hVK with ⟨Y₀, hY₀, hcorr⟩
  refine ⟨Y₀, hY₀, ?_⟩
  intro Y q q' hY hq hqQ hq' hq'Q χ χ' v hvLower hvUpper
  exact characterTwistDistSq_lower_of_correlation_loglog χ χ' v
    (hY₀.trans hY)
    (hcorr Y q q' hY hq hqQ hq' hq'Q χ χ' v hvLower hvUpper)

/-- The polynomial-height prime-correlation estimate, once proved, supplies
the exact two-scale conclusion eventually and uniformly in both bounded
characters.  This theorem fixes all quantifier-order and conductor-prime
bookkeeping around the remaining analytic estimate. -/
theorem eventually_twoScaleTwistSeparationConclusion_of_polynomialHeightBound
    {A D : ℕ} (hD : 0 < D)
    (hVK : PolynomialHeightPrimeCorrelationBound A D (2 * A : ℕ)) :
    ∃ Y₀ : ℕ, 2 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      TwoScaleTwistSeparationConclusion A Y D := by
  obtain ⟨YVK, hYVK, hdist⟩ :=
    polynomialHeight_characterTwistDistSq_lower hVK
  have hloglog : Filter.Tendsto
      (fun Y : ℕ ↦ Real.log (Real.log (Y : ℝ)))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hevent : ∀ᶠ Y : ℕ in Filter.atTop,
      12 * ((4 : ℝ) * A + 2 * PrimeEstimates.mertensBound) ≤
        Real.log (Real.log (Y : ℝ)) :=
    (Filter.tendsto_atTop.1 hloglog
      (12 * ((4 : ℝ) * A + 2 * PrimeEstimates.mertensBound)))
  obtain ⟨N, hN⟩ := (Filter.eventually_atTop.1 hevent)
  let Y₀ := max YVK (max 2 N)
  refine ⟨Y₀, (le_max_left 2 N).trans (le_max_right YVK (max 2 N)), ?_⟩
  intro Y hY
  have hYVKY : YVK ≤ Y := (le_max_left _ _).trans hY
  have hNY : N ≤ Y :=
    (le_max_right 2 N).trans ((le_max_right YVK (max 2 N)).trans hY)
  have hYY : 2 ≤ Y :=
    (le_max_left 2 N).trans ((le_max_right YVK (max 2 N)).trans hY)
  have hthreshold :
      (4 : ℝ) * A ≤
        (1 / 12 : ℝ) * Real.log (Real.log (Y : ℝ)) -
          2 * PrimeEstimates.mertensBound := by
    have := hN Y hNY
    nlinarith [PrimeEstimates.mertensBound_nonneg]
  apply twoScaleTwistSeparationConclusion_of_characterTwistDistSq_lower hYY hD
  intro q hq hqA χ q' hq' hq'A χ' v hvLower hvUpper
  have hlower := hdist Y q q' hYVKY hq hqA hq' hq'A χ χ' v
    hvLower (by simpa using hvUpper)
  push_cast
  exact hthreshold.trans hlower

end

end Erdos67
