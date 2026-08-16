import Wikipedia.GreenTao.Sieve.ComplexZetaModelComparison
import Wikipedia.GreenTao.Sieve.ZetaEulerProductIdentification

/-!
# The complex arithmetic Euler product as zeta model times correction

`ComplexZetaModelComparison` proves, at every sufficiently large prime, that
the exact affine-system local factor divided by its zeta Euler model is
`1 + O_m(p⁻²)`.  This file promotes that local estimate to an unordered
Euler product.

There are three small points which are made explicit here.

* The exceptional cutoff contains both the finite affine-rank exceptional
  set and the quantitative nonvanishing range for the zeta model.
* The zeta model is in fact nonzero at every prime.  Consequently the
  arithmetic/zeta ratio is defined by honest cancellation at all primes.
* Replacing the finitely many uncontrolled ratios by one gives a globally
  square-decaying family.  The cutoff also makes every remaining ratio
  lie in the radius-`1/2` ball around one, so the masked family is
  pointwise nonzero.  Mathlib's finite-change theorem for products in a
  commutative group-with-zero then restores the exceptional factors.

Combining the resulting correction product with
`cutoffZetaEulerLocalFactor_hasProd` identifies the exact arithmetic prime
product as

`(elementary singular factor) * (completed zeta factor) *
  (convergent arithmetic correction)`.

No nonvanishing assertion is made for the correction without an explicit
nonvanishing hypothesis on the arithmetic local factors: a complex finite
average can in principle vanish.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter
open scoped BigOperators

/-! ## Prime-indexed local factors and the common cutoff -/

/-- Natural-valued copy of the arithmetic/zeta ratio error constant. -/
def complexArithmeticZetaRatioErrorNat (m : ℕ) : ℕ :=
  4 * (4 ^ m + complexZetaModelDifferenceNat m)

theorem complexArithmeticZetaRatioErrorConstant_eq_natCast
    (m : ℕ) :
    complexArithmeticZetaRatioErrorConstant m =
      (complexArithmeticZetaRatioErrorNat m : ℝ) := by
  rw [complexArithmeticZetaRatioErrorConstant,
    complexArithmeticZetaDifferenceConstant,
    complexZetaModelDifferenceConstant_eq_natCast,
    complexArithmeticZetaRatioErrorNat]
  push_cast
  ring

/-- A cutoff which both makes the zeta denominator nonzero and makes the
arithmetic/zeta ratio lie in the radius-`1/2` ball around one. -/
def complexArithmeticZetaRatioNonzeroCutoff (m : ℕ) : ℕ :=
  max
    (complexZetaModelNonzeroCutoff m)
    (2 * complexArithmeticZetaRatioErrorNat m)

/-- A cutoff containing both the affine rank exceptions and the
quantitative nonvanishing range used in the local ratio estimate. -/
def complexArithmeticZetaExceptionalBound
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (forms : κ → AffineForm ι ℤ) : ℕ :=
  max
    (exceptionalPrimeBound forms)
    (complexArithmeticZetaRatioNonzeroCutoff
      (Fintype.card κ))

/-- The exact paired Fourier local factor, indexed by the subtype of
natural primes. -/
noncomputable def pairedFourierPrimeLocalFactor
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (R : ℕ) (forms : κ → AffineForm ι ℤ)
    (t u : κ → ℝ) (p : Nat.Primes) : ℂ := by
  letI : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  exact pairedFourierLocalFactor R (p : ℕ) forms t u

/-- The exact arithmetic/zeta local ratio, indexed by natural primes. -/
noncomputable def primePairedFourierArithmeticToZetaLocalRatio
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (R : ℕ) (forms : κ → AffineForm ι ℤ)
    (t u : κ → ℝ) (p : Nat.Primes) : ℂ := by
  letI : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  exact pairedFourierArithmeticToZetaLocalRatio
    R (p : ℕ) forms t u

/-- The zeta Euler factor from `ZetaEulerProductIdentification` is exactly
the finite-system zeta factor used in the local comparison file. -/
theorem cutoffZetaEulerLocalFactor_eq_fourierZetaSystemEulerLocalFactor
    {κ : Type*} [Fintype κ]
    (R : ℕ) (t u : κ → ℝ) (p : Nat.Primes) :
    cutoffZetaEulerLocalFactor R t u p =
      fourierZetaSystemEulerLocalFactor R (p : ℕ) t u := by
  classical
  simp only [cutoffZetaEulerLocalFactor,
    zetaSystemEulerLocalFactor,
    zetaPairEulerLocalFactor,
    fourierZetaSystemEulerLocalFactor,
    fourierPairZetaEulerLocalFactor,
    pairedZetaEulerLocalFactor,
    div_eq_mul_inv]

/-! ## Pointwise nonvanishing of the zeta model -/

/-- A single numerator `1 - p⁻¹z` cannot vanish at a prime when `z` lies
in the closed unit ball. -/
theorem phaseZetaNumerator_ne_zero
    {p : ℕ} (hp : p.Prime)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    1 - (p : ℂ)⁻¹ * z ≠ 0 := by
  have hpR : 0 < (p : ℝ) := by
    exact_mod_cast hp.pos
  have hsmall :
      ‖(p : ℂ)⁻¹ * z‖ ≤ (1 : ℝ) / 2 := by
    calc
      ‖(p : ℂ)⁻¹ * z‖ =
          (1 / (p : ℝ)) * ‖z‖ := by
        rw [norm_mul, norm_inv, Complex.norm_natCast]
        ring
      _ ≤ (1 / (p : ℝ)) * 1 := by
        exact mul_le_mul_of_nonneg_left hz
          (one_div_nonneg.mpr hpR.le)
      _ ≤ (1 : ℝ) / 2 := by
        simp only [mul_one]
        rw [div_le_iff₀ hpR]
        have hp2R : (2 : ℝ) ≤ (p : ℝ) := by
          exact_mod_cast hp.two_le
        nlinarith
  intro hzero
  have heq :
      (1 : ℂ) = (p : ℂ)⁻¹ * z :=
    sub_eq_zero.mp hzero
  have hnorm := congrArg norm heq
  rw [norm_one] at hnorm
  linarith

/-- A one-pair phase-coordinate zeta Euler factor is nonzero. -/
theorem phasePairZetaEulerLocalModel_ne_zero
    {p : ℕ} (hp : p.Prime)
    {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    phasePairZetaEulerLocalModel p z w ≠ 0 := by
  rw [phasePairZetaEulerLocalModel]
  exact div_ne_zero
    (mul_ne_zero
      (phaseZetaNumerator_ne_zero hp hz)
      (phaseZetaNumerator_ne_zero hp hw))
    (phasePairZetaDenominator_ne_zero hp hz hw)

/-- Every one-pair zeta factor at the exact Fourier shifts is nonzero. -/
theorem fourierPairZetaEulerLocalFactor_ne_zero
    {R : ℕ} (hR : 2 ≤ R)
    (p : Nat.Primes) (t u : ℝ) :
    fourierPairZetaEulerLocalFactor R (p : ℕ) t u ≠ 0 := by
  rw [fourierPairZetaEulerLocalFactor_eq_phase
    (by omega) p.prop]
  exact phasePairZetaEulerLocalModel_ne_zero
    p.prop
    (SmoothSieveCutoff.norm_divisorMultiplicativePhase_le_one
      hR p.prop t)
    (SmoothSieveCutoff.norm_divisorMultiplicativePhase_le_one
      hR p.prop u)

/-- The finite-system zeta model is nonzero at every prime. -/
theorem fourierZetaSystemEulerLocalFactor_ne_zero
    {κ : Type*} [Fintype κ]
    {R : ℕ} (hR : 2 ≤ R)
    (p : Nat.Primes) (t u : κ → ℝ) :
    fourierZetaSystemEulerLocalFactor
      R (p : ℕ) t u ≠ 0 := by
  classical
  rw [fourierZetaSystemEulerLocalFactor]
  apply Finset.prod_ne_zero_iff.mpr
  intro q _hq
  exact fourierPairZetaEulerLocalFactor_ne_zero
    hR p (t q) (u q)

/-- The prime-indexed zeta family used by the global Euler-product theorem
is nonzero at every prime. -/
theorem cutoffZetaEulerLocalFactor_ne_zero
    {κ : Type*} [Fintype κ]
    {R : ℕ} (hR : 2 ≤ R)
    (t u : κ → ℝ) (p : Nat.Primes) :
    cutoffZetaEulerLocalFactor R t u p ≠ 0 := by
  rw [cutoffZetaEulerLocalFactor_eq_fourierZetaSystemEulerLocalFactor]
  exact fourierZetaSystemEulerLocalFactor_ne_zero
    hR p t u

/-! ## Square decay and the convergent correction product -/

/-- Explicit good-prime square-error estimate for the arithmetic/zeta
ratio. -/
theorem norm_primePairedFourierArithmeticToZetaLocalRatio_sub_one_le
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    (hindependent : PairwiseIndependentCoefficients forms)
    {R : ℕ} (hR : 2 ≤ R)
    (t u : κ → ℝ) (p : Nat.Primes)
    (hlarge :
      complexArithmeticZetaExceptionalBound forms <
        (p : ℕ)) :
    ‖primePairedFourierArithmeticToZetaLocalRatio
          R forms t u p - 1‖ ≤
      complexArithmeticZetaRatioErrorConstant
          (Fintype.card κ) /
        (p : ℝ) ^ 2 := by
  letI : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  have hexceptional :
      exceptionalPrimeBound forms < (p : ℕ) :=
    (Nat.le_max_left
      (exceptionalPrimeBound forms)
      (complexArithmeticZetaRatioNonzeroCutoff
        (Fintype.card κ))).trans_lt hlarge
  have hcut :
      complexZetaModelNonzeroCutoff
          (Fintype.card κ) ≤
        (p : ℕ) :=
    (Nat.le_max_left
      (complexZetaModelNonzeroCutoff
        (Fintype.card κ))
      (2 * complexArithmeticZetaRatioErrorNat
        (Fintype.card κ))).trans
      ((Nat.le_max_right
        (exceptionalPrimeBound forms)
        (complexArithmeticZetaRatioNonzeroCutoff
          (Fintype.card κ))).trans hlarge.le)
  simpa [primePairedFourierArithmeticToZetaLocalRatio] using
    (norm_pairedFourierArithmeticToZetaLocalRatio_sub_one_le
      hnonzero hindependent hR p.prop
      hexceptional hcut t u)

/-- Every ratio above the explicit cutoff is nonzero; quantitatively it
lies within distance `1/2` of one. -/
theorem primePairedFourierArithmeticToZetaLocalRatio_ne_zero_of_bound
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    (hindependent : PairwiseIndependentCoefficients forms)
    {R : ℕ} (hR : 2 ≤ R)
    (t u : κ → ℝ) (p : Nat.Primes)
    (hlarge :
      complexArithmeticZetaExceptionalBound forms <
        (p : ℕ)) :
    primePairedFourierArithmeticToZetaLocalRatio
      R forms t u p ≠ 0 := by
  have herror :=
    norm_primePairedFourierArithmeticToZetaLocalRatio_sub_one_le
      hnonzero hindependent hR t u p hlarge
  have hcutNat :
      2 * complexArithmeticZetaRatioErrorNat
          (Fintype.card κ) ≤
        (p : ℕ) :=
    (Nat.le_max_right
      (complexZetaModelNonzeroCutoff
        (Fintype.card κ))
      (2 * complexArithmeticZetaRatioErrorNat
        (Fintype.card κ))).trans
      ((Nat.le_max_right
        (exceptionalPrimeBound forms)
        (complexArithmeticZetaRatioNonzeroCutoff
          (Fintype.card κ))).trans hlarge.le)
  have hpR : 0 < (p : ℝ) := by
    exact_mod_cast p.prop.pos
  have hpOne : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast p.prop.one_le
  have hpSq :
      (p : ℝ) ≤ (p : ℝ) ^ 2 := by
    nlinarith
  have hcutReal :
      2 *
          (complexArithmeticZetaRatioErrorNat
            (Fintype.card κ) : ℝ) ≤
        (p : ℝ) := by
    exact_mod_cast hcutNat
  have hsmall :
      complexArithmeticZetaRatioErrorConstant
            (Fintype.card κ) /
          (p : ℝ) ^ 2 ≤
        (1 : ℝ) / 2 := by
    rw [complexArithmeticZetaRatioErrorConstant_eq_natCast]
    rw [div_le_iff₀ (sq_pos_of_pos hpR)]
    nlinarith
  have hhalf := herror.trans hsmall
  intro hzero
  rw [hzero] at hhalf
  norm_num at hhalf

/-- After replacing the finite exceptional range by one, the
arithmetic/zeta ratios satisfy a global `O_m(p⁻²)` estimate. -/
theorem hasComplexPrimeSquareError_primeArithmeticZetaRatio
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    (hindependent : PairwiseIndependentCoefficients forms)
    {R : ℕ} (hR : 2 ≤ R)
    (t u : κ → ℝ) :
    HasComplexPrimeSquareError
      (complexArithmeticZetaRatioErrorConstant
        (Fintype.card κ))
      (boundedMaskedComplexPrimeLocalFactor
        (complexArithmeticZetaExceptionalBound forms)
        (primePairedFourierArithmeticToZetaLocalRatio
          R forms t u)) := by
  exact hasComplexPrimeSquareError_boundedMasked
    (complexArithmeticZetaExceptionalBound forms)
    (complexArithmeticZetaRatioErrorConstant_nonneg
      (Fintype.card κ))
    (fun p hp =>
      norm_primePairedFourierArithmeticToZetaLocalRatio_sub_one_le
        hnonzero hindependent hR t u p hp)

/-- The controlled, masked arithmetic correction Euler product is
multipliable. -/
theorem multipliable_boundedMasked_primeArithmeticZetaRatio
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    (hindependent : PairwiseIndependentCoefficients forms)
    {R : ℕ} (hR : 2 ≤ R)
    (t u : κ → ℝ) :
    Multipliable
      (boundedMaskedComplexPrimeLocalFactor
        (complexArithmeticZetaExceptionalBound forms)
        (primePairedFourierArithmeticToZetaLocalRatio
          R forms t u)) :=
  (hasComplexPrimeSquareError_primeArithmeticZetaRatio
    hnonzero hindependent hR t u).multipliable

/-- Every factor in the masked correction family is nonzero. -/
theorem boundedMasked_primeArithmeticZetaRatio_ne_zero
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    (hindependent : PairwiseIndependentCoefficients forms)
    {R : ℕ} (hR : 2 ≤ R)
    (t u : κ → ℝ) (p : Nat.Primes) :
    boundedMaskedComplexPrimeLocalFactor
        (complexArithmeticZetaExceptionalBound forms)
        (primePairedFourierArithmeticToZetaLocalRatio
          R forms t u) p ≠ 0 := by
  by_cases hp :
      (p : ℕ) ≤
        complexArithmeticZetaExceptionalBound forms
  · rw [boundedMaskedComplexPrimeLocalFactor_of_le hp]
    exact one_ne_zero
  · have hlarge :
        complexArithmeticZetaExceptionalBound forms <
          (p : ℕ) :=
      Nat.lt_of_not_ge hp
    rw [boundedMaskedComplexPrimeLocalFactor_of_lt hlarge]
    exact
      primePairedFourierArithmeticToZetaLocalRatio_ne_zero_of_bound
        hnonzero hindependent hR t u p hlarge

/-- Only finitely many natural primes lie below a fixed numerical bound.
This is the finite-change input used to restore the exceptional local
ratios. -/
theorem finite_setOf_prime_le (B : ℕ) :
    {p : Nat.Primes | (p : ℕ) ≤ B}.Finite := by
  let e : Nat.Primes ↪ ℕ :=
    ⟨fun p => (p : ℕ), Subtype.coe_injective⟩
  change (e ⁻¹' Set.Iic B).Finite
  exact (Set.finite_Iic B).preimage_embedding e

/-- The masked and unmasked ratios agree away from a finite set. -/
theorem boundedMasked_primeArithmeticZetaRatio_eventuallyEq
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (R : ℕ) (forms : κ → AffineForm ι ℤ)
    (t u : κ → ℝ) :
    boundedMaskedComplexPrimeLocalFactor
        (complexArithmeticZetaExceptionalBound forms)
        (primePairedFourierArithmeticToZetaLocalRatio
          R forms t u) =ᶠ[cofinite]
      primePairedFourierArithmeticToZetaLocalRatio
        R forms t u := by
  have hfinite :=
    finite_setOf_prime_le
      (complexArithmeticZetaExceptionalBound forms)
  filter_upwards [hfinite.eventually_cofinite_notMem]
    with p hp
  have hnot :
      ¬(p : ℕ) ≤
        complexArithmeticZetaExceptionalBound forms := by
    simpa only [Set.mem_setOf_eq] using hp
  exact boundedMaskedComplexPrimeLocalFactor_of_lt
    (Nat.lt_of_not_ge hnot)

/-- Restoring the finitely many exceptional ratios preserves
multipliability. -/
theorem multipliable_primePairedFourierArithmeticToZetaLocalRatio
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    (hindependent : PairwiseIndependentCoefficients forms)
    {R : ℕ} (hR : 2 ≤ R)
    (t u : κ → ℝ) :
    Multipliable
      (primePairedFourierArithmeticToZetaLocalRatio
        R forms t u) := by
  let ratio : Nat.Primes → ℂ :=
    primePairedFourierArithmeticToZetaLocalRatio
      R forms t u
  let masked : Nat.Primes → ℂ :=
    boundedMaskedComplexPrimeLocalFactor
      (complexArithmeticZetaExceptionalBound forms) ratio
  have hmasked : Multipliable masked := by
    simpa only [masked, ratio] using
      multipliable_boundedMasked_primeArithmeticZetaRatio
        hnonzero hindependent hR t u
  have hevent : masked =ᶠ[cofinite] ratio := by
    simpa only [masked, ratio] using
      boundedMasked_primeArithmeticZetaRatio_eventuallyEq
        R forms t u
  change Multipliable ratio
  apply hmasked.congr_cofinite₀
  · intro p
    simpa only [masked, ratio] using
      boundedMasked_primeArithmeticZetaRatio_ne_zero
        hnonzero hindependent hR t u p
  · exact hevent

/-- The norms of the unmasked ratio errors are summable.  The uniform
`O_m(p⁻²)` bound is used outside the explicit cutoff; the remaining terms
form a finite modification. -/
theorem summable_norm_primePairedFourierArithmeticToZetaLocalRatio_sub_one
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    (hindependent : PairwiseIndependentCoefficients forms)
    {R : ℕ} (hR : 2 ≤ R)
    (t u : κ → ℝ) :
    Summable
      (fun p : Nat.Primes =>
        ‖primePairedFourierArithmeticToZetaLocalRatio
            R forms t u p - 1‖) := by
  have hmasked :=
    (hasComplexPrimeSquareError_primeArithmeticZetaRatio
      hnonzero hindependent hR t u).summable_norm_error
  apply hmasked.congr_cofinite
  filter_upwards
    [boundedMasked_primeArithmeticZetaRatio_eventuallyEq
      R forms t u]
    with p hp
  rw [hp]

/-- Canonical `HasProd` statement for the convergent arithmetic
correction. -/
theorem primePairedFourierArithmeticToZetaLocalRatio_hasProd
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    (hindependent : PairwiseIndependentCoefficients forms)
    {R : ℕ} (hR : 2 ≤ R)
    (t u : κ → ℝ) :
    HasProd
      (primePairedFourierArithmeticToZetaLocalRatio
        R forms t u)
      (∏' p : Nat.Primes,
        primePairedFourierArithmeticToZetaLocalRatio
          R forms t u p) :=
  (multipliable_primePairedFourierArithmeticToZetaLocalRatio
    hnonzero hindependent hR t u).hasProd

/-! ## Exact global Euler-product identification -/

/-- At every prime, the zeta factor times the arithmetic/zeta ratio is
the exact arithmetic local factor. -/
theorem cutoffZetaEulerLocalFactor_mul_primeArithmeticZetaRatio
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {R : ℕ} (hR : 2 ≤ R)
    (forms : κ → AffineForm ι ℤ)
    (t u : κ → ℝ) (p : Nat.Primes) :
    cutoffZetaEulerLocalFactor R t u p *
        primePairedFourierArithmeticToZetaLocalRatio
          R forms t u p =
      pairedFourierPrimeLocalFactor
        R forms t u p := by
  letI : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  have hzeta :
      fourierZetaSystemEulerLocalFactor
          R (p : ℕ) t u ≠ 0 :=
    fourierZetaSystemEulerLocalFactor_ne_zero
      hR p t u
  rw [cutoffZetaEulerLocalFactor_eq_fourierZetaSystemEulerLocalFactor,
    primePairedFourierArithmeticToZetaLocalRatio,
    pairedFourierPrimeLocalFactor,
    pairedFourierArithmeticToZetaLocalRatio,
    mul_comm,
    div_mul_cancel₀ _ hzeta]

/-- The exact affine-system local factors have an unordered Euler product,
identified as the finite zeta quotient times the convergent arithmetic
correction. -/
theorem pairedFourierPrimeLocalFactor_hasProd
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    (hindependent : PairwiseIndependentCoefficients forms)
    {R : ℕ} (hR : 2 ≤ R)
    (t u : κ → ℝ) :
    HasProd
      (pairedFourierPrimeLocalFactor
        R forms t u)
      ((cutoffZetaSingularFactor R t u *
          cutoffZetaSystemFactor R t u) *
        ∏' p : Nat.Primes,
          primePairedFourierArithmeticToZetaLocalRatio
            R forms t u p) := by
  have hzeta :=
    cutoffZetaEulerLocalFactor_hasProd
      (show 1 < R by omega) t u
  have hratio :=
    primePairedFourierArithmeticToZetaLocalRatio_hasProd
      hnonzero hindependent hR t u
  refine (hzeta.mul hratio).congr_fun ?_
  intro p
  exact
    (cutoffZetaEulerLocalFactor_mul_primeArithmeticZetaRatio
      hR forms t u p).symm

/-- `tprod` form of the arithmetic Euler-product identification. -/
theorem tprod_pairedFourierPrimeLocalFactor_eq
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    (hindependent : PairwiseIndependentCoefficients forms)
    {R : ℕ} (hR : 2 ≤ R)
    (t u : κ → ℝ) :
    (∏' p : Nat.Primes,
        pairedFourierPrimeLocalFactor
          R forms t u p) =
      (cutoffZetaSingularFactor R t u *
          cutoffZetaSystemFactor R t u) *
        ∏' p : Nat.Primes,
          primePairedFourierArithmeticToZetaLocalRatio
            R forms t u p :=
  (pairedFourierPrimeLocalFactor_hasProd
    hnonzero hindependent hR t u).tprod_eq

/-- Conditional nonvanishing of the correction product.  The condition is
kept explicit because the exact complex arithmetic local factors are
finite averages and no unconditional nonvanishing theorem is available. -/
theorem tprod_primePairedFourierArithmeticToZetaLocalRatio_ne_zero
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    (hindependent : PairwiseIndependentCoefficients forms)
    {R : ℕ} (hR : 2 ≤ R)
    (t u : κ → ℝ)
    (hlocal :
      ∀ p : Nat.Primes,
        pairedFourierPrimeLocalFactor
          R forms t u p ≠ 0) :
    (∏' p : Nat.Primes,
        primePairedFourierArithmeticToZetaLocalRatio
          R forms t u p) ≠ 0 := by
  have hratio :
      ∀ p : Nat.Primes,
        primePairedFourierArithmeticToZetaLocalRatio
          R forms t u p ≠ 0 := by
    intro p
    letI : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
    rw [primePairedFourierArithmeticToZetaLocalRatio,
      pairedFourierArithmeticToZetaLocalRatio]
    exact div_ne_zero
      (by simpa [pairedFourierPrimeLocalFactor] using hlocal p)
      (fourierZetaSystemEulerLocalFactor_ne_zero
        hR p t u)
  have hprod :=
    tprod_one_add_ne_zero_of_summable
      (f := fun p : Nat.Primes =>
        primePairedFourierArithmeticToZetaLocalRatio
          R forms t u p - 1)
      (fun p => by
        rw [show
          1 +
              (primePairedFourierArithmeticToZetaLocalRatio
                R forms t u p - 1) =
            primePairedFourierArithmeticToZetaLocalRatio
              R forms t u p by ring]
        exact hratio p)
      (summable_norm_primePairedFourierArithmeticToZetaLocalRatio_sub_one
        hnonzero hindependent hR t u)
  have heq :
      (fun p : Nat.Primes =>
        1 +
          (primePairedFourierArithmeticToZetaLocalRatio
            R forms t u p - 1)) =
        primePairedFourierArithmeticToZetaLocalRatio
          R forms t u := by
    funext p
    ring
  rw [heq] at hprod
  exact hprod

end Wikipedia.SzemeredisTheorem
