import Wikipedia.GreenTao.Sieve.CFZCanonicalCarryEulerBridge
import Wikipedia.GreenTao.Sieve.UnrestrictedPrimeSupportEulerSeries
import Wikipedia.GreenTao.Sieve.CFZCarryHarmonicLcmEulerBound
import Wikipedia.GreenTao.Sieve.PrimeHarmonicProductBound

/-!
# Canonical fixed-carry divisor expansions

On a canonical CFZ carry cell the affine family is fixed before the
divisor variables are chosen.  This file reorganizes the coordinatewise
truncated, squarefree paired-divisor sum by its prime-to-form supports.

The reorganization is exact.  The corresponding unrestricted support
sum factors into the existing paired Fourier local factors, and hence into
the finite-prime-support Euler series.  The difference between these two
finite sums is recorded explicitly; it is precisely the remaining
coordinatewise-truncation splice, with no divisor-dependent affine family.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped ArithmeticFunction.Moebius BigOperators

/-! ## Generic finite prime-support assignments -/

/-- A form-support chosen independently at every prime in `P`. -/
abbrev FixedFamilyPrimeSupportAssignment
    (κ : Type*) [Fintype κ] (P : Finset Nat.Primes) :=
  (p : {p // p ∈ P}) → Finset κ

/-- The complete finite space of form-support assignments on `P`. -/
def fixedFamilyPrimeSupportAssignmentChoices
    (κ : Type*) [Fintype κ] [DecidableEq κ]
    (P : Finset Nat.Primes) :
    Finset (FixedFamilyPrimeSupportAssignment κ P) :=
  Fintype.piFinset fun _p : {p // p ∈ P} =>
    (Finset.univ : Finset κ).powerset

/-- The support assignment carried by a paired divisor family. -/
def fixedFamilyPrimeSupportAssignmentOf
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (P : Finset Nat.Primes) (z : κ → ℕ × ℕ) :
    FixedFamilyPrimeSupportAssignment κ P :=
  fun p => pairedPrimeSupport z (p : ℕ)

theorem fixedFamilyPrimeSupportAssignmentOf_mem_choices
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (P : Finset Nat.Primes) (z : κ → ℕ × ℕ) :
    fixedFamilyPrimeSupportAssignmentOf P z ∈
      fixedFamilyPrimeSupportAssignmentChoices κ P := by
  classical
  simp [fixedFamilyPrimeSupportAssignmentChoices]

/-- Total complex common-zero density, equal to one away from natural
primes.  It is only a bookkeeping device for changing between the
`Nat.Primes` and `Nat.primesLE` index types. -/
noncomputable def primeAffineFamilyZeroDensity
    {κ ι : Type*} [Fintype ι] [DecidableEq ι]
    (forms : κ → AffineForm ι ℤ)
    (p : ℕ) (s : Finset κ) : ℂ :=
  if hp : p.Prime then by
    letI : NeZero p := ⟨hp.ne_zero⟩
    exact (affineFamilyZeroDensity p forms s : ℂ)
  else 1

theorem primeAffineFamilyZeroDensity_of_prime
    {κ ι : Type*} [Fintype ι] [DecidableEq ι]
    (forms : κ → AffineForm ι ℤ)
    {p : ℕ} (hp : p.Prime) (s : Finset κ) :
    primeAffineFamilyZeroDensity forms p s = by
      letI : NeZero p := ⟨hp.ne_zero⟩
      exact (affineFamilyZeroDensity p forms s : ℂ) := by
  simp [primeAffineFamilyZeroDensity, hp]

/-- The common-zero-density product attached to one support assignment. -/
noncomputable def fixedFamilyPrimeSupportDensity
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (forms : κ → AffineForm ι ℤ)
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P) : ℂ :=
  ∏ p : {p // p ∈ P},
    primeAffineFamilyZeroDensity forms (p : ℕ) (support p)

/-- The signed Fourier coefficient of one form-support at one prime. -/
noncomputable def fixedFamilyPrimeLocalCoefficient
    {κ : Type*} [Fintype κ]
    (R : ℕ) (t u : κ → ℝ)
    (p : Nat.Primes) (s : Finset κ) : ℂ :=
  (-1 : ℂ) ^ s.card *
    ∏ q ∈ s,
      pairedFourierPrimeCoefficient
        R (p : ℕ) (t q) (u q)

/-- The exact inclusion--exclusion summand at one prime. -/
noncomputable def fixedFamilyPrimeLocalSupportTerm
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (R : ℕ) (forms : κ → AffineForm ι ℤ)
    (t u : κ → ℝ)
    (p : Nat.Primes) (s : Finset κ) : ℂ := by
  letI : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  exact
    fixedFamilyPrimeLocalCoefficient R t u p s *
      (affineFamilyZeroDensity (p : ℕ) forms s : ℂ)

/-- Product of the signed Fourier coefficients over a finite assignment. -/
noncomputable def fixedFamilyPrimeSupportCoefficient
    {κ : Type*} [Fintype κ]
    (R : ℕ) (t u : κ → ℝ)
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P) : ℂ :=
  ∏ p : {p // p ∈ P},
    fixedFamilyPrimeLocalCoefficient R t u p.1 (support p)

/-- One term in the unrestricted finite support-assignment expansion. -/
noncomputable def fixedFamilyPrimeSupportEulerTerm
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (R : ℕ) (forms : κ → AffineForm ι ℤ)
    (P : Finset Nat.Primes) (t u : κ → ℝ)
    (support : FixedFamilyPrimeSupportAssignment κ P) : ℂ :=
  ∏ p : {p // p ∈ P},
    fixedFamilyPrimeLocalSupportTerm
      R forms t u p.1 (support p)

theorem fixedFamilyPrimeSupportEulerTerm_eq_coefficient_mul_density
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (R : ℕ) (forms : κ → AffineForm ι ℤ)
    (P : Finset Nat.Primes) (t u : κ → ℝ)
    (support : FixedFamilyPrimeSupportAssignment κ P) :
    fixedFamilyPrimeSupportEulerTerm R forms P t u support =
      fixedFamilyPrimeSupportCoefficient R t u support *
        fixedFamilyPrimeSupportDensity forms support := by
  classical
  simp only [fixedFamilyPrimeSupportEulerTerm,
    fixedFamilyPrimeLocalSupportTerm,
    fixedFamilyPrimeSupportCoefficient,
    fixedFamilyPrimeSupportDensity,
    Finset.prod_mul_distrib]
  apply congrArg
    (fun x =>
      (∏ p : {p // p ∈ P},
        fixedFamilyPrimeLocalCoefficient
          R t u p.1 (support p)) * x)
  apply Finset.prod_congr rfl
  intro p _hp
  symm
  exact primeAffineFamilyZeroDensity_of_prime
    forms p.1.prop (support p)

/-! ## Exact unrestricted finite Euler factorization -/

/-- One paired Fourier local factor is exactly its support sum. -/
theorem pairedFourierPrimeLocalFactor_eq_fixedFamilySupportSum
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (R : ℕ) (forms : κ → AffineForm ι ℤ)
    (t u : κ → ℝ) (p : Nat.Primes) :
    pairedFourierPrimeLocalFactor R forms t u p =
      ∑ s ∈ (Finset.univ : Finset κ).powerset,
        fixedFamilyPrimeLocalSupportTerm R forms t u p s := by
  letI : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  unfold pairedFourierPrimeLocalFactor pairedFourierLocalFactor
    fixedFamilyPrimeLocalSupportTerm
    fixedFamilyPrimeLocalCoefficient
  exact
    complexWeightedLocalFactor_eq_inclusionExclusion
      (p : ℕ) forms
      (fun q =>
        pairedFourierPrimeCoefficient
          R (p : ℕ) (t q) (u q))

/-- Summing all form-support assignments factors prime by prime. -/
theorem sum_fixedFamilyPrimeSupportEulerTerm_eq_prod_localFactors
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (R : ℕ) (forms : κ → AffineForm ι ℤ)
    (P : Finset Nat.Primes) (t u : κ → ℝ) :
    ∑ support ∈ fixedFamilyPrimeSupportAssignmentChoices κ P,
        fixedFamilyPrimeSupportEulerTerm
          R forms P t u support =
      ∏ p : {p // p ∈ P},
        pairedFourierPrimeLocalFactor R forms t u p.1 := by
  classical
  simp_rw [
    pairedFourierPrimeLocalFactor_eq_fixedFamilySupportSum]
  unfold fixedFamilyPrimeSupportAssignmentChoices
    fixedFamilyPrimeSupportEulerTerm
  rw [Finset.prod_univ_sum]

/-- The same finite Euler product written using the generic unrestricted
prime-support series from `UnrestrictedPrimeSupportEulerSeries`. -/
theorem sum_unrestrictedPrimeSupportTerm_eq_sum_fixedFamilyAssignments
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (R : ℕ) (forms : κ → AffineForm ι ℤ)
    (P : Finset Nat.Primes) (t u : κ → ℝ) :
    (∑ S ∈ P.powerset,
        unrestrictedPrimeSupportTerm
          (pairedFourierPrimeLocalFactor R forms t u) S) =
      ∑ support ∈ fixedFamilyPrimeSupportAssignmentChoices κ P,
        fixedFamilyPrimeSupportEulerTerm
          R forms P t u support := by
  calc
    (∑ S ∈ P.powerset,
        unrestrictedPrimeSupportTerm
          (pairedFourierPrimeLocalFactor R forms t u) S) =
        ∏ p ∈ P,
          pairedFourierPrimeLocalFactor R forms t u p :=
      sum_unrestrictedPrimeSupportTerm_powerset
        (pairedFourierPrimeLocalFactor R forms t u) P
    _ = ∏ p : {p // p ∈ P},
          pairedFourierPrimeLocalFactor R forms t u p.1 := by
      exact
        (Finset.prod_coe_sort P
          (pairedFourierPrimeLocalFactor R forms t u)).symm
    _ = _ :=
      (sum_fixedFamilyPrimeSupportEulerTerm_eq_prod_localFactors
        R forms P t u).symm

/-! ## The exact coordinatewise-truncated support fibers -/

/-- The Fourier transforms common to every paired divisor term at fixed
frequencies. -/
noncomputable def pairedCutoffFourierEnvelope
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (t u : κ → ℝ) : ℂ :=
  (∏ q, χ.cutoffFourierTransform (t q)) *
    ∏ q, χ.cutoffFourierTransform (u q)

/-- A nonsquarefree paired family makes its transformed Möbius coefficient
vanish pointwise. -/
theorem SmoothSieveCutoff.transformedPairedDivisorFamily_eq_zero_of_not_squarefree
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (z : κ → ℕ × ℕ)
    (hz : ¬SquarefreePairedDivisorChoice z)
    (tu : (κ → ℝ) × (κ → ℝ)) :
    χ.transformedPairedDivisorFamily R z tu = 0 := by
  classical
  by_cases hleft : ∀ q : κ, Squarefree (z q).1
  · have hright : ∃ q : κ, ¬Squarefree (z q).2 := by
      by_contra h
      apply hz
      intro q
      exact ⟨hleft q,
        Classical.byContradiction fun hq => h ⟨q, hq⟩⟩
    obtain ⟨q, hq⟩ := hright
    have hzero :
        (ArithmeticFunction.moebius (z q).2 : ℂ) = 0 := by
      exact_mod_cast
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hq
    unfold transformedPairedDivisorFamily
      transformedDivisorFamilySide
    have hprod :
        (∏ r : κ,
          (ArithmeticFunction.moebius (z r).2 : ℂ) *
            χ.cutoffFourierTransform (tu.2 r) *
              divisorMultiplicativePhase R (z r).2 (tu.2 r)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ q) (by simp [hzero])
    rw [hprod, mul_zero]
  · obtain ⟨q, hq⟩ := Classical.not_forall.mp hleft
    have hzero :
        (ArithmeticFunction.moebius (z q).1 : ℂ) = 0 := by
      exact_mod_cast
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hq
    unfold transformedPairedDivisorFamily
      transformedDivisorFamilySide
    have hprod :
        (∏ r : κ,
          (ArithmeticFunction.moebius (z r).1 : ℂ) *
            χ.cutoffFourierTransform (tu.1 r) *
              divisorMultiplicativePhase R (z r).1 (tu.1 r)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ q) (by simp [hzero])
    rw [hprod, zero_mul]

/-- Möbius zeros reduce any transformed finite divisor sum exactly to its
squarefree part. -/
theorem SmoothSieveCutoff.sum_transformedPairedDivisorFamily_eq_squarefree
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (a : (κ → ℕ × ℕ) → ℂ)
    (tu : (κ → ℝ) × (κ → ℝ)) :
    ∑ z ∈ smoothDivisorFamilyChoices κ R,
        χ.transformedPairedDivisorFamily R z tu * a z =
      ∑ z ∈ SmoothSieveCutoff.squarefreeSmoothPairedDivisorChoices κ R,
        χ.transformedPairedDivisorFamily R z tu * a z := by
  classical
  calc
    (∑ z ∈ smoothDivisorFamilyChoices κ R,
        χ.transformedPairedDivisorFamily R z tu * a z) =
        ∑ z ∈ smoothDivisorFamilyChoices κ R,
          if SquarefreePairedDivisorChoice z then
            χ.transformedPairedDivisorFamily R z tu * a z
          else 0 := by
      apply Finset.sum_congr rfl
      intro z _hzR
      by_cases hz : SquarefreePairedDivisorChoice z
      · simp [hz]
      · rw [
          χ.transformedPairedDivisorFamily_eq_zero_of_not_squarefree
            R z hz tu]
        simp [hz]
    _ = ∑ z ∈ SmoothSieveCutoff.squarefreeSmoothPairedDivisorChoices κ R,
          χ.transformedPairedDivisorFamily R z tu * a z := by
      unfold SmoothSieveCutoff.squarefreeSmoothPairedDivisorChoices
      rw [Finset.sum_filter]

/-- The exact transformed coefficient of one support fiber inside the
coordinatewise box `1 ≤ d_q,e_q ≤ R`. -/
noncomputable def coordinatewiseTruncatedSupportCoefficient
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (P : Finset Nat.Primes) (t u : κ → ℝ)
    (support : FixedFamilyPrimeSupportAssignment κ P) : ℂ :=
  ∑ z ∈ SmoothSieveCutoff.squarefreeSmoothPairedDivisorChoices κ R with
      fixedFamilyPrimeSupportAssignmentOf P z = support,
    χ.transformedPairedDivisorFamily R z (t, u)

/-- Exact fiberwise reorganization of the squarefree coordinatewise
divisor sum. -/
theorem sum_coordinatewiseTruncatedSupportCoefficient_mul_density
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (forms : κ → AffineForm ι ℤ)
    (P : Finset Nat.Primes) (t u : κ → ℝ) :
    ∑ support ∈ fixedFamilyPrimeSupportAssignmentChoices κ P,
        coordinatewiseTruncatedSupportCoefficient
            χ R P t u support *
          fixedFamilyPrimeSupportDensity forms support =
      ∑ z ∈ SmoothSieveCutoff.squarefreeSmoothPairedDivisorChoices κ R,
        χ.transformedPairedDivisorFamily R z (t, u) *
          fixedFamilyPrimeSupportDensity forms
            (fixedFamilyPrimeSupportAssignmentOf P z) := by
  classical
  let s := SmoothSieveCutoff.squarefreeSmoothPairedDivisorChoices κ R
  let choices := fixedFamilyPrimeSupportAssignmentChoices κ P
  let encode :
      (κ → ℕ × ℕ) → FixedFamilyPrimeSupportAssignment κ P :=
    fixedFamilyPrimeSupportAssignmentOf P
  have hmaps :
      ∀ z ∈ s, encode z ∈ choices := by
    intro z _hz
    exact fixedFamilyPrimeSupportAssignmentOf_mem_choices P z
  calc
    (∑ support ∈ choices,
        coordinatewiseTruncatedSupportCoefficient
            χ R P t u support *
          fixedFamilyPrimeSupportDensity forms support) =
        ∑ support ∈ choices,
          ∑ z ∈ s with encode z = support,
            χ.transformedPairedDivisorFamily R z (t, u) *
              fixedFamilyPrimeSupportDensity forms support := by
      apply Finset.sum_congr rfl
      intro support _hsupport
      rw [← Finset.sum_mul]
      rfl
    _ = ∑ support ∈ choices,
          ∑ z ∈ s with encode z = support,
            χ.transformedPairedDivisorFamily R z (t, u) *
              fixedFamilyPrimeSupportDensity forms (encode z) := by
      apply Finset.sum_congr rfl
      intro support _hsupport
      apply Finset.sum_congr rfl
      intro z hz
      have hEq : encode z = support :=
        (Finset.mem_filter.mp hz).2
      rw [hEq]
    _ = ∑ z ∈ s,
          χ.transformedPairedDivisorFamily R z (t, u) *
            fixedFamilyPrimeSupportDensity forms (encode z) :=
      Finset.sum_fiberwise_of_maps_to hmaps
        (fun z =>
          χ.transformedPairedDivisorFamily R z (t, u) *
            fixedFamilyPrimeSupportDensity forms (encode z))
    _ = _ := rfl

/-! ## Replacing the supported prime range by the CRT Euler product -/

/-- Complex-valued counterpart of `prod_primesLEAsPrimes`. -/
theorem prod_primesLEAsPrimes_complex
    (R : ℕ) (f : ℕ → ℂ) :
    (∏ p ∈ primesLEAsPrimes R, f p) =
      ∏ p ∈ Nat.primesLE R, f p := by
  classical
  unfold primesLEAsPrimes
  rw [Finset.prod_map]
  exact Finset.prod_attach _ f

/-- On a supported squarefree divisor family, the density product over all
primes at most `R` is exactly the CRT product over the global LCM. -/
theorem fixedFamilyPrimeSupportDensity_assignmentOf_eq_eulerProduct
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {R : ℕ} {z : κ → ℕ × ℕ}
    (forms : κ → AffineForm ι ℤ)
    (hzR : z ∈ smoothDivisorFamilyChoices κ R)
    (hz : SquarefreePairedDivisorChoice z) :
    fixedFamilyPrimeSupportDensity forms
        (fixedFamilyPrimeSupportAssignmentOf
          (primesLEAsPrimes R) z) =
      ∏ p : (pairedDivisorLcm z).primeFactors,
        (affineFamilyZeroDensity (p : ℕ) forms
          (pairedPrimeSupport z p) : ℂ) := by
  classical
  unfold fixedFamilyPrimeSupportDensity
    fixedFamilyPrimeSupportAssignmentOf
  calc
    (∏ p : {p // p ∈ primesLEAsPrimes R},
        primeAffineFamilyZeroDensity forms (p : ℕ)
          (pairedPrimeSupport z (p : ℕ))) =
        ∏ p ∈ primesLEAsPrimes R,
          primeAffineFamilyZeroDensity forms (p : ℕ)
            (pairedPrimeSupport z (p : ℕ)) := by
      exact
        Finset.prod_coe_sort (primesLEAsPrimes R)
          (fun p : Nat.Primes =>
            (primeAffineFamilyZeroDensity forms (p : ℕ)
              (pairedPrimeSupport z (p : ℕ)) : ℂ))
    _ = ∏ p ∈ Nat.primesLE R,
          primeAffineFamilyZeroDensity forms p
            (pairedPrimeSupport z p) := by
      exact
        prod_primesLEAsPrimes_complex R
          (fun p =>
            primeAffineFamilyZeroDensity forms p
              (pairedPrimeSupport z p))
    _ = ∏ p ∈ (pairedDivisorLcm z).primeFactors,
          primeAffineFamilyZeroDensity forms p
            (pairedPrimeSupport z p) := by
      symm
      apply Finset.prod_subset
        (SmoothSieveCutoff.primeFactors_pairedDivisorLcm_subset_primesLE
          hzR hz)
      intro p hpR hpD
      have hpPrime : p.Prime :=
        Nat.prime_of_mem_primesLE hpR
      letI : NeZero p := ⟨hpPrime.ne_zero⟩
      have hsupport :
          pairedPrimeSupport z p = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        intro hnonempty
        exact hpD
          ((mem_primeFactors_pairedDivisorLcm_iff hz p).2
            ⟨hpPrime, hnonempty⟩)
      rw [primeAffineFamilyZeroDensity_of_prime forms hpPrime,
        hsupport, affineFamilyZeroDensity_empty]
      exact Complex.ofReal_one
    _ = ∏ p : (pairedDivisorLcm z).primeFactors,
          (affineFamilyZeroDensity (p : ℕ) forms
            (pairedPrimeSupport z p) : ℂ) := by
      calc
        (∏ p ∈ (pairedDivisorLcm z).primeFactors,
            primeAffineFamilyZeroDensity forms p
              (pairedPrimeSupport z p)) =
            ∏ p : (pairedDivisorLcm z).primeFactors,
              primeAffineFamilyZeroDensity forms (p : ℕ)
                (pairedPrimeSupport z p) := by
          exact
            (Finset.prod_coe_sort
              (pairedDivisorLcm z).primeFactors
              (fun p : ℕ =>
                primeAffineFamilyZeroDensity forms p
                  (pairedPrimeSupport z p))).symm
        _ = _ := by
          apply Finset.prod_congr rfl
          intro p _hp
          have hpPrime : (p : ℕ).Prime :=
            Nat.prime_of_mem_primeFactors p.2
          letI : NeZero (p : ℕ) := ⟨hpPrime.ne_zero⟩
          exact primeAffineFamilyZeroDensity_of_prime
            forms hpPrime (pairedPrimeSupport z p)

/-! ## The exact truncated-to-unrestricted splice -/

/-- The finite CRT Euler product attached to one paired divisor family and
one fixed affine family. -/
noncomputable def fixedFamilyDivisorEulerProduct
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (forms : κ → AffineForm ι ℤ)
    (z : κ → ℕ × ℕ) : ℂ :=
  ∏ p : (pairedDivisorLcm z).primeFactors, by
    letI : NeZero (p : ℕ) :=
      ⟨(Nat.prime_of_mem_primeFactors p.2).ne_zero⟩
    exact
      (affineFamilyZeroDensity (p : ℕ) forms
        (pairedPrimeSupport z p) : ℂ)

/-- The original finite divisor sum is exactly the support-fiber sum.  This
is the finite divisor-sum reorganization; no Euler approximation has been
made. -/
theorem sum_transformedPairedDivisorFamily_mul_fixedFamilyEulerProduct
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (forms : κ → AffineForm ι ℤ)
    (t u : κ → ℝ) :
    ∑ z ∈ smoothDivisorFamilyChoices κ R,
        χ.transformedPairedDivisorFamily R z (t, u) *
          fixedFamilyDivisorEulerProduct forms z =
      ∑ support ∈
          fixedFamilyPrimeSupportAssignmentChoices
            κ (primesLEAsPrimes R),
        coordinatewiseTruncatedSupportCoefficient
            χ R (primesLEAsPrimes R) t u support *
          fixedFamilyPrimeSupportDensity forms support := by
  classical
  calc
    (∑ z ∈ smoothDivisorFamilyChoices κ R,
        χ.transformedPairedDivisorFamily R z (t, u) *
          fixedFamilyDivisorEulerProduct forms z) =
        ∑ z ∈
            SmoothSieveCutoff.squarefreeSmoothPairedDivisorChoices κ R,
          χ.transformedPairedDivisorFamily R z (t, u) *
            fixedFamilyDivisorEulerProduct forms z :=
      χ.sum_transformedPairedDivisorFamily_eq_squarefree
        R (fixedFamilyDivisorEulerProduct forms) (t, u)
    _ = ∑ z ∈
            SmoothSieveCutoff.squarefreeSmoothPairedDivisorChoices κ R,
          χ.transformedPairedDivisorFamily R z (t, u) *
            fixedFamilyPrimeSupportDensity forms
              (fixedFamilyPrimeSupportAssignmentOf
                (primesLEAsPrimes R) z) := by
      apply Finset.sum_congr rfl
      intro z hz
      have hzData :=
        SmoothSieveCutoff.mem_squarefreeSmoothPairedDivisorChoices.mp hz
      rw [fixedFamilyDivisorEulerProduct,
        fixedFamilyPrimeSupportDensity_assignmentOf_eq_eulerProduct
          forms hzData.1 hzData.2]
    _ = _ :=
      (sum_coordinatewiseTruncatedSupportCoefficient_mul_density
        χ R forms (primesLEAsPrimes R) t u).symm

/-- Difference, at one support assignment, between the actual
coordinatewise-truncated Fourier coefficient and its unrestricted
primewise coefficient. -/
noncomputable def coordinatewiseTruncationSupportDiscrepancy
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (P : Finset Nat.Primes) (t u : κ → ℝ)
    (support : FixedFamilyPrimeSupportAssignment κ P) : ℂ :=
  coordinatewiseTruncatedSupportCoefficient χ R P t u support -
    pairedCutoffFourierEnvelope χ t u *
      fixedFamilyPrimeSupportCoefficient R t u support

/-- Exact fixed-family splice.  The first term is the honest finite Euler
product; the second is the complete coordinatewise-truncation discrepancy,
grouped by prime-to-form support. -/
theorem sum_transformedPairedDivisorFamily_mul_fixedFamilyEulerProduct_eq_euler_add_discrepancy
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (forms : κ → AffineForm ι ℤ)
    (t u : κ → ℝ) :
    ∑ z ∈ smoothDivisorFamilyChoices κ R,
        χ.transformedPairedDivisorFamily R z (t, u) *
          fixedFamilyDivisorEulerProduct forms z =
      pairedCutoffFourierEnvelope χ t u *
          ∏ p :
              {p // p ∈ primesLEAsPrimes R},
            pairedFourierPrimeLocalFactor R forms t u p.1 +
        ∑ support ∈
            fixedFamilyPrimeSupportAssignmentChoices
              κ (primesLEAsPrimes R),
          coordinatewiseTruncationSupportDiscrepancy
              χ R (primesLEAsPrimes R) t u support *
            fixedFamilyPrimeSupportDensity forms support := by
  classical
  rw [
    sum_transformedPairedDivisorFamily_mul_fixedFamilyEulerProduct,
    ← sum_fixedFamilyPrimeSupportEulerTerm_eq_prod_localFactors
      R forms (primesLEAsPrimes R) t u]
  simp_rw [
    fixedFamilyPrimeSupportEulerTerm_eq_coefficient_mul_density]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro support _hsupport
  unfold coordinatewiseTruncationSupportDiscrepancy
  ring

/-- The same splice with the Euler term written as the finite powerset
portion of the unrestricted prime-support series. -/
theorem sum_transformedPairedDivisorFamily_mul_fixedFamilyEulerProduct_eq_unrestrictedSupport_add_discrepancy
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (forms : κ → AffineForm ι ℤ)
    (t u : κ → ℝ) :
    ∑ z ∈ smoothDivisorFamilyChoices κ R,
        χ.transformedPairedDivisorFamily R z (t, u) *
          fixedFamilyDivisorEulerProduct forms z =
      pairedCutoffFourierEnvelope χ t u *
          ∑ S ∈ (primesLEAsPrimes R).powerset,
            unrestrictedPrimeSupportTerm
              (pairedFourierPrimeLocalFactor R forms t u) S +
        ∑ support ∈
            fixedFamilyPrimeSupportAssignmentChoices
              κ (primesLEAsPrimes R),
          coordinatewiseTruncationSupportDiscrepancy
              χ R (primesLEAsPrimes R) t u support *
            fixedFamilyPrimeSupportDensity forms support := by
  rw [
    sum_transformedPairedDivisorFamily_mul_fixedFamilyEulerProduct_eq_euler_add_discrepancy,
    sum_unrestrictedPrimeSupportTerm_powerset]
  exact
    congrArg
      (fun x =>
        pairedCutoffFourierEnvelope χ t u * x +
          ∑ support ∈
              fixedFamilyPrimeSupportAssignmentChoices
                κ (primesLEAsPrimes R),
            coordinatewiseTruncationSupportDiscrepancy
                χ R (primesLEAsPrimes R) t u support *
              fixedFamilyPrimeSupportDensity forms support)
      (Finset.prod_coe_sort
        (primesLEAsPrimes R)
        (pairedFourierPrimeLocalFactor R forms t u))

/-! ## Canonical fixed-carry specialization -/

/-- The fixed-family CRT product on one canonical carry cell, viewed in
`ℂ` for Fourier expansion. -/
noncomputable def cfzCanonicalCarryFixedDivisorEulerProduct
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k : ℕ}
    (N W b : ℕ) (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ) (z : κ → ℕ × ℕ) : ℂ :=
  fixedFamilyDivisorEulerProduct
    (cfzCarryAdjustedFamilyAtVector N W b forms carry) z

/-- Prime-support density on one canonical fixed-carry family. -/
noncomputable def cfzCanonicalCarryPrimeSupportDensity
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k : ℕ}
    (N W b : ℕ) (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P) : ℂ :=
  fixedFamilyPrimeSupportDensity
    (cfzCarryAdjustedFamilyAtVector N W b forms carry) support

/-- Paired Fourier local factor on one canonical fixed-carry family. -/
noncomputable def cfzCanonicalCarryPairedFourierPrimeLocalFactor
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k : ℕ}
    (N W b R : ℕ) (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ) (t u : κ → ℝ)
    (p : Nat.Primes) : ℂ :=
  pairedFourierPrimeLocalFactor R
    (cfzCarryAdjustedFamilyAtVector N W b forms carry) t u p

/-- The fixed-carry Euler product is exactly the CRT density already proved
in `CFZCanonicalCarryEulerBridge`. -/
theorem cfzCanonicalCarryFixedDivisorEulerProduct_eq_density
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k : ℕ}
    (N W b : ℕ) (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ) (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)]
    (hz : SquarefreePairedDivisorChoice z) :
    cfzCanonicalCarryFixedDivisorEulerProduct
        N W b forms carry z =
      (pairedDivisibilityDensity
        (fun q =>
          cfzCarryAdjustedResidueValueAtVector
            (D := pairedDivisorLcm z)
            N W b forms carry q)
        z : ℂ) := by
  rw [
    pairedDivisibilityDensity_cfzCarryVector_eq_eulerProduct
      N W b forms carry z hz]
  unfold cfzCanonicalCarryFixedDivisorEulerProduct
    fixedFamilyDivisorEulerProduct
  push_cast
  rfl

/-- **Canonical fixed-carry divisor expansion.**  The coordinatewise
truncated sum is the finite portion of the unrestricted prime-support
series plus the explicit support-fiber discrepancy.  In particular, the
affine family occurring throughout the discrepancy is independent of the
divisor family `z`. -/
theorem cfzCanonicalCarryFixedDivisorExpansion_eq_unrestrictedSupport_add_discrepancy
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k : ℕ}
    (χ : SmoothSieveCutoff) (N W b R : ℕ)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ) (t u : κ → ℝ) :
    ∑ z ∈ smoothDivisorFamilyChoices κ R,
        χ.transformedPairedDivisorFamily R z (t, u) *
          cfzCanonicalCarryFixedDivisorEulerProduct
            N W b forms carry z =
      pairedCutoffFourierEnvelope χ t u *
          ∑ S ∈ (primesLEAsPrimes R).powerset,
            unrestrictedPrimeSupportTerm
              (cfzCanonicalCarryPairedFourierPrimeLocalFactor
                N W b R forms carry t u) S +
        ∑ support ∈
            fixedFamilyPrimeSupportAssignmentChoices
              κ (primesLEAsPrimes R),
          coordinatewiseTruncationSupportDiscrepancy
              χ R (primesLEAsPrimes R) t u support *
            cfzCanonicalCarryPrimeSupportDensity
              N W b forms carry support := by
  exact
    sum_transformedPairedDivisorFamily_mul_fixedFamilyEulerProduct_eq_unrestrictedSupport_add_discrepancy
      χ R
      (cfzCarryAdjustedFamilyAtVector N W b forms carry)
      t u

/-! ## The carry-weighted canonical endpoint -/

/-- The canonical carry average of the finite unrestricted prime-support
series at fixed Fourier frequencies. -/
noncomputable def cfzCanonicalCarryUnrestrictedFourierAverage
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b R : ℕ) (forms : κ → CFZFormIndex k)
    (t u : κ → ℝ) : ℂ :=
  ∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
    (cfzCanonicalCarryCellDensity
        (N := N) forms carry : ℂ) *
      ∑ S ∈ (primesLEAsPrimes R).powerset,
        unrestrictedPrimeSupportTerm
          (cfzCanonicalCarryPairedFourierPrimeLocalFactor
            N W b R forms carry t u) S

/-- The complete carry-weighted coordinatewise-truncation discrepancy. -/
noncomputable def cfzCanonicalCarryTruncationDiscrepancy
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (W b R : ℕ) (forms : κ → CFZFormIndex k)
    (t u : κ → ℝ) : ℂ :=
  ∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
    (cfzCanonicalCarryCellDensity
        (N := N) forms carry : ℂ) *
      ∑ support ∈
          fixedFamilyPrimeSupportAssignmentChoices
            κ (primesLEAsPrimes R),
        coordinatewiseTruncationSupportDiscrepancy
            χ R (primesLEAsPrimes R) t u support *
          cfzCanonicalCarryPrimeSupportDensity
            N W b forms carry support

/-- Complex coercion of the canonical carry Euler average, expressed as
the weighted sum of the fixed-family products used in this file. -/
theorem coe_cfzCanonicalCarryEulerAverage_eq_sum_fixed
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b : ℕ) (forms : κ → CFZFormIndex k)
    (z : κ → ℕ × ℕ) :
    (cfzCanonicalCarryEulerAverage
        (N := N) W b forms z : ℂ) =
      ∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
        (cfzCanonicalCarryCellDensity
            (N := N) forms carry : ℂ) *
          cfzCanonicalCarryFixedDivisorEulerProduct
            N W b forms carry z := by
  unfold cfzCanonicalCarryEulerAverage
    cfzCanonicalCarryFixedDivisorEulerProduct
    fixedFamilyDivisorEulerProduct
  push_cast
  rfl

/-- Reordering the two finite sums identifies the divisor expansion
weighted by `cfzCanonicalCarryEulerAverage` with the carrywise fixed-family
expansions. -/
theorem sum_transformedPairedDivisorFamily_mul_cfzCanonicalCarryEulerAverage_eq_sum_fixed
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff) (W b R : ℕ)
    (forms : κ → CFZFormIndex k)
    (t u : κ → ℝ) :
    ∑ z ∈ smoothDivisorFamilyChoices κ R,
        χ.transformedPairedDivisorFamily R z (t, u) *
          (cfzCanonicalCarryEulerAverage
            (N := N) W b forms z : ℂ) =
      ∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
        (cfzCanonicalCarryCellDensity
            (N := N) forms carry : ℂ) *
          ∑ z ∈ smoothDivisorFamilyChoices κ R,
            χ.transformedPairedDivisorFamily R z (t, u) *
              cfzCanonicalCarryFixedDivisorEulerProduct
                N W b forms carry z := by
  classical
  simp_rw [coe_cfzCanonicalCarryEulerAverage_eq_sum_fixed]
  calc
    (∑ z ∈ smoothDivisorFamilyChoices κ R,
        χ.transformedPairedDivisorFamily R z (t, u) *
          ∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
            (cfzCanonicalCarryCellDensity
                (N := N) forms carry : ℂ) *
              cfzCanonicalCarryFixedDivisorEulerProduct
                N W b forms carry z) =
        ∑ z ∈ smoothDivisorFamilyChoices κ R,
          ∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
            χ.transformedPairedDivisorFamily R z (t, u) *
              ((cfzCanonicalCarryCellDensity
                  (N := N) forms carry : ℂ) *
                cfzCanonicalCarryFixedDivisorEulerProduct
                  N W b forms carry z) := by
      apply Finset.sum_congr rfl
      intro z _hz
      rw [Finset.mul_sum]
    _ = ∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
          ∑ z ∈ smoothDivisorFamilyChoices κ R,
            χ.transformedPairedDivisorFamily R z (t, u) *
              ((cfzCanonicalCarryCellDensity
                  (N := N) forms carry : ℂ) *
                cfzCanonicalCarryFixedDivisorEulerProduct
                  N W b forms carry z) := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro carry _hcarry
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _hz
      ring

/-- **Carry-weighted canonical divisor-to-Euler splice.**  The entire
canonical Euler average in the divisor expansion is reorganized into one
fixed-family unrestricted Euler series for each carry vector, plus the
single explicit truncation discrepancy above. -/
theorem sum_transformedPairedDivisorFamily_mul_cfzCanonicalCarryEulerAverage_eq_unrestricted_add_discrepancy
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff) (W b R : ℕ)
    (forms : κ → CFZFormIndex k)
    (t u : κ → ℝ) :
    ∑ z ∈ smoothDivisorFamilyChoices κ R,
        χ.transformedPairedDivisorFamily R z (t, u) *
          (cfzCanonicalCarryEulerAverage
            (N := N) W b forms z : ℂ) =
      pairedCutoffFourierEnvelope χ t u *
          cfzCanonicalCarryUnrestrictedFourierAverage
            (N := N) W b R forms t u +
        cfzCanonicalCarryTruncationDiscrepancy
          (N := N) χ W b R forms t u := by
  classical
  rw [
    sum_transformedPairedDivisorFamily_mul_cfzCanonicalCarryEulerAverage_eq_sum_fixed]
  unfold cfzCanonicalCarryUnrestrictedFourierAverage
    cfzCanonicalCarryTruncationDiscrepancy
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro carry _hcarry
  rw [
    cfzCanonicalCarryFixedDivisorExpansion_eq_unrestrictedSupport_add_discrepancy]
  ring

end Wikipedia.SzemeredisTheorem
