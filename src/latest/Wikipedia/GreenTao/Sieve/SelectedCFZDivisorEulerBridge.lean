import Wikipedia.GreenTao.Sieve.SelectedCFZAffineLocalProduct
import Wikipedia.GreenTao.Sieve.MultivariateFourierExpansion
import Wikipedia.GreenTao.Sieve.ComplexEulerProductComparison

/-!
# Selected CFZ divisor sums and exact affine Euler products

The affine residue model has no cyclic representative and therefore needs
no compatibility assumption involving a cyclic modulus `N`.  This file
uses the exact selected-family squarefree CRT theorem to replace every
supported paired-divisor density by its finite product of prime-local
common-zero densities.

The replacement is made both termwise and across the complete finite
smooth-divisor sum.  Fourier inversion then gives an exact integral whose
value is the same finite sum of Euler products.  At the integrand level the
individual cutoff `d ≤ R` is not multiplicatively closed, so no false
pointwise Euler product is asserted for that truncated sum.

A second, genuinely primewise finite expansion is recorded over arbitrary
finite prime support.  Its local factors are the existing paired Fourier
factors.  Primes dividing `W` contribute exactly one for a reduced residue,
while primes outside `W` above the ambient CFZ cutoff satisfy the direct
modular good-prime estimate.
-/

namespace Wikipedia.SzemeredisTheorem

open MeasureTheory
open scoped ArithmeticFunction.Moebius BigOperators

/-! ## A total affine-residue density -/

/-- The selected-family affine paired-divisibility density, extended by
zero only in the degenerate case where the global paired LCM is zero.
Every supported smooth divisor family has nonzero LCM, and every squarefree
family does as well. -/
noncomputable def selectedCFZAffinePairedDivisibilityDensity
    {k W b : ℕ} (e : LinearFormsExponent k)
    (z : SelectedCFZFormIndex e → ℕ × ℕ) : ℝ :=
  if hD : pairedDivisorLcm z = 0 then
    0
  else
    letI : NeZero (pairedDivisorLcm z) := ⟨hD⟩
    pairedDivisibilityDensity
      (fun q : SelectedCFZFormIndex e =>
        cfzWTrickedAffineResidueValue
          (D := pairedDivisorLcm z) W b q.1)
      z

/-- On a nonzero modulus, the totalized definition is the ordinary exact
affine-residue density. -/
theorem selectedCFZAffinePairedDivisibilityDensity_eq
    {k W b : ℕ} (e : LinearFormsExponent k)
    (z : SelectedCFZFormIndex e → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)] :
    selectedCFZAffinePairedDivisibilityDensity
        (W := W) (b := b) e z =
      pairedDivisibilityDensity
        (fun q : SelectedCFZFormIndex e =>
          cfzWTrickedAffineResidueValue
            (D := pairedDivisorLcm z) W b q.1)
        z := by
  simp [selectedCFZAffinePairedDivisibilityDensity,
    NeZero.ne (pairedDivisorLcm z)]

/-! ## Exact termwise and finite-sum Euler products -/

/-- Every squarefree selected paired-divisor family has exactly the finite
prime product supplied by the affine CRT model. -/
theorem selectedCFZAffinePairedDivisibilityDensity_eq_prod
    {k W b : ℕ} (e : LinearFormsExponent k)
    (z : SelectedCFZFormIndex e → ℕ × ℕ)
    (hz : SquarefreePairedDivisorChoice z) :
    selectedCFZAffinePairedDivisibilityDensity
        (W := W) (b := b) e z =
      ∏ p : (pairedDivisorLcm z).primeFactors,
        affineFamilyZeroDensity (p : ℕ)
          (fun q : SelectedCFZFormIndex e =>
            wTrickedAffineForm W b (cfzAffineForm q.1))
          (pairedPrimeSupport z p) := by
  let : NeZero (pairedDivisorLcm z) :=
    ⟨(squarefree_pairedDivisorLcm hz).ne_zero⟩
  rw [selectedCFZAffinePairedDivisibilityDensity_eq]
  exact
    pairedDivisibilityDensity_selectedCFZWTrickedAffineResidueValue_eq_prod
      e z hz

/-- Exact finite Euler-product rewrite of the complete smooth paired-divisor
sum.  Families with zero coefficient disappear; every remaining family is
squarefree by its Möbius factors. -/
theorem
    sum_smoothDivisorFamilyCoefficient_mul_selectedCFZAffineDensity_eq_euler
    {k W b R : ℕ} (χ : ℝ → ℝ)
    (e : LinearFormsExponent k) :
    ∑ z ∈ smoothDivisorFamilyChoices
          (SelectedCFZFormIndex e) R,
        smoothDivisorFamilyCoefficient χ R z *
          selectedCFZAffinePairedDivisibilityDensity
            (W := W) (b := b) e z =
      ∑ z ∈ smoothDivisorFamilyChoices
          (SelectedCFZFormIndex e) R,
        smoothDivisorFamilyCoefficient χ R z *
          ∏ p : (pairedDivisorLcm z).primeFactors,
            affineFamilyZeroDensity (p : ℕ)
              (fun q : SelectedCFZFormIndex e =>
                wTrickedAffineForm W b (cfzAffineForm q.1))
              (pairedPrimeSupport z p) := by
  apply Finset.sum_congr rfl
  intro z _hz
  by_cases hcoefficient :
      smoothDivisorFamilyCoefficient χ R z = 0
  · simp [hcoefficient]
  · rw [selectedCFZAffinePairedDivisibilityDensity_eq_prod
      e z
      (squarefreePairedDivisorChoice_of_coefficient_ne_zero
        χ R z hcoefficient)]

/-- Fourier form of the same exact bridge.  The integral is independent of
any cyclic modulus: its arithmetic coefficient is the affine residue
density above. -/
theorem SmoothSieveCutoff.integral_selectedCFZAffineDivisorExpansion_eq_euler
    {k W b R : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) :
    (∫ tu :
        (SelectedCFZFormIndex e → ℝ) ×
          (SelectedCFZFormIndex e → ℝ),
        χ.divisorExpansionFourierIntegrand R
          (selectedCFZAffinePairedDivisibilityDensity
            (W := W) (b := b) e)
          tu ∂(volume.prod volume)) =
      ((∑ z ∈ smoothDivisorFamilyChoices
            (SelectedCFZFormIndex e) R,
          smoothDivisorFamilyCoefficient χ.toFun R z *
            ∏ p : (pairedDivisorLcm z).primeFactors,
              affineFamilyZeroDensity (p : ℕ)
                (fun q : SelectedCFZFormIndex e =>
                  wTrickedAffineForm W b (cfzAffineForm q.1))
                (pairedPrimeSupport z p) : ℝ) : ℂ) := by
  rw [← χ.sum_smoothDivisorFamilyCoefficient_eq_integral R
    (selectedCFZAffinePairedDivisibilityDensity
      (W := W) (b := b) e)]
  exact_mod_cast
    sum_smoothDivisorFamilyCoefficient_mul_selectedCFZAffineDensity_eq_euler
      χ.toFun e

/-! ## A genuinely primewise finite Fourier expansion -/

/-- The exact paired Fourier factor for a selected W-tricked CFZ family,
indexed by Mathlib's subtype of natural primes. -/
noncomputable def selectedCFZWTrickedPairedFourierPrimeFactor
    {k W b : ℕ} (R : ℕ) (e : LinearFormsExponent k)
    (t u : SelectedCFZFormIndex e → ℝ)
    (p : Nat.Primes) : ℂ :=
  pairedFourierPrimeLocalFactor R
    (fun q : SelectedCFZFormIndex e =>
      wTrickedAffineForm W b (cfzAffineForm q.1))
    t u p

/-- For a finite prime set, choose one selected form-support independently
at every prime.  This is the collapsed support after summing the three
nonempty paired states `(p,1)`, `(1,p)`, and `(p,p)`. -/
def selectedCFZPrimeLocalSupportChoices
    {k : ℕ} (e : LinearFormsExponent k)
    (S : Finset Nat.Primes) :
    Finset
      ((p : {p // p ∈ S}) →
        Finset (SelectedCFZFormIndex e)) :=
  Fintype.piFinset fun _p : {p // p ∈ S} =>
    (Finset.univ : Finset (SelectedCFZFormIndex e)).powerset

/-- The inclusion--exclusion summand attached to one form-support at one
natural prime. -/
noncomputable def selectedCFZPrimeLocalSupportTerm
    {k W b : ℕ} (R : ℕ) (e : LinearFormsExponent k)
    (t u : SelectedCFZFormIndex e → ℝ)
    (p : Nat.Primes) (s : Finset (SelectedCFZFormIndex e)) : ℂ := by
  letI : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  exact
    (((-1 : ℂ) ^ s.card *
        ∏ q ∈ s,
          pairedFourierPrimeCoefficient
            R (p : ℕ) (t q) (u q)) *
      (affineFamilyZeroDensity (p : ℕ)
        (fun q : SelectedCFZFormIndex e =>
          wTrickedAffineForm W b (cfzAffineForm q.1))
        s : ℂ))

/-- One term of the collapsed prime-support expansion.  The coefficient at
`p` is the inclusion--exclusion coefficient built from the exact paired
Fourier prime coefficient; the arithmetic part is the selected affine
common-zero density. -/
noncomputable def selectedCFZPrimeSupportEulerTerm
    {k W b : ℕ} (R : ℕ) (e : LinearFormsExponent k)
    (S : Finset Nat.Primes)
    (t u : SelectedCFZFormIndex e → ℝ)
    (support :
      (p : {p // p ∈ S}) →
        Finset (SelectedCFZFormIndex e)) : ℂ :=
  ∏ p : {p // p ∈ S},
    selectedCFZPrimeLocalSupportTerm
      (W := W) (b := b) R e t u p.1 (support p)

/-- One selected paired Fourier prime factor is its exact finite sum over
collapsed paired-divisor supports. -/
theorem selectedCFZWTrickedPairedFourierPrimeFactor_eq_supportSum
    {k W b : ℕ} (R : ℕ) (e : LinearFormsExponent k)
    (t u : SelectedCFZFormIndex e → ℝ)
    (p : Nat.Primes) :
    selectedCFZWTrickedPairedFourierPrimeFactor
        (W := W) (b := b) R e t u p =
      ∑ s ∈
          (Finset.univ :
            Finset (SelectedCFZFormIndex e)).powerset,
        selectedCFZPrimeLocalSupportTerm
          (W := W) (b := b) R e t u p s := by
  let : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  unfold selectedCFZWTrickedPairedFourierPrimeFactor
    pairedFourierPrimeLocalFactor pairedFourierLocalFactor
    selectedCFZPrimeLocalSupportTerm
  exact
    complexWeightedLocalFactor_eq_inclusionExclusion
      (p : ℕ)
      (fun q : SelectedCFZFormIndex e =>
        wTrickedAffineForm W b (cfzAffineForm q.1))
      (fun q =>
        pairedFourierPrimeCoefficient
          R (p : ℕ) (t q) (u q))

/-- **Exact finite supported Euler product.**  Summing independently over
all collapsed paired-divisor form-supports at the primes in `S` is exactly
the product of the selected paired Fourier local factors. -/
theorem sum_selectedCFZPrimeSupportEulerTerm_eq_prod_localFactors
    {k W b : ℕ} (R : ℕ) (e : LinearFormsExponent k)
    (S : Finset Nat.Primes)
    (t u : SelectedCFZFormIndex e → ℝ) :
    ∑ support ∈ selectedCFZPrimeLocalSupportChoices e S,
        selectedCFZPrimeSupportEulerTerm
          (W := W) (b := b) R e S t u support =
      ∏ p : {p // p ∈ S},
        selectedCFZWTrickedPairedFourierPrimeFactor
          (W := W) (b := b) R e t u p.1 := by
  classical
  simp_rw [
    selectedCFZWTrickedPairedFourierPrimeFactor_eq_supportSum]
  unfold selectedCFZPrimeLocalSupportChoices
    selectedCFZPrimeSupportEulerTerm
  rw [Finset.prod_univ_sum]

/-! ## The W-prime / good-prime split -/

/-- A reduced residue makes every selected paired Fourier factor at a prime
dividing `W` exactly one. -/
theorem selectedCFZWTrickedPairedFourierPrimeFactor_eq_one_of_dvd
    {k W b R : ℕ} (hWb : W.Coprime b)
    (e : LinearFormsExponent k)
    (t u : SelectedCFZFormIndex e → ℝ)
    (p : Nat.Primes) (hpW : (p : ℕ) ∣ W) :
    selectedCFZWTrickedPairedFourierPrimeFactor
        (W := W) (b := b) R e t u p = 1 := by
  let : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  unfold selectedCFZWTrickedPairedFourierPrimeFactor
    pairedFourierPrimeLocalFactor
  exact
    pairedFourierLocalFactor_wTricked_eq_one
      p.prop hpW hWb R
      (fun q : SelectedCFZFormIndex e =>
        cfzAffineForm q.1)
      t u

/-- Outside `W`, above the ambient k-only cutoff, the selected arithmetic
factor differs from its first-order model by `O_k(p⁻²)` using the direct
modular good-prime theorems. -/
theorem
    norm_selectedCFZWTrickedPairedFourierPrimeFactor_sub_firstOrder_le
    {k W b R : ℕ} (hk : 2 ≤ k) (hR : 2 ≤ R)
    (e : LinearFormsExponent k)
    (t u : SelectedCFZFormIndex e → ℝ)
    (p : Nat.Primes) (hpW : ¬(p : ℕ) ∣ W)
    (hlarge :
      wTrickedCFZComplexExceptionalBound k < (p : ℕ)) :
    ‖selectedCFZWTrickedPairedFourierPrimeFactor
          (W := W) (b := b) R e t u p -
        pairedFourierFirstOrderLocalModel
          R (p : ℕ) t u‖ ≤
      (4 : ℝ) ^ Fintype.card (SelectedCFZFormIndex e) /
        (p : ℝ) ^ 2 := by
  let : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  unfold selectedCFZWTrickedPairedFourierPrimeFactor
    pairedFourierPrimeLocalFactor
  exact
    norm_selectedCFZPairedFourierLocalFactor_wTricked_sub_firstOrder_le
      hk p.prop hpW hR hlarge e
      (fun _q : SelectedCFZFormIndex e => b) t u

/-- In a finite prime product all factors at primes dividing `W` disappear
as units, leaving exactly the complementary product. -/
theorem prod_selectedCFZWTrickedPairedFourierPrimeFactor_eq_not_dvd
    {k W b R : ℕ} (hWb : W.Coprime b)
    (e : LinearFormsExponent k)
    (S : Finset Nat.Primes)
    (t u : SelectedCFZFormIndex e → ℝ) :
    S.prod (fun p =>
        selectedCFZWTrickedPairedFourierPrimeFactor
          (W := W) (b := b) R e t u p) =
      (S.filter (fun p : Nat.Primes =>
        ¬(p : ℕ) ∣ W)).prod (fun p =>
        selectedCFZWTrickedPairedFourierPrimeFactor
          (W := W) (b := b) R e t u p) := by
  rw [← Finset.prod_filter_mul_prod_filter_not
    S (fun p : Nat.Primes => (p : ℕ) ∣ W)
    (fun p =>
      selectedCFZWTrickedPairedFourierPrimeFactor
        (W := W) (b := b) R e t u p)]
  have hsmall :
      (S.filter (fun p : Nat.Primes =>
        (p : ℕ) ∣ W)).prod (fun p =>
          selectedCFZWTrickedPairedFourierPrimeFactor
            (W := W) (b := b) R e t u p) = 1 := by
    apply Finset.prod_eq_one
    intro p hp
    exact
      selectedCFZWTrickedPairedFourierPrimeFactor_eq_one_of_dvd
        hWb e t u p (Finset.mem_filter.mp hp).2
  rw [hsmall, one_mul]

/-- The portion of a finite prime support lying outside `W` and above the
ambient selected-CFZ good-prime cutoff. -/
def selectedCFZWTrickedGoodPrimeSupport
    (k W : ℕ) (S : Finset Nat.Primes) : Finset Nat.Primes :=
  S.filter fun p =>
    ¬(p : ℕ) ∣ W ∧
      wTrickedCFZComplexExceptionalBound k < (p : ℕ)

/-- If every prime of `S` outside `W` is above the ambient cutoff, the full
finite product is exactly the product over `selectedCFZWTrickedGoodPrimeSupport`.
The omitted `W`-primes are unit factors. -/
theorem
    prod_selectedCFZWTrickedPairedFourierPrimeFactor_eq_goodPrimeSupport
    {k W b R : ℕ} (hWb : W.Coprime b)
    (e : LinearFormsExponent k)
    (S : Finset Nat.Primes)
    (t u : SelectedCFZFormIndex e → ℝ)
    (hlarge :
      ∀ p ∈ S, ¬(p : ℕ) ∣ W →
        wTrickedCFZComplexExceptionalBound k < (p : ℕ)) :
    S.prod (fun p =>
        selectedCFZWTrickedPairedFourierPrimeFactor
          (W := W) (b := b) R e t u p) =
      (selectedCFZWTrickedGoodPrimeSupport k W S).prod
        (fun p =>
          selectedCFZWTrickedPairedFourierPrimeFactor
            (W := W) (b := b) R e t u p) := by
  rw [
    prod_selectedCFZWTrickedPairedFourierPrimeFactor_eq_not_dvd
      hWb e S t u]
  apply Finset.prod_congr
  · ext p
    simp only [selectedCFZWTrickedGoodPrimeSupport,
      Finset.mem_filter]
    constructor
    · rintro ⟨hpS, hpW⟩
      exact ⟨hpS, hpW, hlarge p hpS hpW⟩
    · rintro ⟨hpS, hpW, _hpLarge⟩
      exact ⟨hpS, hpW⟩
  · intro p _hp
    rfl

/-- Every factor retained by `selectedCFZWTrickedGoodPrimeSupport` obeys
the direct modular `O_k(p⁻²)` estimate. -/
theorem
    norm_selectedCFZWTrickedPairedFourierPrimeFactor_sub_firstOrder_le_of_mem_good
    {k W b R : ℕ} (hk : 2 ≤ k) (hR : 2 ≤ R)
    (e : LinearFormsExponent k)
    (S : Finset Nat.Primes)
    (t u : SelectedCFZFormIndex e → ℝ)
    (p : Nat.Primes)
    (hp : p ∈ selectedCFZWTrickedGoodPrimeSupport k W S) :
    ‖selectedCFZWTrickedPairedFourierPrimeFactor
          (W := W) (b := b) R e t u p -
        pairedFourierFirstOrderLocalModel
          R (p : ℕ) t u‖ ≤
      (4 : ℝ) ^ Fintype.card (SelectedCFZFormIndex e) /
        (p : ℝ) ^ 2 := by
  have hpData :
      ¬(p : ℕ) ∣ W ∧
        wTrickedCFZComplexExceptionalBound k < (p : ℕ) :=
    (Finset.mem_filter.mp hp).2
  exact
    norm_selectedCFZWTrickedPairedFourierPrimeFactor_sub_firstOrder_le
      hk hR e t u p hpData.1 hpData.2

/-- Combined supported-divisor/Fourier bridge with the W-prime unit factors
removed. -/
theorem sum_selectedCFZPrimeSupportEulerTerm_eq_prod_not_dvd
    {k W b R : ℕ} (hWb : W.Coprime b)
    (e : LinearFormsExponent k)
    (S : Finset Nat.Primes)
    (t u : SelectedCFZFormIndex e → ℝ) :
    ∑ support ∈ selectedCFZPrimeLocalSupportChoices e S,
        selectedCFZPrimeSupportEulerTerm
          (W := W) (b := b) R e S t u support =
      (S.filter (fun p : Nat.Primes =>
        ¬(p : ℕ) ∣ W)).prod (fun p =>
          selectedCFZWTrickedPairedFourierPrimeFactor
            (W := W) (b := b) R e t u p) := by
  rw [sum_selectedCFZPrimeSupportEulerTerm_eq_prod_localFactors]
  calc
    (∏ p : {p // p ∈ S},
        selectedCFZWTrickedPairedFourierPrimeFactor
          (W := W) (b := b) R e t u p.1) =
        S.prod (fun p =>
          selectedCFZWTrickedPairedFourierPrimeFactor
            (W := W) (b := b) R e t u p) := by
      exact Finset.prod_coe_sort S _
    _ = _ :=
      prod_selectedCFZWTrickedPairedFourierPrimeFactor_eq_not_dvd
        hWb e S t u

/-- Strongest combined finite-support endpoint: after summing all collapsed
paired-divisor supports, the exact Euler product contains only the primes
outside `W`, and under the displayed coverage hypothesis every remaining
factor is in the direct modular good-prime range. -/
theorem sum_selectedCFZPrimeSupportEulerTerm_eq_prod_goodPrimeSupport
    {k W b R : ℕ} (hWb : W.Coprime b)
    (e : LinearFormsExponent k)
    (S : Finset Nat.Primes)
    (t u : SelectedCFZFormIndex e → ℝ)
    (hlarge :
      ∀ p ∈ S, ¬(p : ℕ) ∣ W →
        wTrickedCFZComplexExceptionalBound k < (p : ℕ)) :
    ∑ support ∈ selectedCFZPrimeLocalSupportChoices e S,
        selectedCFZPrimeSupportEulerTerm
          (W := W) (b := b) R e S t u support =
      (selectedCFZWTrickedGoodPrimeSupport k W S).prod
        (fun p =>
          selectedCFZWTrickedPairedFourierPrimeFactor
            (W := W) (b := b) R e t u p) := by
  rw [sum_selectedCFZPrimeSupportEulerTerm_eq_prod_localFactors]
  calc
    (∏ p : {p // p ∈ S},
        selectedCFZWTrickedPairedFourierPrimeFactor
          (W := W) (b := b) R e t u p.1) =
        S.prod (fun p =>
          selectedCFZWTrickedPairedFourierPrimeFactor
            (W := W) (b := b) R e t u p) := by
      exact Finset.prod_coe_sort S _
    _ = _ :=
      prod_selectedCFZWTrickedPairedFourierPrimeFactor_eq_goodPrimeSupport
        hWb e S t u hlarge

end Wikipedia.SzemeredisTheorem
