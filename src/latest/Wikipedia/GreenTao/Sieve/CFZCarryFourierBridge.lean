import Wikipedia.GreenTao.Sieve.CFZCarryDivisorExpansion
import Wikipedia.GreenTao.Sieve.SelectedCFZDivisorEulerBridge

/-!
# Fourier inversion with the CFZ carry-block average retained

The carry decomposition does not produce one common arithmetic Euler
product.  For a paired divisor family `z`, both the quotient-block box and
the local prime product depend on `pairedDivisorLcm z`.  This file keeps
that dependence inside the finite divisor sum and applies Fourier inversion
only to the smooth coefficient of each individual family.

Thus the exact integrand below has the honest shape

`∑ z, (mean over the quotient blocks belonging to z) *
  (transformed coefficient belonging to z)`.

No multiplicative closure of the truncated choices `d ≤ R` is used.  The
last results also split the exact integral into a finite Fourier box and its
complement, providing the interface needed for a subsequent uniform
Fourier-box comparison and tail estimate.
-/

namespace Wikipedia.SzemeredisTheorem

open MeasureTheory
open scoped ArithmeticFunction.Moebius BigOperators

namespace SmoothSieveCutoff

/-! ## The blockwise arithmetic coefficient -/

/-- The exact prime-local product on one quotient block belonging to one
paired divisor family.  Its type records that the quotient side is
`N / pairedDivisorLcm z`, so products belonging to different `z` are not
silently identified. -/
noncomputable def selectedCFZCarryEulerProductAtBlock
    {k N : ℕ} [NeZero N]
    (W b : ℕ) (e : LinearFormsExponent k)
    (z : SelectedCFZFormIndex e → ℕ × ℕ)
    (a : FiniteBox (fun _ : CFZVariable k =>
      N / pairedDivisorLcm z)) : ℝ :=
  ∏ p : (pairedDivisorLcm z).primeFactors,
    affineFamilyZeroDensity (p : ℕ)
      (cfzCarryAdjustedFamilyAtBlock
        (N := N) (pairedDivisorLcm z) W b
        (fun q : SelectedCFZFormIndex e => q.1)
        (fun v => (a v : ℕ)))
      (pairedPrimeSupport z p)

/-- The selected carry-block Euler coefficient really is the finite mean
of the preceding `z`-dependent products. -/
theorem selectedCFZCarryBlockEulerAverage_eq_mean_productAtBlock
    {k N : ℕ} [NeZero N]
    (W b : ℕ) (e : LinearFormsExponent k)
    (z : SelectedCFZFormIndex e → ℕ × ℕ) :
    selectedCFZCarryBlockEulerAverage
        (N := N) e W b z =
      mean (fun a :
          FiniteBox (fun _ : CFZVariable k =>
            N / pairedDivisorLcm z) =>
        selectedCFZCarryEulerProductAtBlock
          (N := N) W b e z a) := by
  rfl

/-- The existing selected-support theorem removes a whole block product
whenever its squarefree support contains a prime dividing `W`.  This is a
termwise fact; it does not identify the products for different divisor
families. -/
theorem selectedCFZCarryEulerProductAtBlock_eq_zero_of_prime_dvd
    {k N W : ℕ} [NeZero N]
    (b : ℕ) (e : LinearFormsExponent k)
    (z : SelectedCFZFormIndex e → ℕ × ℕ)
    (hz : SquarefreePairedDivisorChoice z)
    (p : (pairedDivisorLcm z).primeFactors)
    (hpW : (p : ℕ) ∣ W) (hWb : W.Coprime b)
    (a : FiniteBox (fun _ : CFZVariable k =>
      N / pairedDivisorLcm z)) :
    selectedCFZCarryEulerProductAtBlock
        (N := N) W b e z a = 0 := by
  unfold selectedCFZCarryEulerProductAtBlock
  apply Finset.prod_eq_zero (Finset.mem_univ p)
  exact
    selectedCFZCarryBlockPrimeLocalDensity_eq_zero_of_dvd
      (N := N) e b z hz p hpW hWb
      (fun v => (a v : ℕ))

/-! ## The carry-dependent Fourier integrand -/

/-- The transformed divisor expansion with the carry-block Euler average
kept as the arithmetic coefficient of each paired divisor family. -/
noncomputable def selectedCFZCarryFourierIntegrand
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff) (R W b : ℕ)
    (e : LinearFormsExponent k)
    (tu :
      (SelectedCFZFormIndex e → ℝ) ×
        (SelectedCFZFormIndex e → ℝ)) : ℂ :=
  χ.divisorExpansionFourierIntegrand R
    (selectedCFZCarryBlockEulerAverage
      (N := N) e W b) tu

/-- Pointwise finite-sum form.  In particular, the quotient-block average
remains inside the `z`-sum and is not replaced by a common Euler product. -/
theorem selectedCFZCarryFourierIntegrand_eq_sum
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff) (R W b : ℕ)
    (e : LinearFormsExponent k)
    (tu :
      (SelectedCFZFormIndex e → ℝ) ×
        (SelectedCFZFormIndex e → ℝ)) :
    χ.selectedCFZCarryFourierIntegrand
        (N := N) R W b e tu =
      ∑ z ∈ smoothDivisorFamilyChoices
          (SelectedCFZFormIndex e) R,
        (selectedCFZCarryBlockEulerAverage
            (N := N) e W b z : ℂ) *
          χ.transformedPairedDivisorFamily R z tu := by
  rfl

/-- Fully exposed form of the same finite integrand.  Every divisor family
retains its own finite quotient-block mean and its own prime support. -/
theorem selectedCFZCarryFourierIntegrand_eq_sum_mean_productAtBlock
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff) (R W b : ℕ)
    (e : LinearFormsExponent k)
    (tu :
      (SelectedCFZFormIndex e → ℝ) ×
        (SelectedCFZFormIndex e → ℝ)) :
    χ.selectedCFZCarryFourierIntegrand
        (N := N) R W b e tu =
      ∑ z ∈ smoothDivisorFamilyChoices
          (SelectedCFZFormIndex e) R,
        ((mean (fun a :
            FiniteBox (fun _ : CFZVariable k =>
              N / pairedDivisorLcm z) =>
          selectedCFZCarryEulerProductAtBlock
            (N := N) W b e z a) : ℝ) : ℂ) *
          χ.transformedPairedDivisorFamily R z tu := by
  rw [χ.selectedCFZCarryFourierIntegrand_eq_sum
    (N := N) R W b e tu]
  apply Finset.sum_congr rfl
  intro z _hz
  rw [selectedCFZCarryBlockEulerAverage_eq_mean_productAtBlock]

/-- The carry-dependent integrand is absolutely integrable.  This uses
only finiteness of the divisor-family sum and absolute integrability of
each transformed coefficient. -/
theorem integrable_selectedCFZCarryFourierIntegrand
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff) (R W b : ℕ)
    (e : LinearFormsExponent k) :
    Integrable
      (χ.selectedCFZCarryFourierIntegrand
        (N := N) R W b e)
      (volume.prod volume) :=
  χ.integrable_divisorExpansionFourierIntegrand R
    (selectedCFZCarryBlockEulerAverage
      (N := N) e W b)

/-! ## Exact divisor-sum and scaled-main-term bridges -/

/-- **Exact carry/Fourier bridge.**  The carry-block Euler divisor sum is
the integral of the finite carry-dependent Fourier integrand. -/
theorem selectedCFZCarryBlockEulerDivisorSum_eq_fourierIntegral
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff) (R W b : ℕ)
    (e : LinearFormsExponent k) :
    (selectedCFZCarryBlockEulerDivisorSum
        (N := N) χ R W b e : ℂ) =
      ∫ tu :
          (SelectedCFZFormIndex e → ℝ) ×
            (SelectedCFZFormIndex e → ℝ),
        χ.selectedCFZCarryFourierIntegrand
          (N := N) R W b e tu
          ∂(volume.prod volume) := by
  exact
    χ.sum_smoothDivisorFamilyCoefficient_eq_integral R
      (selectedCFZCarryBlockEulerAverage
        (N := N) e W b)

/-- The normalized carry-block Euler main term, with both Selberg
prefactors restored, is exactly the same Fourier integral. -/
theorem selectedCFZCarryBlockEulerMainTerm_eq_fourierIntegral
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff) (R W b : ℕ)
    (e : LinearFormsExponent k) :
    (χ.selectedCFZCarryBlockEulerMainTerm
        (N := N) R W b e : ℂ) =
      (normalizedSelbergScale χ.normalizer R W : ℂ) ^
          Fintype.card (SelectedCFZFormIndex e) *
        (((Real.log R ^ 2 : ℝ) : ℂ) ^
            Fintype.card (SelectedCFZFormIndex e) *
          ∫ tu :
              (SelectedCFZFormIndex e → ℝ) ×
                (SelectedCFZFormIndex e → ℝ),
            χ.selectedCFZCarryFourierIntegrand
              (N := N) R W b e tu
              ∂(volume.prod volume)) := by
  unfold selectedCFZCarryBlockEulerMainTerm
  push_cast
  rw [χ.selectedCFZCarryBlockEulerDivisorSum_eq_fourierIntegral
    (N := N) R W b e]

/-! ## Exact finite-box decomposition -/

/-- The product of the two coordinatewise Fourier boxes used by the paired
divisor transform. -/
def selectedCFZPairedFourierBox
    {k : ℕ} (e : LinearFormsExponent k) (T : ℝ) :
    Set
      ((SelectedCFZFormIndex e → ℝ) ×
        (SelectedCFZFormIndex e → ℝ)) :=
  fourierProductBox T ×ˢ fourierProductBox T

theorem measurableSet_selectedCFZPairedFourierBox
    {k : ℕ} (e : LinearFormsExponent k) (T : ℝ) :
    MeasurableSet (selectedCFZPairedFourierBox e T) := by
  unfold selectedCFZPairedFourierBox fourierProductBox
  exact
    Metric.isClosed_closedBall.measurableSet.prod
      Metric.isClosed_closedBall.measurableSet

/-- The exact carry Fourier integral splits into its finite paired box and
the complementary tail. -/
theorem integral_selectedCFZCarryFourierIntegrand_eq_box_add_compl
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff) (R W b : ℕ)
    (e : LinearFormsExponent k) (T : ℝ) :
    (∫ tu :
        (SelectedCFZFormIndex e → ℝ) ×
          (SelectedCFZFormIndex e → ℝ),
        χ.selectedCFZCarryFourierIntegrand
          (N := N) R W b e tu
          ∂(volume.prod volume)) =
      (∫ tu in selectedCFZPairedFourierBox e T,
          χ.selectedCFZCarryFourierIntegrand
            (N := N) R W b e tu
          ∂(volume.prod volume)) +
        ∫ tu in (selectedCFZPairedFourierBox e T)ᶜ,
          χ.selectedCFZCarryFourierIntegrand
            (N := N) R W b e tu
          ∂(volume.prod volume) := by
  symm
  exact
    integral_add_compl
      (measurableSet_selectedCFZPairedFourierBox e T)
      (χ.integrable_selectedCFZCarryFourierIntegrand
        (N := N) R W b e)

/-- Directly usable LFC main-term interface: the fully scaled carry-block
main term is the sum of its finite-box Fourier contribution and its
complementary tail, with the carry-block average still inside both
integrands. -/
theorem selectedCFZCarryBlockEulerMainTerm_eq_fourierBox_add_compl
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff) (R W b : ℕ)
    (e : LinearFormsExponent k) (T : ℝ) :
    (χ.selectedCFZCarryBlockEulerMainTerm
        (N := N) R W b e : ℂ) =
      (normalizedSelbergScale χ.normalizer R W : ℂ) ^
          Fintype.card (SelectedCFZFormIndex e) *
        (((Real.log R ^ 2 : ℝ) : ℂ) ^
            Fintype.card (SelectedCFZFormIndex e) *
          ((∫ tu in selectedCFZPairedFourierBox e T,
              χ.selectedCFZCarryFourierIntegrand
                (N := N) R W b e tu
              ∂(volume.prod volume)) +
            ∫ tu in (selectedCFZPairedFourierBox e T)ᶜ,
              χ.selectedCFZCarryFourierIntegrand
                (N := N) R W b e tu
              ∂(volume.prod volume))) := by
  rw [χ.selectedCFZCarryBlockEulerMainTerm_eq_fourierIntegral
    (N := N) R W b e]
  rw [χ.integral_selectedCFZCarryFourierIntegrand_eq_box_add_compl
    (N := N) R W b e T]

end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem
