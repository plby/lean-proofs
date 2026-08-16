import Wikipedia.GreenTao.Sieve.CFZCanonicalCarryBoundaryBound
import Wikipedia.GreenTao.Sieve.CFZCanonicalDivisorExpansion
import Wikipedia.GreenTao.Sieve.CFZCarryDivisorExpansion
import Wikipedia.GreenTao.Sieve.CFZCarryFourierTailPolylog

/-!
# Summed canonical cyclic-to-Euler boundary

The canonical carry partition compares the cyclic paired-divisibility
density with a divisor-independent affine Euler model.  Its pointwise error
is proportional to the paired-divisor LCM divided by the cyclic modulus.
This file sums that estimate over every divisor family selected by a
Boolean CFZ exponent, restores the Selberg normalization, and records a
joint power-scale limit.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter MeasureTheory Topology
open scoped ArithmeticFunction.Moebius BigOperators

/-- The canonical Euler divisor sum for one Boolean-selected CFZ family. -/
noncomputable def selectedCFZCanonicalEulerDivisorSum
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff) (R W b : ℕ)
    (e : LinearFormsExponent k) : ℝ :=
  ∑ z ∈ smoothDivisorFamilyChoices
        (SelectedCFZFormIndex e) R,
    smoothDivisorFamilyCoefficient χ.toFun R z *
      cfzCanonicalCarryEulerAverage
        (N := N) W b
        (fun q : SelectedCFZFormIndex e => q.1) z

/-- The finite constant contributed by the number of canonical carry
vectors and the uniform boundary estimate for one carry cell. -/
noncomputable def selectedCFZCanonicalCyclicBoundaryConstant
    {k : ℕ} (e : LinearFormsExponent k) : ℕ :=
  (cfzCanonicalCarryVectorChoices
      (SelectedCFZFormIndex e) k).card *
    cfzCanonicalCarryCellErrorConstant
      (SelectedCFZFormIndex e) k

/-- A supported selected divisor term inherits the canonical carry-cell
boundary estimate.  The global fit hypothesis supplies `2D ≤ N` uniformly
for every divisor family in the selected box. -/
theorem SmoothSieveCutoff.abs_selectedCFZ_weightedDensity_sub_canonicalEuler_le
    {k N R : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (e : LinearFormsExponent k)
    (W b : ℕ)
    (hfit :
      2 * R ^ (2 * Fintype.card (SelectedCFZFormIndex e)) ≤ N)
    (z : SelectedCFZFormIndex e → ℕ × ℕ)
    (hz : z ∈ smoothDivisorFamilyChoices
      (SelectedCFZFormIndex e) R) :
    |smoothDivisorFamilyCoefficient χ.toFun R z *
          pairedDivisibilityDensity
            (fun q : SelectedCFZFormIndex e =>
              fun x : CubePoint k N =>
                cfzWTrickedLinearValue W b q.1 x)
            z -
        smoothDivisorFamilyCoefficient χ.toFun R z *
          cfzCanonicalCarryEulerAverage
            (N := N) W b
            (fun q : SelectedCFZFormIndex e => q.1) z| ≤
      |smoothDivisorFamilyCoefficient χ.toFun R z| *
        ((selectedCFZCanonicalCyclicBoundaryConstant e : ℝ) *
          (pairedDivisorLcm z : ℝ) / (N : ℝ)) := by
  classical
  by_cases hcoefficient :
      smoothDivisorFamilyCoefficient χ.toFun R z = 0
  · simp [hcoefficient]
  · have hDpos : 0 < pairedDivisorLcm z :=
      pairedDivisorLcm_pos hz
    letI : NeZero (pairedDivisorLcm z) :=
      ⟨Nat.ne_of_gt hDpos⟩
    have hDpow :
        pairedDivisorLcm z ≤
          R ^ (2 * Fintype.card (SelectedCFZFormIndex e)) :=
      pairedDivisorLcm_selectedCFZ_le_pow e hz
    have hDle : pairedDivisorLcm z ≤ N := by omega
    have hDfit : 2 * pairedDivisorLcm z ≤ N := by omega
    have hsquarefree : SquarefreePairedDivisorChoice z :=
      squarefreePairedDivisorChoice_of_coefficient_ne_zero
        χ.toFun R z hcoefficient
    have hcanonical :=
      abs_pairedDivisibilityDensity_cfz_sub_canonicalCarryEulerAverage_le
        (N := N) W b
        (fun q : SelectedCFZFormIndex e => q.1)
        z hsquarefree hDle
    have hboundary :=
      cfzCanonicalCarryCellBoundaryError_le_div
        (κ := SelectedCFZFormIndex e)
        hk hDpos hDfit
        (fun q : SelectedCFZFormIndex e => q.1)
    rw [← mul_sub, abs_mul]
    calc
      |smoothDivisorFamilyCoefficient χ.toFun R z| *
          |pairedDivisibilityDensity
                (fun q : SelectedCFZFormIndex e =>
                  fun x : CubePoint k N =>
                    cfzWTrickedLinearValue W b q.1 x)
                z -
            cfzCanonicalCarryEulerAverage
              (N := N) W b
              (fun q : SelectedCFZFormIndex e => q.1) z| ≤
        |smoothDivisorFamilyCoefficient χ.toFun R z| *
          (((cfzCanonicalCarryVectorChoices
              (SelectedCFZFormIndex e) k).card : ℝ) *
            cfzCanonicalCarryCellBoundaryError
              (N := N) (pairedDivisorLcm z)
              (fun q : SelectedCFZFormIndex e => q.1)) :=
        mul_le_mul_of_nonneg_left hcanonical (abs_nonneg _)
      _ ≤
        |smoothDivisorFamilyCoefficient χ.toFun R z| *
          (((cfzCanonicalCarryVectorChoices
              (SelectedCFZFormIndex e) k).card : ℝ) *
            ((cfzCanonicalCarryCellErrorConstant
                (SelectedCFZFormIndex e) k : ℝ) *
              (pairedDivisorLcm z : ℝ) / (N : ℝ))) := by
        gcongr
      _ =
        |smoothDivisorFamilyCoefficient χ.toFun R z| *
          ((selectedCFZCanonicalCyclicBoundaryConstant e : ℝ) *
            (pairedDivisorLcm z : ℝ) / (N : ℝ)) := by
        unfold selectedCFZCanonicalCyclicBoundaryConstant
        push_cast
        ring

/-- Sum of the exact coefficient-weighted canonical boundary errors. -/
theorem
    SmoothSieveCutoff.abs_selectedCFZCyclicDivisorSum_sub_canonicalEuler_le_sum
    {k N R : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (e : LinearFormsExponent k)
    (W b : ℕ)
    (hfit :
      2 * R ^ (2 * Fintype.card (SelectedCFZFormIndex e)) ≤ N) :
    |selectedCFZCyclicDivisorSum
          (N := N) χ R W b e -
        selectedCFZCanonicalEulerDivisorSum
          (N := N) χ R W b e| ≤
      ∑ z ∈ smoothDivisorFamilyChoices
          (SelectedCFZFormIndex e) R,
        |smoothDivisorFamilyCoefficient χ.toFun R z| *
          ((selectedCFZCanonicalCyclicBoundaryConstant e : ℝ) *
            (pairedDivisorLcm z : ℝ) / (N : ℝ)) := by
  classical
  unfold selectedCFZCyclicDivisorSum
    selectedCFZCanonicalEulerDivisorSum
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ z ∈ smoothDivisorFamilyChoices
          (SelectedCFZFormIndex e) R,
        (smoothDivisorFamilyCoefficient χ.toFun R z *
              pairedDivisibilityDensity
                (fun q : SelectedCFZFormIndex e =>
                  fun x : CubePoint k N =>
                    cfzWTrickedLinearValue W b q.1 x)
                z -
            smoothDivisorFamilyCoefficient χ.toFun R z *
              cfzCanonicalCarryEulerAverage
                (N := N) W b
                (fun q : SelectedCFZFormIndex e => q.1) z)| ≤
        ∑ z ∈ smoothDivisorFamilyChoices
            (SelectedCFZFormIndex e) R,
          |smoothDivisorFamilyCoefficient χ.toFun R z *
                pairedDivisibilityDensity
                  (fun q : SelectedCFZFormIndex e =>
                    fun x : CubePoint k N =>
                      cfzWTrickedLinearValue W b q.1 x)
                  z -
              smoothDivisorFamilyCoefficient χ.toFun R z *
                cfzCanonicalCarryEulerAverage
                  (N := N) W b
                  (fun q : SelectedCFZFormIndex e => q.1) z| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro z hz
      exact
        χ.abs_selectedCFZ_weightedDensity_sub_canonicalEuler_le
          hk e W b hfit z hz

/-- Factored form retaining the exact coefficient-weighted LCM mass. -/
theorem
    SmoothSieveCutoff.abs_selectedCFZCyclicDivisorSum_sub_canonicalEuler_le_lcmMass
    {k N R : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (e : LinearFormsExponent k)
    (W b : ℕ)
    (hfit :
      2 * R ^ (2 * Fintype.card (SelectedCFZFormIndex e)) ≤ N) :
    |selectedCFZCyclicDivisorSum
          (N := N) χ R W b e -
        selectedCFZCanonicalEulerDivisorSum
          (N := N) χ R W b e| ≤
      (selectedCFZCanonicalCyclicBoundaryConstant e : ℝ) *
        smoothDivisorFamilyLcmMass
          (κ := SelectedCFZFormIndex e) χ.toFun R /
        (N : ℝ) := by
  classical
  calc
    |selectedCFZCyclicDivisorSum
          (N := N) χ R W b e -
        selectedCFZCanonicalEulerDivisorSum
          (N := N) χ R W b e| ≤
      ∑ z ∈ smoothDivisorFamilyChoices
          (SelectedCFZFormIndex e) R,
        |smoothDivisorFamilyCoefficient χ.toFun R z| *
          ((selectedCFZCanonicalCyclicBoundaryConstant e : ℝ) *
            (pairedDivisorLcm z : ℝ) / (N : ℝ)) :=
      χ.abs_selectedCFZCyclicDivisorSum_sub_canonicalEuler_le_sum
        hk e W b hfit
    _ =
      (selectedCFZCanonicalCyclicBoundaryConstant e : ℝ) *
        smoothDivisorFamilyLcmMass
          (κ := SelectedCFZFormIndex e) χ.toFun R /
        (N : ℝ) := by
      unfold smoothDivisorFamilyLcmMass
      simp_rw [div_eq_mul_inv]
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z _hz
      ring

/-- Explicit divisor-box bound for the summed canonical boundary. -/
theorem
    SmoothSieveCutoff.abs_selectedCFZCyclicDivisorSum_sub_canonicalEuler_le_pow
    {k N R : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (e : LinearFormsExponent k)
    (W b : ℕ)
    (hfit :
      2 * R ^ (2 * Fintype.card (SelectedCFZFormIndex e)) ≤ N) :
    |selectedCFZCyclicDivisorSum
          (N := N) χ R W b e -
        selectedCFZCanonicalEulerDivisorSum
          (N := N) χ R W b e| ≤
      (selectedCFZCanonicalCyclicBoundaryConstant e : ℝ) *
        (R ^ (2 * Fintype.card (SelectedCFZFormIndex e)) : ℝ) *
        (R ^ (2 * Fintype.card (SelectedCFZFormIndex e)) : ℝ) /
        (N : ℝ) := by
  have hmass :=
    χ.smoothDivisorFamilyLcmMass_le
      (κ := SelectedCFZFormIndex e) R
  have hconstant :
      0 ≤ (selectedCFZCanonicalCyclicBoundaryConstant e : ℝ) :=
    Nat.cast_nonneg _
  simpa only [mul_assoc] using
    (χ.abs_selectedCFZCyclicDivisorSum_sub_canonicalEuler_le_lcmMass
      hk e W b hfit).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmass hconstant)
        (by positivity))

/-! ## Selberg-scaled canonical main terms -/

/-- The canonical Euler approximation to a cyclic-majorant selected
subproduct mean. -/
noncomputable def SmoothSieveCutoff.selectedCFZCanonicalEulerMainTerm
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff) (R W b : ℕ)
    (e : LinearFormsExponent k) : ℝ :=
  normalizedSelbergScale χ.normalizer R W ^
        Fintype.card (SelectedCFZFormIndex e) *
    ((Real.log R ^ 2) ^
        Fintype.card (SelectedCFZFormIndex e) *
      selectedCFZCanonicalEulerDivisorSum
        (N := N) χ R W b e)

/-- The same canonical main term written as one complex Fourier integral. -/
noncomputable def
    SmoothSieveCutoff.selectedCFZCanonicalEulerFourierMainTerm
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff) (R W b : ℕ)
    (e : LinearFormsExponent k) : ℂ :=
  (normalizedSelbergScale χ.normalizer R W : ℂ) ^
        Fintype.card (SelectedCFZFormIndex e) *
    (((Real.log R ^ 2 : ℝ) : ℂ) ^
        Fintype.card (SelectedCFZFormIndex e) *
      ∫ tu :
          (SelectedCFZFormIndex e → ℝ) ×
            (SelectedCFZFormIndex e → ℝ),
        χ.divisorExpansionFourierIntegrand R
          (fun z =>
            cfzCanonicalCarryEulerAverage
              (N := N) W b
              (fun q : SelectedCFZFormIndex e => q.1) z)
          tu ∂(volume.prod volume))

/-- Exact divisor-to-Fourier identity for the canonical selected main
term. -/
theorem
    SmoothSieveCutoff.coe_selectedCFZCanonicalEulerMainTerm_eq_fourierMainTerm
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff) (R W b : ℕ)
    (e : LinearFormsExponent k) :
    (χ.selectedCFZCanonicalEulerMainTerm
        (N := N) R W b e : ℂ) =
      χ.selectedCFZCanonicalEulerFourierMainTerm
        (N := N) R W b e := by
  have hsum :=
    χ.sum_smoothDivisorFamilyCoefficient_eq_integral R
      (fun z : SelectedCFZFormIndex e → ℕ × ℕ =>
        cfzCanonicalCarryEulerAverage
          (N := N) W b
          (fun q : SelectedCFZFormIndex e => q.1) z)
  calc
    (χ.selectedCFZCanonicalEulerMainTerm
        (N := N) R W b e : ℂ) =
      (normalizedSelbergScale χ.normalizer R W : ℂ) ^
          Fintype.card (SelectedCFZFormIndex e) *
        (((Real.log R ^ 2 : ℝ) : ℂ) ^
            Fintype.card (SelectedCFZFormIndex e) *
          (selectedCFZCanonicalEulerDivisorSum
            (N := N) χ R W b e : ℂ)) := by
      unfold selectedCFZCanonicalEulerMainTerm
      norm_cast
    _ = _ := by
      unfold selectedCFZCanonicalEulerFourierMainTerm
        selectedCFZCanonicalEulerDivisorSum
      rw [hsum]

/-- Pointwise identification of the canonical selected Fourier integrand
with the unrestricted fixed-carry model plus its coordinatewise truncation
discrepancy. -/
theorem
    SmoothSieveCutoff.selectedCFZCanonicalEulerFourierIntegrand_eq_unrestricted_add_discrepancy
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff) (R W b : ℕ)
    (e : LinearFormsExponent k)
    (t u : SelectedCFZFormIndex e → ℝ) :
    χ.divisorExpansionFourierIntegrand R
        (fun z =>
          cfzCanonicalCarryEulerAverage
            (N := N) W b
            (fun q : SelectedCFZFormIndex e => q.1) z)
        (t, u) =
      pairedCutoffFourierEnvelope χ t u *
          cfzCanonicalCarryUnrestrictedFourierAverage
            (N := N) W b R
            (fun q : SelectedCFZFormIndex e => q.1) t u +
        cfzCanonicalCarryTruncationDiscrepancy
          (N := N) χ W b R
          (fun q : SelectedCFZFormIndex e => q.1) t u := by
  simpa only [
    SmoothSieveCutoff.divisorExpansionFourierIntegrand,
    mul_comm] using
    sum_transformedPairedDivisorFamily_mul_cfzCanonicalCarryEulerAverage_eq_unrestricted_add_discrepancy
      (N := N) χ W b R
      (fun q : SelectedCFZFormIndex e => q.1) t u

/-- Exact integral form of the canonical unrestricted-plus-truncation
splice. -/
theorem
    SmoothSieveCutoff.selectedCFZCanonicalEulerFourierMainTerm_eq_integral_unrestricted_add_discrepancy
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff) (R W b : ℕ)
    (e : LinearFormsExponent k) :
    χ.selectedCFZCanonicalEulerFourierMainTerm
        (N := N) R W b e =
      (normalizedSelbergScale χ.normalizer R W : ℂ) ^
          Fintype.card (SelectedCFZFormIndex e) *
        (((Real.log R ^ 2 : ℝ) : ℂ) ^
            Fintype.card (SelectedCFZFormIndex e) *
          ∫ tu :
              (SelectedCFZFormIndex e → ℝ) ×
                (SelectedCFZFormIndex e → ℝ),
            (pairedCutoffFourierEnvelope χ tu.1 tu.2 *
                cfzCanonicalCarryUnrestrictedFourierAverage
                  (N := N) W b R
                  (fun q : SelectedCFZFormIndex e => q.1)
                  tu.1 tu.2 +
              cfzCanonicalCarryTruncationDiscrepancy
                (N := N) χ W b R
                (fun q : SelectedCFZFormIndex e => q.1)
                tu.1 tu.2)
            ∂(volume.prod volume)) := by
  unfold selectedCFZCanonicalEulerFourierMainTerm
  congr 2
  apply integral_congr_ae
  exact ae_of_all _ fun tu =>
    χ.selectedCFZCanonicalEulerFourierIntegrand_eq_unrestricted_add_discrepancy
      (N := N) R W b e tu.1 tu.2

/-- Strong scaled estimate retaining the exact coefficient-weighted LCM
mass. -/
theorem
    SmoothSieveCutoff.abs_mean_linearFormsProduct_cyclicMajorant_sub_canonicalEulerMainTerm_le_lcmMass
    {k N R W b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hR : 1 < R)
    (hb : 0 < b)
    (e : LinearFormsExponent k)
    (hfit :
      2 * R ^ (2 * Fintype.card (SelectedCFZFormIndex e)) ≤ N) :
    |mean
          (linearFormsProduct k N
            (χ.cyclicMajorant R W b) e) -
        χ.selectedCFZCanonicalEulerMainTerm
          (N := N) R W b e| ≤
      |normalizedSelbergScale χ.normalizer R W| ^
          Fintype.card (SelectedCFZFormIndex e) *
        |Real.log R ^ 2| ^
          Fintype.card (SelectedCFZFormIndex e) *
        ((selectedCFZCanonicalCyclicBoundaryConstant e : ℝ) *
          smoothDivisorFamilyLcmMass
            (κ := SelectedCFZFormIndex e) χ.toFun R /
          (N : ℝ)) := by
  classical
  rw [χ.mean_linearFormsProduct_cyclicMajorant_eq_divisorExpansion
    hR hb e]
  change
    |normalizedSelbergScale χ.normalizer R W ^
          Fintype.card (SelectedCFZFormIndex e) *
        ((Real.log R ^ 2) ^
            Fintype.card (SelectedCFZFormIndex e) *
          selectedCFZCyclicDivisorSum
            (N := N) χ R W b e) -
      normalizedSelbergScale χ.normalizer R W ^
          Fintype.card (SelectedCFZFormIndex e) *
        ((Real.log R ^ 2) ^
            Fintype.card (SelectedCFZFormIndex e) *
          selectedCFZCanonicalEulerDivisorSum
            (N := N) χ R W b e)| ≤ _
  rw [← mul_sub, ← mul_sub, abs_mul, abs_mul, abs_pow, abs_pow]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (χ.abs_selectedCFZCyclicDivisorSum_sub_canonicalEuler_le_lcmMass
          hk e W b hfit)
        (pow_nonneg (abs_nonneg _) _))
      (pow_nonneg (abs_nonneg _) _)

/-- Explicit scaled boundary estimate after discarding the divisor
coefficients and using the selected divisor-box cardinality. -/
theorem
    SmoothSieveCutoff.abs_mean_linearFormsProduct_cyclicMajorant_sub_canonicalEulerMainTerm_le_pow
    {k N R W b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hR : 1 < R)
    (hb : 0 < b)
    (e : LinearFormsExponent k)
    (hfit :
      2 * R ^ (2 * Fintype.card (SelectedCFZFormIndex e)) ≤ N) :
    |mean
          (linearFormsProduct k N
            (χ.cyclicMajorant R W b) e) -
        χ.selectedCFZCanonicalEulerMainTerm
          (N := N) R W b e| ≤
      |normalizedSelbergScale χ.normalizer R W| ^
          Fintype.card (SelectedCFZFormIndex e) *
        |Real.log R ^ 2| ^
          Fintype.card (SelectedCFZFormIndex e) *
        ((selectedCFZCanonicalCyclicBoundaryConstant e : ℝ) *
          (R ^ (2 * Fintype.card
            (SelectedCFZFormIndex e)) : ℝ) *
          (R ^ (2 * Fintype.card
            (SelectedCFZFormIndex e)) : ℝ) /
          (N : ℝ)) := by
  have hbase :=
    χ.abs_mean_linearFormsProduct_cyclicMajorant_sub_canonicalEulerMainTerm_le_lcmMass
      (W := W) hk hR hb e hfit
  have hmass :=
    χ.smoothDivisorFamilyLcmMass_le
      (κ := SelectedCFZFormIndex e) R
  have hinner :
      (selectedCFZCanonicalCyclicBoundaryConstant e : ℝ) *
          smoothDivisorFamilyLcmMass
            (κ := SelectedCFZFormIndex e) χ.toFun R /
          (N : ℝ) ≤
        (selectedCFZCanonicalCyclicBoundaryConstant e : ℝ) *
          (R ^ (2 * Fintype.card
            (SelectedCFZFormIndex e)) : ℝ) *
          (R ^ (2 * Fintype.card
            (SelectedCFZFormIndex e)) : ℝ) /
          (N : ℝ) := by
    have hconstant :
        0 ≤ (selectedCFZCanonicalCyclicBoundaryConstant e : ℝ) :=
      Nat.cast_nonneg _
    simpa only [mul_assoc] using
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmass hconstant)
        (by positivity)
  have hprefactor :
      0 ≤
        |normalizedSelbergScale χ.normalizer R W| ^
            Fintype.card (SelectedCFZFormIndex e) *
          |Real.log R ^ 2| ^
            Fintype.card (SelectedCFZFormIndex e) :=
    mul_nonneg
      (pow_nonneg (abs_nonneg _) _)
      (pow_nonneg (abs_nonneg _) _)
  exact hbase.trans
    (mul_le_mul_of_nonneg_left hinner hprefactor)

/-! ## A single polynomial joint scale -/

/-- Uniform power exponent for the canonical cyclic boundary.  Five powers
per ambient CFZ form absorb four divisor-box powers and one Selberg
normalization power. -/
def cfzCanonicalCyclicBoundaryExponent (k : ℕ) : ℕ :=
  5 * Fintype.card (CFZFormIndex k)

/-- The fixed scaled constant in the canonical cyclic boundary estimate. -/
noncomputable def
    SmoothSieveCutoff.selectedCFZCanonicalScaledCyclicBoundaryConstant
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) : ℝ :=
  χ.normalizer⁻¹ ^
      Fintype.card (SelectedCFZFormIndex e) *
    (selectedCFZCanonicalCyclicBoundaryConstant e : ℝ)

theorem
    SmoothSieveCutoff.selectedCFZCanonicalScaledCyclicBoundaryConstant_nonneg
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) :
    0 ≤ χ.selectedCFZCanonicalScaledCyclicBoundaryConstant e := by
  unfold selectedCFZCanonicalScaledCyclicBoundaryConstant
  exact mul_nonneg
    (pow_nonneg (inv_nonneg.mpr χ.normalizer_pos.le) _)
    (Nat.cast_nonneg _)

/-- In the primorial regime the whole scaled boundary is bounded by one
selected-family power `R^(5m)/N`. -/
theorem
    SmoothSieveCutoff.abs_mean_linearFormsProduct_cyclicMajorant_sub_canonicalEulerMainTerm_primorial_le_selectedPower
    {k N R w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hR : 2 ≤ R)
    (hb : 0 < b)
    (e : LinearFormsExponent k)
    (hfit :
      2 * R ^ (2 * Fintype.card (SelectedCFZFormIndex e)) ≤ N) :
    |mean
          (linearFormsProduct k N
            (χ.cyclicMajorant R (primorial w) b) e) -
        χ.selectedCFZCanonicalEulerMainTerm
          (N := N) R (primorial w) b e| ≤
      χ.selectedCFZCanonicalScaledCyclicBoundaryConstant e *
        (R : ℝ) ^
          (5 * Fintype.card (SelectedCFZFormIndex e)) /
        (N : ℝ) := by
  let m := Fintype.card (SelectedCFZFormIndex e)
  have hraw :=
    χ.abs_mean_linearFormsProduct_cyclicMajorant_sub_canonicalEulerMainTerm_le_pow
      (W := primorial w) hk (by omega : 1 < R) hb e hfit
  have hbase :
      |normalizedSelbergScale
          χ.normalizer R (primorial w)| *
          |Real.log R ^ 2| ≤
        χ.normalizer⁻¹ * (1 + Real.log R) :=
    χ.abs_normalizedSelbergScale_mul_logSq_le hR w
  have hbaseNonneg :
      0 ≤
        |normalizedSelbergScale
            χ.normalizer R (primorial w)| *
          |Real.log R ^ 2| := by
    positivity
  have hlogNonneg : 0 ≤ 1 + Real.log R := by
    have hlog :
        0 ≤ Real.log R :=
      (Real.log_pos
        (by exact_mod_cast hR : (1 : ℝ) < R)).le
    linarith
  have hlogLe : 1 + Real.log R ≤ (R : ℝ) := by
    have hRpos : (0 : ℝ) < R := by positivity
    have hlog := Real.log_le_sub_one_of_pos hRpos
    linarith
  have hinvNonneg : 0 ≤ χ.normalizer⁻¹ :=
    inv_nonneg.mpr χ.normalizer_pos.le
  have hupperBaseNonneg :
      0 ≤ χ.normalizer⁻¹ * (1 + Real.log R) :=
    mul_nonneg hinvNonneg hlogNonneg
  have hprefactor :
      |normalizedSelbergScale
          χ.normalizer R (primorial w)| ^ m *
          |Real.log R ^ 2| ^ m ≤
        χ.normalizer⁻¹ ^ m * (R : ℝ) ^ m := by
    calc
      |normalizedSelbergScale
            χ.normalizer R (primorial w)| ^ m *
          |Real.log R ^ 2| ^ m =
        (|normalizedSelbergScale
              χ.normalizer R (primorial w)| *
            |Real.log R ^ 2|) ^ m := by
        rw [mul_pow]
      _ ≤
        (χ.normalizer⁻¹ * (1 + Real.log R)) ^ m :=
          pow_le_pow_left₀ hbaseNonneg hbase m
      _ ≤ (χ.normalizer⁻¹ * (R : ℝ)) ^ m := by
        exact
          pow_le_pow_left₀ hupperBaseNonneg
            (mul_le_mul_of_nonneg_left hlogLe hinvNonneg) m
      _ = χ.normalizer⁻¹ ^ m * (R : ℝ) ^ m := by
        rw [mul_pow]
  have hinner :
      0 ≤
        (selectedCFZCanonicalCyclicBoundaryConstant e : ℝ) *
          (R : ℝ) ^ (2 * m) *
          (R : ℝ) ^ (2 * m) /
          (N : ℝ) := by
    positivity
  calc
    |mean
          (linearFormsProduct k N
            (χ.cyclicMajorant R (primorial w) b) e) -
        χ.selectedCFZCanonicalEulerMainTerm
          (N := N) R (primorial w) b e| ≤
      |normalizedSelbergScale
          χ.normalizer R (primorial w)| ^ m *
        |Real.log R ^ 2| ^ m *
        ((selectedCFZCanonicalCyclicBoundaryConstant e : ℝ) *
          (R : ℝ) ^ (2 * m) *
          (R : ℝ) ^ (2 * m) /
          (N : ℝ)) := by
      simpa only [m] using hraw
    _ ≤
      (χ.normalizer⁻¹ ^ m * (R : ℝ) ^ m) *
        ((selectedCFZCanonicalCyclicBoundaryConstant e : ℝ) *
          (R : ℝ) ^ (2 * m) *
          (R : ℝ) ^ (2 * m) /
          (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hprefactor hinner
    _ =
      χ.selectedCFZCanonicalScaledCyclicBoundaryConstant e *
        (R : ℝ) ^ (5 * m) / (N : ℝ) := by
      unfold selectedCFZCanonicalScaledCyclicBoundaryConstant
      rw [show 5 * m = m + 2 * m + 2 * m by omega,
        pow_add, pow_add]
      ring
    _ = _ := by rfl

/-- Uniform ambient-CFZ power form of the scaled canonical boundary. -/
theorem
    SmoothSieveCutoff.abs_mean_linearFormsProduct_cyclicMajorant_sub_canonicalEulerMainTerm_primorial_le_power
    {k N R w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hR : 2 ≤ R)
    (hb : 0 < b)
    (e : LinearFormsExponent k)
    (hfit :
      2 * R ^ (2 * Fintype.card (SelectedCFZFormIndex e)) ≤ N) :
    |mean
          (linearFormsProduct k N
            (χ.cyclicMajorant R (primorial w) b) e) -
        χ.selectedCFZCanonicalEulerMainTerm
          (N := N) R (primorial w) b e| ≤
      χ.selectedCFZCanonicalScaledCyclicBoundaryConstant e *
        (R : ℝ) ^ cfzCanonicalCyclicBoundaryExponent k /
        (N : ℝ) := by
  have hselected :=
    χ.abs_mean_linearFormsProduct_cyclicMajorant_sub_canonicalEulerMainTerm_primorial_le_selectedPower
      hk hR hb e hfit (w := w)
  have hRone : (1 : ℝ) ≤ R := by
    exact_mod_cast (show 1 ≤ R by omega)
  have hexponent :
      5 * Fintype.card (SelectedCFZFormIndex e) ≤
        cfzCanonicalCyclicBoundaryExponent k := by
    unfold cfzCanonicalCyclicBoundaryExponent
    exact Nat.mul_le_mul_left 5
      (card_selectedCFZFormIndex_le e)
  have hpow :
      (R : ℝ) ^
          (5 * Fintype.card (SelectedCFZFormIndex e)) ≤
        (R : ℝ) ^ cfzCanonicalCyclicBoundaryExponent k :=
    pow_le_pow_right₀ hRone hexponent
  have hconstant :=
    χ.selectedCFZCanonicalScaledCyclicBoundaryConstant_nonneg e
  exact hselected.trans
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow hconstant)
      (by positivity))

/-- Direct complex-Fourier version of the preceding comparison. -/
theorem
    SmoothSieveCutoff.norm_mean_linearFormsProduct_cyclicMajorant_sub_canonicalEulerFourierMainTerm_primorial_le_power
    {k N R w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hR : 2 ≤ R)
    (hb : 0 < b)
    (e : LinearFormsExponent k)
    (hfit :
      2 * R ^ (2 * Fintype.card (SelectedCFZFormIndex e)) ≤ N) :
    ‖(mean
          (linearFormsProduct k N
            (χ.cyclicMajorant R (primorial w) b) e) : ℂ) -
        χ.selectedCFZCanonicalEulerFourierMainTerm
          (N := N) R (primorial w) b e‖ ≤
      χ.selectedCFZCanonicalScaledCyclicBoundaryConstant e *
        (R : ℝ) ^ cfzCanonicalCyclicBoundaryExponent k /
        (N : ℝ) := by
  rw [← χ.coe_selectedCFZCanonicalEulerMainTerm_eq_fourierMainTerm]
  simpa only [← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] using
    χ.abs_mean_linearFormsProduct_cyclicMajorant_sub_canonicalEulerMainTerm_primorial_le_power
      hk hR hb e hfit (w := w)

/-- The power-ratio schedule itself eventually forces the single global
divisor-box fit condition. -/
theorem eventually_two_mul_cfzDivisorBox_le_of_boundaryPower_tendsto_zero
    {k : ℕ}
    (hk : 2 ≤ k)
    (R Nseq : ℕ → ℕ)
    (hN : ∀ n, Nseq n ≠ 0)
    (hR : ∀ᶠ n : ℕ in atTop, 2 ≤ R n)
    (hscale :
      Tendsto
        (fun n : ℕ =>
          (R n : ℝ) ^ cfzCanonicalCyclicBoundaryExponent k /
            (Nseq n : ℝ))
        atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      2 * R n ^ (2 * Fintype.card (CFZFormIndex k)) ≤
        Nseq n := by
  have hfullPos :
      0 < Fintype.card (CFZFormIndex k) := by
    apply Fintype.card_pos_iff.mpr
    exact
      ⟨⟨⟨0, by omega⟩, fun _ => false⟩⟩
  have hclose :
      ∀ᶠ n : ℕ in atTop,
        dist
          ((R n : ℝ) ^
              cfzCanonicalCyclicBoundaryExponent k /
            (Nseq n : ℝ))
          0 < 1 :=
    (Metric.tendsto_nhds.mp hscale) 1 zero_lt_one
  filter_upwards [hR, hclose] with n hRn hcloseN
  have hNposNat : 0 < Nseq n :=
    Nat.pos_of_ne_zero (hN n)
  have hNpos : (0 : ℝ) < Nseq n := by
    exact_mod_cast hNposNat
  have hquotNonneg :
      0 ≤
        (R n : ℝ) ^ cfzCanonicalCyclicBoundaryExponent k /
          (Nseq n : ℝ) :=
    div_nonneg (by positivity) hNpos.le
  have hquotLt :
      (R n : ℝ) ^ cfzCanonicalCyclicBoundaryExponent k /
          (Nseq n : ℝ) < 1 := by
    simpa only [Real.dist_eq, sub_zero,
      abs_of_nonneg hquotNonneg] using hcloseN
  rw [div_lt_one hNpos] at hquotLt
  have hpowLt :
      R n ^ cfzCanonicalCyclicBoundaryExponent k <
        Nseq n := by
    exact_mod_cast hquotLt
  have hextra : 1 ≤ 3 * Fintype.card (CFZFormIndex k) := by
    omega
  have hpowExtra :
      2 ≤ R n ^ (3 * Fintype.card (CFZFormIndex k)) := by
    calc
      2 ≤ R n := hRn
      _ = R n ^ 1 := by simp
      _ ≤ R n ^ (3 * Fintype.card (CFZFormIndex k)) :=
        Nat.pow_le_pow_right (by omega) hextra
  have hboxPower :
      2 * R n ^ (2 * Fintype.card (CFZFormIndex k)) ≤
        R n ^ cfzCanonicalCyclicBoundaryExponent k := by
    calc
      2 * R n ^ (2 * Fintype.card (CFZFormIndex k)) ≤
          R n ^ (3 * Fintype.card (CFZFormIndex k)) *
            R n ^ (2 * Fintype.card (CFZFormIndex k)) :=
        Nat.mul_le_mul_right _ hpowExtra
      _ = R n ^ cfzCanonicalCyclicBoundaryExponent k := by
        rw [← pow_add]
        unfold cfzCanonicalCyclicBoundaryExponent
        congr 1
        omega
  exact hboxPower.trans hpowLt.le

/-- Joint asymptotic vanishing of the complete canonical cyclic boundary.
The power schedule is uniform in the Boolean-selected subfamily; the global
fit condition is likewise stated using the ambient CFZ family. -/
theorem
    SmoothSieveCutoff.tendsto_abs_mean_linearFormsProduct_cyclicMajorant_sub_canonicalEulerMainTerm_primorial_zero_of_power_schedule_and_fit
    {k : ℕ}
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (e : LinearFormsExponent k)
    (R Nseq wseq bseq : ℕ → ℕ)
    (hN : ∀ n, Nseq n ≠ 0)
    (hR : ∀ᶠ n : ℕ in atTop, 2 ≤ R n)
    (hb : ∀ᶠ n : ℕ in atTop, 0 < bseq n)
    (hfit :
      ∀ᶠ n : ℕ in atTop,
        2 * R n ^ (2 * Fintype.card (CFZFormIndex k)) ≤
          Nseq n)
    (hscale :
      Tendsto
        (fun n : ℕ =>
          (R n : ℝ) ^ cfzCanonicalCyclicBoundaryExponent k /
            (Nseq n : ℝ))
        atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        letI : NeZero (Nseq n) := ⟨hN n⟩
        |mean
              (linearFormsProduct k (Nseq n)
                (χ.cyclicMajorant
                  (R n) (primorial (wseq n)) (bseq n)) e) -
            χ.selectedCFZCanonicalEulerMainTerm
              (N := Nseq n) (R n)
              (primorial (wseq n)) (bseq n) e|)
      atTop (𝓝 0) := by
  let C :=
    χ.selectedCFZCanonicalScaledCyclicBoundaryConstant e
  have hupper :
      Tendsto
        (fun n : ℕ =>
          C *
            ((R n : ℝ) ^
                cfzCanonicalCyclicBoundaryExponent k /
              (Nseq n : ℝ)))
        atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hscale)
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n => by
      letI : NeZero (Nseq n) := ⟨hN n⟩
      exact abs_nonneg _
  · filter_upwards [hR, hb, hfit] with n hRn hbn hfitn
    letI : NeZero (Nseq n) := ⟨hN n⟩
    have hcard :
        Fintype.card (SelectedCFZFormIndex e) ≤
          Fintype.card (CFZFormIndex k) :=
      card_selectedCFZFormIndex_le e
    have hpow :
        R n ^ (2 * Fintype.card (SelectedCFZFormIndex e)) ≤
          R n ^ (2 * Fintype.card (CFZFormIndex k)) :=
      Nat.pow_le_pow_right (by omega)
        (Nat.mul_le_mul_left 2 hcard)
    have hselectedFit :
        2 * R n ^ (2 * Fintype.card (SelectedCFZFormIndex e)) ≤
          Nseq n :=
      (Nat.mul_le_mul_left 2 hpow).trans hfitn
    exact
      χ.abs_mean_linearFormsProduct_cyclicMajorant_sub_canonicalEulerMainTerm_primorial_le_power
        hk hRn hbn e hselectedFit (w := wseq n)
  · simpa only [C, mul_div_assoc] using hupper

/-- Complex Fourier-main version of the same joint limit. -/
theorem
    SmoothSieveCutoff.tendsto_norm_mean_linearFormsProduct_cyclicMajorant_sub_canonicalEulerFourierMainTerm_primorial_zero_of_power_schedule_and_fit
    {k : ℕ}
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (e : LinearFormsExponent k)
    (R Nseq wseq bseq : ℕ → ℕ)
    (hN : ∀ n, Nseq n ≠ 0)
    (hR : ∀ᶠ n : ℕ in atTop, 2 ≤ R n)
    (hb : ∀ᶠ n : ℕ in atTop, 0 < bseq n)
    (hfit :
      ∀ᶠ n : ℕ in atTop,
        2 * R n ^ (2 * Fintype.card (CFZFormIndex k)) ≤
          Nseq n)
    (hscale :
      Tendsto
        (fun n : ℕ =>
          (R n : ℝ) ^ cfzCanonicalCyclicBoundaryExponent k /
            (Nseq n : ℝ))
        atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        letI : NeZero (Nseq n) := ⟨hN n⟩
        ‖(mean
              (linearFormsProduct k (Nseq n)
                (χ.cyclicMajorant
                  (R n) (primorial (wseq n)) (bseq n)) e) : ℂ) -
            χ.selectedCFZCanonicalEulerFourierMainTerm
              (N := Nseq n) (R n)
              (primorial (wseq n)) (bseq n) e‖)
      atTop (𝓝 0) := by
  have hreal :=
    χ.tendsto_abs_mean_linearFormsProduct_cyclicMajorant_sub_canonicalEulerMainTerm_primorial_zero_of_power_schedule_and_fit
      hk e R Nseq wseq bseq hN hR hb hfit hscale
  apply hreal.congr'
  exact Filter.Eventually.of_forall fun n => by
    letI : NeZero (Nseq n) := ⟨hN n⟩
    change
      |mean
            (linearFormsProduct k (Nseq n)
              (χ.cyclicMajorant
                (R n) (primorial (wseq n)) (bseq n)) e) -
          χ.selectedCFZCanonicalEulerMainTerm
            (N := Nseq n) (R n)
            (primorial (wseq n)) (bseq n) e| =
        ‖(mean
            (linearFormsProduct k (Nseq n)
              (χ.cyclicMajorant
                (R n) (primorial (wseq n)) (bseq n)) e) : ℂ) -
          χ.selectedCFZCanonicalEulerFourierMainTerm
            (N := Nseq n) (R n)
            (primorial (wseq n)) (bseq n) e‖
    rw [←
      χ.coe_selectedCFZCanonicalEulerMainTerm_eq_fourierMainTerm]
    simp only [← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]

/-- The clean power-schedule endpoint: `R^A_k / N → 0` alone, together
with `R ≥ 2` and positivity of the residue representative, makes the whole
canonical cyclic-to-Euler boundary vanish. -/
theorem
    SmoothSieveCutoff.tendsto_abs_mean_linearFormsProduct_cyclicMajorant_sub_canonicalEulerMainTerm_primorial_zero_of_power_schedule
    {k : ℕ}
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (e : LinearFormsExponent k)
    (R Nseq wseq bseq : ℕ → ℕ)
    (hN : ∀ n, Nseq n ≠ 0)
    (hR : ∀ᶠ n : ℕ in atTop, 2 ≤ R n)
    (hb : ∀ᶠ n : ℕ in atTop, 0 < bseq n)
    (hscale :
      Tendsto
        (fun n : ℕ =>
          (R n : ℝ) ^ cfzCanonicalCyclicBoundaryExponent k /
            (Nseq n : ℝ))
        atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        letI : NeZero (Nseq n) := ⟨hN n⟩
        |mean
              (linearFormsProduct k (Nseq n)
                (χ.cyclicMajorant
                  (R n) (primorial (wseq n)) (bseq n)) e) -
            χ.selectedCFZCanonicalEulerMainTerm
              (N := Nseq n) (R n)
              (primorial (wseq n)) (bseq n) e|)
      atTop (𝓝 0) := by
  have hfit :=
    eventually_two_mul_cfzDivisorBox_le_of_boundaryPower_tendsto_zero
      hk R Nseq hN hR hscale
  exact
    χ.tendsto_abs_mean_linearFormsProduct_cyclicMajorant_sub_canonicalEulerMainTerm_primorial_zero_of_power_schedule_and_fit
      hk e R Nseq wseq bseq hN hR hb hfit hscale

/-- Clean power-schedule endpoint against the exact complex Fourier main
term. -/
theorem
    SmoothSieveCutoff.tendsto_norm_mean_linearFormsProduct_cyclicMajorant_sub_canonicalEulerFourierMainTerm_primorial_zero_of_power_schedule
    {k : ℕ}
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (e : LinearFormsExponent k)
    (R Nseq wseq bseq : ℕ → ℕ)
    (hN : ∀ n, Nseq n ≠ 0)
    (hR : ∀ᶠ n : ℕ in atTop, 2 ≤ R n)
    (hb : ∀ᶠ n : ℕ in atTop, 0 < bseq n)
    (hscale :
      Tendsto
        (fun n : ℕ =>
          (R n : ℝ) ^ cfzCanonicalCyclicBoundaryExponent k /
            (Nseq n : ℝ))
        atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        letI : NeZero (Nseq n) := ⟨hN n⟩
        ‖(mean
              (linearFormsProduct k (Nseq n)
                (χ.cyclicMajorant
                  (R n) (primorial (wseq n)) (bseq n)) e) : ℂ) -
            χ.selectedCFZCanonicalEulerFourierMainTerm
              (N := Nseq n) (R n)
              (primorial (wseq n)) (bseq n) e‖)
      atTop (𝓝 0) := by
  have hfit :=
    eventually_two_mul_cfzDivisorBox_le_of_boundaryPower_tendsto_zero
      hk R Nseq hN hR hscale
  exact
    χ.tendsto_norm_mean_linearFormsProduct_cyclicMajorant_sub_canonicalEulerFourierMainTerm_primorial_zero_of_power_schedule_and_fit
      hk e R Nseq wseq bseq hN hR hb hfit hscale

end Wikipedia.SzemeredisTheorem
