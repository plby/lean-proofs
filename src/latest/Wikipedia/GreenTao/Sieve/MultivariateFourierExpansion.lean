import Wikipedia.GreenTao.Sieve.LinearFormsExpansion
import Wikipedia.GreenTao.Sieve.SmoothCutoffFourierProductTail
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Multivariate Fourier rewrite of the divisor expansion

The finite Selberg-square expansion has two smooth divisor coefficients for
each form.  Fourier inversion turns those `2 * card κ` coefficients into a
single integral over two copies of `κ → ℝ`.

This file proves that rewrite exactly.  All sum/integral interchanges are
finite, while absolute integrability follows coordinatewise from the
Schwartz transform.  The arithmetic divisibility density is left as an
arbitrary real coefficient, ready for the Euler-product comparison.
-/

namespace Wikipedia.SzemeredisTheorem

open MeasureTheory
open scoped ArithmeticFunction.Moebius BigOperators

namespace SmoothSieveCutoff

/-- One `κ`-variable half of the transformed paired-divisor coefficient. -/
noncomputable def transformedDivisorFamilySide
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (d : κ → ℕ) (t : κ → ℝ) : ℂ :=
  ∏ q,
    (ArithmeticFunction.moebius (d q) : ℂ) *
      χ.cutoffFourierTransform (t q) *
        divisorMultiplicativePhase R (d q) (t q)

/-- The coordinatewise transformed divisor family is absolutely
integrable. -/
theorem integrable_transformedDivisorFamilySide
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (d : κ → ℕ) :
    Integrable (χ.transformedDivisorFamilySide R d :
      (κ → ℝ) → ℂ) := by
  rw [MeasureTheory.volume_pi]
  exact Integrable.fintype_prod fun q =>
    χ.integrable_transformedSmoothDivisorSummand R (d q)

/-- Fubini factorization of one half of a transformed divisor family. -/
theorem integral_transformedDivisorFamilySide_eq_prod
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (d : κ → ℕ) :
    (∫ t : κ → ℝ,
        χ.transformedDivisorFamilySide R d t) =
      ∏ q,
        (smoothDivisorSummand χ.toFun R (d q) : ℂ) := by
  unfold transformedDivisorFamilySide
  rw [MeasureTheory.volume_pi]
  calc
    (∫ t : κ → ℝ,
        ∏ q,
          (ArithmeticFunction.moebius (d q) : ℂ) *
            χ.cutoffFourierTransform (t q) *
              divisorMultiplicativePhase R (d q) (t q)
        ∂(Measure.pi fun _ : κ => volume)) =
        ∏ q, ∫ x : ℝ,
          (ArithmeticFunction.moebius (d q) : ℂ) *
            χ.cutoffFourierTransform x *
              divisorMultiplicativePhase R (d q) x :=
      integral_fintype_prod_eq_prod
        (fun q x =>
          (ArithmeticFunction.moebius (d q) : ℂ) *
            χ.cutoffFourierTransform x *
              divisorMultiplicativePhase R (d q) x)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro q _hq
      exact (χ.smoothDivisorSummand_eq_integral R (d q)).symm

/-- The full transformed coefficient for one paired divisor family. -/
noncomputable def transformedPairedDivisorFamily
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (z : κ → ℕ × ℕ)
    (tu : (κ → ℝ) × (κ → ℝ)) : ℂ :=
  χ.transformedDivisorFamilySide R (fun q => (z q).1) tu.1 *
    χ.transformedDivisorFamilySide R (fun q => (z q).2) tu.2

/-- Absolute integrability of one full paired-family integrand. -/
theorem integrable_transformedPairedDivisorFamily
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (z : κ → ℕ × ℕ) :
    Integrable
      (χ.transformedPairedDivisorFamily R z)
      (volume.prod volume) :=
  (χ.integrable_transformedDivisorFamilySide R
      (fun q => (z q).1)).mul_prod
    (χ.integrable_transformedDivisorFamilySide R
      (fun q => (z q).2))

/-- Product-space integral of a paired divisor family. -/
theorem integral_transformedPairedDivisorFamily_eq
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (z : κ → ℕ × ℕ) :
    (∫ tu : (κ → ℝ) × (κ → ℝ),
        χ.transformedPairedDivisorFamily R z tu
        ∂(volume.prod volume)) =
      (∏ q,
          (smoothDivisorSummand
            χ.toFun R (z q).1 : ℂ)) *
        ∏ q,
          (smoothDivisorSummand
            χ.toFun R (z q).2 : ℂ) := by
  unfold transformedPairedDivisorFamily
  rw [integral_prod_mul,
    χ.integral_transformedDivisorFamilySide_eq_prod
      R (fun q => (z q).1),
    χ.integral_transformedDivisorFamilySide_eq_prod
      R (fun q => (z q).2)]

/-- Exact Fourier integral for the smooth coefficient of one paired divisor
family. -/
theorem smoothDivisorFamilyCoefficient_eq_integral
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (z : κ → ℕ × ℕ) :
    (smoothDivisorFamilyCoefficient χ.toFun R z : ℂ) =
      ∫ tu : (κ → ℝ) × (κ → ℝ),
        χ.transformedPairedDivisorFamily R z tu
        ∂(volume.prod volume) := by
  rw [χ.integral_transformedPairedDivisorFamily_eq R z]
  unfold smoothDivisorFamilyCoefficient
  rw [Finset.prod_mul_distrib]
  push_cast
  rfl

/-- Fourier integrand for the entire finite divisor-family sum, with an
arbitrary real arithmetic coefficient attached to each family. -/
noncomputable def divisorExpansionFourierIntegrand
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (density : (κ → ℕ × ℕ) → ℝ)
    (tu : (κ → ℝ) × (κ → ℝ)) : ℂ :=
  ∑ z ∈ smoothDivisorFamilyChoices κ R,
    (density z : ℂ) *
      χ.transformedPairedDivisorFamily R z tu

/-- Absolute integrability of the full finite divisor-family Fourier
integrand. -/
theorem integrable_divisorExpansionFourierIntegrand
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (density : (κ → ℕ × ℕ) → ℝ) :
    Integrable
      (χ.divisorExpansionFourierIntegrand R density)
      (volume.prod volume) := by
  unfold divisorExpansionFourierIntegrand
  apply integrable_finsetSum
  intro z _hz
  exact
    (χ.integrable_transformedPairedDivisorFamily R z).const_mul
      (density z : ℂ)

/-- **Exact multivariate Fourier rewrite.**  The whole finite sum of smooth
paired-divisor coefficients is one absolutely convergent product-space
integral. -/
theorem sum_smoothDivisorFamilyCoefficient_eq_integral
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (density : (κ → ℕ × ℕ) → ℝ) :
    ((∑ z ∈ smoothDivisorFamilyChoices κ R,
        smoothDivisorFamilyCoefficient χ.toFun R z *
          density z : ℝ) : ℂ) =
      ∫ tu : (κ → ℝ) × (κ → ℝ),
        χ.divisorExpansionFourierIntegrand R density tu
        ∂(volume.prod volume) := by
  unfold divisorExpansionFourierIntegrand
  rw [MeasureTheory.integral_finsetSum]
  · push_cast
    apply Finset.sum_congr rfl
    intro z _hz
    rw [integral_const_mul,
      ← χ.smoothDivisorFamilyCoefficient_eq_integral R z]
    ring
  · intro z _hz
    exact
      (χ.integrable_transformedPairedDivisorFamily R z).const_mul
        (density z : ℂ)

/-- The exact CFZ Selberg-majorant mean with its finite divisor sum replaced
by the multivariate Fourier integral. -/
theorem mean_prod_majorant_cfz_eq_fourierIntegral
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    {R W b : ℕ} (hR : 1 < R) (hb : 0 < b) :
    (mean (fun x : CubePoint k N =>
        ∏ q : CFZFormIndex k,
          χ.majorant R W
            (cfzWTrickedLinearValue W b q x)) : ℂ) =
      (normalizedSelbergScale χ.normalizer R W : ℂ) ^
          Fintype.card (CFZFormIndex k) *
        (((Real.log R ^ 2 : ℝ) : ℂ) ^
            Fintype.card (CFZFormIndex k) *
          ∫ tu :
              (CFZFormIndex k → ℝ) ×
                (CFZFormIndex k → ℝ),
            χ.divisorExpansionFourierIntegrand R
              (fun z =>
                pairedDivisibilityDensity
                  (cfzWTrickedLinearValue
                    (k := k) (N := N) W b) z)
              tu ∂(volume.prod volume)) := by
  have hmean :=
    χ.mean_prod_majorant_cfz_eq_divisorExpansion
      (k := k) (N := N) (R := R) (W := W) (b := b)
      hR hb
  have hsum :=
    χ.sum_smoothDivisorFamilyCoefficient_eq_integral R
      (fun z =>
        pairedDivisibilityDensity
          (cfzWTrickedLinearValue
            (k := k) (N := N) W b) z)
  calc
    (mean (fun x : CubePoint k N =>
        ∏ q : CFZFormIndex k,
          χ.majorant R W
            (cfzWTrickedLinearValue W b q x)) : ℂ) =
        ((normalizedSelbergScale χ.normalizer R W ^
            Fintype.card (CFZFormIndex k) *
          ((Real.log R ^ 2) ^
              Fintype.card (CFZFormIndex k) *
            ∑ z ∈ smoothDivisorFamilyChoices
                (CFZFormIndex k) R,
              smoothDivisorFamilyCoefficient χ.toFun R z *
                pairedDivisibilityDensity
                  (cfzWTrickedLinearValue
                    (k := k) (N := N) W b) z) : ℝ) : ℂ) := by
      exact congrArg (fun x : ℝ => (x : ℂ)) hmean
    _ =
        (normalizedSelbergScale χ.normalizer R W : ℂ) ^
            Fintype.card (CFZFormIndex k) *
          (((Real.log R ^ 2 : ℝ) : ℂ) ^
              Fintype.card (CFZFormIndex k) *
            ((∑ z ∈ smoothDivisorFamilyChoices
                  (CFZFormIndex k) R,
                smoothDivisorFamilyCoefficient χ.toFun R z *
                  pairedDivisibilityDensity
                    (cfzWTrickedLinearValue
                      (k := k) (N := N) W b) z : ℝ) : ℂ)) := by
      norm_cast
    _ = _ := by
      rw [hsum]

end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem
