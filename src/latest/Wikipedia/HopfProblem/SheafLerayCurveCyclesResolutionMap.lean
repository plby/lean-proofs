import Wikipedia.HopfProblem.SheafLerayCurveCyclesResolution
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionMaps

/-!
# Cochain maps on the actual all-degree cycles resolutions

The augmentation map is the original map on degree-`n` cycles. The
remaining maps are the original degree-`n` component, degree-`n+1`
cycles map, and degree-`n+1` homology map.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open HomologicalComplex

namespace Wikipedia.HopfProblem.SheafLerayCurve.Abstract

universe u

variable {C : Type u} [Category.{0} C] [Abelian C]
  {K L : CochainComplex C ℕ}

/-- The original differential into cycles commutes with the original cochain map. -/
@[reassoc] theorem cyclesBoundary_naturality (φ : K ⟶ L) (n : ℕ) :
    φ.f n ≫ L.toCycles n (n + 1) =
      K.toCycles n (n + 1) ≫ cyclesMap φ (n + 1) := by
  apply (cancel_mono (L.iCycles (n + 1))).mp
  calc
    (φ.f n ≫ L.toCycles n (n + 1)) ≫ L.iCycles (n + 1) =
        φ.f n ≫ L.d n (n + 1) := by rw [assoc, L.toCycles_i]
    _ = K.d n (n + 1) ≫ φ.f (n + 1) := φ.comm n (n + 1)
    _ = (K.toCycles n (n + 1) ≫ cyclesMap φ (n + 1)) ≫ L.iCycles (n + 1) := by
      rw [assoc, cyclesMap_i, ← assoc, K.toCycles_i]

/-- The genuine map of the original three-term short complexes. -/
@[simps] def cyclesComplexMap (φ : K ⟶ L) (n : ℕ) :
    cyclesComplex K n ⟶ cyclesComplex L n where
  τ₁ := φ.f n
  τ₂ := cyclesMap φ (n + 1)
  τ₃ := homologyMap φ (n + 1)
  comm₁₂ := cyclesBoundary_naturality φ n
  comm₂₃ := (homologyπ_naturality φ (n + 1)).symm

/-- The actual cycles augmented resolution is natural in the original complex. -/
def cyclesResolutionMap (φ : K ⟶ L) (n : ℕ) :
    CuspNormalization.SheafCohomologyResolution.AugmentedResolution.Hom
      (cyclesResolution K n) (cyclesResolution L n) where
  augmentation := cyclesMap φ n
  complex := cyclesComplexMap φ n
  comm := cyclesMap_i φ n

@[simp] theorem cyclesResolutionMap_augmentation (φ : K ⟶ L) (n : ℕ) :
    (cyclesResolutionMap φ n).augmentation = cyclesMap φ n := rfl

@[simp] theorem cyclesResolutionMap_complex (φ : K ⟶ L) (n : ℕ) :
    (cyclesResolutionMap φ n).complex = cyclesComplexMap φ n := rfl

@[simp] theorem cyclesResolutionMap_complex_τ₁ (φ : K ⟶ L) (n : ℕ) :
    (cyclesResolutionMap φ n).complex.τ₁ = φ.f n := rfl

@[simp] theorem cyclesResolutionMap_complex_τ₂ (φ : K ⟶ L) (n : ℕ) :
    (cyclesResolutionMap φ n).complex.τ₂ = cyclesMap φ (n + 1) := rfl

@[simp] theorem cyclesResolutionMap_complex_τ₃ (φ : K ⟶ L) (n : ℕ) :
    (cyclesResolutionMap φ n).complex.τ₃ = homologyMap φ (n + 1) := rfl

end Wikipedia.HopfProblem.SheafLerayCurve.Abstract
