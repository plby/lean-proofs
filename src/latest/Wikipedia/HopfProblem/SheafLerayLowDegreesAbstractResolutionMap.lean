import Wikipedia.HopfProblem.SheafLerayLowDegreesAbstractResolution
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionMaps

/-!
# Maps of the native low-degree augmented resolutions

Every cochain map induces the actual maps on degree-zero homology, degree-zero
objects, degree-one cycles, and degree-one homology.  The universal properties
of cycles and homology prove that these form a map of augmented resolutions.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open HomologicalComplex

namespace Wikipedia.HopfProblem.SheafLerayLowDegrees.Abstract

universe u

variable {C : Type u} [Category.{0} C] [Abelian C]
  {K L : CochainComplex C ℕ}

/-- Restricting the differential to cycles commutes with a cochain map. -/
@[reassoc]
theorem boundaryToCycles_naturality (φ : K ⟶ L) :
    φ.f 0 ≫ boundaryToCycles L = boundaryToCycles K ≫ cyclesMap φ 1 := by
  rw [← cancel_mono (L.iCycles 1)]
  simp only [assoc, boundaryToCycles_iCycles, cyclesMap_i,
    boundaryToCycles_iCycles_assoc]
  exact φ.comm 0 1

/-- The degree-zero homology inclusions commute with the actual homology map. -/
@[reassoc]
theorem initialι_naturality (φ : K ⟶ L) :
    homologyMap φ 0 ≫ initialι L = initialι K ≫ φ.f 0 := by
  rw [← cancel_epi (K.homologyπ 0)]
  simp only [homologyπ_naturality_assoc, homologyπ_initialι,
    homologyπ_initialι_assoc, cyclesMap_i]

/-- The native map of short complexes in the low-degree augmented resolutions. -/
@[simps]
def complexMap (φ : K ⟶ L) : complex K ⟶ complex L where
  τ₁ := φ.f 0
  τ₂ := cyclesMap φ 1
  τ₃ := homologyMap φ 1
  comm₁₂ := boundaryToCycles_naturality φ
  comm₂₃ := (homologyπ_naturality φ 1).symm

/-- A cochain map gives a genuine map of the actual augmented resolutions. -/
def resolutionMap (φ : K ⟶ L) :
    CuspNormalization.SheafCohomologyResolution.AugmentedResolution.Hom
      (resolution K) (resolution L) where
  augmentation := homologyMap φ 0
  complex := complexMap φ
  comm := initialι_naturality φ

@[simp]
theorem resolutionMap_augmentation (φ : K ⟶ L) :
    (resolutionMap φ).augmentation = homologyMap φ 0 := rfl

@[simp]
theorem resolutionMap_complex (φ : K ⟶ L) :
    (resolutionMap φ).complex = complexMap φ := rfl

@[simp]
theorem resolutionMap_complex_τ₁ (φ : K ⟶ L) :
    (resolutionMap φ).complex.τ₁ = φ.f 0 := rfl

@[simp]
theorem resolutionMap_complex_τ₂ (φ : K ⟶ L) :
    (resolutionMap φ).complex.τ₂ = cyclesMap φ 1 := rfl

@[simp]
theorem resolutionMap_complex_τ₃ (φ : K ⟶ L) :
    (resolutionMap φ).complex.τ₃ = homologyMap φ 1 := rfl

end Wikipedia.HopfProblem.SheafLerayLowDegrees.Abstract
