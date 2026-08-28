import Wikipedia.HopfProblem.ConstantSheafSingularComparisonLowExtTruncation
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionMaps

/-!
# Actual maps of cochain resolutions and their degree-two truncations
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.LowExt

open CuspNormalization.SheafCohomologyResolution

universe v u

namespace CochainResolution

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A genuine augmented cochain map. -/
structure Hom (R S : CochainResolution C) where
  augmentation : R.F ⟶ S.F
  complex : R.K ⟶ S.K
  comm : augmentation ≫ S.ι = R.ι ≫ complex.f 0

namespace Hom

variable {R S : CochainResolution C} (φ : Hom R S)

/-- The actual induced map on the kernels of the degree-two differentials. -/
def cycles₂Map : R.cycles₂ ⟶ S.cycles₂ :=
  kernel.map (R.K.d 2 3) (S.K.d 2 3) (φ.complex.f 2) (φ.complex.f 3)
    (φ.complex.comm 2 3).symm

@[reassoc (attr := simp)] theorem cycles₂Map_ι :
    φ.cycles₂Map ≫ kernel.ι (S.K.d 2 3) =
      kernel.ι (R.K.d 2 3) ≫ φ.complex.f 2 :=
  kernel.lift_ι _ _ _

theorem toCycles₂_naturality :
    φ.complex.f 1 ≫ S.toCycles₂ = R.toCycles₂ ≫ φ.cycles₂Map := by
  apply (cancel_mono (kernel.ι (S.K.d 2 3))).mp
  simp only [Category.assoc, toCycles₂_ι, cycles₂Map_ι, toCycles₂_ι_assoc]
  exact φ.complex.comm 1 2

/-- The actual map of the three truncated terms. -/
def shortMap : R.shortComplex ⟶ S.shortComplex where
  τ₁ := φ.complex.f 0
  τ₂ := φ.complex.f 1
  τ₃ := φ.cycles₂Map
  comm₁₂ := φ.complex.comm 0 1
  comm₂₃ := φ.toCycles₂_naturality

/-- A genuine augmented cochain map induces a map of the exact
length-two resolutions, using the actual map on cycles. -/
def truncationMap : AugmentedResolution.Hom R.truncation S.truncation where
  augmentation := φ.augmentation
  complex := φ.shortMap
  comm := φ.comm

theorem shortInclusion_naturality :
    φ.shortMap ≫ S.shortInclusion = R.shortInclusion ≫
      (HomologicalComplex.shortComplexFunctor' C (ComplexShape.up ℕ) 0 1 2).map
        φ.complex := by
  apply ShortComplex.hom_ext
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact φ.cycles₂Map_ι

end Hom

end CochainResolution

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.LowExt
