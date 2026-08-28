import Wikipedia.HopfProblem.SheafCupProductResolutionBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionMaps

/-!
# Genuine maps of partial resolutions and their kernel truncations

Every map on a cycle object is the actual categorical kernel map, and
the bounded-resolution morphism retains the original augmentation map.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafCupProductResolution.PartialResolution

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- An original commuting map of the five terms of partial resolutions. -/
structure Hom (R S : PartialResolution C) where
  augmentation : R.F ⟶ S.F
  τ₀ : R.I₀ ⟶ S.I₀
  τ₁ : R.I₁ ⟶ S.I₁
  τ₂ : R.I₂ ⟶ S.I₂
  τ₃ : R.I₃ ⟶ S.I₃
  commι : augmentation ≫ S.ι = R.ι ≫ τ₀
  comm₀ : τ₀ ≫ S.d₀ = R.d₀ ≫ τ₁
  comm₁ : τ₁ ≫ S.d₁ = R.d₁ ≫ τ₂
  comm₂ : τ₂ ≫ S.d₂ = R.d₂ ≫ τ₃

variable (R : PartialResolution C)

/-- The original kernel inclusion gives the comparison to the untruncated terms. -/
def truncationInclusion : R.truncatedComplex ⟶ R.oneComplex where
  τ₁ := 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := kernel.ι R.d₂
  comm₁₂ := by simp [truncatedComplex]
  comm₂₃ := by simp [truncatedComplex]

namespace Hom

variable {R S : PartialResolution C} (φ : R.Hom S)

/-- The genuine induced map on the kernel of the last differential. -/
def cyclesTwoMap : R.Z₂ ⟶ S.Z₂ :=
  kernel.map R.d₂ S.d₂ φ.τ₂ φ.τ₃ φ.comm₂.symm

@[reassoc (attr := simp)] theorem cyclesTwoMap_ι :
    φ.cyclesTwoMap ≫ kernel.ι S.d₂ = kernel.ι R.d₂ ≫ φ.τ₂ :=
  kernel.lift_ι _ _ _

theorem toCyclesTwo_naturality :
    φ.τ₁ ≫ S.toCyclesTwo = R.toCyclesTwo ≫ φ.cyclesTwoMap := by
  apply (cancel_mono (kernel.ι S.d₂)).mp
  rw [Category.assoc, toCyclesTwo_ι, Category.assoc, cyclesTwoMap_ι,
    ← Category.assoc, toCyclesTwo_ι]
  exact φ.comm₁

/-- The actual map of the original degree-one terms. -/
def oneMap : R.oneComplex ⟶ S.oneComplex where
  τ₁ := φ.τ₀
  τ₂ := φ.τ₁
  τ₃ := φ.τ₂
  comm₁₂ := φ.comm₀
  comm₂₃ := φ.comm₁

/-- The actual map of the original degree-two terms. -/
def twoMap : R.twoComplex ⟶ S.twoComplex where
  τ₁ := φ.τ₁
  τ₂ := φ.τ₂
  τ₃ := φ.τ₃
  comm₁₂ := φ.comm₁
  comm₂₃ := φ.comm₂

/-- The bounded augmented-resolution morphism uses the original maps
and the actual induced cycle-object map. -/
def toAugmentedHom : R.toAugmented.Hom S.toAugmented where
  augmentation := φ.augmentation
  complex :=
    { τ₁ := φ.τ₀
      τ₂ := φ.τ₁
      τ₃ := φ.cyclesTwoMap
      comm₁₂ := φ.comm₀
      comm₂₃ := φ.toCyclesTwo_naturality }
  comm := φ.commι

theorem truncationInclusion_naturality :
    φ.toAugmentedHom.complex ≫ S.truncationInclusion =
      R.truncationInclusion ≫ φ.oneMap := by
  apply ShortComplex.hom_ext
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact φ.cyclesTwoMap_ι

end Hom

end Wikipedia.HopfProblem.SheafCupProductResolution.PartialResolution
