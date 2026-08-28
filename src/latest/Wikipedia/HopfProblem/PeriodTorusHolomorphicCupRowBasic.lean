import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultExact
import Wikipedia.HopfProblem.SheafCupProductResolutionMaps

/-!
# The original torus Dolbeault row as an actual partial resolution

The terms and maps are the original smooth coefficients and native
Dolbeault operators. The last target is the actual zero sheaf. Its
kernel truncation maps to the original bounded resolution by the
literal kernel inclusion, with the identity on the holomorphic sheaf.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Row

open PeriodTorusHolomorphicCohomology
open SheafCupProductResolution CuspNormalization.SheafCohomologyResolution

variable (p : PeriodDomain)

/-- The unchanged native Dolbeault resolution, followed by the actual zero sheaf. -/
def partialResolution : PartialResolution (TopCat.Sheaf AddCommGrpCat (TopCat.of p.Torus)) where
  F := holomorphicSheaf p
  I₀ := Dolbeault.smoothSheaf p
  I₁ := Dolbeault.pairSheaf p
  I₂ := Dolbeault.smoothSheaf p
  I₃ := 0
  ι := Dolbeault.inclusion p
  d₀ := Dolbeault.differential p
  d₁ := Dolbeault.topDifferential p
  d₂ := 0
  ι_d₀ := Dolbeault.inclusion_differential p
  d₀_d₁ := Dolbeault.differential_topDifferential p
  d₁_d₂ := comp_zero
  exact₀ := Dolbeault.initialComplex_exact p
  exact₁ := Dolbeault.dolbeaultComplex_exact p
  exact₂ := (ShortComplex.exact_iff_epi _ rfl).mpr (Dolbeault.topDifferential_epi p)
  mono_ι := Dolbeault.inclusion_mono p

/-- The kernel of the final zero map is canonically the original top coefficient sheaf. -/
def topKernelIso : (partialResolution p).Z₂ ≅ Dolbeault.smoothSheaf p :=
  kernelZeroIsoSource

@[simp] theorem topKernelIso_hom :
    (topKernelIso p).hom = kernel.ι (partialResolution p).d₂ := rfl

/-- The actual truncation maps to the original bounded Dolbeault resolution. -/
def toOriginal :
    (partialResolution p).toAugmented.Hom (Dolbeault.resolution p) where
  augmentation := 𝟙 _
  complex := (partialResolution p).truncationInclusion
  comm := by
    change 𝟙 _ ≫ Dolbeault.inclusion p = Dolbeault.inclusion p ≫ 𝟙 _
    simp

@[simp] theorem toOriginal_augmentation : (toOriginal p).augmentation = 𝟙 _ := rfl

@[simp] theorem toOriginal_complex :
    (toOriginal p).complex = (partialResolution p).truncationInclusion := rfl

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Row
