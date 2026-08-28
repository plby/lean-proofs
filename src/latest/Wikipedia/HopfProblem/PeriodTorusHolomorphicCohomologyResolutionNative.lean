import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeault
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyGlobalFourierScalars
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyResolutionLinearTwo

/-!
# The actual native Ext-to-Fourier comparison on period tori

Literal multiplication of holomorphic and smooth sections is a map of
the genuine augmented Dolbeault resolution. Its global map is compatible
with the actual Fourier-coordinate comparison. Naturality of the original
Ext connecting maps therefore makes the degree-one and degree-two
comparisons complex-linear for the original sheaf-induced scalar action.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology

namespace Dolbeault

/-- Actual scalar multiplication on all four terms is a map of the proved resolution. -/
def scalarResolutionHom (p : PeriodDomain) (c : ℂ) :
    (resolution p).Hom (resolution p) where
  augmentation := (holomorphicScalarEnd p c).asHom
  complex := GlobalFourier.scalarSheafComplexMap p c
  comm := inclusion_scalar p c

@[simp] theorem scalarResolutionHom_augmentation (p : PeriodDomain) (c : ℂ) :
    (scalarResolutionHom p c).augmentation = (holomorphicScalarEnd p c).asHom := rfl

@[simp] theorem scalarResolutionHom_globalMap (p : PeriodDomain) (c : ℂ) :
    (scalarResolutionHom p c).globalMap = GlobalFourier.scalarGlobalMap p c := rfl

/-- The original scalar resolution map commutes with the genuine global-complex comparison. -/
theorem scalarResolutionHom_compare (p : PeriodDomain) (c : ℂ) :
    (scalarResolutionHom p c).globalMap ≫ (GlobalFourier.complexIso p).hom =
      (GlobalFourier.complexIso p).hom ≫
        CuspNormalization.SheafCohomologyScalarResolution.forgottenScalarMap
          (FourierLinear.complex p) c :=
  GlobalFourier.complexIso_scalar p c

end Dolbeault

/-- The genuine degree-one Ext group is identified with actual Fourier-complex homology. -/
def h1FourierEquiv (p : PeriodDomain) :
    H p 1 ≃ₗ[ℂ] (FourierLinear.complex p).homology := by
  letI : Subsingleton (CategoryTheory.Sheaf.H.{0} (Dolbeault.resolution p).complex.X₁ 1) :=
    Dolbeault.smooth_higher_subsingleton p 0
  exact ResolutionLinear.h1LinearEquiv (Dolbeault.resolution p)
    (FourierLinear.complex p) (GlobalFourier.complexIso p)
    (Dolbeault.holomorphicScalarEnd p) (Dolbeault.scalarResolutionHom p)
    (Dolbeault.scalarResolutionHom_augmentation p) (Dolbeault.scalarResolutionHom_compare p)

/-- The genuine degree-two Ext group is identified with the actual top Fourier cokernel. -/
def h2FourierEquiv (p : PeriodDomain) :
    H p 2 ≃ₗ[ℂ] ↥(cokernel (FourierLinear.complex p).g) := by
  letI : Subsingleton (CategoryTheory.Sheaf.H.{0} (Dolbeault.resolution p).complex.X₁ 1) :=
    Dolbeault.smooth_higher_subsingleton p 0
  letI : Subsingleton (CategoryTheory.Sheaf.H.{0} (Dolbeault.resolution p).complex.X₁ 2) :=
    Dolbeault.smooth_higher_subsingleton p 1
  letI : Subsingleton (CategoryTheory.Sheaf.H.{0} (Dolbeault.resolution p).complex.X₂ 1) :=
    Dolbeault.pair_higher_subsingleton p 0
  exact ResolutionLinear.h2LinearEquiv (Dolbeault.resolution p)
    (FourierLinear.complex p) (GlobalFourier.complexIso p)
    (Dolbeault.holomorphicScalarEnd p) (Dolbeault.scalarResolutionHom p)
    (Dolbeault.scalarResolutionHom_augmentation p) (Dolbeault.scalarResolutionHom_compare p)

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology
