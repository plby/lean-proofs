import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyGlobalFourierComplex
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultScalars
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyResolutionLinearOne

/-!
# Original sheaf scalars and the native/Fourier complex comparison

The genuine scalar endomorphisms of the native smooth sheaves induce
the ordinary pointwise scalar map of the actual Fourier complex. This
is the compatibility needed by the Ext-linear resolution comparison.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.GlobalFourier

open CuspNormalization.SheafCohomologyResolution
open CuspNormalization.SheafCohomologyScalarResolution

/-- The original three-term smooth sheaf complex. -/
abbrev nativeSheafComplex (p : PeriodDomain) :=
  ShortComplex.mk (Dolbeault.differential p) (Dolbeault.topDifferential p)
    (Dolbeault.differential_topDifferential p)

/-- Actual pointwise scalar maps on the original sheaf complex. -/
def scalarSheafComplexMap (p : PeriodDomain) (c : ℂ) :
    nativeSheafComplex p ⟶ nativeSheafComplex p where
  τ₁ := (Dolbeault.smoothScalarEnd p c).asHom
  τ₂ := (Dolbeault.pairScalarEnd p c).asHom
  τ₃ := (Dolbeault.smoothScalarEnd p c).asHom
  comm₁₂ := Dolbeault.differential_scalar p c
  comm₂₃ := Dolbeault.topDifferential_scalar p c

/-- The literal global map induced by those genuine sheaf endomorphisms. -/
def scalarGlobalMap (p : PeriodDomain) (c : ℂ) : nativeComplex p ⟶ nativeComplex p :=
  (globalSectionsFunctor (TopCat.of p.Torus)).mapShortComplex.map (scalarSheafComplexMap p c)

@[simp] theorem scalarGlobalMap_one (p : PeriodDomain) (c : ℂ)
    (s : Dolbeault.SmoothSection p ⊤) : (scalarGlobalMap p c).τ₁ s = c • s := rfl

@[simp] theorem scalarGlobalMap_two (p : PeriodDomain) (c : ℂ)
    (s : Dolbeault.PairSection p ⊤) : (scalarGlobalMap p c).τ₂ s = c • s := rfl

@[simp] theorem scalarGlobalMap_three (p : PeriodDomain) (c : ℂ)
    (s : Dolbeault.SmoothSection p ⊤) : (scalarGlobalMap p c).τ₃ s = c • s := rfl

/-- Scalar compatibility holds for the actual entire global-complex map. -/
theorem complexIso_scalar (p : PeriodDomain) (c : ℂ) :
    scalarGlobalMap p c ≫ (complexIso p).hom =
      (complexIso p).hom ≫ forgottenScalarMap (FourierLinear.complex p) c := by
  apply ShortComplex.hom_ext
  · apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    exact (sectionEquiv p).map_smul c s
  · apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    exact (pairSectionEquiv p).map_smul c s
  · apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    exact (sectionEquiv p).map_smul c s

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.GlobalFourier
