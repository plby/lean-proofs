import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyGlobalFourierOperators
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionSections

/-!
# A genuine isomorphism of the native and Fourier global complexes

The source is the literal global-sections functor applied to the actual
native Dolbeault sheaf maps. Both commuting squares are the proved
coordinate derivative comparisons, on all native global sections.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.GlobalFourier

open CuspNormalization.SheafCohomologyResolution

/-- The actual global-sections complex of the three native smooth sheaves. -/
abbrev nativeComplex (p : PeriodDomain) : ShortComplex AddCommGrpCat :=
  (ShortComplex.mk (Dolbeault.differential p) (Dolbeault.topDifferential p)
    (Dolbeault.differential_topDifferential p)).map
      (globalSectionsFunctor (TopCat.of p.Torus))

/-- The genuine termwise comparison, with both actual differential squares commuting. -/
def complexIso (p : PeriodDomain) :
    nativeComplex p ≅ (FourierLinear.complex p).map (forget₂ (ModuleCat ℂ) AddCommGrpCat) :=
  ShortComplex.isoMk (sectionEquiv p).toAddEquiv.toAddCommGrpIso
    (pairSectionEquiv p).toAddEquiv.toAddCommGrpIso
    (sectionEquiv p).toAddEquiv.toAddCommGrpIso
    (by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro s
      exact (pairSectionEquiv_differential p s).symm)
    (by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro s
      exact (sectionEquiv_top p s).symm)

@[simp] theorem complexIso_hom_one (p : PeriodDomain) (s : Dolbeault.SmoothSection p ⊤) :
    (complexIso p).hom.τ₁ s = sectionEquiv p s := rfl

@[simp] theorem complexIso_hom_two (p : PeriodDomain) (s : Dolbeault.PairSection p ⊤) :
    (complexIso p).hom.τ₂ s = pairSectionEquiv p s := rfl

@[simp] theorem complexIso_hom_three (p : PeriodDomain) (s : Dolbeault.SmoothSection p ⊤) :
    (complexIso p).hom.τ₃ s = sectionEquiv p s := rfl

@[simp] theorem complexIso_inv_one (p : PeriodDomain) (f : FourierLinear.Smooth) :
    (complexIso p).inv.τ₁ f = (sectionEquiv p).symm f := rfl

@[simp] theorem complexIso_inv_two (p : PeriodDomain) (a : FourierLinear.Pair) :
    (complexIso p).inv.τ₂ a = (pairSectionEquiv p).symm a := rfl

@[simp] theorem complexIso_inv_three (p : PeriodDomain) (f : FourierLinear.Smooth) :
    (complexIso p).inv.τ₃ f = (sectionEquiv p).symm f := rfl

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.GlobalFourier
