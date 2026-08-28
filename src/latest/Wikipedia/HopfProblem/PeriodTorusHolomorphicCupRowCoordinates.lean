import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupRowOne
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupRowTwo

/-!
# Canonical global coefficient and Haar coordinates for the actual row

The coordinate maps use the original global smooth/Fourier complex
isomorphism, the canonical forgetful homology or cokernel comparison,
and the old Haar-mean isomorphisms. They are not defined by transporting
the native cohomology marking. The actual row comparisons agree with
that original marking on every native class.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Row

open PeriodTorusHolomorphicCohomology
open CuspNormalization.SheafCohomologyScalarResolution
open CuspNormalization.SheafCohomologyResolution

variable (p : PeriodDomain)

/-- Literal global coefficient comparison followed by the two original Haar means. -/
def oneCoordinates : (oneComplex p).homology ≃+ (Fin 2 → ℂ) :=
  (ShortComplex.homologyMapIso (GlobalFourier.complexIso p) ≪≫
    (FourierLinear.complex p).mapHomologyIso linearForget).addCommGroupIsoToAddEquiv.trans
      (FourierLinear.homologyIso p).toLinearEquiv.toAddEquiv

/-- The original top global cokernel, compared by literal coefficients and Haar mean. -/
def topCokernelMean : ↥(cokernel (Dolbeault.resolution p).globalComplex.g) ≃+ ℂ :=
  (ResolutionLinear.cokernelComplexIso (GlobalFourier.complexIso p) ≪≫
    (PreservesCokernel.iso linearForget (FourierLinear.complex p).g).symm
      ).addCommGroupIsoToAddEquiv.trans (FourierLinear.cokernelIso p).toLinearEquiv.toAddEquiv

/-- The canonical actual row cokernel comparison followed by the original top Haar mean. -/
def twoCoordinates : (twoComplex p).homology ≃+ ℂ :=
  (twoOriginalCokernelIso p).addCommGroupIsoToAddEquiv.trans (topCokernelMean p)

/-- The row H¹ map followed by the actual global coordinate map is the old native marking. -/
theorem oneCoordinates_h1Iso (a : H p 1) :
    oneCoordinates p ((h1Iso p).hom a) = PeriodTorusHolomorphicCohomology.h1Equiv p a := by
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (Dolbeault.resolution p).complex.X₁ 1) :=
    Dolbeault.smooth_higher_subsingleton p 0
  exact congrArg (oneCoordinates p)
    (congrArg (fun f : AddCommGrpCat.of (H p 1) ⟶ (oneComplex p).homology => f.hom a)
      (h1Iso_hom_eq_original p))

/-- The row H² map followed by actual top coordinates is the old positive native marking. -/
theorem twoCoordinates_h2Iso (a : H p 2) :
    twoCoordinates p ((h2Iso p).hom a) = PeriodTorusHolomorphicCohomology.h2Equiv p a := by
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (Dolbeault.resolution p).complex.X₁ 1) :=
    Dolbeault.smooth_higher_subsingleton p 0
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (Dolbeault.resolution p).complex.X₁ 2) :=
    Dolbeault.smooth_higher_subsingleton p 1
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (Dolbeault.resolution p).complex.X₂ 1) :=
    Dolbeault.pair_higher_subsingleton p 0
  exact congrArg (topCokernelMean p)
    (congrArg (fun f : AddCommGrpCat.of (H p 2) ⟶
      cokernel (Dolbeault.resolution p).globalComplex.g => f.hom a)
        (h2Iso_hom_comp_original p))

/-- An actual closed row pair has its original two coefficient means. -/
theorem oneCoordinates_class (s : Dolbeault.PairSection p ⊤)
    (hs : Dolbeault.topSection p ⊤ s = 0) :
    oneCoordinates p (oneClass p s hs) = GlobalFourier.pairMean p s :=
  (congrArg (oneCoordinates p) (h1Iso_nativeClass p s hs).symm).trans
    ((oneCoordinates_h1Iso p (nativeH1Class p s hs)).trans (h1Equiv_nativeClass p s hs))

/-- An actual row top class has the positive original coefficient Haar mean. -/
theorem twoCoordinates_class (s : Dolbeault.SmoothSection p ⊤) :
    twoCoordinates p (twoClass p s) = GlobalFourier.mean p s :=
  (congrArg (twoCoordinates p) (h2Iso_nativeClass p s).symm).trans
    ((twoCoordinates_h2Iso p (nativeH2Class p s)).trans (h2Equiv_nativeClass p s))

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Row
