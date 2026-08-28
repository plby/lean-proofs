import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupRowAcyclic
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyNativeConnecting

/-!
# The actual degree-two row class has the original positive marking

The original native top class is the positive double Ext connecting
class. Naturality for the literal kernel-zero inclusion and the genuine
cokernel representative formula determine its image in row homology.
No coordinate or cup-product convention is changed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Row

open PeriodTorusHolomorphicCohomology
open CuspNormalization.SheafCohomologyResolution

variable (p : PeriodDomain)

/-- The original partial-resolution comparison sends the original native top class
to the canonical class of that same coefficient, with positive sign. -/
theorem h2Iso_nativeClass (s : Dolbeault.SmoothSection p ⊤) :
    (h2Iso p).hom (nativeH2Class p s) = twoClass p s := by
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (Dolbeault.resolution p).complex.X₁ 1) :=
    Dolbeault.smooth_higher_subsingleton p 0
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (Dolbeault.resolution p).complex.X₁ 2) :=
    Dolbeault.smooth_higher_subsingleton p 1
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (Dolbeault.resolution p).complex.X₂ 1) :=
    Dolbeault.pair_higher_subsingleton p 0
  apply (twoOriginalCokernelIso p).addCommGroupIsoToAddEquiv.injective
  have hn := congrArg (fun f : AddCommGrpCat.of (H p 2) ⟶
      cokernel (Dolbeault.resolution p).globalComplex.g => f.hom (nativeH2Class p s))
    (h2Iso_hom_comp_original p)
  have hd := congrArg (fun f :
      (globalSectionsFunctor (TopCat.of p.Torus)).obj (Dolbeault.smoothSheaf p) ⟶
        cokernel (Dolbeault.resolution p).globalComplex.g => f.hom s)
    (Dolbeault.resolution p).h2Iso_connecting
  exact hn.trans
    ((congrArg (Dolbeault.resolution p).h2Iso.hom
      (nativeH2Class_eq_globalConnectingTwo p s)).trans
        (hd.trans (twoOriginalCokernelIso_class p s).symm))

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Row
