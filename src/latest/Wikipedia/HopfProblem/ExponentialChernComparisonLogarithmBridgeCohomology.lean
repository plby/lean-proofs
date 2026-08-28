import Wikipedia.HopfProblem.ExponentialChernComparisonLogarithmBridgeBasic
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonLowDegrees

/-!
# The canonical comparison on actual double connecting classes

This identifies the image of the original resolution's double connecting
class under the canonical constant-sheaf comparison. The result is the
existing degree-two cycle-cokernel comparison, with every map unchanged.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ExponentialChernComparison.LogarithmBridge

open ConstantSheafSingularComparison HolomorphicFunctionSheaf.SphereH1

variable (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    (hLC : LocallyContractibleSpace X)

/-- The canonical sheaf/singular comparison, followed by the actual
global cochain comparison, sends the actual double connecting class to
the existing full-complex homology class of its cycle-cokernel section. -/
theorem constantSheafH2Iso_globalConnectingTwo
    (σ : Section (DLog.resolution X hLC).complex.X₃ ⊤) :
    HomologicalComplex.homologyMap (globalCochainComparison X (AddCommGrpCat.of ℂ)) 2
        ((constantSheafH2Iso X (AddCommGrpCat.of ℂ) hLC).hom
          ((DLog.resolution X hLC).globalConnectingTwo σ)) =
      (singularSheafResolution X (AddCommGrpCat.of ℂ) hLC).globalSecondHomologyIso.hom
        (cokernel.π (DLog.resolution X hLC).globalComplex.g σ) := by
  let R := DLog.resolution X hLC
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1) :=
    FineCochains.cochainSheaf_higher_subsingleton X (AddCommGrpCat.of ℂ) 0 0
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 2) :=
    FineCochains.cochainSheaf_higher_subsingleton X (AddCommGrpCat.of ℂ) 0 1
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₂ 1) :=
    FineCochains.cochainSheaf_higher_subsingleton X (AddCommGrpCat.of ℂ) 1 0
  calc
    _ = (constantSheafGlobalH2Iso X (AddCommGrpCat.of ℂ) hLC).hom
        (R.globalConnectingTwo σ) :=
      ConcreteCategory.congr_hom (constantSheafH2Iso_global X (AddCommGrpCat.of ℂ) hLC)
        (R.globalConnectingTwo σ)
    _ = _ := by
      change (singularSheafResolution X (AddCommGrpCat.of ℂ) hLC).globalSecondHomologyIso.hom
          (R.h2Iso.hom (R.globalConnectingTwo σ)) = _
      have hπ : R.h2Iso.hom (R.globalConnectingTwo σ) = cokernel.π R.globalComplex.g σ :=
        ConcreteCategory.congr_hom R.h2Iso_connecting σ
      exact congrArg
        (fun c : ↥(cokernel R.globalComplex.g) =>
          (singularSheafResolution X (AddCommGrpCat.of ℂ) hLC).globalSecondHomologyIso.hom c) hπ

end Wikipedia.HopfProblem.ExponentialChernComparison.LogarithmBridge
