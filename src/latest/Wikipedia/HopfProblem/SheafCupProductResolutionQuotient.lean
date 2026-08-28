import Wikipedia.HopfProblem.SheafCupProductResolutionNaturality
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Native cohomology and the literal kernel/range quotient groups

These are the actual additive kernels of the original global
differentials, divided by their actual boundary images. Mathlib's
canonical abelian-group homology comparison identifies them with the
already proved native sheaf cohomology; no cohomology bridge is assumed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafCupProductResolution.PartialResolution

variable {X : TopCat.{0}} (R : PartialResolution (TopCat.Sheaf AddCommGrpCat.{0} X))

/-- The literal quotient of degree-one global cocycles by actual global boundaries. -/
abbrev GlobalOneQuotient : Type :=
  R.globalOneComplex.g.hom.ker ⧸ R.globalOneComplex.abToCycles.range

/-- The literal quotient of degree-two global cocycles by actual global boundaries. -/
abbrev GlobalTwoQuotient : Type :=
  R.globalTwoComplex.g.hom.ker ⧸ R.globalTwoComplex.abToCycles.range

/-- Native H¹ is the literal actual degree-one kernel/range quotient. -/
def h1QuotientIso [Injective R.I₀] :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} R.F 1) ≅
      AddCommGrpCat.of R.GlobalOneQuotient :=
  R.h1Iso ≪≫ R.globalOneComplex.abHomologyIso

/-- Native H² is the literal actual degree-two kernel/range quotient. -/
def h2QuotientIso [Injective R.I₀] [Injective R.I₁] :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} R.F 2) ≅
      AddCommGrpCat.of R.GlobalTwoQuotient :=
  R.h2Iso ≪≫ R.globalTwoComplex.abHomologyIso

/-- The genuine degree-one comparison as an additive equivalence. -/
def h1QuotientEquiv [Injective R.I₀] :
    CategoryTheory.Sheaf.H.{0} R.F 1 ≃+ R.GlobalOneQuotient :=
  R.h1QuotientIso.addCommGroupIsoToAddEquiv

/-- The genuine degree-two comparison as an additive equivalence. -/
def h2QuotientEquiv [Injective R.I₀] [Injective R.I₁] :
    CategoryTheory.Sheaf.H.{0} R.F 2 ≃+ R.GlobalTwoQuotient :=
  R.h2QuotientIso.addCommGroupIsoToAddEquiv

end Wikipedia.HopfProblem.SheafCupProductResolution.PartialResolution
