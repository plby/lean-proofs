import Wikipedia.HopfProblem.SheafCupProductResolutionGlobal
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionRepresentatives

/-!
# Native sheaf H¹ and H² from the actual partial injective complex

Injectivity supplies the genuine Ext vanishings required by the proved
bounded-resolution comparison. Its kernel truncation is then removed
using the actual global-cycle comparisons, retaining the original terms.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.SheafCupProductResolution.PartialResolution

open CuspNormalization.SheafCohomologyResolution

variable {X : TopCat.{0}}

/-- Injectivity gives genuine positive Ext vanishing for the original coefficient sheaf. -/
theorem injective_higher_subsingleton (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    [Injective F] (n : ℕ) : Subsingleton (CategoryTheory.Sheaf.H.{0} F (n + 1)) := by
  change Subsingleton (Ext.{0} (unitSheaf X) F (n + 1))
  exact subsingleton_of_forall_eq 0 (fun x => Ext.eq_zero_of_injective x)

variable (R : PartialResolution (TopCat.Sheaf AddCommGrpCat.{0} X))

/-- The original complex's actual degree-one cycles coming from the
actual kernel-truncated global cycles. -/
def globalOneCycleMap : (globalSectionsFunctor X).obj R.toAugmented.K ⟶
    R.globalOneComplex.cycles :=
  R.toAugmented.globalCycleMap ≫ ShortComplex.cyclesMap R.globalTruncationInclusion

/-- Native H¹ equals the homology of the original global terms. -/
def h1Iso [Injective R.I₀] : AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} R.F 1) ≅
    R.globalOneComplex.homology := by
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.toAugmented.complex.X₁ 1) :=
    injective_higher_subsingleton R.I₀ 0
  exact R.toAugmented.h1Iso ≪≫ asIso (ShortComplex.homologyMap R.globalTruncationInclusion)

/-- Native H² equals the homology of the original global terms. No
injectivity of the degree-two or degree-three term is required. -/
def h2Iso [Injective R.I₀] [Injective R.I₁] :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} R.F 2) ≅ R.globalTwoComplex.homology := by
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.toAugmented.complex.X₁ 1) :=
    injective_higher_subsingleton R.I₀ 0
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.toAugmented.complex.X₁ 2) :=
    injective_higher_subsingleton R.I₀ 1
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.toAugmented.complex.X₂ 1) :=
    injective_higher_subsingleton R.I₁ 0
  exact R.toAugmented.h2Iso ≪≫ R.globalTwoCokernelIso

/-- The degree-one comparison retains the actual connecting representative. -/
theorem h1Iso_connecting [Injective R.I₀] :
    R.toAugmented.globalConnectingOne ≫ R.h1Iso.hom =
      R.globalOneCycleMap ≫ R.globalOneComplex.homologyπ := by
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.toAugmented.complex.X₁ 1) :=
    injective_higher_subsingleton R.I₀ 0
  change R.toAugmented.globalConnectingOne ≫
      (R.toAugmented.h1Iso.hom ≫ ShortComplex.homologyMap R.globalTruncationInclusion) = _
  rw [← Category.assoc, R.toAugmented.h1Iso_connecting, Category.assoc,
    ShortComplex.homologyπ_naturality]
  exact (Category.assoc _ _ _).symm

/-- The degree-two comparison retains the genuine double connecting representative. -/
theorem h2Iso_connecting [Injective R.I₀] [Injective R.I₁] :
    R.toAugmented.globalConnectingTwo ≫ R.h2Iso.hom =
      R.globalTwoHomologyData.cyclesIso.inv ≫ R.globalTwoComplex.homologyπ := by
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.toAugmented.complex.X₁ 1) :=
    injective_higher_subsingleton R.I₀ 0
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.toAugmented.complex.X₁ 2) :=
    injective_higher_subsingleton R.I₀ 1
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.toAugmented.complex.X₂ 1) :=
    injective_higher_subsingleton R.I₁ 0
  change R.toAugmented.globalConnectingTwo ≫
    (R.toAugmented.h2Iso.hom ≫ R.globalTwoCokernelIso.hom) = _
  rw [← Category.assoc, R.toAugmented.h2Iso_connecting]
  exact R.globalTwoCokernelIso_π

end Wikipedia.HopfProblem.SheafCupProductResolution.PartialResolution
