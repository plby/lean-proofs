import Wikipedia.HopfProblem.SheafCupProductNativeNaturality
import Wikipedia.HopfProblem.SheafCupProductCoefficients

/-!
# Native cup products for constant and holomorphic function sheaves

These products are defined on the original Mathlib sheaf cohomology
groups.  The constant sheaf is the actual sheafification, the
holomorphic sheaf consists of actual analytic-order manifold maps,
and the reduced sheaf consists of actual locally ambient-holomorphic
functions.  Their original coefficient maps preserve the products.
-/

noncomputable section

open CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SheafCupProduct

open CuspNormalization

/-- The cup product of the genuine constant complex sheaf. -/
def constantCup (X : TopCat.{0}) :
    CategoryTheory.Sheaf.H.{0} (SheafConstants.complexAdditiveSheaf X) 1 →+
      CategoryTheory.Sheaf.H.{0} (SheafConstants.complexAdditiveSheaf X) 1 →+
        CategoryTheory.Sheaf.H.{0} (SheafConstants.complexAdditiveSheaf X) 2 :=
  cup (SheafConstants.complexSheaf X) (constantScalarEnd X)

theorem constantCup_self (X : TopCat.{0})
    (a : CategoryTheory.Sheaf.H.{0} (SheafConstants.complexAdditiveSheaf X) 1) :
    constantCup X a a = 0 :=
  cup_self_eq_zero _ _ a

section Holomorphic

variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace B] (I : ModelWithCorners ℂ E B)
  (M : Type) [TopologicalSpace M] [ChartedSpace B M]

/-- The actual holomorphic function sheaf's native degree-one cup product. -/
def holomorphicCup :
    CategoryTheory.Sheaf.H.{0} (HolomorphicFunctionSheaf.additiveSheaf I M) 1 →+
      CategoryTheory.Sheaf.H.{0} (HolomorphicFunctionSheaf.additiveSheaf I M) 1 →+
        CategoryTheory.Sheaf.H.{0} (HolomorphicFunctionSheaf.additiveSheaf I M) 2 :=
  cup (HolomorphicFunctionSheaf.sheaf I M) (SheafCohomology.holomorphicScalarEnd I M)

theorem holomorphicCup_self
    (a : CategoryTheory.Sheaf.H.{0} (HolomorphicFunctionSheaf.additiveSheaf I M) 1) :
    holomorphicCup I M a a = 0 :=
  cup_self_eq_zero _ _ a

theorem holomorphicCup_skew
    (a b : CategoryTheory.Sheaf.H.{0} (HolomorphicFunctionSheaf.additiveSheaf I M) 1) :
    holomorphicCup I M a b = -holomorphicCup I M b a :=
  cup_skew_comm _ _ a b

/-- The literal constant-to-holomorphic cohomology maps preserve the product. -/
theorem holomorphicAdditiveMap_cup
    (a b : CategoryTheory.Sheaf.H.{0}
      (SheafConstants.complexAdditiveSheaf (TopCat.of M)) 1) :
    CategoryTheory.Sheaf.H.map (SheafConstants.holomorphicAdditiveMap I M) 2
        (constantCup (TopCat.of M) a b) =
      holomorphicCup I M
        (CategoryTheory.Sheaf.H.map (SheafConstants.holomorphicAdditiveMap I M) 1 a)
        (CategoryTheory.Sheaf.H.map (SheafConstants.holomorphicAdditiveMap I M) 1 b) :=
  cup_naturality (SheafConstants.holomorphicMap I M)
    (constantScalarEnd (TopCat.of M)) (SheafCohomology.holomorphicScalarEnd I M) a b

end Holomorphic

section Reduced

variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace B] {M : Type} [TopologicalSpace M] [ChartedSpace B M]
  (I : ModelWithCorners ℂ E B) (S : Set M)

local instance reducedHAddCommGroup (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H.{0} (SheafReduced.additiveSheaf I S) n) :=
  CategoryTheory.Abelian.Ext.instAddCommGroup

/-- The actual reduced function sheaf's native degree-one cup product. -/
def reducedCup :
    CategoryTheory.Sheaf.H.{0} (SheafReduced.additiveSheaf I S) 1 →+
      CategoryTheory.Sheaf.H.{0} (SheafReduced.additiveSheaf I S) 1 →+
        CategoryTheory.Sheaf.H.{0} (SheafReduced.additiveSheaf I S) 2 :=
  cup (SheafReduced.sheaf I S) (SheafCohomologyScalarResolution.reducedScalarEnd I S)

theorem reducedCup_self
    (a : CategoryTheory.Sheaf.H.{0} (SheafReduced.additiveSheaf I S) 1) :
    reducedCup I S a a = 0 :=
  cup_self_eq_zero _ _ a

theorem reducedCup_skew
    (a b : CategoryTheory.Sheaf.H.{0} (SheafReduced.additiveSheaf I S) 1) :
    reducedCup I S a b = -reducedCup I S b a :=
  cup_skew_comm _ _ a b

/-- The original map from locally constant functions into the reduced
holomorphic functions preserves the actual native cup product. -/
theorem reducedAdditiveMap_cup
    (a b : CategoryTheory.Sheaf.H.{0}
      (SheafConstants.complexAdditiveSheaf (TopCat.of S)) 1) :
    CategoryTheory.Sheaf.H.map (SheafConstants.reducedAdditiveMap I S) 2
        (constantCup (TopCat.of S) a b) =
      reducedCup I S
        (CategoryTheory.Sheaf.H.map (SheafConstants.reducedAdditiveMap I S) 1 a)
        (CategoryTheory.Sheaf.H.map (SheafConstants.reducedAdditiveMap I S) 1 b) :=
  cup_naturality (SheafConstants.reducedMap I S)
    (constantScalarEnd (TopCat.of S))
    (SheafCohomologyScalarResolution.reducedScalarEnd I S) a b

end Reduced

end Wikipedia.HopfProblem.SheafCupProduct
