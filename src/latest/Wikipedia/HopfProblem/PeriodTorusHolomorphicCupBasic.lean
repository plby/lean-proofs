import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyBasic
import Wikipedia.HopfProblem.SheafCupProductFunctionsLinear
import Wikipedia.HopfProblem.SheafCupProductExteriorBasic

/-!
# The original native holomorphic cup on a period torus

These are the already constructed Godement/Ext cup product and its
bilinear and exterior-square bundles, with the original pointwise
complex scalar action. No coordinate isomorphism is used to define
any product.
-/

noncomputable section

open CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup

open PeriodTorusHolomorphicCohomology

variable (p : PeriodDomain)

/-- The existing genuine native cup, on the unchanged period-torus holomorphic sheaf. -/
def cup : H p 1 →+ H p 1 →+ H p 2 :=
  SheafCupProduct.holomorphicCup (modelWithCornersSelf ℂ ComplexPlane₂) p.Torus

theorem cup_eq_native : cup p =
    SheafCupProduct.holomorphicCup (modelWithCornersSelf ℂ ComplexPlane₂) p.Torus := rfl

/-- The same actual cup, bilinear for the original pointwise complex action. -/
def linearCup : H p 1 →ₗ[ℂ] H p 1 →ₗ[ℂ] H p 2 :=
  SheafCupProduct.holomorphicLinearCup (modelWithCornersSelf ℂ ComplexPlane₂) p.Torus

@[simp] theorem linearCup_apply (a b : H p 1) : linearCup p a b = cup p a b := rfl

theorem cup_self (a : H p 1) : cup p a a = 0 := by
  unfold cup
  exact SheafCupProduct.holomorphicCup_self (modelWithCornersSelf ℂ ComplexPlane₂) p.Torus a

theorem cup_skew (a b : H p 1) : cup p a b = -cup p b a := by
  unfold cup
  exact SheafCupProduct.holomorphicCup_skew (modelWithCornersSelf ℂ ComplexPlane₂) p.Torus a b

theorem linearCup_self (a : H p 1) : linearCup p a a = 0 := cup_self p a

/-- The genuine exterior-square map induced by this actual alternating native cup. -/
def exteriorCup : ⋀[ℂ]^2 (H p 1) →ₗ[ℂ] H p 2 :=
  SheafCupProduct.exteriorPairing (linearCup p) (linearCup_self p)

@[simp] theorem exteriorCup_ιMulti (a : Fin 2 → H p 1) :
    exteriorCup p (exteriorPower.ιMulti ℂ 2 a) = cup p (a 0) (a 1) :=
  SheafCupProduct.exteriorPairing_ιMulti (linearCup p) (linearCup_self p) a

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup
