import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultSections
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultInclusion
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultAcyclic

/-!
# Actual complex scalar actions on the native torus Dolbeault arrows

The original holomorphic-function scalar action and the literal smooth
and pair scalar actions commute with the actual inclusion and both
actual differential maps. These are the actions on the original sheaves,
not scalar structures transported through a dimension calculation.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.Dolbeault

local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂

/-- The original holomorphic sheaf scalar action inducing the native Ext module. -/
abbrev holomorphicScalarEnd (p : PeriodDomain) : ℂ →+* End (holomorphicSheaf p) :=
  CuspNormalization.SheafCohomology.holomorphicScalarEnd I₂ p.Torus

@[simp] theorem holomorphicScalarEnd_eq_smul (p : PeriodDomain) (c : ℂ)
    (U : Opens p.Torus) (f : HolomorphicSection p U) :
    (holomorphicScalarEnd p c).asHom.hom.app (op U) f = c • f := rfl

/-- Literal complex multiplication commutes with the actual inclusion. -/
theorem inclusion_scalar (p : PeriodDomain) (c : ℂ) :
    (holomorphicScalarEnd p c).asHom ≫ inclusion p =
      inclusion p ≫ (smoothScalarEnd p c).asHom := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro f
  exact (inclusionSection p U.unop).map_smul c f

/-- The actual first differential is complex-linear as a sheaf map. -/
theorem differential_scalar (p : PeriodDomain) (c : ℂ) :
    (smoothScalarEnd p c).asHom ≫ differential p =
      differential p ≫ (pairScalarEnd p c).asHom := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  exact (differentialSection p U.unop).map_smul c s

/-- The actual top differential is complex-linear as a sheaf map. -/
theorem topDifferential_scalar (p : PeriodDomain) (c : ℂ) :
    (pairScalarEnd p c).asHom ≫ topDifferential p =
      topDifferential p ≫ (smoothScalarEnd p c).asHom := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  exact (topSection p U.unop).map_smul c s

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.Dolbeault
