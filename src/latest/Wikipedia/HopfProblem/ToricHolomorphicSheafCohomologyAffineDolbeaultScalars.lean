import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyAffineDolbeaultSections
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyAffineDolbeaultAcyclic
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyScalars

/-!
# Actual complex scalar actions on the affine Dolbeault resolution

Constants multiply the genuine holomorphic functions, smooth functions
and smooth coefficient pairs. The literal section linearity proves
commutation of these actual sheaf endomorphisms with all three arrows.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.AffineDolbeault

/-- The actual scalar endomorphism ring map of the holomorphic sheaf. -/
abbrev holomorphicScalarEnd : ℂ →+* End holomorphicSheaf :=
  CuspNormalization.SheafCohomology.holomorphicScalarEnd
    𝓘(ℂ, ℂ × ℂ) (ℂ × ℂ)

@[simp] theorem holomorphicScalarEnd_eq_smul (c : ℂ) (U : Opens (ℂ × ℂ))
    (f : HolomorphicSection U) :
    (holomorphicScalarEnd c).asHom.hom.app (op U) f = c • f := rfl

/-- Literal complex multiplication commutes with the actual inclusion. -/
theorem inclusion_scalar (c : ℂ) :
    (holomorphicScalarEnd c).asHom ≫ inclusion = inclusion ≫ (smoothScalarEnd c).asHom := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro f
  exact (inclusionSection U.unop).map_smul c f

/-- Literal complex multiplication commutes with the first actual derivative. -/
theorem differential_scalar (c : ℂ) :
    (smoothScalarEnd c).asHom ≫ differential = differential ≫ (pairScalarEnd c).asHom := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  exact (differentialSection U.unop).map_smul c s

/-- Literal complex multiplication commutes with the actual top derivative. -/
theorem topDifferential_scalar (c : ℂ) :
    (pairScalarEnd c).asHom ≫ topDifferential = topDifferential ≫ (smoothScalarEnd c).asHom := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  exact (topSection U.unop).map_smul c s

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.AffineDolbeault
