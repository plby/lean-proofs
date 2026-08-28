import Wikipedia.HopfProblem.SheafCupProductGodementForgetBasic

/-!
# Additive derivations on actual commutative-ring sheaves

A derivation is an actual endomorphism of the underlying additive sheaf,
with the literal Leibniz identity on every original section ring.
It is not a ring endomorphism.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Derivation

open SheafCupProduct

variable {X : TopCat.{0}}

/-- Evaluate an underlying additive sheaf map in the original section rings. -/
abbrev sectionMap {F G : GodementRing.RingSheaf X}
    (f : (GodementRing.forgetSheaf X).obj F ⟶ (GodementRing.forgetSheaf X).obj G)
    (U : Opens X) : F.obj.obj (op U) →+ G.obj.obj (op U) :=
  (f.hom.app (op U)).hom

/-- An actual additive sheaf endomorphism satisfying the sectionwise product rule. -/
structure SheafDerivation (F : GodementRing.RingSheaf X) where
  map : End ((GodementRing.forgetSheaf X).obj F)
  leibniz (U : Opens X) (a b : F.obj.obj (op U)) :
    sectionMap map U (a * b) = sectionMap map U a * b + a * sectionMap map U b

namespace SheafDerivation

variable {F : GodementRing.RingSheaf X} (D : SheafDerivation F)

/-- The original additive section operator, with no transported ring structure. -/
abbrev sectionMap (U : Opens X) : F.obj.obj (op U) →+ F.obj.obj (op U) :=
  Derivation.sectionMap D.map U

theorem sectionMap_mul (U : Opens X) (a b : F.obj.obj (op U)) :
    D.sectionMap U (a * b) = D.sectionMap U a * b + a * D.sectionMap U b :=
  D.leibniz U a b

end SheafDerivation

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Derivation
