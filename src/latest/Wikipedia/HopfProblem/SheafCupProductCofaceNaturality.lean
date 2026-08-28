import Wikipedia.HopfProblem.SheafCupProductCofaceMorphism
import Wikipedia.HopfProblem.SheafCupProductCofaceQuotient
import Wikipedia.HopfProblem.SheafCupProductCofaceCosimplicial

/-!
# Coefficient naturality on the actual cohomology quotients

The induced quotient maps come from the actual degreewise ring maps.
Their cup compatibility follows from the literal representative formula.
Actual cosimplicial ring morphisms supply this interface by naturality.
-/

universe u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ u

namespace Wikipedia.HopfProblem.SheafCupProduct.Coface.Data.Morphism

variable {R0 : Type u₀} {R1 : Type u₁} {R2 : Type u₂} {R3 : Type u₃}
variable {S0 : Type v₀} {S1 : Type v₁} {S2 : Type v₂} {S3 : Type v₃}
variable [CommRing R0] [CommRing R1] [CommRing R2] [CommRing R3]
variable [CommRing S0] [CommRing S1] [CommRing S2] [CommRing S3]
variable {D : Coface.Data R0 R1 R2 R3} {E : Coface.Data S0 S1 S2 S3}
variable (M : D.Morphism E)

def cohomologyOneMap : D.CohomologyOne →+ E.CohomologyOne :=
  QuotientAddGroup.lift D.boundariesOne (E.classOne.comp M.cocycleOneMap) (by
    intro a ha
    obtain ⟨r, rfl⟩ := ha
    change E.classOne (M.cocycleOneMap (D.boundaryOne r)) = 0
    rw [M.cocycleOneMap_boundary, E.classOne_boundary])

def cohomologyTwoMap : D.CohomologyTwo →+ E.CohomologyTwo :=
  QuotientAddGroup.lift D.boundariesTwo (E.classTwo.comp M.cocycleTwoMap) (by
    intro a ha
    obtain ⟨r, rfl⟩ := ha
    change E.classTwo (M.cocycleTwoMap (D.boundaryTwo r)) = 0
    rw [M.cocycleTwoMap_boundary, E.classTwo_boundary])

@[simp] theorem cohomologyOneMap_classOne (a : D.CocycleOne) :
    M.cohomologyOneMap (D.classOne a) = E.classOne (M.cocycleOneMap a) := rfl

@[simp] theorem cohomologyTwoMap_classTwo (a : D.CocycleTwo) :
    M.cohomologyTwoMap (D.classTwo a) = E.classTwo (M.cocycleTwoMap a) := rfl

theorem map_cup (a b : D.CohomologyOne) :
    M.cohomologyTwoMap (D.cup a b) =
      E.cup (M.cohomologyOneMap a) (M.cohomologyOneMap b) := by
  obtain ⟨a, rfl⟩ := D.classOne_surjective a
  obtain ⟨b, rfl⟩ := D.classOne_surjective b
  rw [D.cup_classOne, M.cohomologyTwoMap_classTwo, M.cohomologyOneMap_classOne,
    M.cohomologyOneMap_classOne, E.cup_classOne, M.cocycleTwoMap_cup]

end Wikipedia.HopfProblem.SheafCupProduct.Coface.Data.Morphism

open CategoryTheory
open scoped Simplicial

namespace Wikipedia.HopfProblem.SheafCupProduct.Coface

def ofCosimplicialMorphism {X Y : CosimplicialObject CommRingCat.{u}} (f : X ⟶ Y) :
    (ofCosimplicial X).Morphism (ofCosimplicial Y) where
  f0 := (f.app ⦋0⦌).hom
  f1 := (f.app ⦋1⦌).hom
  f2 := (f.app ⦋2⦌).hom
  f3 := (f.app ⦋3⦌).hom
  comm0 i := congrArg (fun g => g.hom) (f.naturality (SimplexCategory.δ i))
  comm1 i := congrArg (fun g => g.hom) (f.naturality (SimplexCategory.δ i))
  comm2 i := congrArg (fun g => g.hom) (f.naturality (SimplexCategory.δ i))

end Wikipedia.HopfProblem.SheafCupProduct.Coface
