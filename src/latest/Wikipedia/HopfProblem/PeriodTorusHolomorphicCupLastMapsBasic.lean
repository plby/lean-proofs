import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupTotalActual
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupRow
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalMapsCategorical

/-!
# The literal native Dolbeault row maps into the actual total resolution

Every component is the original column unit followed by the last
biproduct injection. The actual germ and native derivative squares
prove all differential squares, with identity on the holomorphic sheaf.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.LastMaps

open SheafCupProduct SheafSingularCupComparison
open PeriodTorusHolomorphicCohomology

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable (p : PeriodDomain)

def map0 : (Row.partialResolution p).I₀ ⟶ (totalPartialResolution p).I₀ :=
  Total.columnUnit0 p

def map1 : (Row.partialResolution p).I₁ ⟶ (totalPartialResolution p).I₁ :=
  Total.columnUnit1 p ≫ biprod.inr

def map2 : (Row.partialResolution p).I₂ ⟶ (totalPartialResolution p).I₂ :=
  Total.columnUnit2 p ≫ biprod.inr ≫ biprod.inr

def map3 : (Row.partialResolution p).I₃ ⟶ (totalPartialResolution p).I₃ :=
  Total.columnUnit3 p ≫ biprod.inr ≫ biprod.inr ≫ biprod.inr

/-- The actual native pair column unit is killed by the original vertical differential. -/
theorem columnUnit1_vertical :
    Total.columnUnit1 p ≫ (totalOperators p).categoryData.v01 = 0 := by
  change ((nativePairIso p).hom ≫ Pairs.map (Total.columnUnit0 p)) ≫
    Pairs.map (GodementExact.d0 (Derivation.smoothRingSheaf p)) = 0
  have hz : Total.columnUnit0 p ≫ GodementExact.d0 (Derivation.smoothRingSheaf p) = 0 :=
    GodementExact.augmentation_d0 (Derivation.smoothRingSheaf p)
  rw [Category.assoc, ← Pairs.map_comp, hz, Pairs.map_zero, comp_zero]

theorem comm0 : map0 p ≫ (totalPartialResolution p).d₀ =
    (Row.partialResolution p).d₀ ≫ map1 p :=
  TotalMaps.last_square0 (totalOperators p).categoryData _ _ _
    (GodementExact.augmentation_d0 (Derivation.smoothRingSheaf p))
    (totalOperators p).columnUnit_d0

theorem comm1 : map1 p ≫ (totalPartialResolution p).d₁ =
    (Row.partialResolution p).d₁ ≫ map2 p :=
  TotalMaps.last_square1 (totalOperators p).categoryData _ _ _
    (columnUnit1_vertical p) (totalOperators p).columnUnit_d1

theorem comm2 : map2 p ≫ (totalPartialResolution p).d₂ =
    (Row.partialResolution p).d₂ ≫ map3 p :=
  TotalMaps.last_square2 (totalOperators p).categoryData _ _ _
    (GodementExact.augmentation_d0 (Derivation.smoothRingSheaf p))
    (totalOperators p).columnUnit_d2

/-- The genuine row-to-total map of the original partial resolutions. -/
def toTotal : (Row.partialResolution p).Hom (totalPartialResolution p) where
  augmentation := 𝟙 _
  τ₀ := map0 p
  τ₁ := map1 p
  τ₂ := map2 p
  τ₃ := map3 p
  commι := by
    change 𝟙 _ ≫ (Dolbeault.inclusion p ≫ Total.columnUnit0 p) =
      Dolbeault.inclusion p ≫ Total.columnUnit0 p
    exact Category.id_comp _
  comm₀ := comm0 p
  comm₁ := comm1 p
  comm₂ := comm2 p

@[simp] theorem toTotal_augmentation : (toTotal p).augmentation = 𝟙 _ := rfl

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.LastMaps
