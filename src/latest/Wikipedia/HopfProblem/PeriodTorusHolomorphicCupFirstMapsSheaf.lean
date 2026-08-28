import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupFirstMapsAlgebra
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalMapsCategorical
import Wikipedia.HopfProblem.SheafCupProductGodementExactMaps

/-!
# The original holomorphic Godement resolution maps into the actual total

Every component is the original Godement image of the actual inclusion,
followed by the first biproduct injection. Its signed differential
squares use genuine naturality and proved holomorphic annihilation.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.FirstMaps

open SheafCupProduct SheafSingularCupComparison

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

private theorem comp_pair_lift_zero {X : TopCat.{0}} {F G H : Pairs.AbSheaf X}
    (a : F ⟶ G) (b c : G ⟶ H) (hb : a ≫ b = 0) (hc : a ≫ c = 0) :
    a ≫ Pairs.lift b c = 0 := by
  apply Pairs.hom_ext
  · simp only [Category.assoc, Pairs.lift_fst, hb, zero_comp]
  · simp only [Category.assoc, Pairs.lift_snd, hc, zero_comp]

variable (p : PeriodDomain)

def first0 : GodementExact.I0 (Derivation.holomorphicRingSheaf p) ⟶
    (totalOperators p).I0 := GodementExact.I0Map (Derivation.inclusionRing p)

def first1 : GodementExact.I1 (Derivation.holomorphicRingSheaf p) ⟶
    (totalOperators p).I1 := GodementExact.I1Map (Derivation.inclusionRing p) ≫ biprod.inl

def first2 : GodementExact.I2 (Derivation.holomorphicRingSheaf p) ⟶
    (totalOperators p).I2 := GodementExact.I2Map (Derivation.inclusionRing p) ≫ biprod.inl

def first3 : GodementExact.I3 (Derivation.holomorphicRingSheaf p) ⟶
    (totalOperators p).I3 := GodementExact.I3Map (Derivation.inclusionRing p) ≫ biprod.inl

theorem first0_horizontal : first0 p ≫ (totalOperators p).categoryData.h00 = 0 :=
  comp_pair_lift_zero _ _ _ (Derivation.native_inclusion_derivative0 p 0)
    (Derivation.native_inclusion_derivative0 p 1)

theorem first1_horizontal :
    GodementExact.I1Map (Derivation.inclusionRing p) ≫
      (totalOperators p).categoryData.h10 = 0 :=
  comp_pair_lift_zero _ _ _ (Derivation.native_inclusion_derivative1 p 0)
    (Derivation.native_inclusion_derivative1 p 1)

theorem first2_horizontal :
    GodementExact.I2Map (Derivation.inclusionRing p) ≫
      (totalOperators p).categoryData.h20 = 0 :=
  comp_pair_lift_zero _ _ _ (Derivation.native_inclusion_derivative2 p 0)
    (Derivation.native_inclusion_derivative2 p 1)

theorem first_comm0 : first0 p ≫ (totalOperators p).d0 =
    GodementExact.d0 (Derivation.holomorphicRingSheaf p) ≫ first1 p :=
  TotalMaps.first_square0 (totalOperators p).categoryData _ _ _
    (GodementExact.d0_naturality (Derivation.inclusionRing p)) (first0_horizontal p)

theorem first_comm1 : first1 p ≫ (totalOperators p).d1 =
    GodementExact.d1 (Derivation.holomorphicRingSheaf p) ≫ first2 p :=
  TotalMaps.first_square1 (totalOperators p).categoryData _ _ _
    (GodementExact.d1_naturality (Derivation.inclusionRing p)) (first1_horizontal p)

theorem first_comm2 : first2 p ≫ (totalOperators p).d2 =
    GodementExact.d2 (Derivation.holomorphicRingSheaf p) ≫ first3 p :=
  TotalMaps.first_square2 (totalOperators p).categoryData _ _ _
    (GodementExact.d2_naturality (Derivation.inclusionRing p)) (first2_horizontal p)

/-- The actual augmented map induces the identity on the original holomorphic sheaf. -/
def firstToTotal : (GodementExact.partialResolution (Derivation.holomorphicRingSheaf p)).Hom
    (totalPartialResolution p) where
  augmentation := 𝟙 (PeriodTorusHolomorphicCohomology.holomorphicSheaf p)
  τ₀ := first0 p
  τ₁ := first1 p
  τ₂ := first2 p
  τ₃ := first3 p
  commι := (Category.id_comp _).trans
    (GodementExact.augmentation_naturality (Derivation.inclusionRing p))
  comm₀ := first_comm0 p
  comm₁ := first_comm1 p
  comm₂ := first_comm2 p

@[simp] theorem firstToTotal_augmentation :
    (firstToTotal p).augmentation = 𝟙 (PeriodTorusHolomorphicCohomology.holomorphicSheaf p) := rfl

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.FirstMaps
