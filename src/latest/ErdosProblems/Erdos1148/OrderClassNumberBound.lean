import ErdosProblems.Erdos1148.OrderClassSurjective
import ErdosProblems.Erdos1148.GluedIdealExtension
import ErdosProblems.Erdos1148.ConductorClassCard

/-! # A conductor lower bound for the order class number -/

namespace Erdos1148.DukeArithmetic

open NumberField

theorem conductor_range_card_mul_field_class_card_le_order_class_card
    {d : ℤ} [Fact (¬IsSquare d)] (hd : 0 < d) {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    Nat.card (conductorClassMap ht).range * Nat.card (ClassGroup (𝓞 (QuadraticDiscrAlgebra d))) ≤
      Nat.card (ClassGroup (quadraticOrder d)) := by
  let := quadraticOrder_classGroup_finite hd ht
  have hcard : Nat.card (conductorClassMap ht).range ≤ Nat.card (orderClassExtension ht).ker :=
    Subgroup.card_le_of_le (conductorClassMap_range_le_orderClassExtension_ker ht)
  have hindex : (orderClassExtension ht).ker.index =
      Nat.card (ClassGroup (𝓞 (QuadraticDiscrAlgebra d))) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
      (orderClassExtension ht) (orderClassExtension_surjective ht)).toEquiv
  calc
    _ ≤ Nat.card (orderClassExtension ht).ker *
        Nat.card (ClassGroup (𝓞 (QuadraticDiscrAlgebra d))) := Nat.mul_le_mul_right _ hcard
    _ = Nat.card (ClassGroup (quadraticOrder d)) := by
      rw [← hindex]
      exact (orderClassExtension ht).ker.card_mul_index

theorem field_class_card_mul_residue_index_le_order_class_card_mul_unit_index
    {d : ℤ} [Fact (¬IsSquare d)] (hd : 0 < d) {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    Nat.card (ClassGroup (𝓞 (QuadraticDiscrAlgebra d))) * (orderResidueUnitSubgroup ht).index ≤
      Nat.card (ClassGroup (quadraticOrder d)) * (orderUnitSubgroup ht).index := by
  calc
    _ = (Nat.card (conductorClassMap ht).range *
        Nat.card (ClassGroup (𝓞 (QuadraticDiscrAlgebra d)))) * (orderUnitSubgroup ht).index := by
      rw [← conductorClassMap_range_card_mul_unitIndex ht]
      ring
    _ ≤ _ := Nat.mul_le_mul_right _
      (conductor_range_card_mul_field_class_card_le_order_class_card hd ht)

end Erdos1148.DukeArithmetic
