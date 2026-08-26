import ErdosProblems.Erdos1148.ConductorExactKernel
import ErdosProblems.Erdos1148.OrderClassPacketMass

/-! # The residue-unit index and the size of the conductor class-map image -/

namespace Erdos1148.DukeArithmetic

open NumberField

theorem conductorClassMap_range_card_mul_unitIndex {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    Nat.card (conductorClassMap ht).range * (orderUnitSubgroup ht).index =
      (orderResidueUnitSubgroup ht).index := by
  have h := Subgroup.relIndex_mul_index (show orderResidueUnitSubgroup ht ≤
    orderResidueUnitSubgroup ht ⊔ (conductorUnitReduction d).range from le_sup_left)
  rw [Subgroup.relIndex_sup_left] at h
  rw [← Subgroup.index_ker, conductorClassMap_ker, orderUnitSubgroup_index_eq_residue_relIndex]
  simpa only [mul_comm] using h

theorem residueUnitIndex_le_class_card_mul_unitIndex {d : ℤ} [Fact (¬IsSquare d)]
    (hd : 0 < d) {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    (orderResidueUnitSubgroup ht).index ≤
      Nat.card (ClassGroup (quadraticOrder d)) * (orderUnitSubgroup ht).index := by
  let := quadraticOrder_classGroup_finite hd ht
  have hc : Nat.card (conductorClassMap ht).range ≤ Nat.card (ClassGroup (quadraticOrder d)) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  rw [← conductorClassMap_range_card_mul_unitIndex ht]
  exact Nat.mul_le_mul_right _ hc

end Erdos1148.DukeArithmetic
