import ErdosProblems.Erdos1148.OrderIndexConductor
import ErdosProblems.Erdos1148.ConductorUnitPullback

/-! # Comparing residue-unit and additive order indices -/

namespace Erdos1148.DukeArithmetic

open NumberField

noncomputable def orderResidueAddSubgroup {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    AddSubgroup (𝓞 (QuadraticDiscrAlgebra d) ⧸ quadraticOrderConductor d) :=
  (conductorQuotientMap ht).toAddMonoidHom.range

theorem orderResidueAddSubgroup_comap {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    (orderResidueAddSubgroup ht).comap
      (Ideal.Quotient.mk (quadraticOrderConductor d)).toAddMonoidHom =
        quadraticOrderAddSubgroup ht := by
  ext x
  change Ideal.Quotient.mk (quadraticOrderConductor d) x ∈
    (conductorQuotientMap ht).range ↔ x ∈ quadraticOrderAddSubgroup ht
  rw [quotient_mem_conductorQuotientMap_range_iff]
  constructor
  · intro hx
    exact ⟨⟨(x : QuadraticDiscrAlgebra d), hx⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    exact a.2

theorem orderResidueAddSubgroup_index {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    (orderResidueAddSubgroup ht).index = quadraticOrderIndex ht := by
  have h := (orderResidueAddSubgroup ht).index_comap_of_surjective
    (f := (Ideal.Quotient.mk (quadraticOrderConductor d)).toAddMonoidHom)
    (Ideal.Quotient.mk_surjective)
  rw [orderResidueAddSubgroup_comap] at h
  exact h.symm

theorem orderResidueUnitSubgroup_card_le_addSubgroup {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    Nat.card (orderResidueUnitSubgroup ht) ≤ Nat.card (orderResidueAddSubgroup ht) := by
  let := quadraticOrderConductor_quotient_finite ht
  let f : orderResidueUnitSubgroup ht → orderResidueAddSubgroup ht := fun u =>
    ⟨(u.1 : 𝓞 (QuadraticDiscrAlgebra d) ⧸ quadraticOrderConductor d), by
      obtain ⟨a, ha⟩ := u.2
      exact ⟨(a : quadraticOrder d ⧸ orderConductorIdeal ht), congrArg Units.val ha⟩⟩
  apply Nat.card_le_card_of_injective f
  intro u v huv
  apply Subtype.ext
  apply Units.ext
  exact congrArg Subtype.val huv

theorem orderIndex_mul_residue_units_card_le {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    quadraticOrderIndex ht * Nat.card (𝓞 (QuadraticDiscrAlgebra d) ⧸ quadraticOrderConductor d)ˣ ≤
      Nat.card (𝓞 (QuadraticDiscrAlgebra d) ⧸ quadraticOrderConductor d) *
        (orderResidueUnitSubgroup ht).index := by
  have h := Nat.mul_le_mul_right ((orderResidueUnitSubgroup ht).index)
    (Nat.mul_le_mul_left (quadraticOrderIndex ht)
      (orderResidueUnitSubgroup_card_le_addSubgroup ht))
  have hmul : quadraticOrderIndex ht * Nat.card (orderResidueAddSubgroup ht) =
      Nat.card (𝓞 (QuadraticDiscrAlgebra d) ⧸ quadraticOrderConductor d) := by
    rw [← orderResidueAddSubgroup_index, mul_comm]
    exact (orderResidueAddSubgroup ht).card_mul_index
  rw [hmul, mul_assoc, (orderResidueUnitSubgroup ht).card_mul_index] at h
  exact h

end Erdos1148.DukeArithmetic
