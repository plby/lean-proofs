import ErdosProblems.Erdos1148.QuadraticOrderConductor
import ErdosProblems.Erdos1148.OrderUnitSubgroup

/-! # Recovering order units from the finite conductor quotients -/

namespace Erdos1148.DukeArithmetic

open NumberField

theorem quotient_mem_conductorQuotientMap_range_iff {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) (x : 𝓞 (QuadraticDiscrAlgebra d)) :
    Ideal.Quotient.mk (quadraticOrderConductor d) x ∈ (conductorQuotientMap ht).range ↔
      (x : QuadraticDiscrAlgebra d) ∈ quadraticOrder d := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    change Ideal.Quotient.mk (quadraticOrderConductor d) (quadraticOrderToIntegers ht a) =
      Ideal.Quotient.mk (quadraticOrderConductor d) x at ha
    have hm := quadraticOrderConductor_mem_order (Ideal.Quotient.eq.mp ha)
    change (a : QuadraticDiscrAlgebra d) - (x : QuadraticDiscrAlgebra d) ∈ quadraticOrder d at hm
    simpa using (quadraticOrder d).sub_mem a.2 hm
  · intro hx
    refine ⟨Ideal.Quotient.mk (orderConductorIdeal ht) ⟨(x : QuadraticDiscrAlgebra d), hx⟩, ?_⟩
    rfl

lemma unit_mem_map_range_iff {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Injective f) (u : Bˣ) :
    u ∈ (Units.map f.toMonoidHom).range ↔ (u : B) ∈ f.range ∧ (↑u⁻¹ : B) ∈ f.range := by
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨⟨(v : A), rfl⟩, ⟨(↑v⁻¹ : A), rfl⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    have hab : a * b = 1 := by
      apply hf
      rw [map_mul, map_one, ha, hb]
      exact u.val_inv
    let v : Aˣ := ⟨a, b, hab, by rw [mul_comm]; exact hab⟩
    exact ⟨v, Units.ext ha⟩

theorem mem_orderUnitSubgroup_iff {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) (u : (𝓞 (QuadraticDiscrAlgebra d))ˣ) :
    u ∈ orderUnitSubgroup ht ↔ (u : QuadraticDiscrAlgebra d) ∈ quadraticOrder d ∧
      (↑u⁻¹ : QuadraticDiscrAlgebra d) ∈ quadraticOrder d := by
  rw [orderUnitSubgroup, orderUnitMap,
    unit_mem_map_range_iff _ (quadraticOrderToIntegers_injective ht)]
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    constructor
    · rw [← ha]
      exact a.2
    · rw [← hb]
      exact b.2
  · rintro ⟨ha, hb⟩
    exact ⟨⟨⟨(u : QuadraticDiscrAlgebra d), ha⟩, rfl⟩,
      ⟨⟨(↑u⁻¹ : QuadraticDiscrAlgebra d), hb⟩, rfl⟩⟩

noncomputable def conductorUnitReduction (d : ℤ) [Fact (¬IsSquare d)] :
    (𝓞 (QuadraticDiscrAlgebra d))ˣ →*
      (𝓞 (QuadraticDiscrAlgebra d) ⧸ quadraticOrderConductor d)ˣ :=
  Units.map (Ideal.Quotient.mk (quadraticOrderConductor d)).toMonoidHom

noncomputable def orderResidueUnitSubgroup {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    Subgroup (𝓞 (QuadraticDiscrAlgebra d) ⧸ quadraticOrderConductor d)ˣ :=
  (Units.map (conductorQuotientMap ht).toMonoidHom).range

theorem orderUnitSubgroup_eq_conductor_comap {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    orderUnitSubgroup ht = (orderResidueUnitSubgroup ht).comap (conductorUnitReduction d) := by
  ext u
  rw [mem_orderUnitSubgroup_iff]
  change _ ↔ conductorUnitReduction d u ∈ (Units.map (conductorQuotientMap ht).toMonoidHom).range
  rw [unit_mem_map_range_iff _ (conductorQuotientMap_injective ht)]
  change _ ↔ Ideal.Quotient.mk (quadraticOrderConductor d) (u : 𝓞 (QuadraticDiscrAlgebra d)) ∈
    (conductorQuotientMap ht).range ∧
    Ideal.Quotient.mk (quadraticOrderConductor d) (↑u⁻¹ : 𝓞 (QuadraticDiscrAlgebra d)) ∈
      (conductorQuotientMap ht).range
  rw [quotient_mem_conductorQuotientMap_range_iff, quotient_mem_conductorQuotientMap_range_iff]

theorem orderUnitSubgroup_index_eq_residue_relIndex {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    (orderUnitSubgroup ht).index =
      (orderResidueUnitSubgroup ht).relIndex (conductorUnitReduction d).range := by
  rw [orderUnitSubgroup_eq_conductor_comap, Subgroup.index_comap]

end Erdos1148.DukeArithmetic
