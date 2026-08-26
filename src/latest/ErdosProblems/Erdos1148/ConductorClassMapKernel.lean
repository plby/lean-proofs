import ErdosProblems.Erdos1148.ConductorClassMap

/-! # Residue units that act trivially on the order class group -/

namespace Erdos1148.DukeArithmetic

open NumberField
open scoped nonZeroDivisors

theorem conductorGluedIdeal_eq_one_of_orderResidue {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d)
    {u : (𝓞 (QuadraticDiscrAlgebra d) ⧸ quadraticOrderConductor d)ˣ}
    (hu : u ∈ orderResidueUnitSubgroup ht) : conductorGluedIdeal ht u = 1 := by
  have hmem := (unit_mem_map_range_iff _ (conductorQuotientMap_injective ht) u).mp hu
  apply le_antisymm
  · rintro _ ⟨x, rfl, hx⟩
    have hp := (conductorQuotientMap ht).range.mul_mem hx hmem.1
    have hx' : Ideal.Quotient.mk (quadraticOrderConductor d) x ∈
        (conductorQuotientMap ht).range := by
      simpa only [mul_assoc, Units.inv_mul, mul_one] using hp
    have hxo := (quotient_mem_conductorQuotientMap_range_iff ht x).mp hx'
    exact (FractionalIdeal.mem_one_iff (quadraticOrder d)⁰).mpr ⟨⟨(x : _), hxo⟩, rfl⟩
  · apply FractionalIdeal.one_le.mpr
    refine ⟨1, rfl, ?_⟩
    simpa using hmem.2

theorem conductorClassMap_eq_one_of_orderResidue {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d)
    {u : (𝓞 (QuadraticDiscrAlgebra d) ⧸ quadraticOrderConductor d)ˣ}
    (hu : u ∈ orderResidueUnitSubgroup ht) : conductorClassMap ht u = 1 := by
  have hunit : conductorGluedIdealHom ht u = 1 :=
    Units.ext (conductorGluedIdeal_eq_one_of_orderResidue ht hu)
  change ClassGroup.mk (QuadraticDiscrAlgebra d) (conductorGluedIdealHom ht u) = 1
  rw [hunit, map_one]

theorem conductorGluedIdeal_reducedUnit {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) (u : (𝓞 (QuadraticDiscrAlgebra d))ˣ) :
    conductorGluedIdeal ht (conductorUnitReduction d u) =
      FractionalIdeal.spanSingleton (quadraticOrder d)⁰ (u : QuadraticDiscrAlgebra d) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl, hx⟩
    have hxq : Ideal.Quotient.mk (quadraticOrderConductor d) (x * (↑u⁻¹ : _)) ∈
        (conductorQuotientMap ht).range := by
      change Ideal.Quotient.mk (quadraticOrderConductor d) x *
        Ideal.Quotient.mk (quadraticOrderConductor d) (↑u⁻¹ : _) ∈ _ at hx
      simpa only [map_mul] using hx
    have hxo := (quotient_mem_conductorQuotientMap_range_iff ht (x * (↑u⁻¹ : _))).mp hxq
    refine (FractionalIdeal.mem_spanSingleton (quadraticOrder d)⁰).mpr
      ⟨⟨((x * (↑u⁻¹ : 𝓞 (QuadraticDiscrAlgebra d)) : 𝓞 (QuadraticDiscrAlgebra d)) :
        QuadraticDiscrAlgebra d), hxo⟩, ?_⟩
    change ((x : QuadraticDiscrAlgebra d) * (↑u⁻¹ : QuadraticDiscrAlgebra d)) *
      (u : QuadraticDiscrAlgebra d) = x
    rw [mul_assoc, ← NumberField.Units.coe_mul, inv_mul_cancel, NumberField.Units.coe_one, mul_one]
  · intro z hz
    obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_spanSingleton (quadraticOrder d)⁰).mp hz
    refine ⟨quadraticOrderToIntegers ht a * (u : 𝓞 (QuadraticDiscrAlgebra d)), rfl, ?_⟩
    have ha : Ideal.Quotient.mk (quadraticOrderConductor d) (quadraticOrderToIntegers ht a) ∈
        (conductorQuotientMap ht).range := ⟨Ideal.Quotient.mk (orderConductorIdeal ht) a, rfl⟩
    change Ideal.Quotient.mk (quadraticOrderConductor d)
      (quadraticOrderToIntegers ht a * (u : 𝓞 (QuadraticDiscrAlgebra d))) *
      Ideal.Quotient.mk (quadraticOrderConductor d) (↑u⁻¹ : _) ∈ _
    rw [← map_mul, mul_assoc, Units.mul_inv, mul_one]
    exact ha

theorem conductorClassMap_reducedUnit {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) (u : (𝓞 (QuadraticDiscrAlgebra d))ˣ) :
    conductorClassMap ht (conductorUnitReduction d u) = 1 := by
  let v : (QuadraticDiscrAlgebra d)ˣ :=
    Units.map (algebraMap (𝓞 (QuadraticDiscrAlgebra d)) (QuadraticDiscrAlgebra d)).toMonoidHom u
  have hunit : conductorGluedIdealHom ht (conductorUnitReduction d u) =
      toPrincipalIdeal (quadraticOrder d) (QuadraticDiscrAlgebra d) v := by
    apply Units.ext
    rw [coe_toPrincipalIdeal]
    exact conductorGluedIdeal_reducedUnit ht u
  change ClassGroup.mk (QuadraticDiscrAlgebra d)
    (conductorGluedIdealHom ht (conductorUnitReduction d u)) = 1
  rw [hunit, classGroup_mk_principal]

theorem residueUnits_sup_reducedUnits_le_conductorClassMap_ker
    {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    orderResidueUnitSubgroup ht ⊔ (conductorUnitReduction d).range ≤
      (conductorClassMap ht).ker := by
  apply sup_le
  · intro u hu
    exact conductorClassMap_eq_one_of_orderResidue ht hu
  · rintro _ ⟨u, rfl⟩
    exact conductorClassMap_reducedUnit ht u

end Erdos1148.DukeArithmetic
