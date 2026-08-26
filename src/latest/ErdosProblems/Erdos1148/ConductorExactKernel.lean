import ErdosProblems.Erdos1148.ConductorClassMapKernel

/-! # The exact kernel of the conductor residue class map -/

namespace Erdos1148.DukeArithmetic

open NumberField
open scoped nonZeroDivisors

theorem conductorGluedIdeal_eq_one_iff {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d)
    (u : (𝓞 (QuadraticDiscrAlgebra d) ⧸ quadraticOrderConductor d)ˣ) :
    conductorGluedIdeal ht u = 1 ↔ u ∈ orderResidueUnitSubgroup ht := by
  constructor
  · intro hu
    have hi := conductorGluedIdeal_mul_inverse ht u
    rw [hu, one_mul] at hi
    have h₁ : (1 : QuadraticDiscrAlgebra d) ∈ conductorGluedIdeal ht u := by
      rw [hu]
      exact FractionalIdeal.one_mem_one (quadraticOrder d)⁰
    have h₂ : (1 : QuadraticDiscrAlgebra d) ∈ conductorGluedIdeal ht u⁻¹ := by
      rw [hi]
      exact FractionalIdeal.one_mem_one (quadraticOrder d)⁰
    have h₁' := (mem_conductorGluedIdeal_coe_iff ht u 1).mp h₁
    have h₂' := (mem_conductorGluedIdeal_coe_iff ht u⁻¹ 1).mp h₂
    apply (unit_mem_map_range_iff _ (conductorQuotientMap_injective ht) u).mpr
    constructor
    · simpa using h₂'
    · simpa using h₁'
  · exact conductorGluedIdeal_eq_one_of_orderResidue ht

theorem exists_unit_of_conductorGluedIdeal_eq_span {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d)
    (u : (𝓞 (QuadraticDiscrAlgebra d) ⧸ quadraticOrderConductor d)ˣ)
    (a : QuadraticDiscrAlgebra d)
    (ha : conductorGluedIdeal ht u = FractionalIdeal.spanSingleton (quadraticOrder d)⁰ a) :
    ∃ v : (𝓞 (QuadraticDiscrAlgebra d))ˣ, (v : QuadraticDiscrAlgebra d) = a := by
  have ha_mem : a ∈ conductorGluedIdeal ht u := by
    rw [ha]
    exact FractionalIdeal.mem_spanSingleton_self _ _
  obtain ⟨a₀, ha₀, _⟩ := ha_mem
  have hprod : (1 : QuadraticDiscrAlgebra d) ∈
      FractionalIdeal.spanSingleton (quadraticOrder d)⁰ a * conductorGluedIdeal ht u⁻¹ := by
    rw [← ha, conductorGluedIdeal_mul_inverse]
    exact FractionalIdeal.one_mem_one (quadraticOrder d)⁰
  obtain ⟨b, hb, hab⟩ := FractionalIdeal.mem_singleton_mul.mp hprod
  obtain ⟨b₀, hb₀, _⟩ := hb
  have hab₀ : a₀ * b₀ = 1 := by
    apply RingOfIntegers.coe_injective
    change (a₀ : QuadraticDiscrAlgebra d) * (b₀ : QuadraticDiscrAlgebra d) = 1
    rw [ha₀, hb₀]
    exact hab.symm
  exact ⟨⟨a₀, b₀, hab₀, by rw [mul_comm]; exact hab₀⟩, ha₀⟩

theorem conductorClassMap_ker_le_residueUnits_sup_reducedUnits
    {d : ℤ} [Fact (¬IsSquare d)] {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    (conductorClassMap ht).ker ≤
      orderResidueUnitSubgroup ht ⊔ (conductorUnitReduction d).range := by
  intro u hu
  change ClassGroup.mk (QuadraticDiscrAlgebra d) (conductorGluedIdealHom ht u) = 1 at hu
  have hp := ClassGroup.mk_eq_one_iff.mp hu
  change (conductorGluedIdeal ht u :
    Submodule (quadraticOrder d) (QuadraticDiscrAlgebra d)).IsPrincipal at hp
  obtain ⟨a, ha⟩ := hp.principal
  have ha' : conductorGluedIdeal ht u = FractionalIdeal.spanSingleton (quadraticOrder d)⁰ a := by
    apply FractionalIdeal.coeToSubmodule_injective
    change (conductorGluedIdeal ht u : Submodule (quadraticOrder d) (QuadraticDiscrAlgebra d)) =
      (FractionalIdeal.spanSingleton (quadraticOrder d)⁰ a :
        Submodule (quadraticOrder d) (QuadraticDiscrAlgebra d))
    rw [FractionalIdeal.coe_spanSingleton]
    exact ha
  obtain ⟨v, hv⟩ := exists_unit_of_conductorGluedIdeal_eq_span ht u a ha'
  have heq : conductorGluedIdeal ht u = conductorGluedIdeal ht (conductorUnitReduction d v) := by
    rw [conductorGluedIdeal_reducedUnit, hv]
    exact ha'
  have hres : u * (conductorUnitReduction d v)⁻¹ ∈ orderResidueUnitSubgroup ht := by
    apply (conductorGluedIdeal_eq_one_iff ht _).mp
    rw [← conductorGluedIdeal_mul, heq, conductorGluedIdeal_mul_inverse]
  have hl : orderResidueUnitSubgroup ht ≤
      orderResidueUnitSubgroup ht ⊔ (conductorUnitReduction d).range := le_sup_left
  have hr : (conductorUnitReduction d).range ≤
      orderResidueUnitSubgroup ht ⊔ (conductorUnitReduction d).range := le_sup_right
  have hm := (orderResidueUnitSubgroup ht ⊔ (conductorUnitReduction d).range).mul_mem
    (hl hres) (hr ⟨v, rfl⟩)
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hm

theorem conductorClassMap_ker {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    (conductorClassMap ht).ker =
      orderResidueUnitSubgroup ht ⊔ (conductorUnitReduction d).range :=
  le_antisymm (conductorClassMap_ker_le_residueUnits_sup_reducedUnits ht)
    (residueUnits_sup_reducedUnits_le_conductorClassMap_ker ht)

end Erdos1148.DukeArithmetic
