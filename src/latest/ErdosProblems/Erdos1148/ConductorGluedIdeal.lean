import ErdosProblems.Erdos1148.ConductorUnitPullback

/-! # Fractional ideals obtained by gluing a residue unit across the conductor -/

namespace Erdos1148.DukeArithmetic

open NumberField
open scoped nonZeroDivisors

noncomputable def conductorGluedSubmodule {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d)
    (u : (𝓞 (QuadraticDiscrAlgebra d) ⧸ quadraticOrderConductor d)ˣ) :
    Submodule (quadraticOrder d) (QuadraticDiscrAlgebra d) where
  carrier := {z | ∃ x : 𝓞 (QuadraticDiscrAlgebra d), (x : QuadraticDiscrAlgebra d) = z ∧
    Ideal.Quotient.mk (quadraticOrderConductor d) x * (↑u⁻¹) ∈ (conductorQuotientMap ht).range}
  zero_mem' := by
    refine ⟨0, rfl, ?_⟩
    simpa using (conductorQuotientMap ht).range.zero_mem
  add_mem' := by
    rintro _ _ ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩
    refine ⟨x + y, rfl, ?_⟩
    simpa only [map_add, add_mul] using (conductorQuotientMap ht).range.add_mem hx hy
  smul_mem' := by
    rintro a _ ⟨x, rfl, hx⟩
    refine ⟨quadraticOrderToIntegers ht a * x, rfl, ?_⟩
    have ha : Ideal.Quotient.mk (quadraticOrderConductor d) (quadraticOrderToIntegers ht a) ∈
        (conductorQuotientMap ht).range :=
      ⟨Ideal.Quotient.mk (orderConductorIdeal ht) a, rfl⟩
    simpa only [map_mul, mul_assoc] using (conductorQuotientMap ht).range.mul_mem ha hx

theorem conductorGluedSubmodule_isFractional {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d)
    (u : (𝓞 (QuadraticDiscrAlgebra d) ⧸ quadraticOrderConductor d)ˣ) :
    IsFractional (quadraticOrder d)⁰ (conductorGluedSubmodule ht u) := by
  obtain ⟨a, ha, hall⟩ := exists_order_multiple_all_integers (d := d)
  refine ⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha, ?_⟩
  rintro _ ⟨x, rfl, _⟩
  exact ⟨⟨(a : QuadraticDiscrAlgebra d) * (x : QuadraticDiscrAlgebra d), hall x⟩, rfl⟩

noncomputable def conductorGluedIdeal {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d)
    (u : (𝓞 (QuadraticDiscrAlgebra d) ⧸ quadraticOrderConductor d)ˣ) :
    FractionalIdeal (quadraticOrder d)⁰ (QuadraticDiscrAlgebra d) :=
  ⟨conductorGluedSubmodule ht u, conductorGluedSubmodule_isFractional ht u⟩

theorem mem_conductorGluedIdeal_coe_iff {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d)
    (u : (𝓞 (QuadraticDiscrAlgebra d) ⧸ quadraticOrderConductor d)ˣ)
    (x : 𝓞 (QuadraticDiscrAlgebra d)) :
    (x : QuadraticDiscrAlgebra d) ∈ conductorGluedIdeal ht u ↔
      Ideal.Quotient.mk (quadraticOrderConductor d) x * (↑u⁻¹) ∈
        (conductorQuotientMap ht).range := by
  constructor
  · rintro ⟨y, hy, hyu⟩
    have hyx : y = x := RingOfIntegers.coe_injective hy
    simpa only [hyx] using hyu
  · intro hx
    exact ⟨x, rfl, hx⟩

theorem conductor_mem_conductorGluedIdeal {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d)
    (u : (𝓞 (QuadraticDiscrAlgebra d) ⧸ quadraticOrderConductor d)ˣ)
    {x : 𝓞 (QuadraticDiscrAlgebra d)} (hx : x ∈ quadraticOrderConductor d) :
    (x : QuadraticDiscrAlgebra d) ∈ conductorGluedIdeal ht u := by
  rw [mem_conductorGluedIdeal_coe_iff, Ideal.Quotient.eq_zero_iff_mem.mpr hx, zero_mul]
  exact (conductorQuotientMap ht).range.zero_mem

theorem lift_mem_conductorGluedIdeal {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d)
    (u : (𝓞 (QuadraticDiscrAlgebra d) ⧸ quadraticOrderConductor d)ˣ)
    {x : 𝓞 (QuadraticDiscrAlgebra d)}
    (hx : Ideal.Quotient.mk (quadraticOrderConductor d) x = (u : _)) :
    (x : QuadraticDiscrAlgebra d) ∈ conductorGluedIdeal ht u := by
  rw [mem_conductorGluedIdeal_coe_iff, hx, Units.mul_inv]
  exact (conductorQuotientMap ht).range.one_mem

end Erdos1148.DukeArithmetic
