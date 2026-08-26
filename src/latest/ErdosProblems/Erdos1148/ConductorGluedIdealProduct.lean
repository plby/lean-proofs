import ErdosProblems.Erdos1148.ConductorGluedIdeal

/-! # Multiplication and inverses of conductor-glued fractional ideals -/

namespace Erdos1148.DukeArithmetic

open NumberField
open scoped nonZeroDivisors

theorem conductorGluedIdeal_mul_le {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d)
    (u v : (𝓞 (QuadraticDiscrAlgebra d) ⧸ quadraticOrderConductor d)ˣ) :
    conductorGluedIdeal ht u * conductorGluedIdeal ht v ≤ conductorGluedIdeal ht (u * v) := by
  apply FractionalIdeal.mul_le.mpr
  rintro _ ⟨x, rfl, hx⟩ _ ⟨y, rfl, hy⟩
  refine ⟨x * y, rfl, ?_⟩
  have h := (conductorQuotientMap ht).range.mul_mem hx hy
  convert h using 1
  simp only [map_mul, mul_inv_rev, Units.val_mul]
  ring

theorem conductorGluedIdeal_one {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) : conductorGluedIdeal ht 1 = 1 := by
  ext z
  constructor
  · rintro ⟨x, rfl, hx⟩
    have hx' : Ideal.Quotient.mk (quadraticOrderConductor d) x ∈
        (conductorQuotientMap ht).range := by simpa using hx
    have hxo := (quotient_mem_conductorQuotientMap_range_iff ht x).mp hx'
    exact (FractionalIdeal.mem_one_iff (quadraticOrder d)⁰).mpr ⟨⟨(x : _), hxo⟩, rfl⟩
  · intro hz
    obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff (quadraticOrder d)⁰).mp hz
    refine ⟨quadraticOrderToIntegers ht a, rfl, ?_⟩
    simpa using ((quotient_mem_conductorQuotientMap_range_iff ht
      (quadraticOrderToIntegers ht a)).mpr a.2)

theorem conductor_mem_gluedIdeal_mul_inverse {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d)
    (u : (𝓞 (QuadraticDiscrAlgebra d) ⧸ quadraticOrderConductor d)ˣ)
    {c : 𝓞 (QuadraticDiscrAlgebra d)} (hc : c ∈ quadraticOrderConductor d) :
    (c : QuadraticDiscrAlgebra d) ∈ conductorGluedIdeal ht u * conductorGluedIdeal ht u⁻¹ := by
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective
    (u : 𝓞 (QuadraticDiscrAlgebra d) ⧸ quadraticOrderConductor d)
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective
    (↑u⁻¹ : 𝓞 (QuadraticDiscrAlgebra d) ⧸ quadraticOrderConductor d)
  have hxy : x * y - 1 ∈ quadraticOrderConductor d := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, map_mul, map_one, hx, hy, Units.mul_inv, sub_self]
  have hcx : c * x ∈ quadraticOrderConductor d :=
    (quadraticOrderConductor d).mul_mem_right x hc
  have hfirst := FractionalIdeal.mul_mem_mul (conductor_mem_conductorGluedIdeal ht u hcx)
    (lift_mem_conductorGluedIdeal ht u⁻¹ hy)
  have hsecond := FractionalIdeal.mul_mem_mul (conductor_mem_conductorGluedIdeal ht u hc)
    (conductor_mem_conductorGluedIdeal ht u⁻¹ hxy)
  have hsub := ((conductorGluedIdeal ht u * conductorGluedIdeal ht u⁻¹ :
    FractionalIdeal (quadraticOrder d)⁰ (QuadraticDiscrAlgebra d)) :
    Submodule (quadraticOrder d) (QuadraticDiscrAlgebra d)).sub_mem hfirst hsecond
  have heq : ((c * x : 𝓞 (QuadraticDiscrAlgebra d)) : QuadraticDiscrAlgebra d) *
      (y : QuadraticDiscrAlgebra d) - (c : QuadraticDiscrAlgebra d) *
      ((x * y - 1 : 𝓞 (QuadraticDiscrAlgebra d)) : QuadraticDiscrAlgebra d) = c := by
    push_cast
    ring
  rwa [heq] at hsub

theorem conductorGluedIdeal_mul_inverse {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d)
    (u : (𝓞 (QuadraticDiscrAlgebra d) ⧸ quadraticOrderConductor d)ˣ) :
    conductorGluedIdeal ht u * conductorGluedIdeal ht u⁻¹ = 1 := by
  apply le_antisymm
  · simpa only [mul_inv_cancel, conductorGluedIdeal_one] using conductorGluedIdeal_mul_le ht u u⁻¹
  · apply FractionalIdeal.one_le.mpr
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective
      (u : 𝓞 (QuadraticDiscrAlgebra d) ⧸ quadraticOrderConductor d)
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective
      (↑u⁻¹ : 𝓞 (QuadraticDiscrAlgebra d) ⧸ quadraticOrderConductor d)
    have hxy : x * y - 1 ∈ quadraticOrderConductor d := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub, map_mul, map_one, hx, hy, Units.mul_inv, sub_self]
    have hfirst := FractionalIdeal.mul_mem_mul (lift_mem_conductorGluedIdeal ht u hx)
      (lift_mem_conductorGluedIdeal ht u⁻¹ hy)
    have hsecond := conductor_mem_gluedIdeal_mul_inverse ht u hxy
    have hsub := ((conductorGluedIdeal ht u * conductorGluedIdeal ht u⁻¹ :
      FractionalIdeal (quadraticOrder d)⁰ (QuadraticDiscrAlgebra d)) :
      Submodule (quadraticOrder d) (QuadraticDiscrAlgebra d)).sub_mem hfirst hsecond
    have heq : (x : QuadraticDiscrAlgebra d) * (y : QuadraticDiscrAlgebra d) -
        ((x * y - 1 : 𝓞 (QuadraticDiscrAlgebra d)) : QuadraticDiscrAlgebra d) = 1 := by
      push_cast
      ring
    rwa [heq] at hsub

end Erdos1148.DukeArithmetic
