import ErdosProblems.Erdos1148.QuadraticOrderIntegers
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient

/-! # A nonzero conductor ideal for the discriminant order -/

namespace Erdos1148.DukeArithmetic

open NumberField
open scoped nonZeroDivisors

theorem exists_order_multiple_all_integers {d : ℤ} [Fact (¬IsSquare d)] :
    ∃ a : quadraticOrder d, a ≠ 0 ∧ ∀ x : 𝓞 (QuadraticDiscrAlgebra d),
      (a : QuadraticDiscrAlgebra d) * (x : QuadraticDiscrAlgebra d) ∈ quadraticOrder d := by
  classical
  let b := RingOfIntegers.basis (QuadraticDiscrAlgebra d)
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples_of_finite (quadraticOrder d)⁰
    (fun i => (b i : QuadraticDiscrAlgebra d))
  refine ⟨a, mem_nonZeroDivisors_iff_ne_zero.mp a.2, ?_⟩
  intro x
  have hrepr : (x : QuadraticDiscrAlgebra d) =
      ∑ i, (b.repr x i : QuadraticDiscrAlgebra d) * (b i : QuadraticDiscrAlgebra d) := by
    have h := congrArg (fun z : 𝓞 (QuadraticDiscrAlgebra d) => (z : QuadraticDiscrAlgebra d))
      (b.sum_repr x)
    simpa only [map_sum, map_zsmul, zsmul_eq_mul, map_mul, map_intCast] using h.symm
  rw [hrepr, Finset.mul_sum]
  apply (quadraticOrder d).sum_mem
  intro i _
  obtain ⟨y, hy⟩ := ha i
  have hy' : (y : QuadraticDiscrAlgebra d) =
      ((a : quadraticOrder d) : QuadraticDiscrAlgebra d) * (b i : QuadraticDiscrAlgebra d) := hy
  rw [mul_left_comm, ← hy']
  exact (quadraticOrder d).mul_mem (intCast_mem (quadraticOrder d) (b.repr x i)) y.2

def quadraticOrderConductor (d : ℤ) [Fact (¬IsSquare d)] :
    Ideal (𝓞 (QuadraticDiscrAlgebra d)) where
  carrier := {x | ∀ y : 𝓞 (QuadraticDiscrAlgebra d),
    (x : QuadraticDiscrAlgebra d) * (y : QuadraticDiscrAlgebra d) ∈ quadraticOrder d}
  zero_mem' := by intro y; simpa using (quadraticOrder d).zero_mem
  add_mem' hx hy z := by
    simpa only [map_add, add_mul] using (quadraticOrder d).add_mem (hx z) (hy z)
  smul_mem' r x hx y := by
    have h := hx (r * y)
    change (x : QuadraticDiscrAlgebra d) *
      ((r : QuadraticDiscrAlgebra d) * (y : QuadraticDiscrAlgebra d)) ∈ quadraticOrder d at h
    change ((r : QuadraticDiscrAlgebra d) * (x : QuadraticDiscrAlgebra d)) *
      (y : QuadraticDiscrAlgebra d) ∈ quadraticOrder d
    simpa only [mul_assoc, mul_left_comm] using h

lemma mem_quadraticOrderConductor {d : ℤ} [Fact (¬IsSquare d)]
    (x : 𝓞 (QuadraticDiscrAlgebra d)) :
    x ∈ quadraticOrderConductor d ↔ ∀ y : 𝓞 (QuadraticDiscrAlgebra d),
      (x : QuadraticDiscrAlgebra d) * (y : QuadraticDiscrAlgebra d) ∈ quadraticOrder d := Iff.rfl

lemma quadraticOrderConductor_mem_order {d : ℤ} [Fact (¬IsSquare d)]
    {x : 𝓞 (QuadraticDiscrAlgebra d)} (hx : x ∈ quadraticOrderConductor d) :
    (x : QuadraticDiscrAlgebra d) ∈ quadraticOrder d := by
  simpa using hx 1

theorem quadraticOrderConductor_ne_bot {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) : quadraticOrderConductor d ≠ ⊥ := by
  obtain ⟨a, ha, hall⟩ := exists_order_multiple_all_integers (d := d)
  have hmem : quadraticOrderToIntegers ht a ∈ quadraticOrderConductor d := hall
  intro hbot
  rw [hbot, Ideal.mem_bot] at hmem
  apply ha
  exact (quadraticOrderToIntegers_injective ht) (by simpa using hmem)

theorem quadraticOrderConductor_quotient_finite {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    Finite (𝓞 (QuadraticDiscrAlgebra d) ⧸ quadraticOrderConductor d) :=
  (quadraticOrderConductor d).finiteQuotientOfFreeOfNeBot (quadraticOrderConductor_ne_bot ht)

noncomputable def orderConductorIdeal {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) : Ideal (quadraticOrder d) :=
  (quadraticOrderConductor d).comap (quadraticOrderToIntegers ht)

noncomputable def conductorQuotientMap {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    (quadraticOrder d ⧸ orderConductorIdeal ht) →+*
      (𝓞 (QuadraticDiscrAlgebra d) ⧸ quadraticOrderConductor d) :=
  Ideal.quotientMap (quadraticOrderConductor d) (quadraticOrderToIntegers ht) le_rfl

theorem conductorQuotientMap_injective {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) : Function.Injective (conductorQuotientMap ht) :=
  Ideal.quotientMap_injective

theorem orderConductorIdeal_quotient_finite {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    Finite (quadraticOrder d ⧸ orderConductorIdeal ht) := by
  let := quadraticOrderConductor_quotient_finite ht
  exact Finite.of_injective (conductorQuotientMap ht) (conductorQuotientMap_injective ht)

end Erdos1148.DukeArithmetic
