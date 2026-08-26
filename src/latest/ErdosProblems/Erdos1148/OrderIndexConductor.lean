import ErdosProblems.Erdos1148.QuadraticOrderIndex
import ErdosProblems.Erdos1148.QuadraticOrderConductor
import Mathlib.GroupTheory.IndexNSmul

/-! # The order index annihilates the quotient by the conductor -/

namespace Erdos1148.DukeArithmetic

open NumberField

theorem orderIndex_mul_integer_mem_order {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) (x : 𝓞 (QuadraticDiscrAlgebra d)) :
    (quadraticOrderIndex ht : QuadraticDiscrAlgebra d) * (x : QuadraticDiscrAlgebra d) ∈
      quadraticOrder d := by
  obtain ⟨a, ha⟩ := (quadraticOrderAddSubgroup ht).nsmul_index_mem x
  have hval : (a : QuadraticDiscrAlgebra d) =
      (quadraticOrderIndex ht : QuadraticDiscrAlgebra d) * (x : QuadraticDiscrAlgebra d) := by
    have h := congrArg
      (fun z : 𝓞 (QuadraticDiscrAlgebra d) => (z : QuadraticDiscrAlgebra d)) ha
    change (a : QuadraticDiscrAlgebra d) =
      algebraMap (𝓞 (QuadraticDiscrAlgebra d)) (QuadraticDiscrAlgebra d)
        (quadraticOrderIndex ht • x) at h
    rw [map_nsmul, nsmul_eq_mul] at h
    exact h
  rw [← hval]
  exact a.2

theorem quadraticOrderIndex_mem_conductor {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    (quadraticOrderIndex ht : 𝓞 (QuadraticDiscrAlgebra d)) ∈ quadraticOrderConductor d := by
  intro x
  exact orderIndex_mul_integer_mem_order ht x

theorem span_orderIndex_le_conductor {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    Ideal.span {(quadraticOrderIndex ht : 𝓞 (QuadraticDiscrAlgebra d))} ≤
      quadraticOrderConductor d :=
  (Ideal.span_singleton_le_iff_mem _).mpr (quadraticOrderIndex_mem_conductor ht)

theorem conductor_quotient_card_dvd_orderIndex_sq {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    Nat.card (𝓞 (QuadraticDiscrAlgebra d) ⧸ quadraticOrderConductor d) ∣
      quadraticOrderIndex ht ^ 2 := by
  have hle : (nsmulAddMonoidHom (α := 𝓞 (QuadraticDiscrAlgebra d))
      (quadraticOrderIndex ht)).range ≤ (quadraticOrderConductor d).toAddSubgroup := by
    rintro _ ⟨x, rfl⟩
    change (quadraticOrderIndex ht) • x ∈ quadraticOrderConductor d
    rw [nsmul_eq_mul]
    exact (quadraticOrderConductor d).mul_mem_right x (quadraticOrderIndex_mem_conductor ht)
  have h := AddSubgroup.index_dvd_of_le hle
  rw [AddSubgroup.index_range_nsmul, RingOfIntegers.rank, quadraticDiscrAlgebra_finrank] at h
  exact h

end Erdos1148.DukeArithmetic
