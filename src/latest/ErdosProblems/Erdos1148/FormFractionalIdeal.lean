import ErdosProblems.Erdos1148.FormLatticeBasis

/-! # The proper fractional ideal associated with a primitive integral form -/

namespace Erdos1148.DukeArithmetic

open scoped nonZeroDivisors

instance quadraticOrderAlgebra (d : ℤ) : Algebra (quadraticOrder d) (QuadraticDiscrAlgebra d) :=
  (quadraticOrder d).subtype.toAlgebra

lemma quadraticOrder_algebraMap (d : ℤ) (u : quadraticOrder d) :
    algebraMap (quadraticOrder d) (QuadraticDiscrAlgebra d) u = u.1 := rfl

instance quadraticOrder_faithfulSMul (d : ℤ) :
    FaithfulSMul (quadraticOrder d) (QuadraticDiscrAlgebra d) where
  eq_of_smul_eq_smul := by
    intro u v h
    apply Subtype.ext
    have h1 := h (1 : QuadraticDiscrAlgebra d)
    simpa only [Algebra.smul_def, quadraticOrder_algebraMap, mul_one] using h1

noncomputable def formIdealSubmodule {d : ℤ} {t : ℤ × ℤ × ℤ}
    (ht : discr t = d) (ha : t.1 ≠ 0) : Submodule (quadraticOrder d) (QuadraticDiscrAlgebra d) where
  carrier := (formIdealLattice (d := d) t ha : Set (QuadraticDiscrAlgebra d))
  zero_mem' := (formIdealLattice (d := d) t ha).zero_mem
  add_mem' := (formIdealLattice (d := d) t ha).add_mem
  smul_mem' := by
    intro u z hz
    change z ∈ formIdealLattice (d := d) t ha at hz
    change (u : QuadraticDiscrAlgebra d) * z ∈ formIdealLattice t ha
    exact formIdealLattice_order_mul_mem ht ha u.2 hz

lemma mem_formIdealSubmodule {d : ℤ} {t : ℤ × ℤ × ℤ}
    (ht : discr t = d) (ha : t.1 ≠ 0) (z : QuadraticDiscrAlgebra d) :
    z ∈ formIdealSubmodule ht ha ↔ z ∈ formIdealLattice t ha := Iff.rfl

theorem formIdealSubmodule_isFractional {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) (ha : t.1 ≠ 0) :
    IsFractional (quadraticOrder d)⁰ (formIdealSubmodule ht ha) := by
  refine ⟨((2 * t.1 : ℤ) : quadraticOrder d), ?_, ?_⟩
  · apply mem_nonZeroDivisors_iff_ne_zero.mpr
    exact Int.cast_ne_zero.mpr (mul_ne_zero (by norm_num) ha)
  · intro z hz
    refine ⟨⟨((2 * t.1 : ℤ) : QuadraticDiscrAlgebra d) * z,
      formIdealLattice_clear_denominator t ha hz⟩, ?_⟩
    rfl

noncomputable def formFractionalIdeal {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) (ha : t.1 ≠ 0) :
    FractionalIdeal (quadraticOrder d)⁰ (QuadraticDiscrAlgebra d) :=
  ⟨formIdealSubmodule ht ha, formIdealSubmodule_isFractional ht ha⟩

lemma one_mem_formFractionalIdeal {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) (ha : t.1 ≠ 0) :
    (1 : QuadraticDiscrAlgebra d) ∈ formFractionalIdeal ht ha :=
  one_mem_formIdealLattice t ha

theorem formFractionalIdeal_ne_zero {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) (ha : t.1 ≠ 0) :
    formFractionalIdeal ht ha ≠ 0 := by
  intro hz
  have hmem := one_mem_formFractionalIdeal ht ha
  rw [hz] at hmem
  simp at hmem

end Erdos1148.DukeArithmetic
