import ErdosProblems.Erdos1148.FormLatticeAction
import ErdosProblems.Erdos1148.InvertibleFormIdeal

/-! # Integral changes of form multiply the associated ideal by a principal ideal -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups nonZeroDivisors

theorem formFractionalIdeal_action_eq_span_mul {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) (ha : t.1 ≠ 0) (γ : SL(2, ℤ))
    (ha' : (formAction γ t).1 ≠ 0) :
    formFractionalIdeal ht ha =
      FractionalIdeal.spanSingleton (quadraticOrder d)⁰ (formActionScale t ha γ) *
        formFractionalIdeal ((discr_formAction γ t).trans ht) ha' := by
  let c := formActionScale (d := d) t ha γ
  have hc : c ≠ 0 := formActionScale_ne_zero ht ha γ ha'
  apply le_antisymm
  · intro w hw
    have hy : w / c ∈ formFractionalIdeal ((discr_formAction γ t).trans ht) ha' := by
      change w / c ∈ formIdealLattice (formAction γ t) ha'
      rw [formIdealLattice_action_mem_iff ht ha γ ha']
      change w / c * c ∈ formIdealLattice t ha
      rw [div_mul_cancel₀ _ hc]
      exact hw
    have hprod := FractionalIdeal.mul_mem_mul
      (FractionalIdeal.mem_spanSingleton_self (quadraticOrder d)⁰ c) hy
    have heq : c * (w / c) = w := by field_simp
    rw [heq] at hprod
    exact hprod
  · apply FractionalIdeal.mul_le.mpr
    intro x hx y hy
    obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).mp hx
    have hcy : c * y ∈ formFractionalIdeal ht ha := by
      change c * y ∈ formIdealLattice t ha
      rw [mul_comm]
      exact (formIdealLattice_action_mem_iff ht ha γ ha' y).mp hy
    have h := (formFractionalIdeal ht ha :
      Submodule (quadraticOrder d) (QuadraticDiscrAlgebra d)).smul_mem r hcy
    change (r • c) * y ∈ (formFractionalIdeal ht ha :
      Submodule (quadraticOrder d) (QuadraticDiscrAlgebra d))
    simpa only [smul_mul_assoc] using h

end Erdos1148.DukeArithmetic
