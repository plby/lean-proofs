import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Integer Gauss sums of quadratic forms over the field with two elements

The sign sum is defined without choosing a basis. Its square is the cardinality
of the vector space when the polar form is nondegenerate. The proof uses
translation cancellation for nontrivial linear characters.

This is quadratic-form algebra only. No geometric Kervaire invariant or
framed-bordism computation is assumed or asserted here.
-/

open scoped BigOperators

namespace NoExoticSixSphere.Arf

abbrev F₂ := ZMod 2

def sign (a : F₂) : ℤ := if a = 0 then 1 else -1

@[simp] theorem sign_zero : sign 0 = 1 := by simp [sign]

@[simp] theorem sign_one : sign 1 = -1 := by norm_num [sign]

theorem sign_add (a b : F₂) : sign (a + b) = sign a * sign b := by
  fin_cases a <;> fin_cases b <;> decide

@[simp] theorem sign_mul_self (a : F₂) : sign a * sign a = 1 := by
  fin_cases a <;> decide

theorem sign_injective : Function.Injective sign := by decide

def gaussSum {V : Type*} [Fintype V] (q : V → F₂) : ℤ := ∑ x, sign (q x)

theorem gaussSum_equiv {V W : Type*} [Fintype V] [Fintype W]
    (q : W → F₂) (e : V ≃ W) : gaussSum (q ∘ e) = gaussSum q :=
  Equiv.sum_comp e (fun x ↦ sign (q x))

theorem gaussSum_prod {V W : Type*} [Fintype V] [Fintype W]
    (q : V → F₂) (r : W → F₂) :
    gaussSum (fun p : V × W ↦ q p.1 + r p.2) = gaussSum q * gaussSum r := by
  simp only [gaussSum, Fintype.sum_prod_type, sign_add, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

variable {V : Type*} [AddCommGroup V] [Module F₂ V] [Fintype V]

theorem gaussSum_linear_eq_zero (l : V →ₗ[F₂] F₂) (a : V) (ha : l a = 1) :
    gaussSum l = 0 := by
  have he := Equiv.sum_comp (Equiv.addRight a) (fun x ↦ sign (l x))
  change (∑ x : V, sign (l (x + a))) = ∑ x : V, sign (l x) at he
  simp only [map_add, ha, sign_add, sign_one, mul_neg_one,
    Finset.sum_neg_distrib] at he
  change -gaussSum l = gaussSum l at he
  linarith

theorem gaussSum_polar_eq_zero (q : QuadraticForm F₂ V)
    (hq : q.polarBilin.Nondegenerate) (z : V) (hz : z ≠ 0) :
    gaussSum (fun x ↦ q.polarBilin x z) = 0 := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, q.polarBilin a z ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hz (hq.2 z hn)
  have ha' : q.polarBilin a z = 1 := by
    generalize q.polarBilin a z = c at *
    have hc : c = 0 ∨ c = 1 := by
      fin_cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    exact hc.resolve_left ha
  exact gaussSum_linear_eq_zero (q.polarBilin.flip z) a ha'

omit [Fintype V] in
theorem sign_quadratic_translate (q : QuadraticForm F₂ V) (x z : V) :
    sign (q x) * sign (q (x + z)) = sign (q z) * sign (q.polarBilin x z) := by
  rw [QuadraticMap.map_add q x z, sign_add, sign_add]
  change sign (q x) * (sign (q x) * sign (q z) * sign (q.polarBilin x z)) = _
  calc
    _ = (sign (q x) * sign (q x)) * (sign (q z) * sign (q.polarBilin x z)) := by ring
    _ = _ := by rw [sign_mul_self, one_mul]

theorem gaussSum_sq (q : QuadraticForm F₂ V) (hq : q.polarBilin.Nondegenerate) :
    gaussSum q ^ 2 = Fintype.card V := by
  classical
  calc
    gaussSum q ^ 2 = ∑ x : V, ∑ y : V, sign (q x) * sign (q y) := by
      simp only [gaussSum, pow_two, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm
    _ = ∑ x : V, ∑ z : V, sign (q x) * sign (q (x + z)) := by
      apply Finset.sum_congr rfl
      intro x _
      exact (Equiv.sum_comp (Equiv.addLeft x) (fun y ↦ sign (q x) * sign (q y))).symm
    _ = ∑ z : V, ∑ x : V, sign (q x) * sign (q (x + z)) := Finset.sum_comm
    _ = ∑ z : V, sign (q z) * gaussSum (fun x ↦ q.polarBilin x z) := by
      simp only [sign_quadratic_translate, gaussSum, Finset.mul_sum]
    _ = Fintype.card V := by
      rw [Finset.sum_eq_single 0]
      · simp [gaussSum]
      · intro z _ hz
        rw [gaussSum_polar_eq_zero q hq z hz, mul_zero]
      · simp

theorem gaussSum_ne_zero (q : QuadraticForm F₂ V) (hq : q.polarBilin.Nondegenerate) :
    gaussSum q ≠ 0 := by
  intro h
  have hs := gaussSum_sq q hq
  have hc : (0 : ℤ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  rw [h] at hs
  norm_num at hs
  omega

end NoExoticSixSphere.Arf
