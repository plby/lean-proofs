import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

/-! # Uniform bounds for nonprincipal Dirichlet-character partial sums -/

namespace Erdos1148.DukeArithmetic

lemma sum_range_zmod_eq_sum_univ {A : Type*} [AddCommMonoid A]
    {q : ℕ} [NeZero q] (f : ZMod q → A) :
    ∑ n ∈ Finset.range q, f n = ∑ a : ZMod q, f a := by
  classical
  apply Finset.sum_bij (fun (n : ℕ) _ => (n : ZMod q))
  · intro n hn
    exact Finset.mem_univ _
  · intro a ha b hb hab
    have h := congrArg ZMod.val hab
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp ha),
      Nat.mod_eq_of_lt (Finset.mem_range.mp hb)] using h
  · intro a _
    exact ⟨a.val, Finset.mem_range.mpr a.val_lt, ZMod.natCast_zmod_val a⟩
  · intro n hn
    rfl

theorem dirichlet_sum_range_eq_remainder {F : Type*} [NormedField F] {q : ℕ} [NeZero q]
    (χ : DirichletCharacter F q) (hχ : χ ≠ 1) (n : ℕ) :
    ∑ k ∈ Finset.range n, χ k = ∑ k ∈ Finset.range (n % q), χ k := by
  have hzero : ∑ k ∈ Finset.range q, χ k = 0 := by
    rw [sum_range_zmod_eq_sum_univ]
    exact MulChar.sum_eq_zero_of_ne_one hχ
  have hperiod : Function.Periodic (fun m => ∑ k ∈ Finset.range m, χ k) q := by
    intro m
    change (∑ k ∈ Finset.range (m + q), χ k) = ∑ k ∈ Finset.range m, χ k
    rw [Nat.add_comm m q, Finset.sum_range_add, hzero, zero_add]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Nat.cast_add, CharP.cast_eq_zero, zero_add]
  have h := hperiod.nat_mul (n / q) (n % q)
  change (∑ k ∈ Finset.range (n % q + n / q * q), χ k) =
    ∑ k ∈ Finset.range (n % q), χ k at h
  have hn : n % q + n / q * q = n := by
    simpa only [Nat.mul_comm] using Nat.mod_add_div n q
  rwa [hn] at h

theorem dirichlet_norm_sum_range_le {F : Type*} [NormedField F] {q : ℕ} [NeZero q]
    (χ : DirichletCharacter F q) (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ Finset.range n, χ k‖ ≤ q := by
  rw [dirichlet_sum_range_eq_remainder χ hχ]
  calc
    _ ≤ ∑ k ∈ Finset.range (n % q), ‖χ k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range (n % q), (1 : ℝ) :=
      Finset.sum_le_sum (fun k _ => χ.norm_le_one k)
    _ = (n % q : ℕ) := by simp
    _ ≤ (q : ℝ) := by exact_mod_cast (Nat.mod_lt n (NeZero.pos q)).le

theorem dirichlet_norm_sum_Ico_le {F : Type*} [NormedField F] {q : ℕ} [NeZero q]
    (χ : DirichletCharacter F q) (hχ : χ ≠ 1) (a b : ℕ) :
    ‖∑ k ∈ Finset.Ico a b, χ k‖ ≤ 2 * q := by
  by_cases hab : a ≤ b
  · rw [eq_sub_of_add_eq' (Finset.sum_range_add_sum_Ico (fun k => χ k) hab)]
    exact (norm_sub_le _ _).trans (by
      have ha := dirichlet_norm_sum_range_le χ hχ a
      have hb := dirichlet_norm_sum_range_le χ hχ b
      linarith)
  · simp only [Finset.Ico_eq_empty_of_le (Nat.le_of_not_ge hab), Finset.sum_empty, norm_zero]
    positivity

end Erdos1148.DukeArithmetic
