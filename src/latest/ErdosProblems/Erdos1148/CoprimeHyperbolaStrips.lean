import ErdosProblems.Erdos1148.PrincipalCharacterMean
import ErdosProblems.Erdos1148.CoprimeZetaConvolution
import Mathlib.Algebra.Order.Floor.Semifield

/-! # Unweighted hyperbola-strip estimates for a principal and a real character -/

namespace Erdos1148.DukeArithmetic

open Finset

lemma character_sum_Ioc_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℝ q)
    (hχ : χ ≠ 1) (n : ℕ) : ‖∑ k ∈ Ioc 0 n, χ k‖ ≤ 2 * q := by
  rw [← Ico_add_one_add_one_eq_Ioc]
  exact dirichlet_norm_sum_Ico_le χ hχ _ _

lemma character_sum_Ioc_norm_le_length {q : ℕ} (χ : DirichletCharacter ℝ q) (n : ℕ) :
    ‖∑ k ∈ Ioc 0 n, χ k‖ ≤ n := by
  calc
    _ ≤ ∑ k ∈ Ioc 0 n, ‖χ k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Ioc 0 n, (1 : ℝ) := sum_le_sum (fun k _ => χ.norm_le_one k)
    _ = _ := by simp

lemma principal_character_div_error_le {q : ℕ} [NeZero q] (X m : ℕ) :
    ‖(∑ k ∈ Ioc 0 (X / m), (1 : DirichletCharacter ℝ q) k) -
      principalCharacterMean q * ((X : ℝ) / m)‖ ≤ 5 * q := by
  have hfloor : ‖(X / m : ℕ) - (X : ℝ) / m‖ ≤ 1 := by
    rw [Real.norm_eq_abs, ← Nat.floor_div_eq_div (K := ℝ)]
    exact Nat.abs_floor_sub_le (by positivity)
  have hmean := principalCharacterMean_nonneg q
  have hmean1 := principalCharacterMean_le_one (q := q)
  have herr := principal_character_sum_Ioc_error_le (q := q) (X / m)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  calc
    _ = ‖((∑ k ∈ Ioc 0 (X / m), (1 : DirichletCharacter ℝ q) k) -
        principalCharacterMean q * (X / m : ℕ)) +
        principalCharacterMean q * ((X / m : ℕ) - (X : ℝ) / m)‖ := by congr 1; ring
    _ ≤ ‖(∑ k ∈ Ioc 0 (X / m), (1 : DirichletCharacter ℝ q) k) -
        principalCharacterMean q * (X / m : ℕ)‖ +
        ‖principalCharacterMean q * ((X / m : ℕ) - (X : ℝ) / m)‖ := norm_add_le _ _
    _ ≤ 4 * q + 1 := by
      apply add_le_add herr
      rw [norm_mul, Real.norm_of_nonneg hmean]
      exact (mul_le_mul_of_nonneg_left hfloor hmean).trans (by simpa using hmean1)
    _ ≤ _ := by linarith

theorem coprime_hyperbola_main_strip_error_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (X N : ℕ) :
    ‖(∑ m ∈ Ioc 0 N, χ m * ∑ n ∈ Ioc 0 (X / m), (1 : DirichletCharacter ℝ q) n) -
      principalCharacterMean q * X * realDirichletPartialSum χ 1 N‖ ≤ 5 * q * N := by
  have heq : (∑ m ∈ Ioc 0 N, χ m * ∑ n ∈ Ioc 0 (X / m), (1 : DirichletCharacter ℝ q) n) -
      principalCharacterMean q * X * realDirichletPartialSum χ 1 N =
      ∑ m ∈ Ioc 0 N, χ m * ((∑ n ∈ Ioc 0 (X / m), (1 : DirichletCharacter ℝ q) n) -
        principalCharacterMean q * ((X : ℝ) / m)) := by
    rw [realDirichletPartialSum_eq_sum_Ioc, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro m hm
    rw [Real.rpow_neg_one]
    ring
  rw [heq]
  calc
    _ ≤ ∑ m ∈ Ioc 0 N, ‖χ m * ((∑ n ∈ Ioc 0 (X / m), (1 : DirichletCharacter ℝ q) n) -
        principalCharacterMean q * ((X : ℝ) / m))‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ Ioc 0 N, (5 * q : ℝ) := by
      apply sum_le_sum
      intro m hm
      rw [norm_mul]
      exact (mul_le_mul (χ.norm_le_one m) (principal_character_div_error_le X m)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ = _ := by simp [mul_comm]

theorem coprime_hyperbola_second_strip_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) (X N : ℕ) :
    ‖∑ n ∈ Ioc 0 N, (1 : DirichletCharacter ℝ q) n * ∑ m ∈ Ioc 0 (X / n), χ m‖ ≤
      2 * q * N := by
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, ‖(1 : DirichletCharacter ℝ q) n * ∑ m ∈ Ioc 0 (X / n), χ m‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _n ∈ Ioc 0 N, (2 * q : ℝ) := by
      apply sum_le_sum
      intro n hn
      rw [norm_mul]
      exact (mul_le_mul ((1 : DirichletCharacter ℝ q).norm_le_one n)
        (character_sum_Ioc_norm_le χ hχ (X / n)) (norm_nonneg _) zero_le_one).trans_eq
          (one_mul _)
    _ = _ := by simp [mul_comm]

end Erdos1148.DukeArithmetic
