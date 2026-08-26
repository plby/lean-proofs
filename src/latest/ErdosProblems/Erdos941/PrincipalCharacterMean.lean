/- Adapted from the checked repository proof in Erdos1148/PrincipalCharacterMean.lean. -/
import ErdosProblems.Erdos941.DirichletPartialSums
import Mathlib.Tactic.Positivity

/-! # The principal character has mean phi(q)/q with bounded error -/

namespace Erdos941.Analytic

open Finset

lemma periodic_sum_range_eq_remainder {A : Type*} [AddCommMonoid A] {q : ℕ}
    (f : ℕ → A) (hf : Function.Periodic f q) (hzero : ∑ k ∈ range q, f k = 0) (n : ℕ) :
    ∑ k ∈ range n, f k = ∑ k ∈ range (n % q), f k := by
  have hperiod : Function.Periodic (fun m => ∑ k ∈ range m, f k) q := by
    intro m
    change (∑ k ∈ range (m + q), f k) = ∑ k ∈ range m, f k
    rw [Nat.add_comm m q, sum_range_add, hzero, zero_add]
    exact sum_congr rfl (fun k _ => by simpa only [Nat.add_comm q] using hf k)
  have h := hperiod.nat_mul (n / q) (n % q)
  change (∑ k ∈ range (n % q + n / q * q), f k) = ∑ k ∈ range (n % q), f k at h
  rwa [show n % q + n / q * q = n by simpa only [Nat.mul_comm] using Nat.mod_add_div n q] at h

noncomputable def principalCharacterMean (q : ℕ) : ℝ := (q.totient : ℝ) / q

lemma principalCharacterMean_nonneg (q : ℕ) : 0 ≤ principalCharacterMean q := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma principalCharacterMean_le_one {q : ℕ} [NeZero q] : principalCharacterMean q ≤ 1 := by
  apply (div_le_one (by exact_mod_cast NeZero.pos q : (0 : ℝ) < q)).mpr
  exact_mod_cast Nat.totient_le q

lemma principalCharacterMean_pos {q : ℕ} [NeZero q] : 0 < principalCharacterMean q := by
  exact div_pos (by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q))
    (by exact_mod_cast NeZero.pos q)

lemma principal_character_sum_range_period {q : ℕ} [NeZero q] :
    ∑ k ∈ range q, (1 : DirichletCharacter ℝ q) k = (q.totient : ℝ) := by
  classical
  rw [sum_range_zmod_eq_sum_univ, MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]

lemma principal_character_sum_range_error_le {q : ℕ} [NeZero q] (n : ℕ) :
    ‖(∑ k ∈ range n, (1 : DirichletCharacter ℝ q) k) - principalCharacterMean q * n‖ ≤
      2 * q := by
  let f : ℕ → ℝ := fun k => (1 : DirichletCharacter ℝ q) k - principalCharacterMean q
  have hf : Function.Periodic f q := by
    intro k
    simp only [f, Nat.cast_add, CharP.cast_eq_zero, add_zero]
  have hsum : ∑ k ∈ range q, f k = 0 := by
    simp only [f, sum_sub_distrib, principal_character_sum_range_period, sum_const,
      card_range, nsmul_eq_mul, principalCharacterMean]
    have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
    field_simp
    ring
  have hnorm (k : ℕ) : ‖f k‖ ≤ 2 := by
    apply (norm_sub_le _ _).trans
    have hχ := (1 : DirichletCharacter ℝ q).norm_le_one k
    rw [Real.norm_of_nonneg (principalCharacterMean_nonneg q)]
    linarith [principalCharacterMean_le_one (q := q)]
  have heq : (∑ k ∈ range n, (1 : DirichletCharacter ℝ q) k) - principalCharacterMean q * n =
      ∑ k ∈ range n, f k := by simp [f, sum_sub_distrib, mul_comm]
  rw [heq, periodic_sum_range_eq_remainder f hf hsum n]
  calc
    _ ≤ ∑ k ∈ range (n % q), ‖f k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ range (n % q), (2 : ℝ) := sum_le_sum (fun k _ => hnorm k)
    _ = 2 * (n % q : ℕ) := by simp [mul_comm]
    _ ≤ 2 * (q : ℝ) := mul_le_mul_of_nonneg_left
      (by exact_mod_cast (Nat.mod_lt n (NeZero.pos q)).le) (by norm_num)

theorem principal_character_sum_Ioc_error_le {q : ℕ} [NeZero q] (n : ℕ) :
    ‖(∑ k ∈ Ioc 0 n, (1 : DirichletCharacter ℝ q) k) - principalCharacterMean q * n‖ ≤
      4 * q := by
  have heq : (∑ k ∈ Ioc 0 n, (1 : DirichletCharacter ℝ q) k) - principalCharacterMean q * n =
      ((∑ k ∈ range (n + 1), (1 : DirichletCharacter ℝ q) k) -
        principalCharacterMean q * (n + 1)) -
      ((∑ k ∈ range 1, (1 : DirichletCharacter ℝ q) k) - principalCharacterMean q) := by
    rw [← Ico_add_one_add_one_eq_Ioc, Nat.zero_add, eq_sub_of_add_eq'
      (sum_range_add_sum_Ico (fun k => (1 : DirichletCharacter ℝ q) k) (by omega : 1 ≤ n + 1))]
    ring
  rw [heq]
  apply (norm_sub_le _ _).trans
  have h1 := principal_character_sum_range_error_le (q := q) (n + 1)
  have h2 := principal_character_sum_range_error_le (q := q) 1
  push_cast at h1 h2
  simp only [mul_one] at h2
  linarith

end Erdos941.Analytic
