import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! # A fixed entropy saving when at least half the blocks are inexpensive -/

namespace Erdos1148.DukeArithmetic

theorem avoidance_block_coefficient_bound {a C : ℝ} (ha : 0 ≤ a) (haone : a ≤ 1)
    (hC : 1 ≤ C) (haC : a * C ≤ 1 / 4) {k b : ℕ} (hhalf : 2 * b ≤ k) :
    (a ^ 2) ^ (k - b) * C ^ b ≤ (1 / 4 : ℝ) ^ k := by
  have hbk : b ≤ k := by omega
  have hexp : k ≤ 2 * (k - b) := by omega
  have haPow : (a ^ 2) ^ (k - b) ≤ a ^ k := by
    rw [← pow_mul]
    exact pow_le_pow_of_le_one ha haone hexp
  have hCPow : C ^ b ≤ C ^ k := pow_le_pow_right₀ hC hbk
  calc
    (a ^ 2) ^ (k - b) * C ^ b ≤ a ^ k * C ^ k :=
      mul_le_mul haPow hCPow (pow_nonneg (zero_le_one.trans hC) _) (pow_nonneg ha _)
    _ = (a * C) ^ k := (mul_pow a C k).symm
    _ ≤ (1 / 4 : ℝ) ^ k := pow_le_pow_left₀ (mul_nonneg ha (zero_le_one.trans hC)) haC k

theorem avoidance_block_cost_bound {a C e : ℝ} (ha : 0 ≤ a) (haone : a ≤ 1)
    (hC : 1 ≤ C) (haC : a * C ≤ 1 / 4) (he : 0 ≤ e) {k b : ℕ} (hhalf : 2 * b ≤ k) :
    (C * e) ^ b * ((a ^ 2) * e) ^ (k - b) ≤ (e / 4) ^ k := by
  have hbk : b ≤ k := by omega
  have hsum : b + (k - b) = k := Nat.add_sub_of_le hbk
  have hePow : e ^ b * e ^ (k - b) = e ^ k := by rw [← pow_add, hsum]
  calc
    (C * e) ^ b * ((a ^ 2) * e) ^ (k - b) =
        ((a ^ 2) ^ (k - b) * C ^ b) * (e ^ b * e ^ (k - b)) := by rw [mul_pow, mul_pow]; ring
    _ = ((a ^ 2) ^ (k - b) * C ^ b) * e ^ k := by rw [hePow]
    _ ≤ (1 / 4 : ℝ) ^ k * e ^ k := mul_le_mul_of_nonneg_right
      (avoidance_block_coefficient_bound ha haone hC haC hhalf) (pow_nonneg he _)
    _ = (e / 4) ^ k := by rw [← mul_pow]; congr 1; ring

theorem avoidance_pattern_factor (k : ℕ) (e : ℝ) :
    (2 : ℝ) ^ k * (e / 4) ^ k = (e / 2) ^ k := by
  rw [← mul_pow]
  congr 1
  ring

theorem avoidance_block_product_bound {ι : Type*} (s : Finset ι) (bad : ι → Prop)
    [DecidablePred bad] {a C e : ℝ} (ha : 0 ≤ a) (haone : a ≤ 1) (hC : 1 ≤ C)
    (haC : a * C ≤ 1 / 4) (he : 0 ≤ e) (hhalf : 2 * (s.filter bad).card ≤ s.card) :
    (∏ i ∈ s, if bad i then C * e else (a ^ 2) * e) ≤ (e / 4) ^ s.card := by
  classical
  have hcard : (s.filter (fun i => ¬bad i)).card = s.card - (s.filter bad).card := by
    have h := s.card_filter_add_card_filter_not bad
    omega
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, hcard]
  exact avoidance_block_cost_bound ha haone hC haC he hhalf

theorem exists_avoidance_block_cost_parameter {C : ℝ} (hC : 1 ≤ C) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ a * C ≤ 1 / 4 := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  refine ⟨1 / (4 * C), by positivity, ?_, ?_⟩
  · apply (div_le_one (by positivity)).mpr
    linarith only [hC]
  · have heq : 1 / (4 * C) * C = (1 / 4 : ℝ) := by field_simp [hCpos.ne']
    exact heq.le

end Erdos1148.DukeArithmetic
