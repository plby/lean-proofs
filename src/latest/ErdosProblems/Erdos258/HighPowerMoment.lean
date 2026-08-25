import ErdosProblems.Erdos258.PrimePowers
import ErdosProblems.Erdos258.SievePrimePowers
import ErdosProblems.Erdos248.PrimeSumBounds
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# A uniform second moment using only single-prime-power estimates

Charge the first five copies of each prime to `ω`.  For the remaining copies,
Cauchy--Schwarz with weights `1/(p*j)` bounds the square of their count by
four times the sum of `(p*j)^2` over the corresponding divisibility events.
The single-prime-power estimate makes this summable in both `p` and `j`.
-/

open Erdos248
open scoped BigOperators

namespace Erdos258

noncomputable def highPowerGeometricConstant : ℝ :=
  ∑' j : ℕ, (j : ℝ) ^ 2 * (1 / 2 : ℝ) ^ j

theorem highPowerGeometricConstant_nonneg : 0 ≤ highPowerGeometricConstant := by
  apply tsum_nonneg
  intro j
  positivity

theorem sum_geometric_second_moment_le (S : Finset ℕ) :
    (∑ j ∈ S, (j : ℝ) ^ 2 * (1 / 2 : ℝ) ^ j) ≤ highPowerGeometricConstant := by
  exact (summable_pow_mul_geometric_of_norm_lt_one 2
    (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).sum_le_tsum S (fun j hj => by positivity)

theorem sum_Icc_inv_sq_le_two (a R : ℕ) (ha : 1 ≤ a) :
    (∑ j ∈ Finset.Icc a R, (1 : ℝ) / (j : ℝ) ^ 2) ≤ 2 := by
  calc
    (∑ j ∈ Finset.Icc a R, (1 : ℝ) / (j : ℝ) ^ 2) ≤
        ∑ j ∈ Finset.Icc 1 R, (1 : ℝ) / (j : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc ha le_rfl)
        (fun j hj hja => by positivity)
    _ ≤ 2 := sum_Icc_one_div_sq_le_two R

theorem highPowerRect_inv_sq_le_four (R : ℕ) :
    (∑ pj ∈ (Finset.Icc 2 R) ×ˢ (Finset.Icc 6 R),
      ((1 : ℝ) / ((pj.1 : ℝ) * pj.2)) ^ 2) ≤ 4 := by
  have hid (p j : ℕ) : ((1 : ℝ) / ((p : ℝ) * j)) ^ 2 =
      (1 / (p : ℝ) ^ 2) * (1 / (j : ℝ) ^ 2) := by
    simp [one_div, mul_pow, mul_inv_rev, mul_comm]
  simp_rw [Finset.sum_product, hid, ← Finset.mul_sum]
  rw [← Finset.sum_mul]
  have hp := sum_Icc_inv_sq_le_two 2 R (by omega)
  have hj := sum_Icc_inv_sq_le_two 6 R (by omega)
  have hp0 : 0 ≤ ∑ p ∈ Finset.Icc 2 R, (1 : ℝ) / (p : ℝ) ^ 2 := by positivity
  have hj0 : 0 ≤ ∑ j ∈ Finset.Icc 6 R, (1 : ℝ) / (j : ℝ) ^ 2 := by positivity
  nlinarith

theorem highPrimePowerCount_sq_le (m R : ℕ) :
    (highPrimePowerCount m R : ℝ) ^ 2 ≤
      4 * ∑ p ∈ Finset.Icc 2 R, ∑ j ∈ Finset.Icc 6 R,
        if p.Prime ∧ p ^ j ≤ R ∧ p ^ j ∣ m then ((p : ℝ) * j) ^ 2 else 0 := by
  let S := (Finset.Icc 2 R) ×ˢ (Finset.Icc 6 R)
  let f : ℕ × ℕ → ℝ := fun pj => 1 / ((pj.1 : ℝ) * pj.2)
  let g : ℕ × ℕ → ℝ := fun pj =>
    if pj.1.Prime ∧ pj.1 ^ pj.2 ≤ R ∧ pj.1 ^ pj.2 ∣ m
    then (pj.1 : ℝ) * pj.2 else 0
  have hsum : (highPrimePowerCount m R : ℝ) = ∑ pj ∈ S, f pj * g pj := by
    simp only [highPrimePowerCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [show (∑ pj ∈ S, f pj * g pj) =
        ∑ p ∈ Finset.Icc 2 R, ∑ j ∈ Finset.Icc 6 R, f (p, j) * g (p, j) from
      Finset.sum_product _ _ _]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro j hj
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by
      have := (Finset.mem_Icc.mp hp).1; omega)
    have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by
      have := (Finset.mem_Icc.mp hj).1; omega)
    dsimp [f, g]
    split_ifs
    · field_simp
    · simp
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S f g
  rw [← hsum] at hcs
  have hf : (∑ pj ∈ S, f pj ^ 2) ≤ 4 := highPowerRect_inv_sq_le_four R
  have hg0 : 0 ≤ ∑ pj ∈ S, g pj ^ 2 := Finset.sum_nonneg fun pj hpj => sq_nonneg _
  calc
    (highPrimePowerCount m R : ℝ) ^ 2 ≤ (∑ pj ∈ S, f pj ^ 2) * ∑ pj ∈ S, g pj ^ 2 := hcs
    _ ≤ 4 * ∑ pj ∈ S, g pj ^ 2 := mul_le_mul_of_nonneg_right hf hg0
    _ = _ := by
      congr 1
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [g]
      split_ifs <;> simp

theorem highPower_weight_div_le {p j : ℕ} (hp : 2 ≤ p) (hj : 6 ≤ j) :
    ((p : ℝ) * j) ^ 2 / (p : ℝ) ^ (j - 1) ≤
      32 * (1 / (p : ℝ) ^ 2) * ((j : ℝ) ^ 2 * (1 / 2 : ℝ) ^ j) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hsplit : (p : ℝ) ^ (j - 1) = (p : ℝ) ^ 4 * (p : ℝ) ^ (j - 5) := by
    rw [← pow_add]
    congr 1
    omega
  have htwo : (2 : ℝ) ^ j = 32 * (2 : ℝ) ^ (j - 5) := by
    rw [show j = 5 + (j - 5) by omega, pow_add]
    norm_num
  have hpow : (2 : ℝ) ^ (j - 5) ≤ (p : ℝ) ^ (j - 5) :=
    pow_le_pow_left₀ (by norm_num) hpR _
  calc
    ((p : ℝ) * j) ^ 2 / (p : ℝ) ^ (j - 1) =
        (j : ℝ) ^ 2 / ((p : ℝ) ^ 2 * (p : ℝ) ^ (j - 5)) := by
      rw [hsplit]
      field_simp
    _ ≤ (j : ℝ) ^ 2 / ((p : ℝ) ^ 2 * (2 : ℝ) ^ (j - 5)) := by
      apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
    _ = 32 * (1 / (p : ℝ) ^ 2) * ((j : ℝ) ^ 2 * (1 / 2 : ℝ) ^ j) := by
      rw [div_pow, one_pow, htwo]
      field_simp

theorem highPowerRect_weight_div_le (R : ℕ) :
    (∑ p ∈ Finset.Icc 2 R, ∑ j ∈ Finset.Icc 6 R,
      ((p : ℝ) * j) ^ 2 / (p : ℝ) ^ (j - 1)) ≤ 64 * highPowerGeometricConstant := by
  calc
    (∑ p ∈ Finset.Icc 2 R, ∑ j ∈ Finset.Icc 6 R,
        ((p : ℝ) * j) ^ 2 / (p : ℝ) ^ (j - 1)) ≤
        ∑ p ∈ Finset.Icc 2 R, ∑ j ∈ Finset.Icc 6 R,
          32 * (1 / (p : ℝ) ^ 2) * ((j : ℝ) ^ 2 * (1 / 2 : ℝ) ^ j) := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro j hj
      exact highPower_weight_div_le (Finset.mem_Icc.mp hp).1 (Finset.mem_Icc.mp hj).1
    _ ≤ ∑ p ∈ Finset.Icc 2 R,
        32 * (1 / (p : ℝ) ^ 2) * highPowerGeometricConstant := by
      apply Finset.sum_le_sum
      intro p hp
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_geometric_second_moment_le _) (by positivity)
    _ = 32 * (∑ p ∈ Finset.Icc 2 R, (1 : ℝ) / (p : ℝ) ^ 2) * highPowerGeometricConstant := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ 64 * highPowerGeometricConstant := by
      have h := sum_Icc_inv_sq_le_two 2 R (by omega)
      nlinarith [highPowerGeometricConstant_nonneg]

theorem highPowerRect_weight_le (R : ℕ) :
    (∑ p ∈ Finset.Icc 2 R, ∑ j ∈ Finset.Icc 6 R, ((p : ℝ) * j) ^ 2) ≤ (R : ℝ) ^ 6 := by
  have hp : ((Finset.Icc 2 R).card : ℝ) ≤ R := by
    exact_mod_cast (show (Finset.Icc 2 R).card ≤ R by simp)
  have hj : ((Finset.Icc 6 R).card : ℝ) ≤ R := by
    exact_mod_cast (show (Finset.Icc 6 R).card ≤ R by simp)
  calc
    (∑ p ∈ Finset.Icc 2 R, ∑ j ∈ Finset.Icc 6 R, ((p : ℝ) * j) ^ 2) ≤
        ∑ _p ∈ Finset.Icc 2 R, ∑ _j ∈ Finset.Icc 6 R, ((R : ℝ) * R) ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro j hj
      gcongr
      · exact_mod_cast (Finset.mem_Icc.mp hp).2
      · exact_mod_cast (Finset.mem_Icc.mp hj).2
    _ = ((Finset.Icc 2 R).card : ℝ) * (Finset.Icc 6 R).card * ((R : ℝ) * R) ^ 2 := by
      simp [mul_assoc]
    _ ≤ (R : ℝ) * R * ((R : ℝ) * R) ^ 2 := by gcongr
    _ = (R : ℝ) ^ 6 := by ring

theorem weighted_highPower_sum_swap (N R k : ℕ) (w : ℕ → ℝ) :
    (∑ n ∈ Finset.Ico N (2 * N), w n *
      ∑ p ∈ Finset.Icc 2 R, ∑ j ∈ Finset.Icc 6 R,
        if p.Prime ∧ p ^ j ≤ R ∧ p ^ j ∣ n + k then ((p : ℝ) * j) ^ 2 else 0) =
      ∑ p ∈ Finset.Icc 2 R, ∑ j ∈ Finset.Icc 6 R,
        if p.Prime ∧ p ^ j ≤ R then
          ((p : ℝ) * j) ^ 2 * divisorEventMass N k (p ^ j) w else 0 := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hpc : p.Prime ∧ p ^ j ≤ R
  · simp only [hpc.1, hpc.2, true_and, if_true]
    unfold divisorEventMass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    split_ifs <;> ring
  · have hfalse (n : ℕ) : ¬(p.Prime ∧ p ^ j ≤ R ∧ p ^ j ∣ n + k) := by
      intro h
      exact hpc ⟨h.1, h.2.1⟩
    simp [hpc, hfalse]

/-- The only distributional hypothesis is a bound for one prime power at a
time.  Cauchy--Schwarz supplies the second moment without pair correlations. -/
theorem highPower_second_moment_le (N R k : ℕ) {w : ℕ → ℝ} {M E : ℝ}
    (hw : ∀ n, 0 ≤ w n) (hM : 0 ≤ M) (hE : 0 ≤ E)
    (hevent : ∀ p j, p.Prime → 6 ≤ j → p ^ j ≤ R →
      divisorEventMass N k (p ^ j) w ≤ M / p ^ (j - 1) + E) :
    (∑ n ∈ Finset.Ico N (2 * N), w n * (highPrimePowerCount (n + k) R : ℝ) ^ 2) ≤
      4 * (64 * highPowerGeometricConstant * M + (R : ℝ) ^ 6 * E) := by
  have hsum :
      (∑ n ∈ Finset.Ico N (2 * N), w n * (highPrimePowerCount (n + k) R : ℝ) ^ 2) ≤
        4 * ∑ p ∈ Finset.Icc 2 R, ∑ j ∈ Finset.Icc 6 R,
          if p.Prime ∧ p ^ j ≤ R then
            ((p : ℝ) * j) ^ 2 * divisorEventMass N k (p ^ j) w else 0 := by
    rw [← weighted_highPower_sum_swap N R k w, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have h := mul_le_mul_of_nonneg_left (highPrimePowerCount_sq_le (n + k) R) (hw n)
    simpa [mul_left_comm, mul_assoc] using h
  apply hsum.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    (∑ p ∈ Finset.Icc 2 R, ∑ j ∈ Finset.Icc 6 R,
        if p.Prime ∧ p ^ j ≤ R then
          ((p : ℝ) * j) ^ 2 * divisorEventMass N k (p ^ j) w else 0) ≤
        ∑ p ∈ Finset.Icc 2 R, ∑ j ∈ Finset.Icc 6 R,
          (((p : ℝ) * j) ^ 2 / p ^ (j - 1) * M + ((p : ℝ) * j) ^ 2 * E) := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro j hj
      by_cases hpc : p.Prime ∧ p ^ j ≤ R
      · rw [if_pos hpc]
        have h := mul_le_mul_of_nonneg_left
          (hevent p j hpc.1 (Finset.mem_Icc.mp hj).1 hpc.2)
          (sq_nonneg ((p : ℝ) * j))
        convert h using 1
        ring
      · rw [if_neg hpc]
        positivity
    _ = (∑ p ∈ Finset.Icc 2 R, ∑ j ∈ Finset.Icc 6 R,
          ((p : ℝ) * j) ^ 2 / p ^ (j - 1)) * M +
        (∑ p ∈ Finset.Icc 2 R, ∑ j ∈ Finset.Icc 6 R, ((p : ℝ) * j) ^ 2) * E := by
      simp only [Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ 64 * highPowerGeometricConstant * M + (R : ℝ) ^ 6 * E :=
      add_le_add (mul_le_mul_of_nonneg_right (highPowerRect_weight_div_le R) hM)
        (mul_le_mul_of_nonneg_right (highPowerRect_weight_le R) hE)

end Erdos258
