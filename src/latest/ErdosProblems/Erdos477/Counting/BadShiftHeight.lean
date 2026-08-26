/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Every positive bad shift has a selected sextic witness of height O_c(U^(6/5)).
Formal author: Codex.
-/

import ErdosProblems.Erdos477.BadShifts
import ErdosProblems.Erdos477.IntegerDiagonal

namespace Erdos477.Counting

noncomputable def badShiftHeight (c : ℤ) (N : ℕ) : ℝ :=
  (1 + (c.natAbs : ℝ)) * (N : ℝ) ^ ((6 : ℝ) / 5)

lemma badShiftHeight_ge_one (c : ℤ) (N : ℕ) (hN : 1 ≤ N) : 1 ≤ badShiftHeight c N := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpower : 1 ≤ (N : ℝ) ^ ((6 : ℝ) / 5) := Real.one_le_rpow hNr (by norm_num)
  unfold badShiftHeight
  nlinarith [show (0 : ℝ) ≤ c.natAbs from Nat.cast_nonneg _]

lemma sixth_root_height_bound (c : ℤ) (N m : ℕ) (hN : 1 ≤ N)
    (hm : (m : ℝ) ^ 5 ≤ (N : ℝ) ^ 6 + c.natAbs) :
    (m : ℝ) ≤ badShiftHeight c N := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hC : (1 : ℝ) ≤ 1 + (c.natAbs : ℝ) := by
    have h := (Nat.cast_nonneg c.natAbs : (0 : ℝ) ≤ c.natAbs)
    linarith
  have hC5 : 1 + (c.natAbs : ℝ) ≤ (1 + (c.natAbs : ℝ)) ^ 5 :=
    le_self_pow₀ hC (by decide)
  have hN6 : (1 : ℝ) ≤ (N : ℝ) ^ 6 := one_le_pow₀ hNr
  have hscale : (N : ℝ) ^ 6 + c.natAbs ≤
      (1 + (c.natAbs : ℝ)) ^ 5 * (N : ℝ) ^ 6 := by
    have h := mul_le_mul_of_nonneg_right hC5 (pow_nonneg (Nat.cast_nonneg N) 6)
    have hc := mul_le_mul_of_nonneg_left hN6 (Nat.cast_nonneg c.natAbs : (0 : ℝ) ≤ c.natAbs)
    nlinarith
  have hp : ((N : ℝ) ^ ((6 : ℝ) / 5)) ^ 5 = (N : ℝ) ^ 6 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
    norm_num
  apply le_of_pow_le_pow_left₀ (by decide : 5 ≠ 0)
    ((by norm_num : (0 : ℝ) ≤ 1).trans (badShiftHeight_ge_one c N hN))
  simpa only [badShiftHeight, mul_pow, hp] using hm.trans hscale

theorem badShift_bounded_point (c : ℤ) (hc : c ∉ PowerValues 6)
    (N t : ℕ) (ht : 1 ≤ t) (htN : t ≤ N) (hbad : IsBadShift c t) :
    ∃ z : Fin 3 → ℤ, IntegerDiagonalPoint c z ∧ z 0 = (t : ℤ) ∧
      ∀ i, |(z i : ℝ)| ≤ badShiftHeight c N := by
  obtain ⟨u, v, heq, hbound⟩ := badShift_witness_bound hc hbad
  have hN : 1 ≤ N := ht.trans htN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hmax : ((max u v : ℕ) : ℝ) ^ 5 ≤ (N : ℝ) ^ 6 + c.natAbs := by
    have hbound' : ((max u v : ℕ) : ℝ) ^ 5 ≤ (t : ℝ) ^ 6 + c.natAbs := by
      exact_mod_cast (by simpa only [Int.natCast_natAbs] using hbound :
        ((max u v : ℕ) : ℤ) ^ 5 ≤ (t : ℤ) ^ 6 + (c.natAbs : ℤ))
    have hp : (t : ℝ) ^ 6 ≤ (N : ℝ) ^ 6 :=
      pow_le_pow_left₀ (Nat.cast_nonneg t) (by exact_mod_cast htN) 6
    exact hbound'.trans (add_le_add hp le_rfl)
  have hm := sixth_root_height_bound c N (max u v) hN hmax
  have hNheight : (N : ℝ) ≤ badShiftHeight c N := by
    have hp : (N : ℝ) ≤ (N : ℝ) ^ ((6 : ℝ) / 5) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hNr (by norm_num : (1 : ℝ) ≤ 6 / 5)
    unfold badShiftHeight
    have hn := Real.rpow_nonneg (Nat.cast_nonneg N) ((6 : ℝ) / 5)
    nlinarith [show (0 : ℝ) ≤ c.natAbs from Nat.cast_nonneg _]
  refine ⟨![(t : ℤ), (v : ℤ), (u : ℤ)], ?_, rfl, ?_⟩
  · change 1 ≤ (t : ℤ) ∧ 0 ≤ (v : ℤ) ∧ 0 ≤ (u : ℤ) ∧
      (t : ℤ) ^ 6 + (v : ℤ) ^ 6 - (u : ℤ) ^ 6 = c
    exact ⟨by exact_mod_cast ht, Nat.cast_nonneg _, Nat.cast_nonneg _, by omega⟩
  · intro i
    fin_cases i
    · change |((t : ℤ) : ℝ)| ≤ _
      simp only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
      exact (by exact_mod_cast htN : (t : ℝ) ≤ N).trans hNheight
    · change |((v : ℤ) : ℝ)| ≤ _
      simp only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg v : (0 : ℝ) ≤ v)]
      exact (by exact_mod_cast le_max_right u v : (v : ℝ) ≤ max u v).trans hm
    · change |((u : ℤ) : ℝ)| ≤ _
      simp only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg u : (0 : ℝ) ≤ u)]
      exact (by exact_mod_cast le_max_left u v : (u : ℝ) ≤ max u v).trans hm

#print axioms badShift_bounded_point
-- 'Erdos477.Counting.badShift_bounded_point' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
