/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The sharp leading lower bound for the entropy of the counting frames.
Informal source: BBMST equation (19), with the lower limit obtained by finite truncation.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.EntropyTruncationLower

namespace Erdos1189

open Filter

noncomputable def entropyScale (x : ℝ) : ℝ := x ^ 3 / Real.log x ^ 2

lemma entropyScale_pos {x : ℝ} (hx : 1 < x) : 0 < entropyScale x :=
  div_pos (pow_pos (zero_lt_one.trans hx) _) (sq_pos_of_pos (Real.log_pos hx))

lemma countingWeight_asymptotic :
    Tendsto (fun x : ℝ => (simpsonWeight (countingInteger x) : ℝ) / realLogPower 2 x)
      atTop (nhds (tau / 2)) := by
  have ht := countingSize_asymptotic.sub tendsto_inv_realLogPower_two
  simp only [sub_zero] at ht
  apply ht.congr'
  exact Eventually.of_forall fun x => by
    dsimp only [countingSize]
    rw [Nat.cast_add, Nat.cast_one]
    ring

lemma countingWeight_over_entropyScale :
    Tendsto (fun x : ℝ => (simpsonWeight (countingInteger x) : ℝ) / entropyScale x)
      atTop (nhds 0) := by
  have ht := countingWeight_asymptotic.mul
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : x ≠ 0 := (zero_lt_one.trans hx).ne'
  have hl0 : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  dsimp [realLogPower, entropyScale]
  field_simp

lemma truncated_entropy_bound_limit (T : ℕ) (a D : ℝ) :
    Tendsto (fun x : ℝ =>
      (a / Real.log x * truncatedScoreMoment T x -
        D * (simpsonWeight (countingInteger x) : ℝ)) / entropyScale x)
      atTop (nhds (a * partialTau T / 3)) := by
  have ht := ((truncatedScoreMoment_asymptotic T).const_mul a).sub
    (countingWeight_over_entropyScale.const_mul D)
  have ht' : Tendsto (fun x : ℝ => a * (truncatedScoreMoment T x / realLogPower 3 x) -
      D * ((simpsonWeight (countingInteger x) : ℝ) / entropyScale x))
      atTop (nhds (a * partialTau T / 3)) := by
    simpa only [mul_zero, sub_zero, mul_div_assoc] using ht
  apply ht'.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : x ≠ 0 := (zero_lt_one.trans hx).ne'
  have hl0 : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  dsimp [realLogPower, entropyScale]
  field_simp

lemma exists_entropy_truncation_constant {b : ℝ} (hb : b < tau ^ 2 / 3) :
    ∃ T : ℕ, ∃ a : ℝ, 0 ≤ a ∧ a < partialTau T ∧ b < a * partialTau T / 3 := by
  have ha : Tendsto (fun T : ℕ => partialTau T - 1 / ((T : ℝ) + 1))
      atTop (nhds tau) := by
    simpa only [sub_zero] using partialTau_tendsto.sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hprod := (ha.mul partialTau_tendsto).div_const 3
  simp only [← pow_two] at hprod
  obtain ⟨T, hT0, hTb⟩ := ((tendsto_order.mp ha).1 0 tau_pos).and
    ((tendsto_order.mp hprod).1 b hb) |>.exists
  refine ⟨T, partialTau T - 1 / ((T : ℝ) + 1), hT0.le, ?_, hTb⟩
  have : (0 : ℝ) < 1 / ((T : ℝ) + 1) := by positivity
  linarith

/-- Every smaller constant is eventually a lower bound for the normalized frame entropy. -/
theorem countingEntropy_eventually_lower {b : ℝ} (hb : b < tau ^ 2 / 3) :
    ∀ᶠ x : ℝ in atTop, b < countingEntropy x / entropyScale x := by
  obtain ⟨T, a, ha, haT, hbT⟩ := exists_entropy_truncation_constant hb
  obtain ⟨D, hD⟩ := eventually_entropy_truncation_lower T T ha haT
  filter_upwards [hD, (tendsto_order.mp (truncated_entropy_bound_limit T a D)).1 b hbT,
    eventually_gt_atTop (1 : ℝ)] with x hx hbx hx1
  exact hbx.trans_le (div_le_div_of_nonneg_right hx (entropyScale_pos hx1).le)

end Erdos1189
