/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerSourceBudgetInequalities

/-!
# Sharp fixed-height budget for the coprime completion

The exact p.52 nodal count has asymptotic logarithmic size
`(192 / 36) * log 3` source-height units.  Retaining the rank factor in the
admissible-scale lower bound pays the `/36` floor loss and leaves strictly
more than `11/2` units.  Two units pay the boundary growth and half a unit
pays the `4/3` Cauchy radius/gap factor, leaving the required three units.
-/

noncomputable section

namespace Erdos240.VDPLParameters

variable {ι : Type*} [Fintype ι] (P : VDPLParameters ι)

/-- At an admissible level, the exact p.52 coprime-node count supplies more
than `11/2` fixed source-height units. -/
theorem eleven_halves_mul_sourceHeight_lt_coprime_count_log_three
    [Nonempty ι] {J : ℕ} (hJ : P.LevelOK J) :
    (11 / 2 : ℝ) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) <
      ((P.R (J + 1) * (P.q - 1) / P.q) * (P.Sstep J / 4) : ℕ) *
        Real.log 3 := by
  let x : ℝ := P.levelScale J
  let A : ℝ := ((P.q ^ J : ℕ) : ℝ) * P.h
  let T : ℝ := ((P.Sstep J / 4 : ℕ) : ℝ)
  have hxRank := P.fiveHundredTwelve_mul_rank_add_one_lt_levelScale hJ
  have hrank : (2 : ℝ) ≤ P.rank + 1 := by
    exact_mod_cast Nat.succ_le_succ P.rank_pos
  have hx : (1024 : ℝ) < x := by
    dsimp only [x]
    nlinarith
  have hA : 0 < A := by
    dsimp only [A]
    have hqpow : 0 < P.q ^ J := pow_pos (by simp [q]) J
    exact mul_pos (by exact_mod_cast hqpow) (by exact_mod_cast P.h_pos)
  have hTfloor : x / 36 - 1 < T := by
    dsimp only [x, T]
    rw [P.Sstep_div_four_eq_floor_levelScale_div_thirtySix]
    linarith [Nat.lt_floor_add_one (P.levelScale J / 36)]
  have hTpos : 0 < T := by
    have : (0 : ℝ) < x / 36 - 1 := by linarith
    linarith
  have hsource :
      (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld = A * x := by
    dsimp only [A, x]
    rw [← P.levelScale_mul_qpow_mul_h J]
    ring_nf
  have hbase :
      (11 / 2 : ℝ) * (A * x) <
        (1.0986122885 : ℝ) * ((192 * A) * (x / 36 - 1)) := by
    nlinarith [mul_lt_mul_of_pos_left hx hA]
  have hfloor :
      (1.0986122885 : ℝ) * ((192 * A) * (x / 36 - 1)) <
        (1.0986122885 : ℝ) * ((192 * A) * T) := by
    exact mul_lt_mul_of_pos_left
      (mul_lt_mul_of_pos_left hTfloor (by positivity)) (by norm_num)
  have hlog : (1.0986122885 : ℝ) < Real.log 3 :=
    Real.log_three_gt_d9
  have hlogStep :
      (1.0986122885 : ℝ) * ((192 * A) * T) <
        ((192 * A) * T) * Real.log 3 := by
    have hZ : 0 < (192 * A) * T := mul_pos (by positivity) hTpos
    nlinarith [mul_lt_mul_of_pos_left hlog hZ]
  have hcount :
      (((P.R (J + 1) * (P.q - 1) / P.q) *
          (P.Sstep J / 4) : ℕ) : ℝ) = (192 * A) * T := by
    rw [P.successor_coprime_node_count_eq J]
    dsimp only [A, T]
    push_cast
    ring
  rw [hsource, hcount]
  exact hbase.trans (hfloor.trans hlogStep)

/-- Inverse-cube form of the sharp `11/2` p.52 nodal decay. -/
theorem coprime_decay_pow_lt_exp_neg_eleven_halves_sourceHeight
    [Nonempty ι] {J : ℕ} (hJ : P.LevelOK J) :
    ((3 : ℝ)⁻¹) ^
        ((P.R (J + 1) * (P.q - 1) / P.q) * (P.Sstep J / 4)) <
      Real.exp (-(11 / 2 : ℝ) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld)) := by
  apply pow_lt_exp_of_mul_log_lt (by positivity)
  rw [Real.log_inv]
  have h := P.eleven_halves_mul_sourceHeight_lt_coprime_count_log_three hJ
  push_cast at h ⊢
  linarith

/-- The exact nodal decay pays the two-unit boundary growth and the `4/3`
Cauchy radius/gap loss, while retaining three fixed source-height units. -/
theorem four_thirds_mul_growth_mul_coprime_decay_lt_exp_neg_three_sourceHeight
    [Nonempty ι] {J : ℕ} (hJ : P.LevelOK J) {growth : ℝ}
    (hgrowth : growth ≤ Real.exp
      (2 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) :
    (4 / 3 : ℝ) * growth *
        ((3 : ℝ)⁻¹) ^
          ((P.R (J + 1) * (P.q - 1) / P.q) * (P.Sstep J / 4)) <
      Real.exp (-(3 * ((P.h : ℝ) * P.k * P.Omega *
        Real.log P.OmegaOld))) := by
  let H : ℝ := (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld
  let decay : ℝ := ((3 : ℝ)⁻¹) ^
    ((P.R (J + 1) * (P.q - 1) / P.q) * (P.Sstep J / 4))
  have hH : (1 : ℝ) ≤ H := by
    simpa only [H] using P.one_le_sourceHeightUnit
  have hdecay : decay < Real.exp (-(11 / 2 : ℝ) * H) := by
    simpa only [decay, H] using
      P.coprime_decay_pow_lt_exp_neg_eleven_halves_sourceHeight hJ
  have hlog : Real.log (4 / 3 : ℝ) < 1 / 2 := by
    have h := Real.log_lt_sub_one_of_pos
      (by norm_num : (0 : ℝ) < 4 / 3) (by norm_num : (4 / 3 : ℝ) ≠ 1)
    norm_num at h ⊢
    linarith
  have hfactor : (4 / 3 : ℝ) < Real.exp (H / 2) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)]
    exact Real.exp_lt_exp.mpr (by nlinarith)
  calc
    (4 / 3 : ℝ) * growth * decay ≤
        (4 / 3 : ℝ) * Real.exp (2 * H) * decay := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by simpa only [H] using hgrowth) (by norm_num))
        (by positivity)
    _ < (4 / 3 : ℝ) * Real.exp (2 * H) *
        Real.exp (-(11 / 2 : ℝ) * H) := by
      exact mul_lt_mul_of_pos_left hdecay
        (mul_pos (by norm_num) (Real.exp_pos _))
    _ = (4 / 3 : ℝ) *
        (Real.exp (2 * H) * Real.exp (-(11 / 2 : ℝ) * H)) := by ring
    _ = (4 / 3 : ℝ) * Real.exp (-(7 / 2 : ℝ) * H) := by
      rw [← Real.exp_add]
      congr 1
      ring_nf
    _ < Real.exp (H / 2) * Real.exp (-(7 / 2 : ℝ) * H) := by
      exact mul_lt_mul_of_pos_right hfactor (Real.exp_pos _)
    _ = Real.exp (-(3 * H)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = Real.exp (-(3 * ((P.h : ℝ) * P.k * P.Omega *
        Real.log P.OmegaOld))) := rfl

end Erdos240.VDPLParameters

#print axioms Erdos240.VDPLParameters.eleven_halves_mul_sourceHeight_lt_coprime_count_log_three
#print axioms Erdos240.VDPLParameters.coprime_decay_pow_lt_exp_neg_eleven_halves_sourceHeight
#print axioms Erdos240.VDPLParameters.four_thirds_mul_growth_mul_coprime_decay_lt_exp_neg_three_sourceHeight
