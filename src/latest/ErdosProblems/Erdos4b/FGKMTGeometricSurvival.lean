/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSurvivalStep
import ErdosProblems.Erdos4b.FGKMTGeometricBatchWeights
import ErdosProblems.Erdos4b.FGKMTCoveringHistory

/-! # Geometric survival with an additive degree-error budget -/

namespace Erdos4b.FGKMT

noncomputable section

def geometricSurvival (j : ℕ) : ℝ := (1 / 5 : ℝ) ^ j

theorem geometricSurvival_pos (j : ℕ) : 0 < geometricSurvival j :=
  pow_pos (by norm_num) j

theorem geometricSurvival_antitone : Antitone geometricSurvival :=
  pow_right_anti₀ (by norm_num) (by norm_num)

theorem geometricSurvival_le_one (j : ℕ) : geometricSurvival j ≤ 1 :=
  geometricSurvival_antitone (Nat.zero_le j)

theorem survivalStep_geometric (j : ℕ) :
    survivalStep (geometricSurvival j) (geometricBatchTarget j) =
      geometricSurvival (j + 1) := by
  change geometricSurvival j *
    Real.exp (-(geometricSurvival j * Real.log 5) / geometricSurvival j) = _
  have hc : -(geometricSurvival j * Real.log 5) / geometricSurvival j = -Real.log 5 := by
    field_simp [(geometricSurvival_pos j).ne']
  rw [hc, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 5)]
  simp only [geometricSurvival, pow_succ]
  ring

theorem log_five_le_two : Real.log 5 ≤ 2 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 5)).mpr
  have he : (5 / 2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  nlinarith

theorem geometric_error_budget {m j : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (hj : j ≤ m)
    (hsmall : ((m : ℝ) + 1) * ε ≤ geometricSurvival m / 4) :
    (j : ℝ) * ε ≤ geometricSurvival j / 4 ∧ ε ≤ geometricSurvival j / 4 := by
  have hjR : (j : ℝ) ≤ m := by exact_mod_cast hj
  have hupper : ((m : ℝ) + 1) * ε ≤ geometricSurvival j / 4 :=
    hsmall.trans (div_le_div_of_nonneg_right (geometricSurvival_antitone hj) (by norm_num))
  constructor
  · exact (mul_le_mul_of_nonneg_right (by linarith : (j : ℝ) ≤ m + 1) hε).trans hupper
  · nlinarith [mul_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m) hε]

universe u v w

variable {I : ℕ → Type u} {Ω : ℕ → Type v} {α : Type w}
  [∀ j, Fintype (I j)] [∀ j, Fintype (Ω j)] [DecidableEq α]
  (F : (j : ℕ) → FiniteEdgeFamily (I j) (Ω j) α)

theorem coveringSurvival_geometric_error {m : ℕ} {ε : ℝ} (a : α)
    (hdegree : ∀ j < m, |(F j).degree a - geometricBatchTarget j| ≤ ε)
    {j : ℕ} (hj : j ≤ m) :
    |coveringSurvival F j a - geometricSurvival j| ≤ (j : ℝ) * ε := by
  induction j with
  | zero => simp [coveringSurvival, geometricSurvival]
  | succ j ih =>
    have hjm : j < m := Nat.lt_of_succ_le hj
    have hstep := survivalStep_sub_le (coveringSurvival_pos F j a)
      (geometricSurvival_pos j) ((F j).degree_nonneg a) (geometricBatchTarget_pos j).le
    have hrec : coveringSurvival F (j + 1) a =
        survivalStep (coveringSurvival F j a) ((F j).degree a) := rfl
    rw [hrec, ← survivalStep_geometric j]
    refine hstep.trans ((add_le_add (ih (Nat.le_of_lt hjm)) (hdegree j hjm)).trans_eq ?_)
    push_cast
    ring

theorem coveringSurvival_geometric_bounds {m : ℕ} {ε : ℝ} (a : α) (hε : 0 ≤ ε)
    (hdegree : ∀ j < m, |(F j).degree a - geometricBatchTarget j| ≤ ε)
    (hsmall : ((m : ℝ) + 1) * ε ≤ geometricSurvival m / 4)
    {j : ℕ} (hj : j ≤ m) :
    (3 / 4 : ℝ) * geometricSurvival j ≤ coveringSurvival F j a ∧
      coveringSurvival F j a ≤ (5 / 4 : ℝ) * geometricSurvival j := by
  have herror := (coveringSurvival_geometric_error F a hdegree hj).trans
    (geometric_error_budget hε hj hsmall).1
  obtain ⟨hlo, hhi⟩ := abs_le.mp herror
  constructor <;> linarith

theorem coveringSurvival_geometric_lower {m : ℕ} {ε : ℝ} (a : α) (hε : 0 ≤ ε)
    (hdegree : ∀ j < m, |(F j).degree a - geometricBatchTarget j| ≤ ε)
    (hsmall : ((m : ℝ) + 1) * ε ≤ geometricSurvival m / 4)
    {j : ℕ} (hj : j ≤ m) :
    geometricSurvival m / 2 ≤ coveringSurvival F j a := by
  have hlow := (coveringSurvival_geometric_bounds F a hε hdegree hsmall hj).1
  have hmono := geometricSurvival_antitone hj
  have hpos := (geometricSurvival_pos m).le
  linarith

theorem coveringSurvival_geometric_degree {m : ℕ} {ε : ℝ} (a : α) (hε : 0 ≤ ε)
    (hdegree : ∀ j < m, |(F j).degree a - geometricBatchTarget j| ≤ ε)
    (hsmall : ((m : ℝ) + 1) * ε ≤ geometricSurvival m / 4)
    {j : ℕ} (hj : j < m) : (F j).degree a ≤ 4 * coveringSurvival F j a := by
  have hlow := (coveringSurvival_geometric_bounds F a hε hdegree hsmall hj.le).1
  have herror := (abs_le.mp (hdegree j hj)).2
  have heps := (geometric_error_budget hε hj.le hsmall).2
  have ht : geometricBatchTarget j ≤ 2 * geometricSurvival j := by
    change geometricSurvival j * Real.log 5 ≤ 2 * geometricSurvival j
    nlinarith [mul_le_mul_of_nonneg_left log_five_le_two (geometricSurvival_pos j).le]
  have hpos := (geometricSurvival_pos j).le
  linarith

end

end Erdos4b.FGKMT
