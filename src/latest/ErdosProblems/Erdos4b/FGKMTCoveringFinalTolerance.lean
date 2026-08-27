/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCoveringConditions

/-! # The final singleton tolerance is at most one half -/

namespace Erdos4b.FGKMT.CoveringConditions

noncomputable section

universe u v w

variable {I : ℕ → Type u} {Ω : ℕ → Type v} {α : Type w}
  [∀ j, Fintype (I j)] [∀ j, Fintype (Ω j)] [DecidableEq α]
  {F : (j : ℕ) → FiniteEdgeFamily (I j) (Ω j) α}
  {V : Finset α} {r A m : ℕ} {κ δ D : ℝ}

theorem final_tolerance_le_half (H : CoveringConditions F V r A m κ δ D) :
    coveringTolerance δ (m + 1) ≤ 1 / 2 := by
  have hS : 2 ≤ coveringScale A D κ := (by norm_num : (2 : ℝ) ≤ 256).trans H.scale_ge
  have hbase : 1 / coveringScale A D κ ≤ (1 / 2 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hS
  have hexp : 10 ^ (m + 1) ≤ 10 ^ (m + 2) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsmall : δ ≤ (1 / 2 : ℝ) ^ (10 ^ (m + 1)) :=
    H.smallness.trans ((pow_le_pow_left₀ (by positivity) hbase _).trans
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hexp))
  apply (pow_le_pow_iff_left₀ (coveringTolerance_pos H.error_pos _).le
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by positivity : (10 : ℕ) ^ (m + 1) ≠ 0)).mp
  rw [coveringTolerance_pow H.error_pos.le]
  exact hsmall

end

end Erdos4b.FGKMT.CoveringConditions
