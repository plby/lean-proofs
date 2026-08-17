/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos651.Definitions

/-! The asymptotic incompatibility at the end of the resolution of Problem 651. -/

namespace Erdos651

open Filter Set
open scoped Topology

noncomputable section

theorem subexponential_not_exponentialLowerBound
    {f : ℕ → ℕ} (hf : HasSubexponentialUpperBound f) :
    ¬ HasExponentialLowerBound f := by
  rintro ⟨c, hc, hlow⟩
  let ε : ℝ := Real.logb 2 (1 + c)
  have hbase : 0 < 1 + c := by linarith
  have hε : 0 < ε := by
    dsimp [ε]
    exact Real.logb_pos (by norm_num : (1 : ℝ) < 2) (by linarith)
  obtain ⟨n, hup, hlo⟩ := ((hf ε hε).and hlow).exists
  have heq : (2 : ℝ) ^ (ε * (n : ℝ)) = (1 + c) ^ n := by
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [show (2 : ℝ) ^ ε = 1 + c by
      dsimp [ε]
      exact Real.rpow_logb (by norm_num) (by norm_num) hbase]
    exact Real.rpow_natCast (1 + c) n
  exact (not_lt_of_ge (hup.trans_eq heq)) hlo

end

end Erdos651
