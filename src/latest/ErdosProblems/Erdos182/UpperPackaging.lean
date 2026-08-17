/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos182.JSUpper

/-!
# Erdős Problem 182: packaging the upper bound

This file converts the integer-logarithm forcing statement used by the
combinatorial proof into the real iterated-logarithm upper bound for the
literal extremal number.
-/

open Filter

namespace Erdos182

/-- The floor-valued binary logarithm is at most the real binary logarithm. -/
lemma natCast_log2_le_logb (m : ℕ) (hm : 0 < m) :
    (Nat.log2 m : ℝ) ≤ Real.logb 2 (m : ℝ) := by
  rw [Real.logb]
  apply (le_div_iff₀ (Real.log_pos one_lt_two)).2
  rw [← Real.log_pow]
  apply Real.strictMonoOn_log.monotoneOn
  · change 0 < (2 : ℝ) ^ Nat.log2 m
    positivity
  · change 0 < (m : ℝ)
    positivity
  · exact_mod_cast (show 2 ^ Nat.log2 m ≤ m by
      simpa only [Nat.log2_eq_log_two] using
        Nat.pow_log_le_self 2 (Nat.ne_of_gt hm))

/-- The twice-iterated floor-valued binary logarithm is at most the real
twice-iterated binary logarithm once the arguments are positive. -/
lemma natCast_log2_log2_le_logLog2 (n : ℕ) (hn : 4 ≤ n) :
    (Nat.log2 (Nat.log2 n) : ℝ) ≤ logLog2 n := by
  have hlog2pos : 0 < Nat.log2 n := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_pos (by omega) (by omega)
  have hinner := natCast_log2_le_logb n (by omega)
  calc
    (Nat.log2 (Nat.log2 n) : ℝ) ≤
        Real.logb 2 (Nat.log2 n : ℝ) :=
      natCast_log2_le_logb _ hlog2pos
    _ ≤ Real.logb 2 (Real.logb 2 (n : ℝ)) := by
      rw [Real.logb, Real.logb]
      apply div_le_div_of_nonneg_right _ (Real.log_pos one_lt_two).le
      exact Real.log_le_log (Nat.cast_pos.2 hlog2pos) hinner
    _ = logLog2 n := rfl

open scoped Classical in
/-- An eventual natural-number forcing threshold implies the corresponding
real-valued upper bound for `regularExtremalNumber`. -/
theorem regularExtremalNumber_upper_of_nVertex_forcing
    (k : ℕ) (hk : 0 < k)
    (hforcing : ∃ C : ℕ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ G : SimpleGraph (Fin n),
        C * Nat.log2 (Nat.log2 n) * n ≤ G.edgeFinset.card →
          ContainsRegularSubgraph G k) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (regularExtremalNumber n k : ℝ) ≤ C * ((n : ℝ) * logLog2 n) := by
  classical
  obtain ⟨C, hC, N, hforce⟩ := hforcing
  refine ⟨(C : ℝ), by positivity, ?_⟩
  apply regularExtremalNumber_upper_of_graph_forcing k hk
  filter_upwards [eventually_ge_atTop (max N 4)] with n hn G hEdges
  apply hforce n (le_trans (le_max_left _ _) hn) G
  have hlog := natCast_log2_log2_le_logLog2 n
    (le_trans (le_max_right _ _) hn)
  have hNatCast :
      ((C * Nat.log2 (Nat.log2 n) * n : ℕ) : ℝ) ≤
        (G.edgeFinset.card : ℝ) := by
    calc
      ((C * Nat.log2 (Nat.log2 n) * n : ℕ) : ℝ) =
          (C : ℝ) * (Nat.log2 (Nat.log2 n) : ℝ) * (n : ℝ) := by
            norm_num
      _ ≤ (C : ℝ) * logLog2 n * (n : ℝ) := by
        gcongr
      _ = (C : ℝ) * ((n : ℝ) * logLog2 n) := by ring
      _ ≤ (G.edgeFinset.card : ℝ) := hEdges
  exact_mod_cast hNatCast

end Erdos182
