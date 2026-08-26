/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 John Jennings. All rights reserved.
Released under Apache 2.0 license; see Erdos927/LICENSE.
Modified for this repository and Lean/Mathlib 4.33.0.
-/
/-
Erdős Problem 927.
Informal proof: Joel H. Spencer, "On cliques in graphs" (1971).
Formal authors: John Jennings and Aristotle (Harmonic).
Jake Mallen replaced native evaluation with kernel-checked proofs in the selected copy.
Source: https://www.erdosproblems.com/927#post-6850
https://gist.githubusercontent.com/JohnEdwardJennings/24c9debc9854cb118fbc1314c70941c3/raw/b4fc5ef91876a89018b10508c479c000258504fb/Erdos927.lean
https://github.com/Jayyhk/erdos-lean/tree/cc6c94bd3f9de7c4cf7703ed40d8fd06380780a3/problems/927
Original and selected toolchain: Lean 4.28.0.
Selected Mathlib commit: 8f9d9cff6bd728b17a24e163c9402775d9e6a365.
-/
import ErdosProblems.Erdos927.Construction

namespace Erdos927

/-- Even the eventual upper-bound direction of the conjectured asymptotic formula fails. -/
theorem not_erdos_927 :
    ¬ (∃ C n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → g n + Nat.log 2 n + logStar n ≤ n + C) := by
  rintro ⟨C, n₀, hC⟩
  obtain ⟨m, hm⟩ := logStar_unbounded (C + 6)
  let n := max (max m 16) n₀
  have hn16 : 16 ≤ n := (le_max_right m 16).trans (le_max_left _ _)
  have hnm : m ≤ n := (le_max_left m 16).trans (le_max_left _ _)
  have hn₀ : n₀ ≤ spN n := (le_max_right _ _).trans (le_spN n)
  have hsp := spencer_lower_bound n hn16
  have hls : C + 6 < logStar (spN n) :=
    hm.trans_le (logStar_mono (hnm.trans (le_spN n)))
  have hbound := hC (spN n) hn₀
  omega

#print axioms not_erdos_927
-- 'Erdos927.not_erdos_927' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos927
