/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 John Jennings. All rights reserved.
Released under Apache 2.0 license; see LICENSE.
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
import ErdosProblems.Erdos927.Small

set_option linter.mathlibStandardSet false

namespace Erdos927

/-
# Spencer's Lower Bound — Main Theorem

This file connects Spencer's graph construction to the disproof
of Erdős Problem 927.
-/

/-! ## Core combinatorial claim -/

/-- For each size d with 5 ≤ d ≤ spB n, there exists a maximal clique of size d
  in Spencer's graph. This is the core combinatorial claim. -/
theorem spencer_clique_sizes (n : ℕ) (hn : n ≥ 16) :
    ∀ d : ℕ, 5 ≤ d → d ≤ spB n →
    ∃ s : Finset (SpVtx n (spA n)),
      IsMaximalClique (spGraph n) s ∧ s.card = d := by
  classical
  intro d hd1 hd2
  by_cases hmed : d ≤ 2 ^ n + n
  · by_cases hsmall : d ≤ n
    · exact small_clique_exists n hn d hd1 hsmall
    · exact medium_clique_exists n (by omega) d (by omega) hmed
  · exact big_clique_exists n hn d (by omega) hd2

/-! ## Main bound -/

/-- spB n ≥ 5 for n ≥ 2. -/
lemma spB_ge_five (n : ℕ) (hn : n ≥ 2) : spB n ≥ 5 := by
  classical
  unfold spB
  have h1 : 2 ^ n ≥ 4 := by
    calc 2 ^ n ≥ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn
    _ = 4 := by norm_num
  have h2 := spA_pos n
  omega

/-- For each n ≥ 16, Spencer's construction gives
  g(spN n) ≥ spB n - 4. -/
theorem spencer_construction (n : ℕ) (hn : n ≥ 16) :
    spN n ≤ n + 6 + g (spN n) := by
  classical
  have hcliques := spencer_clique_sizes n hn
  have hcard := spVtx_card n
  have hge : spB n - 4 ≤ g (spN n) := by
    have hsub : Finset.Icc 5 (spB n) ⊆ maximalCliqueSizes (spGraph n) := by
      apply maximalCliqueSizes_card_ge
      intro k hk
      simp [Finset.mem_Icc] at hk
      exact hcliques k hk.1 hk.2
    have hcard_icc : (Finset.Icc 5 (spB n)).card = spB n - 4 := by
      rw [Nat.card_Icc]
      have := spB_ge_five n (by omega : n ≥ 2)
      omega
    calc spB n - 4 = (Finset.Icc 5 (spB n)).card := hcard_icc.symm
      _ ≤ (maximalCliqueSizes (spGraph n)).card :=
          Finset.card_le_card hsub
      _ ≤ g (Fintype.card (SpVtx n (spA n))) :=
          g_ge_of_card (spGraph n) rfl
      _ = g (spN n) := by rw [hcard]
  have heq := spN_eq n (by omega : n ≥ 2)
  omega

/-- Spencer's lower bound with log: for n ≥ 16,
  g(spN n) ≥ spN n - Nat.log 2 (spN n) - 6. -/
theorem spencer_lower_bound (n : ℕ) (hn : n ≥ 16) :
    spN n ≤ g (spN n) + Nat.log 2 (spN n) + 6 := by
  classical
  rw [spencer_log n hn]
  linarith [spencer_construction n hn]

/-- The disproof: for any C, there exists N ≥ 2 with
  g(N) + log₂(N) + logStar(N) > N + C. -/
theorem spencer_disproof_key (C : ℕ) :
    ∃ N : ℕ, N ≥ 2 ∧ N + C < g N + Nat.log 2 N + logStar N := by
  classical
  obtain ⟨m, hm⟩ := logStar_unbounded (C + 6)
  set n := max m 16 with hn_def
  have hn16 : n ≥ 16 := le_max_right _ _
  have hnm : n ≥ m := le_max_left _ _
  use spN n
  refine ⟨spN_ge_two n (by omega), ?_⟩
  have hsp := spencer_lower_bound n hn16
  have hls : C + 6 < logStar (spN n) :=
    lt_of_lt_of_le hm (logStar_mono (le_trans hnm (le_spN n)))
  omega

end Erdos927
