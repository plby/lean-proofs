/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Licensed under the Apache License, Version 2.0; see Erdos884/LICENSE.
Modified for this repository and Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 884.
Informal proof: Daniel Larsen, building on Terence Tao's construction.
Formal proof: Claude Fable 5, with minor guidance from R. J. Honicky.
Source: https://www.erdosproblems.com/884#post-7362
https://github.com/honicky/erdos884/tree/323e9a01306df1e094b434beaa48c018370fe258
Original Lean/Mathlib version: 4.31.0.
Original Mathlib commit: fabf563a7c95a166b8d7b6efca11c8b4dc9d911f.
The port reuses the repository's existing PNT+ Selberg sieve by Arend Mellendijk.
-/
import ErdosProblems.Erdos884.MultiScale

/-!
# Erdős Problem 884 — the disproof (final statement)

Combining the multiscale construction (`exists_ratio_large`) with the bridge to the
official formal-conjectures statement (`Bridge884`), we conclude:

  it is NOT the case that
    ∑_{d < e, d,e ∣ n} 1/(e - d)  =O  1 + ∑_{consecutive divisors d < e of n} 1/(e - d)

as functions of `n → ∞`, i.e. Erdős problem #884 has a negative answer (Daniel Larsen).

In the ≪ notation of formal-conjectures, this refutes
  `sumDivisorInvPairwiseDifference ≪ 1 + sumDivisorInvConsecutiveDifference`.
-/

namespace Erdos884

theorem not_erdos_884 :
    ¬ (sumDivisorInvPairwiseDifference =O[Filter.atTop]
      (1 + sumDivisorInvConsecutiveDifference)) := by
  intro h
  obtain ⟨c, hc⟩ := Asymptotics.isBigO_iff.mp h
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp hc
  obtain ⟨n, hn_ge, hn_ne, hlt⟩ :=
    exists_ratio_large (max c 1) (lt_of_lt_of_le one_pos (le_max_right c 1)) n₀
  have hb := hn₀ n hn_ge
  have hgap : (0 : ℝ) ≤ gapSum n.divisors := gapSum_nonneg _
  have hT : ‖sumDivisorInvPairwiseDifference n‖ = pairSum n.divisors := by
    rw [Real.norm_of_nonneg (sumDivisorInvPairwise_nonneg n hn_ne),
        sumDivisorInvPairwiseDifference_eq hn_ne]
  have hS : ‖(1 + sumDivisorInvConsecutiveDifference) n‖ = 1 + gapSum n.divisors := by
    have happ : (1 + sumDivisorInvConsecutiveDifference) n
        = 1 + sumDivisorInvConsecutiveDifference n := by
      simp [Pi.add_apply]
    rw [happ, sumDivisorInvConsecutiveDifference_eq hn_ne,
        Real.norm_of_nonneg (by linarith)]
  rw [hT, hS] at hb
  have hchain : pairSum n.divisors ≤ max c 1 * (1 + gapSum n.divisors) :=
    hb.trans (mul_le_mul_of_nonneg_right (le_max_left c 1) (by linarith))
  exact absurd hchain (not_le.mpr hlt)

#print axioms not_erdos_884
-- 'Erdos884.not_erdos_884' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos884
