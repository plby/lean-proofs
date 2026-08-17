/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/
import ErdosProblems.Erdos55.OmittedIntervals

/-!
# The sharp lower bound in the Conlon--Fox--Pham resolution

An eventual bound with absolute constant `1/65536` gives a quadratic dyadic
counting estimate.  Taking `h = r / 2` makes its coefficient small enough for
the red/blue mass argument, hence weak scales are unbounded.  The sparse
rank-and-bit coloring constructed in `OmittedIntervals` then disproves Ramsey
`r`-completeness.  Finite sets are handled separately.
-/

namespace Erdos55

/-- The lower-bound half of the resolution, with an explicit admissible
absolute constant. -/
theorem conlonFoxPham_lowerBound : CFPLowerBound := by
  refine ⟨(1 : ℝ) / 65536, by norm_num, ?_⟩
  intro r hr A hcount
  by_cases hAfin : (A : Set ℕ).Finite
  · exact finite_not_ramseyComplete (by omega) hAfin
  · have hAinf : (A : Set ℕ).Infinite := hAfin
    obtain ⟨N₀, hN₀⟩ := hcount
    obtain ⟨K, hK, hquad⟩ := eventually_dyadicCount_le_quadratic
      hAinf A.2 (c := (1 : ℝ) / 65536) (by norm_num) r N₀ hN₀
    let h := r / 2
    let β : ℝ := ((1 : ℝ) / 65536) * r
    have hh : 0 < h := by
      dsimp only [h]
      omega
    have hhr : 2 * h ≤ r := by
      dsimp only [h]
      omega
    have hrh : r ≤ 3 * h := by
      dsimp only [h]
      omega
    have hrhR : (r : ℝ) ≤ 3 * h := by exact_mod_cast hrh
    have hβ : 0 ≤ β := by
      dsimp only [β]
      positivity
    have hβsmall : 8192 * β ≤ (h : ℝ) := by
      dsimp only [β]
      norm_num
      nlinarith [show (0 : ℝ) ≤ h by positivity]
    have hquad' : ∀ k, K ≤ k →
        (dyadicCount (A : Set ℕ) k : ℝ) ≤ β * (k : ℝ) ^ 2 := by
      intro k hk
      simpa [β] using hquad k hk
    have hunbounded : ∀ b, ∃ j, b < j ∧ WeakScale (A : Set ℕ) h j :=
      weakScale_unbounded_of_quadratic hAinf A.2 hh hK hβ hβsmall hquad'
    exact not_ramseyComplete_of_weakScale_unbounded hAinf hh hhr hunbounded

end Erdos55
