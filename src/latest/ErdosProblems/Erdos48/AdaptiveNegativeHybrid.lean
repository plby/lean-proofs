/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.AdaptiveHybridTaylor
import ErdosProblems.Erdos48.NegativeHybridTaylor

/-! # Variable-length negative-phase hybrid large sieve -/

open scoped BigOperators

noncomputable section

namespace Erdos48

/-- The adaptive hybrid estimate with the negative logarithmic phase used
by the zero detector. -/
theorem intervalIntegral_primitiveNegativeDirichletBlockMass_variable_le
    {ι : Type*} [Fintype ι]
    (Q : ℕ) (H : ι → ℕ) (s : ι → Finset ℕ) (m0 : ι → ℕ)
    (hs : ∀ i, s i ⊆ Finset.Ioc (m0 i) (m0 i + H i))
    (x : ι → ℝ) {δ T B : ℝ}
    (hδ : 0 < δ) (hT : 0 ≤ T)
    (hsep : ∀ r t, r ≠ t → δ ≤ |x r - x t|)
    (c : ℕ → ℂ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (s i) (s j))
    (hB : 0 ≤ B)
    (hoffset : ∀ i, ∀ n ∈ s i, |Real.log n - x i| ≤ B) :
    (∫ t in (0 : ℝ)..T,
        primitiveNegativeDirichletBlockMass Q s c t) ≤
      Real.exp 1 * Real.exp ((T * B) ^ 2) *
        (T + 2 * Real.pi * δ⁻¹) *
          ∑ i, (((H i : ℕ) : ℝ) + (Q : ℝ) ^ 2) *
            ∑ n ∈ s i, ‖c n‖ ^ 2 := by
  let d : ℕ → ℝ := fun n ↦ -blockLogOffset x s n
  have hd : ∀ i, ∀ n ∈ s i, |d n| ≤ B := by
    intro i n hn
    rw [show d n = -(Real.log n - x i) by
      dsimp [d]
      rw [blockLogOffset_eq x s hdisj i hn], abs_neg]
    exact hoffset i n hn
  have hsepNeg : ∀ r t, r ≠ t → δ ≤ |(-x r) - (-x t)| := by
    intro r t hrt
    simpa only [neg_sub_neg, abs_neg] using hsep t r hrt.symm
  have hmain := intervalIntegral_primitiveHybridMass_variable_le
    Q H s m0 hs (fun i ↦ -x i) hδ hT hsepNeg c d hB hd
  rw [show primitiveHybridMass Q (fun i ↦ -x i) s c d =
      primitiveNegativeDirichletBlockMass Q s c by
    funext t
    exact primitiveHybridMass_neg_blockLogOffset_eq Q x s c hdisj t] at hmain
  exact hmain

end Erdos48
