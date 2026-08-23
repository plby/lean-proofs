/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 1096.
https://www.erdosproblems.com/forum/thread/1096

Informal authors:
- Paul Erdős
- Vilmos Komornik

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1096.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/1096.lean
-/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos1096.Erdos1096Accumulation

/-!
# Erdős Problem 1096

For every base sufficiently close to one, the successive gaps in the ordered
binary spectrum tend to zero.  The detailed mathematical proof and the
Leanization map are in `tex/1096.tex`.
-/

open Filter Set
open scoped BigOperators Pointwise Topology

namespace Erdos1096

noncomputable section

theorem erdos_1096 :
    answer(True) ↔ ∃ ε > 0, ∀ q, 1 < q → q < 1 + ε →
    ∀ x : ℕ → ℝ, StrictMono x → Set.range x = { ∑ i ∈ S, q ^ i | S : Finset ℕ } →
    Tendsto (fun k => x (k + 1) - x k) atTop (𝓝 0) := by
  constructor
  · intro htrue
    refine ⟨1 / 1000, by norm_num, fun q hq hqε x hx hrange ↦ ?_⟩
    have hqbound : q < 1001 / 1000 := by
      norm_num at hqε ⊢
      exact hqε
    have hsq1 : 1 < q ^ 2 := one_lt_pow₀ hq (by omega)
    have hsqbound : q ^ 2 < 101 / 100 := by
      calc
        q ^ 2 < (1001 / 1000 : ℝ) ^ 2 :=
          pow_lt_pow_left₀ hqbound (by linarith) (by omega)
        _ < 101 / 100 := by norm_num
    have hsq2 : q ^ 2 < 2 := hsqbound.trans (by norm_num)
    have hsmall : SmallDisjointDifferences (q ^ 2) :=
      smallDisjointDifferences_of_smallSpectrumDifferences
        (smallSpectrumDifferences_below_one_hundred_one_hundredths hsq1 hsqbound)
    have hdense : EventuallyRightDense (Spectrum q) :=
      spectrum_eventuallyRightDense_of_square_smallDifferences hq hsq2 hsmall
    have hrange' : Set.range x = Spectrum q := by
      rw [hrange]
      ext a
      simp only [Spectrum, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨S, rfl⟩
        exact ⟨S, rfl⟩
      · rintro ⟨S, rfl⟩
        exact ⟨S, rfl⟩
    exact gaps_tendsto_zero_of_eventuallyRightDense hx hrange'
      (strictMono_spectrum_tendsto_atTop hq hx hrange') hdense
  · intro h
    trivial

#print axioms Erdos1096.erdos_1096

end

end Erdos1096
