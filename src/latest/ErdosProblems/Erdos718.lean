/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of the resolution of Erdős Problem 718.
https://www.erdosproblems.com/718

Informal authors:
- János Komlós and Endre Szemerédi
- Béla Bollobás and Andrew Thomason
- Robin Thomas and Paul Wollan (linkedness theorem used in the proof)

Formal authors:
- Codex

The accompanying detailed proof and Leanization plan is `tex/718.tex`.
-/

import ErdosProblems.Erdos718.Erdos718Core
import ErdosProblems.Erdos717.DensityTheorem
import Mathlib.Data.Real.Basic

open SimpleGraph

namespace Erdos718

/-- The natural-number edge-count form of the density theorem: five times
`r²` times the number of vertices suffices. -/
theorem containsCliqueSubdivision_of_edgeCard
    {V : Type} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (r : ℕ)
    (hE : 5 * (r * r) * Fintype.card V ≤ G.edgeSet.ncard) :
    ContainsCliqueSubdivision G r := by
  classical
  apply Erdos717.ThomasWollanMassed.containsCliqueSubdivision_of_five_mul_sq_mul_card_le_edges
    G r Fintype.card_pos
  rw [MaderPrototype.card_edgeFinset_eq_ncard_edgeSet]
  exact hE

/-- The equivalent average-degree-style, cross-multiplied form advertised in
the mathematical writeup. -/
theorem containsCliqueSubdivision_of_averageDegree
    {V : Type} [Fintype V] [Nonempty V]
    (r : ℕ) (G : SimpleGraph V)
    (havg : 10 * (r ^ 2) * Fintype.card V ≤
      2 * G.edgeSet.ncard) :
    ContainsCliqueSubdivision G r := by
  apply containsCliqueSubdivision_of_edgeCard G r
  have havg' : 2 * (5 * (r * r) * Fintype.card V) ≤
      2 * G.edgeSet.ncard := by
    calc
      2 * (5 * (r * r) * Fintype.card V) =
          10 * (r ^ 2) * Fintype.card V := by ring
      _ ≤ 2 * G.edgeSet.ncard := havg
  omega

/-- Erdős Problem 718 has an affirmative answer.  The explicit real constant
`C = 5` works for every nonempty finite graph. -/
theorem erdos718 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (r : ℕ) (V : Type) [Fintype V] [Nonempty V]
        (G : SimpleGraph V),
        C * (r : ℝ) ^ 2 * (Fintype.card V : ℝ) ≤
            (G.edgeSet.ncard : ℝ) →
          ContainsCliqueSubdivision G r := by
  refine ⟨5, by positivity, ?_⟩
  intro r V _ _ G hE
  apply containsCliqueSubdivision_of_edgeCard G r
  have hNat : 5 * (r ^ 2) * Fintype.card V ≤ G.edgeSet.ncard := by
    exact_mod_cast hE
  simpa only [pow_two] using hNat

/-- Underscored alias following the naming convention used by some nearby
formalizations in this repository. -/
theorem erdos_718 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (r : ℕ) (V : Type) [Fintype V] [Nonempty V]
        (G : SimpleGraph V),
        C * (r : ℝ) ^ 2 * (Fintype.card V : ℝ) ≤
            (G.edgeSet.ncard : ℝ) →
          ContainsCliqueSubdivision G r :=
  erdos718

end Erdos718
