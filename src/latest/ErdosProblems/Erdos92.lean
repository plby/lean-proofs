/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 92.
https://www.erdosproblems.com/forum/thread/92

Informal authors:
- L. Alpöge

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos92.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/92.lean
-/
import ErdosProblems.Erdos90b

/-!
# Erdős Problem 92: the unit-distance conjecture

The proposed uniform upper bound
`n ^ (1 + C / log (log n))` is false.  In fact, the imported constructive
theorem produces a counterexample above every prescribed cardinality
threshold, for every fixed positive `C`.
-/

syntax (name := answerSyntax92) "answer(" term ")" : term
macro_rules
  | `(answer($t)) => `($t)

namespace Erdos92

/-- A point of the Euclidean plane. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- The number of unordered pairs of distinct points of `P` at distance one. -/
noncomputable abbrev unitDistancePairs (P : Finset Point) : ℕ :=
  Erdos.unitDist P

/-- The literal uniform-constant formulation of the proposed upper bound:
there are `C > 0` and a threshold `N` such that every `n`-point planar set,
for every `n ≥ N`, has at most `n ^ (1 + C / log (log n))` unit-distance
pairs. -/
def UnitDistanceUpperBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ P : Finset Point, P.card = n →
      (unitDistancePairs P : ℝ) ≤
        (n : ℝ) ^ (1 + C / Real.log (Real.log n))

/-- Counterexamples exist above every cardinality threshold and for every
positive value of the constant in the proposed exponent. -/
theorem arbitrarily_large_counterexamples :
    ∀ C : ℝ, 0 < C → ∀ N : ℕ,
      ∃ (n : ℕ) (P : Finset Point),
        N ≤ n ∧ P.card = n ∧
          (n : ℝ) ^ (1 + C / Real.log (Real.log n)) <
            (unitDistancePairs P : ℝ) := by
  simpa only [unitDistancePairs, Erdos90b.unitDistancePairs] using
    Erdos90b.erdos_90b

/-- No uniform constant can make the proposed upper bound hold eventually. -/
theorem not_unitDistanceUpperBound : ¬ UnitDistanceUpperBound := by
  rintro ⟨C, hC, N, hupper⟩
  obtain ⟨n, P, hn, hcard, hlarge⟩ :=
    arbitrarily_large_counterexamples C hC N
  exact (not_lt_of_ge (hupper n hn P hcard)) hlarge

/-- Erdős Problem 92 has a negative answer. -/
theorem erdos_92 : answer(False) ↔ UnitDistanceUpperBound := by
  constructor
  · intro h
    exact h.elim
  · intro h
    exact (not_unitDistanceUpperBound h).elim

#print axioms Erdos92.erdos_92

end Erdos92
