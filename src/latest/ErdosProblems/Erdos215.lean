/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 215.
https://www.erdosproblems.com/forum/thread/215

Informal authors:
- Steve Jackson
- R. Daniel Mauldin

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos215.md
-/
import ErdosProblems.Erdos215.FinalAssembly
import ErdosProblems.Erdos215.SelectorPrimeExtensionFinal

/-!
# Erdős Problem 215

Jackson and Mauldin proved in ZFC that there is a subset of the Euclidean
plane meeting every translated and rotated copy of `ℤ²` in exactly one point.
The internal construction establishes their stronger partial-Steinhaus
statement; `erdos215_of_jmStrong` performs the exact final conversion.
-/

namespace Erdos215

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- The stronger Jackson--Mauldin conclusion used by the construction. -/
def JMStrong : Prop :=
  ∃ S : Set Point, IsPartialSteinhaus S ∧ HitsEveryLattice S

/-- The strong Jackson--Mauldin statement implies the literal formulation of
Erdős Problem 215. -/
theorem erdos215_of_jmStrong (h : JMStrong) : ∃ S : Set Point, IsSteinhaus S := by
  rcases h with ⟨S, hpartial, hhits⟩
  exact ⟨S, isSteinhaus_of_partial_of_hits hpartial hhits⟩

/-- The Jackson--Mauldin partial-Steinhaus set meeting every oriented
integer lattice. -/
theorem jmStrong : JMStrong :=
  exists_partial_hitsEveryLattice_of_literalPrimeExtension
    Selector.PrimeExtension.literalPrimeExtension

/-- Positive resolution of Erdős Problem 215 (Steinhaus's lattice-copy
problem): a planar set meets every translated and rotated copy of `ℤ²` in
exactly one point. -/
theorem erdos215 : ∃ S : Set Point, IsSteinhaus S :=
  erdos215_of_jmStrong jmStrong

end

end Erdos215
