/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of the negative resolution of Erdős Problem 591.
https://www.erdosproblems.com/591

The positive relation is due to Schipperus; the explicit negative
six-clique construction is the Hajnal--Larson handbook construction.
Larson's sharper negative five-clique relation is not needed here.

Formal authors: Codex
Detailed mathematical reconstruction and Leanization plan: tex/591.tex
-/
import ErdosProblems.Erdos591.PositiveEndpoint
import ErdosProblems.Erdos591.ExactDensity

/-!
# Erdős Problem 591

The implication from the red-copy/blue-triangle relation to all finite
blue-clique alternatives is false. The ordinal `omega^(omega^2)` satisfies
the positive relation for three, but not the relation for six.

`OrdinalCardinalRamsey`, imported from Problem 590, measures the red
clique by its exact order type and the blue clique by its cardinality.
-/

open Cardinal Ordinal

namespace Erdos591

/-- The explicit ordinal witnessing the negative answer. -/
noncomputable abbrev erdos591Ordinal : Ordinal.{0} := ω ^ (ω ^ 2)

/-- The exact positive/negative partition pair resolving Problem 591. -/
theorem erdos_591_counterexample :
    OrdinalCardinalRamsey erdos591Ordinal erdos591Ordinal (3 : Cardinal.{0}) ∧
      ¬ OrdinalCardinalRamsey erdos591Ordinal erdos591Ordinal (6 : Cardinal.{0}) :=
  ⟨schipperus_two, Negative.Exact.handbook_negative_six⟩

/-- **Erdős Problem 591: no.** The triangle alternative does not imply
the analogous relation for every finite blue clique. -/
theorem not_erdos_591 :
    ¬ ∀ α : Ordinal.{0}, OrdinalCardinalRamsey α α (3 : Cardinal.{0}) →
      ∀ n : ℕ, 3 ≤ n → OrdinalCardinalRamsey α α (n : Cardinal.{0}) := by
  intro h
  exact erdos_591_counterexample.2
    (h erdos591Ordinal erdos_591_counterexample.1 6 (by decide))

/-- Compatibility name for the negative resolution. -/
theorem erdos_591 :
    ¬ ∀ α : Ordinal.{0}, OrdinalCardinalRamsey α α (3 : Cardinal.{0}) →
      ∀ n : ℕ, 3 ≤ n → OrdinalCardinalRamsey α α (n : Cardinal.{0}) :=
  not_erdos_591

#print axioms erdos_591_counterexample
#print axioms not_erdos_591
#print axioms erdos_591

end Erdos591
