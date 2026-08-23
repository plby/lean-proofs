/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib

/-!
# Erdős Problem 110

There is no uniform eventual bound on the order of finite subgraphs of
prescribed chromatic number in graphs of chromatic number `ℵ₁`.

The mathematical construction and a lemma-by-lemma Leanization plan are in
`tex/110.tex`.
-/

open Filter Set

namespace Erdos110

noncomputable section

universe u

/-- Exact chromatic number `ℵ₁`: an `ω₁`-coloring exists, but a countable
coloring does not. -/
def IsAlephOneChromatic {V : Type u} (G : SimpleGraph V) : Prop :=
  Nonempty (G.Coloring (Set.Iio (Ordinal.omega.{0} 1))) ∧
    IsEmpty (G.Coloring ℕ)

/-- A graph together with its vertex type.  The universe is fixed only so
that the collection of graphs quantified over below is itself a Lean type. -/
structure BundledGraph where
  Vertex : Type 1
  graph : SimpleGraph Vertex

/-- `F` is the uniform bound proposed in Problem 110.  The subgraph is an
arbitrary (not necessarily induced) Mathlib subgraph, and finiteness is stated
explicitly because `Set.ncard` is zero on infinite sets. -/
def HasUniformBound (F : ℕ → ℕ) : Prop :=
  ∀ X : BundledGraph,
    IsAlephOneChromatic X.graph →
      ∀ᶠ n : ℕ in atTop,
        ∃ H : X.graph.Subgraph,
          H.verts.Finite ∧ H.verts.ncard ≤ F n ∧
            H.coe.chromaticNumber = n

/-- A graph witnessing failure of `F` at arbitrarily large chromatic
numbers.  This is exactly the pointwise negation needed for the eventual
quantifier in `HasUniformBound`. -/
def IsCounterexampleFor (F : ℕ → ℕ) (X : BundledGraph) : Prop :=
  IsAlephOneChromatic X.graph ∧
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∀ H : X.graph.Subgraph,
        H.verts.Finite → H.verts.ncard ≤ F n →
          H.coe.chromaticNumber ≠ n

/-- The quantitative conclusion of Lambie-Hanson's theorem, in the form
needed here.  Every finite subgraph on fewer than `f n` vertices has
chromatic number strictly below `n`, simultaneously for all `n ≥ 3`. -/
def HasSlowFiniteGrowth (f : ℕ → ℕ) (X : BundledGraph) : Prop :=
  IsAlephOneChromatic X.graph ∧
    ∀ n : ℕ, 3 ≤ n → ∀ H : X.graph.Subgraph,
      H.verts.Finite → H.verts.ncard < f n →
        H.coe.chromaticNumber < n

/-- An arbitrarily-late pointwise counterexample defeats an eventual uniform
bound. -/


theorem erdos_110 :
    ¬ ∃ F : ℕ → ℕ, HasUniformBound F := by
  sorry

end

end Erdos110
