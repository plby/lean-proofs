/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos110

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

theorem not_erdos_110 :
    ¬ ∃ F : ℕ → ℕ, HasUniformBound F := by
  sorry

end Erdos110
