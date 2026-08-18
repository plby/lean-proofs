/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib

/-!
# Erdős Problem 136: the exact finite colouring problem

This file defines the Erdős--Gyárfás function `f(n, 4, 5)` using Mathlib's
edge type for a complete simple graph.  Thus a colouring assigns colours
only to genuine unordered edges (and never to diagonal pairs).
-/

namespace Erdos136

open Finset

attribute [local instance] Classical.propDecidable

/-- A complete-graph edge colouring is a `(4,5)`-colouring if the six edges
of every embedded copy of `K₄` receive at least five distinct colours. -/
def Is45Coloring {n k : ℕ}
    (C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k)) : Prop :=
  ∀ v : Fin 4 ↪ Fin n,
    5 ≤ (Finset.univ.image (C.pullback v)).card

/-- `Kₙ` admits a `(4,5)`-colouring whose palette has `k` colours. -/
def Colorable (n k : ℕ) : Prop :=
  ∃ C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k), Is45Coloring C

/-- Some finite palette always suffices: assign a different colour to every
edge of `Kₙ`. -/
theorem colorable_nonempty (n : ℕ) : ∃ k, Colorable n k := by
  let E : Type := (⊤ : SimpleGraph (Fin n)).edgeSet
  let C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin (Fintype.card E)) :=
    fun e ↦ Fintype.equivFin E e
  refine ⟨Fintype.card E, C, ?_⟩
  intro v
  let vg : (⊤ : SimpleGraph (Fin 4)) ↪g (⊤ : SimpleGraph (Fin n)) :=
    ⟨v, by simp⟩
  have hpull : Function.Injective (C.pullback v) := by
    intro e e' heq
    apply vg.mapEdgeSet.injective
    apply (Fintype.equivFin E).injective
    exact heq
  rw [Finset.card_image_of_injective _ hpull]
  rw [SimpleGraph.edgeSet_univ_card,
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  norm_num [Nat.choose]

/-- The function in Erdős Problem 136: the least palette size for which
`Kₙ` has a `(4,5)`-colouring. -/
noncomputable def erdos136Fun (n : ℕ) : ℕ :=
  Nat.find (colorable_nonempty n)

/-- The minimum palette size is itself attainable. -/
theorem erdos136Fun_spec (n : ℕ) : Colorable n (erdos136Fun n) :=
  Nat.find_spec (colorable_nonempty n)

/-- Any palette admitting a `(4,5)`-colouring has at least
`erdos136Fun n` colours. -/
theorem erdos136Fun_min {n k : ℕ} (h : Colorable n k) : erdos136Fun n ≤ k :=
  Nat.find_min' (colorable_nonempty n) h

end Erdos136
