/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/
import ErdosProblems.Erdos58.Critical
import ErdosProblems.Erdos58.Linkage
import Mathlib.Tactic

/-!
# Compatibility between the two connectivity interfaces for Erdős 58

The critical-subgraph construction does not include a redundant vertex-card
bound in its definition.  The cycle argument does.  At the positive degree
threshold of Gyárfás's theorem, the missing bound follows immediately from
`degree_lt_card_verts`.
-/

namespace Erdos58.Structural

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A positive structural minimum-degree bound implies that the vertex type
has at least three elements. -/
theorem card_three_le_of_minDegree' {j : ℕ} (hj : 0 < j) [Nonempty V]
    (hdegree : ∀ v : V, 2 * j + 1 ≤ G.degree v) :
    3 ≤ Fintype.card V := by
  let v : V := Classical.choice (inferInstance : Nonempty V)
  have hlt : G.degree v < Fintype.card V := G.degree_lt_card_verts v
  have hle := hdegree v
  omega

/-- The connectivity conclusion of `Critical.vertexTwoConnected`, converted
to the interface used by the longest-cycle proof. -/
theorem twoConnected_of_vertexTwoConnected_minDegree {j : ℕ} (hj : 0 < j)
    (hconn : Critical.VertexTwoConnected G)
    (hdegree : ∀ v : V, 2 * j + 1 ≤ G.degree v) :
    TwoConnected G := by
  letI : Nonempty V := hconn.1.nonempty
  refine ⟨card_three_le_of_minDegree' G hj hdegree, hconn.1, ?_⟩
  intro v
  let e : {w : V // w ≠ v} ≃ ({v}ᶜ : Set V) :=
    { toFun := fun w ↦ ⟨w.1, by
        intro hw
        exact w.property (by simpa using hw)⟩
      invFun := fun w ↦ ⟨w.1, by
        intro hw
        apply w.property
        simp [hw]⟩
      left_inv := fun w ↦ by ext; rfl
      right_inv := fun w ↦ by ext; rfl }
  let ge : Critical.deleteVertex G v ≃g G.induce ({v}ᶜ : Set V) :=
    { __ := e
      map_rel_iff' := by
        rintro ⟨a, ha⟩ ⟨b, hb⟩
        rfl }
  exact ge.connected_iff.mp (hconn.2 v)

end Erdos58.Structural
