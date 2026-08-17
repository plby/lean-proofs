/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

/-!
# Cyclic subsets for Erdős Problem 622

This file fixes the exact finite predicate and the uniform asymptotic target
used in the formalization of Erdős Problem 622.  A subset is cyclic when it is
the vertex set of an ordinary simple cycle; in particular, subsets with fewer
than three vertices are not cyclic.  This differs at one point from Mathlib's
graph-level `SimpleGraph.IsHamiltonian`, which regards a singleton graph as
Hamiltonian by convention.
-/

open Filter

namespace Erdos622

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A vertex subset is spanned by a cycle when its induced graph has a
Hamiltonian cycle in the ordinary, length-at-least-three sense.  The cycle may
have chords: it need not be an induced cycle. -/
def IsSpannedByCycle (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∃ v : (S : Set V), ∃ p : (G.induce (S : Set V)).Walk v v,
    p.IsHamiltonianCycle

/-- The finite family of all subsets of the vertex set that are spanned by a
cycle. -/
noncomputable def cycleSpannedSubsets (G : SimpleGraph V) : Finset (Finset V) :=
  (Finset.univ : Finset V).powerset.filter (IsSpannedByCycle G)

/-- The uniform epsilon formulation of the asymptotically sharp affirmative
answer to Erdős Problem 622. -/
def Resolution : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    ∀ G : SimpleGraph (Fin (2 * n)),
      G.IsRegularOfDegree (n + 1) →
        ((1 / 2 : ℝ) - ε) * (2 : ℝ) ^ (2 * n) ≤
          ((cycleSpannedSubsets G).card : ℝ)

@[simp] theorem mem_cycleSpannedSubsets {G : SimpleGraph V} {S : Finset V} :
    S ∈ cycleSpannedSubsets G ↔ IsSpannedByCycle G S := by
  simp [cycleSpannedSubsets]

omit [DecidableEq V] in
theorem card_all_vertex_subsets :
    ((Finset.univ : Finset V).powerset).card = 2 ^ Fintype.card V := by
  simp

theorem cycleSpannedSubsets_subset_powerset (G : SimpleGraph V) :
    cycleSpannedSubsets G ⊆ (Finset.univ : Finset V).powerset := by
  intro S hS
  exact (Finset.mem_filter.mp hS).1

theorem card_cycleSpannedSubsets_le (G : SimpleGraph V) :
    (cycleSpannedSubsets G).card ≤ 2 ^ Fintype.card V := by
  calc
    (cycleSpannedSubsets G).card ≤ ((Finset.univ : Finset V).powerset).card :=
      Finset.card_le_card (cycleSpannedSubsets_subset_powerset G)
    _ = 2 ^ Fintype.card V := card_all_vertex_subsets

omit [Fintype V] in
theorem IsSpannedByCycle.card_three_le {G : SimpleGraph V} {S : Finset V}
    (hS : IsSpannedByCycle G S) : 3 ≤ S.card := by
  obtain ⟨v, p, hp⟩ := hS
  have hlen : p.length = S.card := by
    simpa using hp.length_eq
  exact hlen ▸ hp.three_le_length

omit [Fintype V] in
theorem not_isSpannedByCycle_of_card_lt_three {G : SimpleGraph V} {S : Finset V}
    (hS : S.card < 3) : ¬ IsSpannedByCycle G S := by
  intro hcycle
  have := IsSpannedByCycle.card_three_le hcycle
  omega

omit [Fintype V] in
@[simp] theorem not_isSpannedByCycle_empty (G : SimpleGraph V) :
    ¬ IsSpannedByCycle G ∅ := by
  exact not_isSpannedByCycle_of_card_lt_three (by simp)

omit [Fintype V] in
@[simp] theorem not_isSpannedByCycle_singleton (G : SimpleGraph V) (v : V) :
    ¬ IsSpannedByCycle G {v} := by
  exact not_isSpannedByCycle_of_card_lt_three (by simp)

omit [Fintype V] in
theorem not_isSpannedByCycle_pair (G : SimpleGraph V) (u v : V) :
    ¬ IsSpannedByCycle G {u, v} := by
  apply not_isSpannedByCycle_of_card_lt_three
  have hcard : ({u, v} : Finset V).card ≤ 2 := by
    simpa [Finset.pair_comm] using Finset.card_insert_le v {u}
  omega

omit [Fintype V] in
theorem isSpannedByCycle_iff_isHamiltonian {G : SimpleGraph V} {S : Finset V}
    (hS : 3 ≤ S.card) :
    IsSpannedByCycle G S ↔ (G.induce (S : Set V)).IsHamiltonian := by
  constructor
  · rintro ⟨v, p, hp⟩ _
    exact ⟨v, p, hp⟩
  · intro hham
    have hcard : Fintype.card (S : Set V) ≠ 1 := by
      simpa using (show S.card ≠ 1 by omega)
    exact hham hcard

section Relabel

variable {W : Type*} [Fintype W] [DecidableEq W]

omit [Fintype V] [Fintype W] in
/-- Relabelling the vertices of both the graph and the chosen subset preserves
the property of being exactly spanned by a cycle. -/
theorem isSpannedByCycle_map_iff {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) (S : Finset V) :
    IsSpannedByCycle G S ↔
      IsSpannedByCycle H (S.map f.toEquiv.toEmbedding) := by
  have hcoe :
      (↑(S.map f.toEquiv.toEmbedding) : Set W) =
        f '' (↑S : Set V) :=
    Finset.coe_map _ _
  have hbij :
      Set.BijOn f (↑S : Set V) (↑(S.map f.toEquiv.toEmbedding) : Set W) := by
    rw [hcoe]
    exact f.injective.bijOn_image
  let fi : G.induce (S : Set V) ≃g
      H.induce (S.map f.toEquiv.toEmbedding : Set W) :=
    f.induce hbij
  constructor
  · rintro ⟨v, p, hp⟩
    exact ⟨fi v, p.map fi.toHom, hp.map fi.bijective⟩
  · rintro ⟨v, p, hp⟩
    exact ⟨fi.symm v, p.map fi.symm.toHom, hp.map fi.symm.bijective⟩

/-- The number of cyclic subsets is invariant under graph isomorphism. -/
theorem card_cycleSpannedSubsets_congr {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) :
    (cycleSpannedSubsets G).card = (cycleSpannedSubsets H).card := by
  let e : Finset V ≃ Finset W := f.toEquiv.finsetCongr
  have he : ∀ S : Finset V,
      S ∈ cycleSpannedSubsets G ↔ e S ∈ cycleSpannedSubsets H := by
    intro S
    rw [mem_cycleSpannedSubsets, mem_cycleSpannedSubsets]
    exact isSpannedByCycle_map_iff f S
  have hcard := Fintype.card_congr (e.subtypeEquiv he)
  simpa only [Fintype.card_coe] using hcard

end Relabel

end Erdos622
