/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Set.Card

/-!
# Erdős Problem 182: foundational definitions

This file gives the literal finite-graph formulation of the problem and the
associated extremal number.  In particular, a regular subgraph is not required
to be induced or spanning, but it is required to have at least one vertex.
-/

open Finset Fintype
open scoped Classical

namespace Erdos182

/-- `ContainsRegularSubgraph G k` means that `G` has a nonempty (not
necessarily induced or spanning) subgraph all of whose vertices have degree
exactly `k` inside that subgraph. -/
def ContainsRegularSubgraph {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ H : G.Subgraph, H.verts.Nonempty ∧
    ∀ v : H.verts, (H.coe.neighborSet v).ncard = k

/-- A graph is `k`-regular-subgraph-free if it has no nonempty `k`-regular
subgraph. -/
def IsRegularSubgraphFree {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) : Prop :=
  ¬ ContainsRegularSubgraph G k

/-- The finite set of labelled `k`-regular-subgraph-free graphs on `n`
vertices. -/
noncomputable def regularSubgraphFreeGraphs (n k : ℕ) :
    Finset (SimpleGraph (Fin n)) :=
  open scoped Classical in
  Finset.univ.filter fun G ↦ IsRegularSubgraphFree G k

/-- The maximum number of edges in a graph on `n` labelled vertices which
contains no nonempty `k`-regular subgraph.

When no such graph exists the finite supremum has its standard value `0`.
For the range of Erdős Problem 182 (`k ≥ 3`) the admissible family is
nonempty; see `regularSubgraphFreeGraphs_nonempty`. -/
noncomputable def regularExtremalNumber (n k : ℕ) : ℕ :=
  open scoped Classical in
  (regularSubgraphFreeGraphs n k).sup fun G ↦ G.edgeFinset.card

@[simp]
lemma mem_regularSubgraphFreeGraphs {n k : ℕ} {G : SimpleGraph (Fin n)} :
    G ∈ regularSubgraphFreeGraphs n k ↔ IsRegularSubgraphFree G k := by
  classical
  simp [regularSubgraphFreeGraphs]

lemma bot_isRegularSubgraphFree {V : Type*} [Fintype V] {k : ℕ} (hk : 0 < k) :
    IsRegularSubgraphFree (⊥ : SimpleGraph V) k := by
  rintro ⟨H, hHne, hHreg⟩
  obtain ⟨v, hv⟩ := hHne
  let v' : H.verts := ⟨v, hv⟩
  have hneighbors : H.coe.neighborSet v' = ∅ := by
    ext w
    constructor
    · intro hw
      have : False := by
        simpa using (H.coe_adj_sub v' w hw : (⊥ : SimpleGraph V).Adj v' w)
      exact this.elim
    · simp
  have hzero : (H.coe.neighborSet v').ncard = 0 := by
    rw [hneighbors]
    simp
  exact (Nat.ne_of_gt hk) ((hHreg v').symm.trans hzero)

lemma regularSubgraphFreeGraphs_nonempty {n k : ℕ} (hk : 0 < k) :
    (regularSubgraphFreeGraphs n k).Nonempty := by
  classical
  exact ⟨⊥, mem_regularSubgraphFreeGraphs.mpr (bot_isRegularSubgraphFree hk)⟩

/-- Every admissible labelled graph has at most the extremal number of edges. -/
lemma card_edgeFinset_le_regularExtremalNumber {n k : ℕ}
    (G : SimpleGraph (Fin n)) (hG : IsRegularSubgraphFree G k) :
    G.edgeFinset.card ≤ regularExtremalNumber n k := by
  classical
  exact Finset.le_sup (f := fun H : SimpleGraph (Fin n) ↦ H.edgeFinset.card)
    (mem_regularSubgraphFreeGraphs.mpr hG)

/-- The extremal number never exceeds the number of edges in the complete
graph. -/
lemma regularExtremalNumber_le_choose (n k : ℕ) :
    regularExtremalNumber n k ≤ n.choose 2 := by
  classical
  rw [regularExtremalNumber, Finset.sup_le_iff]
  intro G _
  simpa using G.card_edgeFinset_le_card_choose_two

/-- The extremal number is at most `m` exactly when every admissible labelled
graph has at most `m` edges. -/
lemma regularExtremalNumber_le_iff {n k m : ℕ} :
    regularExtremalNumber n k ≤ m ↔
      ∀ G : SimpleGraph (Fin n), IsRegularSubgraphFree G k → G.edgeFinset.card ≤ m := by
  classical
  simp only [regularExtremalNumber, Finset.sup_le_iff]
  constructor
  · intro h G hG
    exact h G (mem_regularSubgraphFreeGraphs.mpr hG)
  · intro h G hG
    exact h G (mem_regularSubgraphFreeGraphs.mp hG)

/-- A strict lower bound for the extremal number is witnessed by an admissible
labelled graph.  The positivity assumption is precisely what guarantees that
the admissible family is nonempty. -/
lemma lt_regularExtremalNumber_iff {n k m : ℕ} (hk : 0 < k) :
    m < regularExtremalNumber n k ↔
      ∃ G : SimpleGraph (Fin n),
        IsRegularSubgraphFree G k ∧ m < G.edgeFinset.card := by
  classical
  constructor
  · intro hm
    obtain ⟨G, hGmem, hGcard⟩ := Finset.exists_mem_eq_sup
      (regularSubgraphFreeGraphs n k) (regularSubgraphFreeGraphs_nonempty hk)
      (fun H : SimpleGraph (Fin n) ↦ H.edgeFinset.card)
    exact ⟨G, mem_regularSubgraphFreeGraphs.mp hGmem,
      hGcard ▸ hm⟩
  · rintro ⟨G, hG, hm⟩
    exact hm.trans_le (card_edgeFinset_le_regularExtremalNumber G hG)

/-- A graph realizes the extremal number for avoiding nonempty `k`-regular
subgraphs. -/
noncomputable def IsRegularExtremal {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) : Prop :=
  IsRegularSubgraphFree G k ∧
    ∀ H : SimpleGraph V, IsRegularSubgraphFree H k →
      H.edgeFinset.card ≤ G.edgeFinset.card

/-- For every positive target degree, the finite maximum is attained. -/
lemma exists_regularExtremalGraph (n k : ℕ) (hk : 0 < k) :
    ∃ G : SimpleGraph (Fin n),
      IsRegularSubgraphFree G k ∧
      G.edgeFinset.card = regularExtremalNumber n k := by
  classical
  obtain ⟨G, hGmem, hGcard⟩ := Finset.exists_mem_eq_sup
    (regularSubgraphFreeGraphs n k) (regularSubgraphFreeGraphs_nonempty hk)
    (fun H : SimpleGraph (Fin n) ↦ H.edgeFinset.card)
  exact ⟨G, mem_regularSubgraphFreeGraphs.mp hGmem, hGcard.symm⟩

/-- A chosen labelled extremizer.  The proof of `0 < k` is an argument because
for degree zero and a nonempty vertex set there is no admissible graph. -/
noncomputable def regularExtremalGraph (n k : ℕ) (hk : 0 < k) :
    SimpleGraph (Fin n) :=
  Classical.choose (exists_regularExtremalGraph n k hk)

lemma regularExtremalGraph_isRegularSubgraphFree (n k : ℕ) (hk : 0 < k) :
    IsRegularSubgraphFree (regularExtremalGraph n k hk) k :=
  (Classical.choose_spec (exists_regularExtremalGraph n k hk)).1

lemma regularExtremalGraph_card_edgeFinset (n k : ℕ) (hk : 0 < k) :
    (regularExtremalGraph n k hk).edgeFinset.card = regularExtremalNumber n k :=
  (Classical.choose_spec (exists_regularExtremalGraph n k hk)).2

lemma regularExtremalGraph_isRegularExtremal (n k : ℕ) (hk : 0 < k) :
    IsRegularExtremal (regularExtremalGraph n k hk) k := by
  refine ⟨regularExtremalGraph_isRegularSubgraphFree n k hk, ?_⟩
  intro H hH
  rw [regularExtremalGraph_card_edgeFinset n k hk]
  exact card_edgeFinset_le_regularExtremalNumber H hH

/-- Characterization of extremizers on the canonical labelled vertex set. -/
lemma isRegularExtremal_iff {n k : ℕ} {G : SimpleGraph (Fin n)}
    (hk : 0 < k) :
    IsRegularExtremal G k ↔
      IsRegularSubgraphFree G k ∧
        G.edgeFinset.card = regularExtremalNumber n k := by
  constructor
  · intro hG
    refine ⟨hG.1, le_antisymm
      (card_edgeFinset_le_regularExtremalNumber G hG.1) ?_⟩
    rw [← regularExtremalGraph_card_edgeFinset n k hk]
    exact hG.2 _ (regularExtremalGraph_isRegularSubgraphFree n k hk)
  · rintro ⟨hGfree, hGcard⟩
    refine ⟨hGfree, ?_⟩
    intro H hH
    rw [hGcard]
    exact card_edgeFinset_le_regularExtremalNumber H hH

/-- The exact specification of the finite maximum: it is attained and bounds
every admissible graph. -/
lemma regularExtremalNumber_spec (n k : ℕ) (hk : 0 < k) :
    (∃ G : SimpleGraph (Fin n),
      IsRegularSubgraphFree G k ∧ G.edgeFinset.card = regularExtremalNumber n k) ∧
    (∀ G : SimpleGraph (Fin n), IsRegularSubgraphFree G k →
      G.edgeFinset.card ≤ regularExtremalNumber n k) := by
  exact ⟨exists_regularExtremalGraph n k hk,
    fun G hG ↦ card_edgeFinset_le_regularExtremalNumber G hG⟩

/-- Crossing the extremal number forces a regular subgraph. -/
lemma containsRegularSubgraph_of_regularExtremalNumber_lt {n k : ℕ}
    (G : SimpleGraph (Fin n))
    (hG : regularExtremalNumber n k < G.edgeFinset.card) :
    ContainsRegularSubgraph G k := by
  by_contra hfree
  exact (Nat.not_lt_of_ge
    (card_edgeFinset_le_regularExtremalNumber G hfree)) hG

/-- Exact threshold formulation: for positive `k`, every labelled graph with
at least `m` edges contains a nonempty `k`-regular subgraph exactly when `m`
is strictly larger than the extremal number. -/
lemma regularExtremalNumber_lt_iff_forall_contains {n k m : ℕ} (hk : 0 < k) :
    regularExtremalNumber n k < m ↔
      ∀ G : SimpleGraph (Fin n), m ≤ G.edgeFinset.card →
        ContainsRegularSubgraph G k := by
  constructor
  · intro hExt G hEdges
    apply containsRegularSubgraph_of_regularExtremalNumber_lt G
    exact hExt.trans_le hEdges
  · intro hGuarantee
    by_contra hnot
    have hm : m ≤ regularExtremalNumber n k := Nat.le_of_not_gt hnot
    let G := regularExtremalGraph n k hk
    have hContains : ContainsRegularSubgraph G k := by
      apply hGuarantee G
      simpa [G, regularExtremalGraph_card_edgeFinset n k hk] using hm
    exact (regularExtremalGraph_isRegularSubgraphFree n k hk) hContains

end Erdos182
