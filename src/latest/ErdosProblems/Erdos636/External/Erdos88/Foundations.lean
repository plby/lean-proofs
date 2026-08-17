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

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 88: foundational definitions

This file fixes the exact finite-graph predicates and elementary bookkeeping
used by the formalization of Erdős Problem 88.
-/

open SimpleGraph

namespace Erdos88

universe u

/-- A graph on `Fin n` has no homogeneous set of size at least
`ε * log n`, with `log` the natural logarithm.  A homogeneous set is either
a clique or an independent set. -/
def HomogeneousFree {n : ℕ} (ε : ℝ) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ S : Finset (Fin n),
    (G.IsClique (S : Set (Fin n)) ∨ G.IsIndepSet (S : Set (Fin n))) →
      (S.card : ℝ) < ε * Real.log n

/-- The base-two version of `HomogeneousFree`, matching the `C`-Ramsey
terminology in Kwan--Sah--Sauermann--Sawhney. -/
def RamseyFree {n : ℕ} (C : ℝ) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ S : Finset (Fin n),
    (G.IsClique (S : Set (Fin n)) ∨ G.IsIndepSet (S : Set (Fin n))) →
      (S.card : ℝ) < C * Real.logb 2 n

/-- The number of edges of `G` having both endpoints in `S`. -/
noncomputable def inducedEdges {V : Type u} [Fintype V]
    (G : SimpleGraph V) (S : Finset V) : ℕ :=
  Nat.card (G.induce (S : Set V)).edgeSet

@[simp] lemma inducedEdges_empty {V : Type u} [Fintype V]
    (G : SimpleGraph V) : inducedEdges G ∅ = 0 := by
  classical
  have hbot : G.induce ((↑(∅ : Finset V) : Set V)) = ⊥ := by
    rw [SimpleGraph.eq_bot_iff_forall_not_adj]
    intro x _y _hxy
    simpa using x.property
  rw [inducedEdges, hbot]
  simp

/-- `inducedEdges` is exactly the edge count of Mathlib's induced graph. -/
lemma inducedEdges_eq_card_edgeFinset_induce {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    inducedEdges G S = (G.induce (S : Set V)).edgeFinset.card := by
  classical
  rw [inducedEdges, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]

/-- The induced-edge count is also the cardinality of the edge finset
filtered by the condition that both endpoints lie in `S`. -/
lemma inducedEdges_eq_card_filter {V : Type u} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) :
    inducedEdges G S =
      (G.edgeFinset.filter fun e ↦ e.toFinset ⊆ S).card := by
  rw [inducedEdges_eq_card_edgeFinset_induce]
  exact (G.card_filter_edgeFinset_toFinset_subset S).symm

@[simp] lemma inducedEdges_univ {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    inducedEdges G Finset.univ = G.edgeFinset.card := by
  classical
  rw [inducedEdges, SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
  have hU : (↑(Finset.univ : Finset V) : Set V) = Set.univ := by ext; simp
  rw [hU]
  exact Nat.card_congr G.induceUnivIso.mapEdgeSet

/-- A clique in an induced graph is the same clique after forgetting the
subtype proof. -/
lemma isClique_induce_iff {V : Type u} (G : SimpleGraph V) {U : Set V}
    {T : Set U} :
    (G.induce U).IsClique T ↔ G.IsClique (Subtype.val '' T) :=
  SimpleGraph.isClique_induce_iff

/-- An independent set in an induced graph is the same independent set after
forgetting the subtype proof. -/
lemma isIndepSet_induce_iff {V : Type u} (G : SimpleGraph V) {U : Set V}
    {T : Set U} :
    (G.induce U).IsIndepSet T ↔ G.IsIndepSet (Subtype.val '' T) := by
  constructor
  · intro h x hx y hy hxy
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    exact h hx hy (fun hxy' ↦ hxy (congrArg Subtype.val hxy'))
  · intro h x hx y hy hxy
    exact h ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ (fun hxy' ↦ hxy (Subtype.ext hxy'))

/-- Inducing commutes with graph complementation. -/
@[simp] lemma induce_compl {V : Type u} (G : SimpleGraph V) (U : Set V) :
    Gᶜ.induce U = (G.induce U)ᶜ := by
  ext x y
  simp only [SimpleGraph.induce_adj, SimpleGraph.compl_adj]
  exact and_congr (not_congr Subtype.val_injective.eq_iff) Iff.rfl

/-- The natural-log homogeneous-set condition is invariant under graph
complementation. -/
@[simp] lemma homogeneousFree_compl {n : ℕ} {ε : ℝ}
    (G : SimpleGraph (Fin n)) : HomogeneousFree ε Gᶜ ↔ HomogeneousFree ε G := by
  simp only [HomogeneousFree, G.isClique_compl, G.isIndepSet_compl]
  aesop

/-- The base-two Ramsey condition is invariant under graph complementation. -/
@[simp] lemma ramseyFree_compl {n : ℕ} {C : ℝ}
    (G : SimpleGraph (Fin n)) : RamseyFree C Gᶜ ↔ RamseyFree C G := by
  simp only [RamseyFree, G.isClique_compl, G.isIndepSet_compl]
  aesop

/-- Exact conversion between the natural logarithm and the base-two logarithm. -/
lemma log_mul_logb_two (x : ℝ) : Real.log 2 * Real.logb 2 x = Real.log x := by
  rw [← Real.log_div_log]
  field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]

/-- The threshold used in `HomogeneousFree` is exactly the KSSS base-two
threshold with constant `ε * log 2`. -/
lemma mul_logb_two_eq_mul_log (ε x : ℝ) :
    (ε * Real.log 2) * Real.logb 2 x = ε * Real.log x := by
  rw [mul_assoc, log_mul_logb_two]

/-- The natural-log and base-two formulations of the homogeneous-set
condition are definitionally equivalent after rescaling the constant. -/
lemma homogeneousFree_iff_ramseyFree {n : ℕ} (ε : ℝ)
    (G : SimpleGraph (Fin n)) :
    HomogeneousFree ε G ↔ RamseyFree (ε * Real.log 2) G := by
  simp only [HomogeneousFree, RamseyFree, mul_logb_two_eq_mul_log]

@[simp] lemma card_fin (n : ℕ) : Fintype.card (Fin n) = n := Fintype.card_fin n

/-- A finset and its corresponding subtype have the same cardinality. -/
lemma card_subtype_coe_finset {V : Type u} (S : Finset V) :
    Fintype.card (S : Set V) = S.card := by
  simp

/-- Forgetting subtype proofs preserves the cardinality of a finite set. -/
lemma card_image_subtype_val {V : Type u} [DecidableEq V] {U : Set V} (T : Finset U) :
    (T.image Subtype.val).card = T.card := by
  exact Finset.card_image_of_injective T Subtype.val_injective

end Erdos88
