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

import ErdosProblems.Erdos182.Codegree
import ErdosProblems.Erdos182.Roof

/-!
# Janzer--Sudakov codegree cleaning on active bipartite graphs

This file discharges the per-stage hypothesis of the ordered codegree-cleaning
algorithm from bipartite `K_{k,k}`-freeness and the integer KST power bound.  It
then transports the result across `Fintype.equivFin`, producing an ambient
`BipartiteGraph` subgraph supported on specified active vertex sets.
-/

namespace Erdos182

open scoped BigOperators Classical

namespace CodegreeCleaning

variable {n : ℕ} {B : Type*} [Fintype B] [DecidableEq B]

private def IsBadLater (F : EdgeSet n B) (D : ℕ) (u v : Fin n) : Prop :=
  u.val < v.val ∧ D < pairCodegree F u v

private def IsPivotNeighbor (F : EdgeSet n B) (u : Fin n) (b : B) : Prop :=
  (u, b) ∈ F

private theorem card_pivotNeighbor (F : EdgeSet n B) (u : Fin n) :
    Fintype.card {b : B // IsPivotNeighbor F u b} = rowCard F u.val := by
  classical
  let S := rightNeighbors (edgeRel F) u
  let e : {b : B // IsPivotNeighbor F u b} ≃ {b : B // b ∈ S} :=
    { toFun := fun b ↦ ⟨b.1, by
        dsimp [S, rightNeighbors]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.2⟩⟩
      invFun := fun b ↦ ⟨b.1, by
        dsimp [S, rightNeighbors] at b
        exact (Finset.mem_filter.mp b.2).2⟩
      left_inv := fun b ↦ by cases b; rfl
      right_inv := fun b ↦ by cases b; rfl }
  rw [rowCard_eq_rightNeighbors]
  calc
    Fintype.card {b : B // IsPivotNeighbor F u b} =
        Fintype.card {b : B // b ∈ S} := Fintype.card_congr e
    _ = S.card := Fintype.card_coe S
    _ = (rightNeighbors (edgeRel F) u).card := rfl

private theorem restricted_rightNeighbors_card
    (F : EdgeSet n B) (D : ℕ) (u : Fin n)
    (v : {v : Fin n // IsBadLater F D u v}) :
    (rightNeighbors
      (fun v : {v : Fin n // IsBadLater F D u v} ↦
        fun b : {b : B // IsPivotNeighbor F u b} ↦ (v.1, b.1) ∈ F) v).card =
      pairCodegree F u v.1 := by
  classical
  let L := rightNeighbors
    (fun v : {v : Fin n // IsBadLater F D u v} ↦
      fun b : {b : B // IsPivotNeighbor F u b} ↦ (v.1, b.1) ∈ F) v
  let R := (Finset.univ : Finset B).filter fun b ↦
    (u, b) ∈ F ∧ (v.1, b) ∈ F
  let f : {b // b ∈ L} → {b // b ∈ R} := fun b ↦
    ⟨b.1.1, by
      have hb := (Finset.mem_filter.mp b.2).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨b.1.2, hb⟩⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro b b' h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : {b // b ∈ R} ↦ z.1) h
    · intro b
      refine ⟨⟨⟨b.1, ?_⟩, ?_⟩, ?_⟩
      · exact (Finset.mem_filter.mp b.2).2.1
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp b.2).2.2⟩
      · apply Subtype.ext
        rfl
  change L.card = R.card
  simpa only [Fintype.card_coe] using Fintype.card_congr (Equiv.ofBijective f hf)

private theorem card_deleted_eq_restricted_edgeCount
    (F : EdgeSet n B) (D : ℕ) (u : Fin n) :
    (F \ eraseBadAt F D u).card =
      bipartiteEdgeCount
        (fun v : {v : Fin n // IsBadLater F D u v} ↦
          fun b : {b : B // IsPivotNeighbor F u b} ↦ (v.1, b.1) ∈ F) := by
  classical
  let X := F \ eraseBadAt F D u
  let R := Finset.univ.filter fun
    e : {v : Fin n // IsBadLater F D u v} ×
      {b : B // IsPivotNeighbor F u b} ↦ (e.1.1, e.2.1) ∈ F
  let f : {e // e ∈ X} → {e // e ∈ R} := fun e ↦
    ⟨⟨⟨e.1.1, by
          have heX := Finset.mem_sdiff.mp e.2
          have htriple : u.val < e.1.1.val ∧
              D < pairCodegree F u e.1.1 ∧ (u, e.1.2) ∈ F := by
            by_contra htriple
            exact heX.2 (Finset.mem_filter.mpr ⟨heX.1, htriple⟩)
          exact ⟨htriple.1, htriple.2.1⟩⟩,
        ⟨e.1.2, by
          have heX := Finset.mem_sdiff.mp e.2
          have htriple : u.val < e.1.1.val ∧
              D < pairCodegree F u e.1.1 ∧ (u, e.1.2) ∈ F := by
            by_contra htriple
            exact heX.2 (Finset.mem_filter.mpr ⟨heX.1, htriple⟩)
          exact htriple.2.2⟩⟩,
      by
        simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
        exact (Finset.mem_sdiff.mp e.2).1⟩
  have hf : Function.Bijective f := by
    constructor
    · intro e e' h
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg (fun z ↦ z.1.1)
          (congrArg Subtype.val h)
      · exact congrArg (fun z ↦ z.2.1)
          (congrArg Subtype.val h)
    · intro e
      refine ⟨⟨(e.1.1.1, e.1.2.1), ?_⟩, ?_⟩
      · apply Finset.mem_sdiff.mpr
        have heF : (e.1.1.1, e.1.2.1) ∈ F := by
          simpa only [R, Finset.mem_filter, Finset.mem_univ, true_and] using e.2
        refine ⟨heF, ?_⟩
        exact fun hkeep ↦ (Finset.mem_filter.mp hkeep).2
          ⟨e.1.1.2.1, e.1.1.2.2, e.1.2.2⟩
      · apply Subtype.ext
        apply Prod.ext <;> rfl
  change X.card = ∑ v : {v : Fin n // IsBadLater F D u v},
    (rightNeighbors
      (fun v : {v : Fin n // IsBadLater F D u v} ↦
        fun b : {b : B // IsPivotNeighbor F u b} ↦ (v.1, b.1) ∈ F) v).card
  have hR : R.card =
      ∑ v : {v : Fin n // IsBadLater F D u v},
        (rightNeighbors
          (fun v : {v : Fin n // IsBadLater F D u v} ↦
            fun b : {b : B // IsPivotNeighbor F u b} ↦ (v.1, b.1) ∈ F) v).card := by
    simp only [R, rightNeighbors, Finset.card_filter]
    rw [← Finset.univ_product_univ, Finset.sum_product]
  calc
    X.card = R.card := by
      simpa only [Fintype.card_coe] using Fintype.card_congr (Equiv.ofBijective f hf)
    _ = _ := hR

/-- The KST estimate supplies the deletion bound at one cleaning stage. -/
theorem deletedAt_le_mul_rowCard_of_isBipartiteKFree
    (E F : EdgeSet n B) (D k : ℕ) (u : Fin n)
    (hk : 0 < k) (hFE : F ⊆ E)
    (hfree : IsBipartiteKFree (edgeRel E) k)
    (hpow : k ^ (k + 1) * (rowCard F u.val) ^ (k - 1) ≤ (D + 1) ^ k) :
    (F \ eraseBadAt F D u).card ≤ k * rowCard F u.val := by
  classical
  let r := fun v : {v : Fin n // IsBadLater F D u v} ↦
    fun b : {b : B // IsPivotNeighbor F u b} ↦ (v.1, b.1) ∈ F
  have hfreeF : IsBipartiteKFree (edgeRel F) k :=
    hfree.mono fun a b hab ↦ hFE hab
  have hfreer : IsBipartiteKFree r k := by
    exact IsBipartiteKFree.restrict (edgeRel F) hfreeF
      (fun v : Fin n ↦ IsBadLater F D u v)
      (fun b : B ↦ IsPivotNeighbor F u b)
  have hmin : ∀ v : {v : Fin n // IsBadLater F D u v},
      D + 1 ≤ (rightNeighbors r v).card := by
    intro v
    rw [restricted_rightNeighbors_card F D u v]
    exact Nat.succ_le_iff.mpr v.2.2
  have hpow' : k ^ (k + 1) *
      Fintype.card {b : B // IsPivotNeighbor F u b} ^ (k - 1) ≤ (D + 1) ^ k := by
    simpa only [card_pivotNeighbor F u] using hpow
  have hkst := kst_edge_bound_of_minDegree_pow r hk hfreer hmin hpow'
  rw [card_deleted_eq_restricted_edgeCount F D u]
  simpa only [card_pivotNeighbor F u] using hkst

/-- Unconditional sequential codegree cleaning: its only numerical input is
the root-free KST power inequality at every pivot stage. -/
theorem sequential_codegree_cleaning_of_isBipartiteKFree
    (E : EdgeSet n B) (D k : ℕ) (hk : 0 < k)
    (hfree : IsBipartiteKFree (edgeRel E) k)
    (hpow : ∀ i (hi : i < n),
      k ^ (k + 1) * (rowCard (cleanSeq E D i) i) ^ (k - 1) ≤ (D + 1) ^ k) :
    ∃ E' : EdgeSet n B,
      E' ⊆ E ∧ E.card ≤ (k + 1) * E'.card ∧
      ∀ u v : Fin n, u ≠ v → pairCodegree E' u v ≤ D := by
  apply sequential_codegree_cleaning E D k
  intro i hi
  rw [cleanSeq]
  simp only [hi, dite_true]
  exact deletedAt_le_mul_rowCard_of_isBipartiteKFree
    E (cleanSeq E D i) D k ⟨i, hi⟩ hk
    (cleanSeq_antitone E D (Nat.zero_le i)) hfree (hpow i hi)

/-- Caller-chosen-cutoff form of Lemma 3.2.  A maximum row-degree bound
turns one KST power estimate into all the stagewise estimates. -/
theorem sequential_codegree_cleaning_of_maxDegree_pow
    (E : EdgeSet n B) (D k m : ℕ) (hk : 0 < k)
    (hfree : IsBipartiteKFree (edgeRel E) k)
    (hmax : ∀ u : Fin n, rowCard E u.val ≤ m)
    (hpow : k ^ (k + 1) * m ^ (k - 1) ≤ (D + 1) ^ k) :
    ∃ E' : EdgeSet n B,
      E' ⊆ E ∧ E.card ≤ (k + 1) * E'.card ∧
      ∀ u v : Fin n, u ≠ v → pairCodegree E' u v ≤ D := by
  apply sequential_codegree_cleaning_of_isBipartiteKFree E D k hk hfree
  intro i hi
  have hsub : cleanSeq E D i ⊆ E := cleanSeq_antitone E D (Nat.zero_le i)
  have hrow : rowCard (cleanSeq E D i) i ≤ m := by
    calc
      rowCard (cleanSeq E D i) i ≤ rowCard E i := by
        unfold rowCard
        apply Finset.card_le_card
        intro e he
        simp only [Finset.mem_filter] at he ⊢
        exact ⟨hsub he.1, he.2⟩
      _ ≤ m := hmax ⟨i, hi⟩
  exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hrow _)).trans hpow

end CodegreeCleaning

namespace BipartiteGraph

variable {A B : Type*} [Fintype A] [Fintype B]

/-- Encode an arbitrary finite left vertex type by `Fin (card A)`. -/
noncomputable def reindexedEdgeSet (G : BipartiteGraph A B) :
    CodegreeCleaning.EdgeSet (Fintype.card A) B := by
  classical
  exact Finset.univ.filter fun e ↦ G.Adj ((Fintype.equivFin A).symm e.1) e.2

@[simp] theorem mem_reindexedEdgeSet (G : BipartiteGraph A B)
    (i : Fin (Fintype.card A)) (b : B) :
    (i, b) ∈ G.reindexedEdgeSet ↔ G.Adj ((Fintype.equivFin A).symm i) b := by
  classical
  simp [reindexedEdgeSet]

/-- Decode an ordered edge set after reindexing the left class. -/
def ofReindexedEdgeSet
    (E : CodegreeCleaning.EdgeSet (Fintype.card A) B) : BipartiteGraph A B where
  Adj a b := ((Fintype.equivFin A) a, b) ∈ E

@[simp] theorem ofReindexedEdgeSet_adj
    (E : CodegreeCleaning.EdgeSet (Fintype.card A) B) (a : A) (b : B) :
    (ofReindexedEdgeSet E).Adj a b ↔ ((Fintype.equivFin A) a, b) ∈ E := Iff.rfl

theorem reindexedEdgeSet_ofReindexedEdgeSet
    (E : CodegreeCleaning.EdgeSet (Fintype.card A) B) :
    (ofReindexedEdgeSet E).reindexedEdgeSet = E := by
  classical
  apply Finset.ext
  intro e
  constructor
  · intro he
    have hp := (Finset.mem_filter.mp he).2
    change ((Fintype.equivFin A) ((Fintype.equivFin A).symm e.1), e.2) ∈ E at hp
    simpa only [Equiv.apply_symm_apply] using hp
  · intro he
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change ((Fintype.equivFin A) ((Fintype.equivFin A).symm e.1), e.2) ∈ E
    simpa only [Equiv.apply_symm_apply] using he

private theorem card_reindexedEdgeSet_eq_bipartiteEdgeCount
    (G : BipartiteGraph A B) :
    G.reindexedEdgeSet.card = bipartiteEdgeCount G.Adj := by
  classical
  let e := Fintype.equivFin A
  let S := G.reindexedEdgeSet
  let T := (Finset.univ : Finset (A × B)).filter fun z ↦ G.Adj z.1 z.2
  let f : {z // z ∈ S} → {z // z ∈ T} := fun z ↦
    ⟨(e.symm z.1.1, z.1.2), by
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa only [S, reindexedEdgeSet, Finset.mem_filter, Finset.mem_univ,
        true_and, e] using z.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro z z' h
      apply Subtype.ext
      apply Prod.ext
      · apply e.symm.injective
        exact congrArg (fun w ↦ w.1.1) h
      · exact congrArg (fun w ↦ w.1.2) h
    · intro z
      refine ⟨⟨(e z.1.1, z.1.2), ?_⟩, ?_⟩
      · simp only [S, reindexedEdgeSet, Finset.mem_filter, Finset.mem_univ,
          true_and, e, Equiv.symm_apply_apply]
        exact (Finset.mem_filter.mp z.2).2
      · apply Subtype.ext
        apply Prod.ext
        · exact e.symm_apply_apply z.1.1
        · rfl
  calc
    S.card = T.card := by
      simpa only [Fintype.card_coe] using
        Fintype.card_congr (Equiv.ofBijective f hf)
    _ = bipartiteEdgeCount G.Adj :=
      (CodegreeCleaning.bipartiteEdgeCount_eq_card_filter G.Adj).symm

private theorem edgeCount_eq_bipartiteEdgeCount (G : BipartiteGraph A B) :
    G.edgeCount = bipartiteEdgeCount G.Adj := by
  rw [bipartiteEdgeCount_eq_sum_left]
  rfl

theorem card_reindexedEdgeSet_eq_edgeCount (G : BipartiteGraph A B) :
    G.reindexedEdgeSet.card = G.edgeCount := by
  rw [card_reindexedEdgeSet_eq_bipartiteEdgeCount, edgeCount_eq_bipartiteEdgeCount]

theorem edgeCount_ofReindexedEdgeSet
    (E : CodegreeCleaning.EdgeSet (Fintype.card A) B) :
    (ofReindexedEdgeSet E).edgeCount = E.card := by
  rw [← card_reindexedEdgeSet_eq_edgeCount (ofReindexedEdgeSet E),
    reindexedEdgeSet_ofReindexedEdgeSet]

private theorem reindexed_isBipartiteKFree {G : BipartiteGraph A B} {k : ℕ}
    (hfree : IsBipartiteKFree G.Adj k) :
    IsBipartiteKFree
      (CodegreeCleaning.edgeRel G.reindexedEdgeSet) k := by
  classical
  intro s hs
  let e := Fintype.equivFin A
  let emb : Fin (Fintype.card A) ↪ A := e.symm.toEmbedding
  let S : Finset A := s.map emb
  have hScard : S.card = k := by simp [S, hs]
  have heq : commonRight
      (CodegreeCleaning.edgeRel G.reindexedEdgeSet) s = commonRight G.Adj S := by
    ext b
    simp only [commonRight, Finset.mem_filter, Finset.mem_univ, true_and,
      CodegreeCleaning.edgeRel, mem_reindexedEdgeSet, S, Finset.mem_map, emb]
    constructor
    · intro hb a ha
      obtain ⟨i, hi, rfl⟩ := ha
      exact hb i hi
    · intro hb i hi
      exact hb (e.symm i) ⟨i, hi, rfl⟩
  rw [heq]
  exact hfree S hScard

private theorem rowCard_reindexedEdgeSet
    (G : BipartiteGraph A B) (i : Fin (Fintype.card A)) :
    CodegreeCleaning.rowCard G.reindexedEdgeSet i.val =
      G.leftDegree ((Fintype.equivFin A).symm i) := by
  classical
  rw [CodegreeCleaning.rowCard_eq_rightNeighbors]
  unfold BipartiteGraph.leftDegree
  congr 1
  ext b
  simp only [Erdos182.rightNeighbors, BipartiteGraph.rightNeighbors,
    Finset.mem_filter, Finset.mem_univ, true_and, CodegreeCleaning.edgeRel,
    mem_reindexedEdgeSet]

/-- **Janzer--Sudakov Lemma 3.2 on active vertex sets.**

For a `K_{k,k}`-free bipartite graph supported on `A₀ × B₀` and of
maximum left degree at most `m`, this produces a subgraph retaining at least a
`1/(k+1)` fraction of the edges and having the KST codegree bound. -/
theorem exists_codegreeCleaning_active_of_pow
    (G : BipartiteGraph A B) (A₀ : Finset A) (B₀ : Finset B)
    (D k m : ℕ) (hk : 0 < k)
    (hsupport : G.SupportedOn A₀ B₀)
    (hfree : IsBipartiteKFree G.Adj k)
    (hmax : ∀ a ∈ A₀, G.leftDegree a ≤ m)
    (hpow : k ^ (k + 1) * m ^ (k - 1) ≤ (D + 1) ^ k) :
    ∃ H : BipartiteGraph A B,
      H ≤ G ∧ H.SupportedOn A₀ B₀ ∧
      G.edgeCount ≤ (k + 1) * H.edgeCount ∧
      ∀ u v : A, u ≠ v →
        ((Finset.univ : Finset B).filter fun b ↦ H.Adj u b ∧ H.Adj v b).card ≤ D := by
  classical
  let E := G.reindexedEdgeSet
  have hmaxE : ∀ i : Fin (Fintype.card A),
      CodegreeCleaning.rowCard E i.val ≤ m := by
    intro i
    rw [rowCard_reindexedEdgeSet]
    by_cases ha : (Fintype.equivFin A).symm i ∈ A₀
    · exact hmax _ ha
    · have hz : G.leftDegree ((Fintype.equivFin A).symm i) = 0 := by
        rw [leftDegree, Finset.card_eq_zero]
        apply Finset.not_nonempty_iff_eq_empty.mp
        rintro ⟨b, hb⟩
        exact ha (hsupport ((G.mem_rightNeighbors _ _).mp hb)).1
      simp [hz]
  obtain ⟨E', hsub, hcard, hcodeg⟩ :=
    CodegreeCleaning.sequential_codegree_cleaning_of_maxDegree_pow E D k m hk
      (reindexed_isBipartiteKFree hfree) hmaxE hpow
  let H : BipartiteGraph A B := ofReindexedEdgeSet E'
  refine ⟨H, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    have hmemE : ((Fintype.equivFin A) a, b) ∈ E := hsub hab
    simpa only [E, mem_reindexedEdgeSet, Equiv.symm_apply_apply] using hmemE
  · intro a b hab
    exact hsupport (show G.Adj a b from by
      have hmemE : ((Fintype.equivFin A) a, b) ∈ E := hsub hab
      simpa only [E, mem_reindexedEdgeSet, Equiv.symm_apply_apply] using hmemE)
  · simpa only [E, H, card_reindexedEdgeSet_eq_edgeCount,
      edgeCount_ofReindexedEdgeSet] using hcard
  · intro u v huv
    have huv' : (Fintype.equivFin A) u ≠ (Fintype.equivFin A) v :=
      (Fintype.equivFin A).injective.ne huv
    have hc := hcodeg (Fintype.equivFin A u) (Fintype.equivFin A v) huv'
    simpa only [CodegreeCleaning.pairCodegree, H, ofReindexedEdgeSet_adj] using hc

end BipartiteGraph

end Erdos182
