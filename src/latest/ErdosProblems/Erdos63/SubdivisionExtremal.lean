/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos63.Subdivision
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Preorder.Finite

/-!
# The skewed-bipartite subdivision lemma

This file formalizes Proposition 3.16 of Liu--Montgomery.  The proof takes a
maximal partial assignment of distinct vertices of `U` to ordered pairs of
vertices of `W`.  An unused vertex of `U` has a neighborhood `A` in `W`; the
maximality of the assignment says that every ordered pair from `A` has already
been assigned a distinct common neighbor.  Any `d` vertices of `A` are then
the core vertices of a copy of `oneSubdivisionClique d`.

The paper tacitly works with a nonempty large set `U`.  That condition is
included explicitly below: without it, the printed statement has the
degenerate counterexample `U = W = ∅` and `d > 0`.
-/

open Function
open scoped SimpleGraph

namespace Erdos63

variable {V : Type*}

/-- Candidate assignments `(p,u)`, where `p` is an ordered pair of distinct
vertices of `W` and `u ∈ U` is adjacent to both entries of `p`. -/
private def pairCandidates [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (U W : Finset V) : Finset ((V × V) × V) :=
  (W.offDiag ×ˢ U).filter fun z ↦ G.Adj z.2 z.1.1 ∧ G.Adj z.2 z.1.2

private lemma mem_pairCandidates [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (U W : Finset V) (p : V × V) (u : V) :
    (p, u) ∈ pairCandidates G U W ↔
      p ∈ W.offDiag ∧ u ∈ U ∧ G.Adj u p.1 ∧ G.Adj u p.2 := by
  simp [pairCandidates, and_assoc]

/-- A partial assignment is good when both projections are injective.  Thus a
pair receives at most one representative and a vertex represents at most one
pair. -/
private def GoodAssignment [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (U W : Finset V) (M : Finset ((V × V) × V)) : Prop :=
  M ⊆ pairCandidates G U W ∧
    Set.InjOn Prod.fst (M : Set ((V × V) × V)) ∧
      Set.InjOn Prod.snd (M : Set ((V × V) × V))

private lemma offDiag_card_lt_of_nonempty_right [DecidableEq V]
    (U W : Finset V) (hU : U.Nonempty) (hcard : W.card ^ 2 ≤ U.card) :
    W.offDiag.card < U.card := by
  rw [Finset.offDiag_card]
  by_cases hW : W.Nonempty
  · have hWpos : 0 < W.card := Finset.card_pos.mpr hW
    have hsq : W.card * W.card ≤ U.card := by
      simpa [pow_two] using hcard
    have hpred : W.card - 1 < W.card := Nat.sub_lt hWpos (by omega)
    have heq : W.card * W.card - W.card = W.card * (W.card - 1) := by
      simpa using (Nat.mul_sub_left_distrib W.card W.card 1).symm
    rw [heq]
    exact (Nat.mul_lt_mul_of_pos_left hpred hWpos).trans_le hsq
  · have hWzero : W.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hW)
    have hUpos : 0 < U.card := Finset.card_pos.mpr hU
    simp [hWzero, hUpos]

/-- Liu--Montgomery Proposition 3.16, with the necessary nonemptiness condition
made explicit. -/
theorem liuMontgomery_skewed_bipartite_subdivision [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U W : Finset V) (d : ℕ)
    (hUW : Disjoint U W) (hU : U.Nonempty)
    (hcard : W.card ^ 2 ≤ U.card)
    (hdeg : ∀ u ∈ U, d ≤ (W.filter fun w ↦ G.Adj u w).card) :
    oneSubdivisionClique d ⊑ G := by
  classical
  let goodSets : Finset (Finset ((V × V) × V)) :=
    (pairCandidates G U W).powerset.filter (GoodAssignment G U W)
  have hempty : (∅ : Finset ((V × V) × V)) ∈ goodSets := by
    simp [goodSets, GoodAssignment]
  obtain ⟨M, hMmax⟩ := goodSets.exists_maximal ⟨∅, hempty⟩
  have hMgood : GoodAssignment G U W M := by
    exact (Finset.mem_filter.mp hMmax.1).2

  have hfst_subset : M.image Prod.fst ⊆ W.offDiag := by
    intro p hp
    obtain ⟨z, hzM, rfl⟩ := Finset.mem_image.mp hp
    exact ((mem_pairCandidates G U W z.1 z.2).mp (hMgood.1 hzM)).1
  have hMcard_fst : (M.image Prod.fst).card = M.card :=
    Finset.card_image_of_injOn hMgood.2.1
  have hMcard_le : M.card ≤ W.offDiag.card := by
    rw [← hMcard_fst]
    exact Finset.card_le_card hfst_subset
  have hMcard_lt : M.card < U.card :=
    hMcard_le.trans_lt (offDiag_card_lt_of_nonempty_right U W hU hcard)

  let used : Finset V := M.image Prod.snd
  have hused_card : used.card = M.card := by
    exact Finset.card_image_of_injOn hMgood.2.2
  have hused_lt : used.card < U.card := by simpa [hused_card] using hMcard_lt
  obtain ⟨u, huU, huUnused⟩ := Finset.exists_mem_notMem_of_card_lt_card hused_lt

  let A : Finset V := W.filter fun w ↦ G.Adj u w
  have hAcard : d ≤ A.card := hdeg u huU

  have hrepresented : ∀ p ∈ A.offDiag, ∃ v, (p, v) ∈ M := by
    intro p hpA
    by_contra hnot
    push_neg at hnot
    have hpdata := Finset.mem_offDiag.mp hpA
    have hp1 := Finset.mem_filter.mp hpdata.1
    have hp2 := Finset.mem_filter.mp hpdata.2.1
    have hpW : p ∈ W.offDiag := Finset.mem_offDiag.mpr
      ⟨hp1.1, hp2.1, hpdata.2.2⟩
    have hzCand : (p, u) ∈ pairCandidates G U W :=
      (mem_pairCandidates G U W p u).mpr ⟨hpW, huU, hp1.2, hp2.2⟩
    have hgoodInsert : GoodAssignment G U W (insert (p, u) M) := by
      refine ⟨?_, ?_, ?_⟩
      · intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hzM
        · exact hzCand
        · exact hMgood.1 hzM
      · intro a ha b hb hab
        rcases Finset.mem_insert.mp ha with rfl | haM <;>
          rcases Finset.mem_insert.mp hb with rfl | hbM
        · rfl
        · exfalso
          apply hnot b.2
          convert hbM using 1
          exact Prod.ext hab rfl
        · exfalso
          apply hnot a.2
          convert haM using 1
          exact Prod.ext hab.symm rfl
        · exact hMgood.2.1 haM hbM hab
      · intro a ha b hb hab
        rcases Finset.mem_insert.mp ha with rfl | haM <;>
          rcases Finset.mem_insert.mp hb with rfl | hbM
        · rfl
        · exfalso
          apply huUnused
          exact Finset.mem_image.mpr ⟨b, hbM, hab.symm⟩
        · exfalso
          apply huUnused
          exact Finset.mem_image.mpr ⟨a, haM, hab⟩
        · exact hMgood.2.2 haM hbM hab
    have hinGood : insert (p, u) M ∈ goodSets := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_powerset.mpr hgoodInsert.1, hgoodInsert⟩
    have hback : insert (p, u) M ⊆ M :=
      hMmax.2 hinGood (Finset.subset_insert (p, u) M)
    exact hnot u (hback (Finset.mem_insert_self (p, u) M))

  obtain ⟨core, hcore_range⟩ : ∃ core : Fin d ↪ V, Set.range core ⊆ A := by
    apply Function.Embedding.exists_of_card_le_finset
    simpa using hAcard
  have hcoreA (i : Fin d) : core i ∈ A := hcore_range (Set.mem_range_self i)
  have hcoreW (i : Fin d) : core i ∈ W := (Finset.mem_filter.mp (hcoreA i)).1

  let edgePair : SubdivisionEdge d → V × V := fun e ↦
    (core e.1.1, core e.1.2)
  have hedgePairA (e : SubdivisionEdge d) : edgePair e ∈ A.offDiag := by
    apply Finset.mem_offDiag.mpr
    refine ⟨hcoreA e.1.1, hcoreA e.1.2, ?_⟩
    exact fun h ↦ ne_of_lt e.2 (core.injective h)

  let middle : SubdivisionEdge d → V := fun e ↦
    Classical.choose (hrepresented (edgePair e) (hedgePairA e))
  have hmiddleM (e : SubdivisionEdge d) : (edgePair e, middle e) ∈ M := by
    exact Classical.choose_spec (hrepresented (edgePair e) (hedgePairA e))
  have hmiddleCand (e : SubdivisionEdge d) :
      (edgePair e, middle e) ∈ pairCandidates G U W :=
    hMgood.1 (hmiddleM e)
  have hmiddleU (e : SubdivisionEdge d) : middle e ∈ U :=
    ((mem_pairCandidates G U W (edgePair e) (middle e)).mp (hmiddleCand e)).2.1
  have hmiddleAdjLeft (e : SubdivisionEdge d) :
      G.Adj (middle e) (core e.1.1) :=
    ((mem_pairCandidates G U W (edgePair e) (middle e)).mp (hmiddleCand e)).2.2.1
  have hmiddleAdjRight (e : SubdivisionEdge d) :
      G.Adj (middle e) (core e.1.2) :=
    ((mem_pairCandidates G U W (edgePair e) (middle e)).mp (hmiddleCand e)).2.2.2
  have hmiddle_injective : Injective middle := by
    intro e f hef
    have hpairs : edgePair e = edgePair f := congrArg Prod.fst
      (hMgood.2.2 (hmiddleM e) (hmiddleM f) hef)
    apply Subtype.ext
    apply Prod.ext
    · exact core.injective (congrArg Prod.fst hpairs)
    · exact core.injective (congrArg Prod.snd hpairs)

  let vertexMap : SubdivisionVertex d → V
    | .inl i => core i
    | .inr e => middle e
  have hvertexMap_injective : Injective vertexMap := by
    intro x y hxy
    cases x with
    | inl i =>
        cases y with
        | inl j =>
            have hij : core i = core j := by simpa [vertexMap] using hxy
            exact congrArg Sum.inl (core.injective hij)
        | inr e =>
            have hie : core i = middle e := by simpa [vertexMap] using hxy
            exfalso
            exact (Finset.disjoint_left.mp hUW (hmiddleU e)
              (hie ▸ hcoreW i))
    | inr e =>
        cases y with
        | inl i =>
            have hei : middle e = core i := by simpa [vertexMap] using hxy
            exfalso
            exact (Finset.disjoint_left.mp hUW (hmiddleU e)
              (hei.symm ▸ hcoreW i))
        | inr f =>
            have hef : middle e = middle f := by simpa [vertexMap] using hxy
            exact congrArg Sum.inr (hmiddle_injective hef)

  let hom : oneSubdivisionClique d →g G :=
    ⟨vertexMap, by
      intro x y hxy
      cases x with
      | inl i =>
          cases y with
          | inl j => exact False.elim hxy
          | inr e =>
              rcases hxy with h | h
              · simpa [vertexMap, h] using (hmiddleAdjLeft e).symm
              · simpa [vertexMap, h] using (hmiddleAdjRight e).symm
      | inr e =>
          cases y with
          | inl i =>
              rcases hxy with h | h
              · simpa [vertexMap, h] using hmiddleAdjLeft e
              · simpa [vertexMap, h] using hmiddleAdjRight e
          | inr f => exact False.elim hxy⟩
  exact ⟨⟨hom, hvertexMap_injective⟩⟩

/-- Contrapositive form used in deletion arguments: if the indicated
subdivision is absent, some vertex of `U` has fewer than `d` neighbors in
`W`. -/
theorem exists_few_neighbors_of_no_oneSubdivisionClique [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U W : Finset V) (d : ℕ)
    (hUW : Disjoint U W) (hU : U.Nonempty)
    (hcard : W.card ^ 2 ≤ U.card)
    (hfree : ¬ oneSubdivisionClique d ⊑ G) :
    ∃ u ∈ U, (W.filter fun w ↦ G.Adj u w).card < d := by
  by_contra h
  push_neg at h
  exact hfree (liuMontgomery_skewed_bipartite_subdivision G U W d hUW hU hcard h)

end Erdos63
