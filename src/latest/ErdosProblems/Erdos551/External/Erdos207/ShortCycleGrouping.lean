/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos551.External.Erdos207.CycleDecompositionAugmentation

/-!
# Grouping edge-disjoint short cycles

KSSS group a family of edge-disjoint triangles, four-cycles, and five-cycles
by pairing every five-cycle with one four-cycle and putting the remaining
four-cycles into triples.  This file proves that finite combinatorial step in
the exact quotient-root language accepted by `FullCycleCoverBank`.
-/

namespace Erdos207

open Finset

noncomputable section

abbrev ShortCycleIndex (I₃ I₄ I₅ : Type*) := I₃ ⊕ (I₄ ⊕ I₅)

/-- A finite indexed family of realized short cycles.  Embeddings are used
because all short cycles constructed in the path-cover expansion are simple. -/
structure ShortCycleFamily (Y I₃ I₄ I₅ : Type*) where
  triangle : I₃ → (Fin 3 ↪ Y)
  fourCycle : I₄ → (Fin 4 ↪ Y)
  fiveCycle : I₅ → (Fin 5 ↪ Y)

abbrev ShortCycleFamily.graph
    {Y I₃ I₄ I₅ : Type*} (F : ShortCycleFamily Y I₃ I₄ I₅) :
    ShortCycleIndex I₃ I₄ I₅ → SimpleGraph Y
  | .inl i => (SimpleGraph.cycleGraph 3).map (F.triangle i)
  | .inr (.inl i) => (SimpleGraph.cycleGraph 4).map (F.fourCycle i)
  | .inr (.inr i) => (SimpleGraph.cycleGraph 5).map (F.fiveCycle i)

def ShortCycleFamily.PairwiseDisjoint
    {Y I₃ I₄ I₅ : Type*} (F : ShortCycleFamily Y I₃ I₄ I₅) : Prop :=
  ∀ i j, i ≠ j → Disjoint (F.graph i) (F.graph j)

abbrev ShortCycleGroupIndex (I₃ I₅ : Type*) (k : ℕ) :=
  I₃ ⊕ (I₅ ⊕ Fin k)

/-- An arbitrary finite four-cycle index type can be put into the required
five-cycle slots and three-cycle slots as soon as the cardinalities agree. -/
def fourCycleGroupingEquiv
    {I₄ I₅ : Type*} [Fintype I₄] [Fintype I₅]
    (k : ℕ) (hcard : Fintype.card I₄ = Fintype.card I₅ + 3 * k) :
    I₄ ≃ I₅ ⊕ (Fin k × Fin 3) :=
  Fintype.equivOfCardEq (by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    omega)

/-- Original short-cycle indices belonging to one grouped root. -/
def shortCycleGroupConstituents
    {I₃ I₄ I₅ : Type*} [DecidableEq I₃] [DecidableEq I₄] [DecidableEq I₅]
    {k : ℕ} (e₄ : I₄ ≃ I₅ ⊕ (Fin k × Fin 3)) :
    ShortCycleGroupIndex I₃ I₅ k →
      Finset (ShortCycleIndex I₃ I₄ I₅)
  | .inl i => {.inl i}
  | .inr (.inl i) =>
      {.inr (.inl (e₄.symm (.inl i))), .inr (.inr i)}
  | .inr (.inr t) =>
      {.inr (.inl (e₄.symm (.inr (t, 0)))),
        .inr (.inl (e₄.symm (.inr (t, 1)))),
        .inr (.inl (e₄.symm (.inr (t, 2))))}

/-- The unique group to which an original short cycle is assigned. -/
def shortCycleGroupOwner
    {I₃ I₄ I₅ : Type*} {k : ℕ}
    (e₄ : I₄ ≃ I₅ ⊕ (Fin k × Fin 3)) :
    ShortCycleIndex I₃ I₄ I₅ → ShortCycleGroupIndex I₃ I₅ k
  | .inl i => .inl i
  | .inr (.inl j) =>
      match e₄ j with
      | .inl i => .inr (.inl i)
      | .inr (t, _) => .inr (.inr t)
  | .inr (.inr i) => .inr (.inl i)

lemma shortCycleGroupOwner_eq_of_mem
    {I₃ I₄ I₅ : Type*} [DecidableEq I₃] [DecidableEq I₄] [DecidableEq I₅]
    {k : ℕ} (e₄ : I₄ ≃ I₅ ⊕ (Fin k × Fin 3))
    {a : ShortCycleGroupIndex I₃ I₅ k}
    {x : ShortCycleIndex I₃ I₄ I₅}
    (hx : x ∈ shortCycleGroupConstituents e₄ a) :
    shortCycleGroupOwner e₄ x = a := by
  rcases a with i | (i | t)
  · simp only [shortCycleGroupConstituents, mem_singleton] at hx
    subst x
    rfl
  · simp only [shortCycleGroupConstituents, mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · simp [shortCycleGroupOwner]
    · rfl
  · simp only [shortCycleGroupConstituents, mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> simp [shortCycleGroupOwner]

lemma shortCycle_mem_groupConstituents_owner
    {I₃ I₄ I₅ : Type*} [DecidableEq I₃] [DecidableEq I₄] [DecidableEq I₅]
    {k : ℕ} (e₄ : I₄ ≃ I₅ ⊕ (Fin k × Fin 3))
    (x : ShortCycleIndex I₃ I₄ I₅) :
    x ∈ shortCycleGroupConstituents e₄ (shortCycleGroupOwner e₄ x) := by
  rcases x with i | (j | i)
  · simp [shortCycleGroupOwner, shortCycleGroupConstituents]
  · cases hej : e₄ j with
    | inl i =>
        have hsymm : e₄.symm (.inl i) = j := by
          apply e₄.injective
          simpa [hej]
        simp [shortCycleGroupOwner, shortCycleGroupConstituents, hej, hsymm]
    | inr p =>
        rcases p with ⟨t, z⟩
        have hsymm : e₄.symm (.inr (t, z)) = j := by
          apply e₄.injective
          simpa [hej]
        fin_cases z <;>
          simp [shortCycleGroupOwner, shortCycleGroupConstituents,
            hej, ← hsymm]
  · simp [shortCycleGroupOwner, shortCycleGroupConstituents]

lemma shortCycleGroupConstituents_disjoint
    {I₃ I₄ I₅ : Type*} [DecidableEq I₃] [DecidableEq I₄] [DecidableEq I₅]
    {k : ℕ} (e₄ : I₄ ≃ I₅ ⊕ (Fin k × Fin 3))
    {a b : ShortCycleGroupIndex I₃ I₅ k} (hab : a ≠ b) :
    Disjoint (shortCycleGroupConstituents e₄ a)
      (shortCycleGroupConstituents e₄ b) := by
  rw [Finset.disjoint_left]
  intro x hxa hxb
  apply hab
  exact (shortCycleGroupOwner_eq_of_mem e₄ hxa).symm.trans
    (shortCycleGroupOwner_eq_of_mem e₄ hxb)

/-- The graph represented by one grouped root. -/
def groupedShortCycleGraph
    {Y I₃ I₄ I₅ : Type*}
    [DecidableEq I₃] [DecidableEq I₄] [DecidableEq I₅]
    {k : ℕ} (F : ShortCycleFamily Y I₃ I₄ I₅)
    (e₄ : I₄ ≃ I₅ ⊕ (Fin k × Fin 3))
    (a : ShortCycleGroupIndex I₃ I₅ k) : SimpleGraph Y :=
  graphSup (shortCycleGroupConstituents e₄ a) F.graph

lemma disjoint_graphSup_graphSup_of_index_disjoint
    {I Y : Type*} [DecidableEq I]
    {s t : Finset I} {G : I → SimpleGraph Y}
    (hindex : Disjoint s t)
    (hpair : ∀ i j, i ≠ j → Disjoint (G i) (G j)) :
    Disjoint (graphSup s G) (graphSup t G) := by
  unfold graphSup
  rw [Finset.disjoint_sup_left]
  intro i hi
  rw [Finset.disjoint_sup_right]
  intro j hj
  apply hpair i j
  intro hij
  subst j
  exact Finset.disjoint_left.mp hindex hi hj

lemma groupedShortCycleGraph_pairwiseDisjoint
    {Y I₃ I₄ I₅ : Type*}
    [DecidableEq I₃] [DecidableEq I₄] [DecidableEq I₅]
    {k : ℕ} (F : ShortCycleFamily Y I₃ I₄ I₅)
    (hF : F.PairwiseDisjoint)
    (e₄ : I₄ ≃ I₅ ⊕ (Fin k × Fin 3))
    {a b : ShortCycleGroupIndex I₃ I₅ k} (hab : a ≠ b) :
    Disjoint (groupedShortCycleGraph F e₄ a)
      (groupedShortCycleGraph F e₄ b) :=
  disjoint_graphSup_graphSup_of_index_disjoint
    (shortCycleGroupConstituents_disjoint e₄ hab) hF

lemma fullCycleCoverRoot_triangle_eq_cycle
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (f : Fin 3 ↪ Y) :
    fullCycleCoverRoot (.triangle f) =
      ((SimpleGraph.cycleGraph 3).map f).map
        (fullCycleCoverBaseEmbedding Y) := by
  have hbase : coveredGraph ({finThreeTriple} : TripleSystemOn (Fin 3)) =
      SimpleGraph.cycleGraph 3 := by
    ext a b
    simp [coveredGraph_adj, finThreeTriple,
      SimpleGraph.cycleGraph_three_eq_top]
  change coveredGraph
      {mapTriple (f.trans (fullCycleCoverBaseEmbedding Y)) finThreeTriple} = _
  rw [show ({mapTriple (f.trans (fullCycleCoverBaseEmbedding Y))
      finThreeTriple} : TripleSystemOn (FullCycleCoverVertex Y)) =
      mapTripleSystem (f.trans (fullCycleCoverBaseEmbedding Y))
        ({finThreeTriple} : TripleSystemOn (Fin 3)) by
        simp [mapTripleSystem, mapTripleEmbedding],
    coveredGraph_mapTripleSystem, hbase,
    SimpleGraph.map_map]
  congr 1

/-- The allowed full-bank copy corresponding to one group. -/
def groupedFullCycleCoverCopy
    {Y I₃ I₄ I₅ : Type*} [Fintype Y] [DecidableEq Y]
    [DecidableEq I₃] [DecidableEq I₄] [DecidableEq I₅]
    {k : ℕ} (F : ShortCycleFamily Y I₃ I₄ I₅)
    (hF : F.PairwiseDisjoint)
    (e₄ : I₄ ≃ I₅ ⊕ (Fin k × Fin 3)) :
    ShortCycleGroupIndex I₃ I₅ k → FullCycleCoverCopy Y
  | .inl i => .triangle (F.triangle i)
  | .inr (.inl i) =>
      let j := e₄.symm (.inl i)
      .c4c5 (c4c5QuotientMapOfEmbedded
        (F.fourCycle j) (F.fiveCycle i)
        (edgeFaithfulMap_of_injective (F.fourCycle j).injective)
        (edgeFaithfulMap_of_injective (F.fiveCycle i).injective)
        (by
          simpa only [ShortCycleFamily.graph] using
            hF (.inr (.inl j)) (.inr (.inr i)) (by simp)))
  | .inr (.inr t) =>
      let j₀ := e₄.symm (.inr (t, 0))
      let j₁ := e₄.symm (.inr (t, 1))
      let j₂ := e₄.symm (.inr (t, 2))
      .threeC4 (threeC4QuotientMapOfEmbedded
        (F.fourCycle j₀) (F.fourCycle j₁) (F.fourCycle j₂)
        (edgeFaithfulMap_of_injective (F.fourCycle j₀).injective)
        (edgeFaithfulMap_of_injective (F.fourCycle j₁).injective)
        (edgeFaithfulMap_of_injective (F.fourCycle j₂).injective)
        (by
          simpa only [ShortCycleFamily.graph] using
            hF (.inr (.inl j₀)) (.inr (.inl j₁)) (by
              intro h
              have hj : j₀ = j₁ := Sum.inl.inj (Sum.inr.inj h)
              have := e₄.symm.injective hj
              simp at this))
        (by
          simpa only [ShortCycleFamily.graph] using
            hF (.inr (.inl j₀)) (.inr (.inl j₂)) (by
              intro h
              have hj : j₀ = j₂ := Sum.inl.inj (Sum.inr.inj h)
              have := e₄.symm.injective hj
              simp at this))
        (by
          simpa only [ShortCycleFamily.graph] using
            hF (.inr (.inl j₁)) (.inr (.inl j₂)) (by
              intro h
              have hj : j₁ = j₂ := Sum.inl.inj (Sum.inr.inj h)
              have := e₄.symm.injective hj
              simp at this)))

lemma fullCycleCoverRoot_grouped_eq
    {Y I₃ I₄ I₅ : Type*} [Fintype Y] [DecidableEq Y]
    [DecidableEq I₃] [DecidableEq I₄] [DecidableEq I₅]
    {k : ℕ} (F : ShortCycleFamily Y I₃ I₄ I₅)
    (hF : F.PairwiseDisjoint)
    (e₄ : I₄ ≃ I₅ ⊕ (Fin k × Fin 3))
    (a : ShortCycleGroupIndex I₃ I₅ k) :
    fullCycleCoverRoot (groupedFullCycleCoverCopy F hF e₄ a) =
      (groupedShortCycleGraph F e₄ a).map
        (fullCycleCoverBaseEmbedding Y) := by
  rcases a with (i | i)
  · change fullCycleCoverRoot (.triangle (F.triangle i)) = _
    rw [fullCycleCoverRoot_triangle_eq_cycle]
    simp [groupedFullCycleCoverCopy, groupedShortCycleGraph,
      shortCycleGroupConstituents, graphSup, ShortCycleFamily.graph]
  · rcases i with (i | t)
    · change fullCycleCoverRoot (.c4c5 _) = _
      rw [fullCycleCoverRoot_c4c5OfEmbedded_eq]
      simp [groupedFullCycleCoverCopy, groupedShortCycleGraph,
        shortCycleGroupConstituents, graphSup, ShortCycleFamily.graph]
    · change fullCycleCoverRoot (.threeC4 _) = _
      rw [fullCycleCoverRoot_threeC4OfEmbedded_eq]
      simp [groupedFullCycleCoverCopy, groupedShortCycleGraph,
        shortCycleGroupConstituents, graphSup, ShortCycleFamily.graph]
      congr 1
      ac_rfl

/-- The finite set of all grouped roots. -/
def groupedFullCycleCoverSet
    {Y I₃ I₄ I₅ : Type*} [Fintype Y] [DecidableEq Y]
    [Fintype I₃] [Fintype I₅]
    [DecidableEq I₃] [DecidableEq I₄] [DecidableEq I₅]
    {k : ℕ} (F : ShortCycleFamily Y I₃ I₄ I₅)
    (hF : F.PairwiseDisjoint)
    (e₄ : I₄ ≃ I₅ ⊕ (Fin k × Fin 3)) :
    Finset (FullCycleCoverCopy Y) :=
  univ.image (groupedFullCycleCoverCopy F hF e₄)

/-- Pairing every five-cycle and grouping the remaining four-cycles in
threes produces an exact `HasFullCycleCoverGrouping` certificate. -/
theorem hasFullCycleCoverGrouping_of_shortCycles
    {Y I₃ I₄ I₅ : Type*} [Fintype Y] [DecidableEq Y]
    [Fintype I₃] [Fintype I₄] [Fintype I₅]
    [DecidableEq I₃] [DecidableEq I₄] [DecidableEq I₅]
    (F : ShortCycleFamily Y I₃ I₄ I₅)
    (hF : F.PairwiseDisjoint)
    (k : ℕ) (hcard : Fintype.card I₄ = Fintype.card I₅ + 3 * k) :
    HasFullCycleCoverGrouping
      ((graphSup univ F.graph).map (fullCycleCoverBaseEmbedding Y)) := by
  let e₄ := fourCycleGroupingEquiv k hcard
  let selected := groupedFullCycleCoverSet F hF e₄
  refine ⟨selected, ?_, ?_⟩
  · unfold selected groupedFullCycleCoverSet graphSup
    rw [Finset.sup_image]
    change univ.sup (fun a =>
      fullCycleCoverRoot (groupedFullCycleCoverCopy F hF e₄ a)) = _
    simp_rw [fullCycleCoverRoot_grouped_eq F hF e₄]
    have hmap :
        (univ.sup (groupedShortCycleGraph F e₄)).map
            (fullCycleCoverBaseEmbedding Y) =
          univ.sup ((fun G : SimpleGraph Y =>
            G.map (fullCycleCoverBaseEmbedding Y)) ∘
              groupedShortCycleGraph F e₄) := by
      exact Finset.apply_sup_eq_sup_comp
        (s := (univ : Finset (ShortCycleGroupIndex I₃ I₅ k)))
        (f := groupedShortCycleGraph F e₄)
        (g := fun G : SimpleGraph Y =>
          G.map (fullCycleCoverBaseEmbedding Y))
        (fun G K => SimpleGraph.map_sup_function G K _)
        (by
          ext u v
          rw [SimpleGraph.map_adj]
          simp)
    change univ.sup ((fun G : SimpleGraph Y =>
      G.map (fullCycleCoverBaseEmbedding Y)) ∘
        groupedShortCycleGraph F e₄) = _
    rw [← hmap]
    congr 1
    unfold groupedShortCycleGraph graphSup
    apply le_antisymm
    · apply Finset.sup_le
      intro a _
      apply Finset.sup_le
      intro i _
      exact Finset.le_sup (Finset.mem_univ i)
    · apply Finset.sup_le
      intro i _
      exact le_trans
        (Finset.le_sup (f := F.graph)
          (shortCycle_mem_groupConstituents_owner e₄ i))
        (Finset.le_sup
          (f := fun a => (shortCycleGroupConstituents e₄ a).sup F.graph)
          (Finset.mem_univ (shortCycleGroupOwner e₄ i)))
  · intro i hi j hj hij
    unfold selected groupedFullCycleCoverSet at hi hj
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hj
    rw [fullCycleCoverRoot_grouped_eq, fullCycleCoverRoot_grouped_eq]
    apply SimpleGraph.disjoint_map_embedding
    apply groupedShortCycleGraph_pairwiseDisjoint F hF e₄
    intro hab
    subst b
    exact hij rfl

end

end Erdos207
