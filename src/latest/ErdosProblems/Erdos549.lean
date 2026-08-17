/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib
import Util.Ramsey

/-!
# Erdős Problem 549 is false

The conjecture asserted that every tree with bipartition class sizes `k`
and `2 * k` has Ramsey number `4 * k - 1`.  Norin, Sun, and Zhao disproved
it using double stars.  This file gives an exact finite specialization of
their construction: the three-fold clique blow-up of the line graph of
`K₇` is a red graph on 63 vertices such that neither it nor its complement
contains `S(31,15)`.  That double star is a tree with bipartition class
sizes 16 and 32, while `4 * 16 - 1 = 63`.

The detailed mathematical proof and source audit are in `tex/549.tex`.
-/

namespace Erdos549

open Finset SimpleGraph

/-! ## The graph Ramsey number -/

/-- At `N` vertices, every red-blue coloring contains a monochromatic copy
of `T`.  The host type is quantified by cardinality so that explicit finite
witnesses need not be transported to `Fin N`. -/
def GraphRamseyAt {V : Type*} [Fintype V] (T : SimpleGraph V) (N : ℕ) : Prop :=
  ∀ (W : Type) [Fintype W], Fintype.card W = N →
    ∀ H : SimpleGraph W, T ⊑ H ∨ T ⊑ Hᶜ

/-- Finite clique Ramsey theory implies existence of a graph Ramsey
threshold for every finite graph. -/
theorem graphRamseyAt_exists {V : Type*} [Fintype V] (T : SimpleGraph V) :
    ∃ N, GraphRamseyAt T N := by
  classical
  let t := Fintype.card V
  refine ⟨Ramsey.ramseyNumber t t, ?_⟩
  intro W _ hcard H
  have hramsey :=
    Ramsey.ramseyProperty_of_card hcard (Ramsey.ramseyNumber_spec t t) H
  have hTtopV : T ⊑ completeGraph V :=
    SimpleGraph.IsContained.of_le le_top
  have htopVFin : completeGraph V ⊑ completeGraph (Fin t) :=
    (SimpleGraph.Iso.completeGraph (Fintype.equivFin V)).isContained
  have hTFin : T ⊑ completeGraph (Fin t) := hTtopV.trans htopVFin
  by_cases hclique : H.CliqueFree t
  · right
    have hindep : ¬H.IndepSetFree t := fun hi ↦ hramsey ⟨hclique, hi⟩
    have hcompl : ¬Hᶜ.CliqueFree t := by simpa using hindep
    exact hTFin.trans ((not_cliqueFree_iff_top_isContained t).mp hcompl)
  · left
    exact hTFin.trans ((not_cliqueFree_iff_top_isContained t).mp hclique)

/-- The ordinary two-color Ramsey number of a finite graph. -/
noncomputable def graphRamseyNumber {V : Type*} [Fintype V]
    (T : SimpleGraph V) : ℕ :=
  sInf {N : ℕ | GraphRamseyAt T N}

/-- The Ramsey property holds at the Ramsey number. -/
theorem graphRamseyNumber_spec {V : Type*} [Fintype V] (T : SimpleGraph V) :
    GraphRamseyAt T (graphRamseyNumber T) :=
  csInf_mem (graphRamseyAt_exists T)

/-- `T` has a covering bipartition with class sizes `k` and `2 * k`. -/
def HasBipartitionSizes {V : Type*} [Fintype V]
    (T : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ A B : Finset V,
    A.card = k ∧ B.card = 2 * k ∧
      (A : Set V) ∪ (B : Set V) = Set.univ ∧
      T.IsBipartiteWith (A : Set V) (B : Set V)

/-- The literal universal assertion in Erdős Problem 549. -/
def Erdos549Statement : Prop :=
  ∀ (V : Type) [Fintype V] (T : SimpleGraph V) (k : ℕ),
    T.IsTree → HasBipartitionSizes T k →
      graphRamseyNumber T = 4 * k - 1

/-! ## Double stars -/

/-- The vertices of `S(n,m)`: two centers, `n` leaves at the first
center, and `m` leaves at the second. -/
inductive DoubleStarVertex (n m : ℕ) where
  | leftCenter
  | rightCenter
  | leftLeaf (i : Fin n)
  | rightLeaf (j : Fin m)
  deriving DecidableEq, Fintype

/-- The double star `S(n,m)`. -/
def doubleStar (n m : ℕ) : SimpleGraph (DoubleStarVertex n m) where
  Adj u v :=
    match u, v with
    | .leftCenter, .rightCenter => True
    | .rightCenter, .leftCenter => True
    | .leftCenter, .leftLeaf _ => True
    | .leftLeaf _, .leftCenter => True
    | .rightCenter, .rightLeaf _ => True
    | .rightLeaf _, .rightCenter => True
    | _, _ => False
  symm := ⟨by
    intro u v h
    cases u <;> cases v <;> simp_all⟩
  loopless := ⟨by
    intro u h
    cases u <;> simp_all⟩

instance doubleStarDecidableRel (n m : ℕ) :
    DecidableRel (doubleStar n m).Adj := fun u v ↦ by
  cases u <;> cases v <;> simp only [doubleStar] <;> infer_instance

/-- The smaller canonical bipartition class: the first center and the
leaves at the second center. -/
def smallPart (n m : ℕ) : Finset (DoubleStarVertex n m) :=
  insert .leftCenter (Finset.univ.image .rightLeaf)

/-- The larger canonical bipartition class. -/
def largePart (n m : ℕ) : Finset (DoubleStarVertex n m) :=
  insert .rightCenter (Finset.univ.image .leftLeaf)

abbrev CounterVertex := DoubleStarVertex 31 15

/-- The concrete double star `S(31,15)`. -/
abbrev counterexampleTree : SimpleGraph CounterVertex := doubleStar 31 15

lemma counterVertex_card : Fintype.card CounterVertex = 48 := by
  decide

/-- The two displayed parts form the canonical bipartition of
`S(31,15)`. -/
lemma counterexampleTree_isBipartiteWith :
    counterexampleTree.IsBipartiteWith
      (smallPart 31 15 : Set CounterVertex)
      (largePart 31 15 : Set CounterVertex) := by
  constructor
  · simp [Set.disjoint_left, smallPart, largePart]
  · intro u v h
    cases u <;> cases v <;>
      simp_all [counterexampleTree, doubleStar, smallPart, largePart]

lemma counterexampleTree_connected : counterexampleTree.Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨.leftCenter, ?_⟩
  intro v
  cases v with
  | leftCenter => exact .rfl
  | rightCenter =>
      exact (show counterexampleTree.Adj .leftCenter .rightCenter by
        simp [counterexampleTree, doubleStar]).reachable
  | leftLeaf i =>
      exact (show counterexampleTree.Adj .leftCenter (.leftLeaf i) by
        simp [counterexampleTree, doubleStar]).reachable
  | rightLeaf j =>
      exact
        (show counterexampleTree.Adj .leftCenter .rightCenter by
          simp [counterexampleTree, doubleStar]).reachable.trans
        (show counterexampleTree.Adj .rightCenter (.rightLeaf j) by
          simp [counterexampleTree, doubleStar]).reachable

/-- `S(31,15)` is a tree. -/
lemma counterexampleTree_isTree : counterexampleTree.IsTree := by
  rw [isTree_iff_connected_and_card]
  refine ⟨counterexampleTree_connected, ?_⟩
  have hedge : counterexampleTree.edgeFinset.card = 47 := by
    rw [← isBipartiteWith_sum_degrees_eq_card_edges
      counterexampleTree_isBipartiteWith]
    decide
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← edgeFinset_card,
    hedge, counterVertex_card]

/-- The canonical bipartition of `S(31,15)` has sizes 16 and 32. -/
lemma counterexampleTree_bipartition :
    HasBipartitionSizes counterexampleTree 16 := by
  refine ⟨smallPart 31 15, largePart 31 15, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · ext v
    cases v <;> simp [smallPart, largePart]
  · exact counterexampleTree_isBipartiteWith

lemma counterexampleTree_leftCenter_degree :
    counterexampleTree.degree (.leftCenter) = 32 := by
  decide

/-- A host of maximum degree at most 31 cannot contain `S(31,15)`. -/
lemma counterexampleTree_notContained_of_degree_le
    {W : Type*} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (hdegree : ∀ v, H.degree v ≤ 31) :
    ¬counterexampleTree ⊑ H := by
  classical
  rintro ⟨f⟩
  have hmono := f.degree_le (.leftCenter : CounterVertex)
  rw [counterexampleTree_leftCenter_degree] at hmono
  have hupper := hdegree (f .leftCenter)
  omega

/-- If every edge has neighborhood union of size at most 47, the host
cannot contain `S(31,15)`. -/
lemma counterexampleTree_notContained_of_neighborUnion_le
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (hunion : ∀ u v, H.Adj u v →
      (H.neighborFinset u ∪ H.neighborFinset v).card ≤ 47) :
    ¬counterexampleTree ⊑ H := by
  classical
  rintro ⟨f⟩
  let emb : CounterVertex ↪ W := ⟨f, f.injective⟩
  let image : Finset W := Finset.univ.map emb
  have himage :
      image ⊆ H.neighborFinset (f .leftCenter) ∪
        H.neighborFinset (f .rightCenter) := by
    intro z hz
    rcases Finset.mem_map.mp hz with ⟨x, _, rfl⟩
    simp only [Finset.mem_union, mem_neighborFinset]
    cases x with
    | leftCenter =>
        exact Or.inr <| f.toHom.map_adj <| by
          simp [counterexampleTree, doubleStar]
    | rightCenter =>
        exact Or.inl <| f.toHom.map_adj <| by
          simp [counterexampleTree, doubleStar]
    | leftLeaf i =>
        exact Or.inl <| f.toHom.map_adj <| by
          simp [counterexampleTree, doubleStar]
    | rightLeaf j =>
        exact Or.inr <| f.toHom.map_adj <| by
          simp [counterexampleTree, doubleStar]
  have himageCard : image.card = 48 := by
    simp [image, counterVertex_card]
  have hbridge : H.Adj (f .leftCenter) (f .rightCenter) :=
    f.toHom.map_adj <| by simp [counterexampleTree, doubleStar]
  have hupper := hunion (f .leftCenter) (f .rightCenter) hbridge
  have hlower := Finset.card_le_card himage
  rw [himageCard] at hlower
  omega

/-! ## The three-fold clique blow-up of `L(K₇)` -/

/-- An edge of `K₇`, represented as a two-element finset. -/
abbrev K7Edge := {e : Finset (Fin 7) // e.card = 2}

/-- Three copies of each of the 21 edges of `K₇`. -/
abbrev WitnessVertex := K7Edge × Fin 3

/-- The underlying line-graph labels that meet at least one of `e,f`. -/
def baseNeighborLabels (e f : K7Edge) : Finset K7Edge :=
  Finset.univ.filter fun g ↦
    ((g.1 ∩ e.1).Nonempty ∨ (g.1 ∩ f.1).Nonempty)

/-- Adjacent vertices of `L(K₇)` have at most 15 labels in the union of
their closed blow-up neighborhoods. -/
lemma baseNeighborLabels_card_le :
    ∀ e f : K7Edge, (e.1 ∩ f.1).Nonempty →
      (baseNeighborLabels e f).card ≤ 15 := by
  decide

/-- Distinct vertices are adjacent when their underlying `K₇` edges
meet.  This is the three-fold clique blow-up of `L(K₇)`. -/
def witnessGraph : SimpleGraph WitnessVertex where
  Adj x y := x ≠ y ∧ ((x.1 : Finset (Fin 7)) ∩ y.1).Nonempty
  symm := ⟨by
    intro x y h
    exact ⟨h.1.symm, by simpa [Finset.inter_comm] using h.2⟩⟩
  loopless := ⟨by
    intro x h
    exact h.1 rfl⟩

instance witnessGraphDecidableRel : DecidableRel witnessGraph.Adj :=
  fun x y ↦ by
    change Decidable (x ≠ y ∧ ((x.1 : Finset (Fin 7)) ∩ y.1).Nonempty)
    infer_instance

lemma witnessVertex_card : Fintype.card WitnessVertex = 63 := by
  decide

lemma witnessGraph_degree : ∀ v, witnessGraph.degree v = 32 := by
  decide

lemma witnessGraph_neighborUnion :
    ∀ u v, witnessGraph.Adj u v →
      (witnessGraph.neighborFinset u ∪ witnessGraph.neighborFinset v).card ≤ 45 := by
  intro u v huv
  let s := witnessGraph.neighborFinset u ∪ witnessGraph.neighborFinset v
  let labels := s.image Prod.fst
  have hlabelsMaps : (s : Set WitnessVertex).MapsTo Prod.fst (baseNeighborLabels u.1 v.1) := by
    intro z hz
    change z ∈ witnessGraph.neighborFinset u ∪ witnessGraph.neighborFinset v at hz
    rw [Finset.mem_union] at hz
    change z.1 ∈ baseNeighborLabels u.1 v.1
    rw [baseNeighborLabels, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hz with hzu | hzv
    · have hzuAdj : witnessGraph.Adj u z :=
        (witnessGraph.mem_neighborFinset u z).mp hzu
      exact Or.inl (show (z.1.1 ∩ u.1.1).Nonempty from hzuAdj.symm.2)
    · have hzvAdj : witnessGraph.Adj v z :=
        (witnessGraph.mem_neighborFinset v z).mp hzv
      exact Or.inr (show (z.1.1 ∩ v.1.1).Nonempty from hzvAdj.symm.2)
  have hlabelsSubset : labels ⊆ baseNeighborLabels u.1 v.1 := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨z, hz, rfl⟩
    exact hlabelsMaps hz
  have hlabelsCard : labels.card ≤ 15 :=
    (Finset.card_le_card hlabelsSubset).trans
      (baseNeighborLabels_card_le u.1 v.1 huv.2)
  have hfiber : ∀ e ∈ labels, #{z ∈ s | z.1 = e} ≤ 3 := by
    intro e _
    let fiber := s.filter fun z ↦ z.1 = e
    have hmap : (fiber : Set WitnessVertex).MapsTo Prod.snd
        ((Finset.univ : Finset (Fin 3)) : Set (Fin 3)) := by
      intro z _
      exact Finset.mem_univ z.2
    have hinj : Set.InjOn Prod.snd (fiber : Set WitnessVertex) := by
      intro a ha b hb hab
      have hae : a.1 = e := (Finset.mem_filter.mp ha).2
      have hbe : b.1 = e := (Finset.mem_filter.mp hb).2
      exact Prod.ext (hae.trans hbe.symm) hab
    exact (Finset.card_le_card_of_injOn Prod.snd hmap hinj).trans_eq (by simp)
  have hsum := Finset.sum_le_sum hfiber
  rw [← Finset.card_eq_sum_card_image (fun z : WitnessVertex ↦ z.1) s] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  exact hsum.trans <| (Nat.mul_le_mul_right 3 hlabelsCard).trans_eq (by norm_num)

lemma witnessGraph_compl_degree : ∀ v, witnessGraphᶜ.degree v = 30 := by
  decide

lemma counterexampleTree_notContained_witnessGraph :
    ¬counterexampleTree ⊑ witnessGraph := by
  apply counterexampleTree_notContained_of_neighborUnion_le
  intro u v huv
  exact Nat.le_trans (witnessGraph_neighborUnion u v huv) (by norm_num)

lemma counterexampleTree_notContained_witnessGraph_compl :
    ¬counterexampleTree ⊑ witnessGraphᶜ := by
  apply counterexampleTree_notContained_of_degree_le
  intro v
  rw [witnessGraph_compl_degree v]
  norm_num

/-- The explicit red-blue coloring of `K₆₃` has no monochromatic
`S(31,15)`. -/
theorem not_graphRamseyAt_counterexampleTree_63 :
    ¬GraphRamseyAt counterexampleTree 63 := by
  intro h
  rcases h WitnessVertex witnessVertex_card witnessGraph with hred | hblue
  · exact counterexampleTree_notContained_witnessGraph hred
  · exact counterexampleTree_notContained_witnessGraph_compl hblue

/-- Erdős Problem 549 is false.  The counterexample is the tree
`S(31,15)`, whose bipartition classes have sizes 16 and 32. -/
theorem erdos_549 : ¬Erdos549Statement := by
  intro h
  have heq : graphRamseyNumber counterexampleTree = 63 := by
    simpa using h CounterVertex counterexampleTree 16
      counterexampleTree_isTree counterexampleTree_bipartition
  have hspec := graphRamseyNumber_spec counterexampleTree
  rw [heq] at hspec
  exact not_graphRamseyAt_counterexampleTree_63 hspec

end Erdos549

#print axioms Erdos549.erdos_549
