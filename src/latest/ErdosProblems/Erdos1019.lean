/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 1019.
https://www.erdosproblems.com/forum/thread/1019

Informal authors:
- Miklós Simonovits

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1019.md
-/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Tactic.Linarith.Frontend
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 1019

Simonovits proved that an `n`-vertex graph with

`⌊n²/4⌋ + ⌊(n+1)/2⌋`

edges contains a saturated planar graph on more than three vertices.  We formalize the sharper
form recorded in the source discussion: the graph contains either `K₄` or a bipyramid
`C_l ∨ 2K₁` for some `l ≥ 3`.  These two graphs are planar triangulations and have respectively
`6 = 3*4-6` and `3*l = 3*(l+2)-6` edges.

The proof is the sharp Simonovits induction.  At one edge below the claimed threshold, every graph
without one of the two witnesses is the join of a tree and an independent set whose orders differ
by at most two.  Adding one edge to such a join produces one of the witnesses.
-/

open scoped SimpleGraph
open Finset

namespace Erdos1019

/-- The sharp one-edge-lower extremal value. -/
def lowerThreshold (n : ℕ) : ℕ := n * n / 4 + (n - 1) / 2

/-- The edge threshold in Erdős Problem 1019. -/
def problemThreshold (n : ℕ) : ℕ := n * n / 4 + (n + 1) / 2

/-- The degree removed in the sharp induction. -/
def stepDegree (n : ℕ) : ℕ := (n + 1) / 2

/-- The bipyramid over an `l`-cycle.  Its vertices are the equatorial vertices `Fin l` and two
apices indexed by `Bool`. -/
def bipyramidGraph (l : ℕ) : SimpleGraph (Fin l ⊕ Bool) where
  Adj u v := match u, v with
    | Sum.inl i, Sum.inl j => (SimpleGraph.cycleGraph l).Adj i j
    | Sum.inl _, Sum.inr _ => True
    | Sum.inr _, Sum.inl _ => True
    | Sum.inr _, Sum.inr _ => False
  symm := ⟨by
    intro u v h
    rcases u with i | p <;> rcases v with j | q
    · exact ((SimpleGraph.cycleGraph l).adj_comm i j).mp h
    · exact h
    · exact h
    · exact h⟩
  loopless := ⟨by
    intro u
    cases u <;> simp⟩

instance bipyramidGraph_decidableRel (l : ℕ) :
    DecidableRel (bipyramidGraph l).Adj := by
  intro u v
  rcases u with i | b <;> rcases v with j | c
  · change Decidable ((SimpleGraph.cycleGraph l).Adj i j)
    exact inferInstance
  · exact isTrue trivial
  · exact isTrue trivial
  · exact isFalse id

/-- The stronger concrete conclusion in Simonovits's resolution. -/
def HasTarget {V : Type*} (G : SimpleGraph V) : Prop :=
  (⊤ : SimpleGraph (Fin 4)) ⊑ G ∨
    ∃ l : ℕ, 3 ≤ l ∧ bipyramidGraph l ⊑ G

/-- The number of edges of `G` whose two endpoints lie in the finite set `U`.  We use `ncard`
so that this mathematical quantity does not retain a choice of decidability instance. -/
noncomputable def edgeCountOn {V : Type*} [Fintype V] (G : SimpleGraph V)
    (U : Finset V) : ℕ :=
  (G.induce (U : Set V)).edgeSet.ncard

lemma edgeCountOn_eq_card_edgeFinset {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) :
    edgeCountOn G U = #(G.induce (U : Set V)).edgeFinset := by
  unfold edgeCountOn
  rw [Set.ncard_eq_toFinset_card']
  rfl

lemma edgeSet_ncard_eq_card_edgeFinset {V : Type*} (G : SimpleGraph V)
    [Fintype G.edgeSet] : G.edgeSet.ncard = #G.edgeFinset := by
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  exact (SimpleGraph.edgeFinset_card).symm

/-- When every non-isolated vertex lies in `U`, inducing on `U` does not change the number of
edges.  The proof is phrased with `ncard`, hence is independent of finite-instance choices. -/
lemma edgeCountOn_eq_edgeSet_ncard_of_support_subset
    {V : Type*} [Fintype V] (G : SimpleGraph V) (U : Finset V)
    (hsupp : G.support ⊆ (U : Set V)) :
    edgeCountOn G U = G.edgeSet.ncard := by
  let inc : (U : Set V) ↪ V := Function.Embedding.subtype _
  let F : Sym2 (U : Set V) → Sym2 V := inc.sym2Map
  have himage : F '' (G.induce (U : Set V)).edgeSet = G.edgeSet := by
    apply Set.Subset.antisymm
    · intro e he
      obtain ⟨d, hd, rfl⟩ := he
      induction d using Sym2.inductionOn with
      | _ a b => exact hd
    · intro e he
      induction e using Sym2.inductionOn with
      | _ a b =>
        have hab : G.Adj a b := he
        have ha : a ∈ G.support := ⟨b, hab⟩
        have hb : b ∈ G.support := ⟨a, hab.symm⟩
        refine ⟨s(⟨a, hsupp ha⟩, ⟨b, hsupp hb⟩), hab, ?_⟩
        rfl
  unfold edgeCountOn
  rw [← himage, Set.ncard_image_of_injective _ inc.sym2Map.injective]

/-- The target-free extremal configuration: on `U`, the graph is the join of a tree on `A`
and an independent set `B`, and the tree side is between zero and two vertices larger. -/
def IsBalancedTreeJoinOn {V : Type*} (G : SimpleGraph V)
    (U A B : Finset V) : Prop :=
  (A : Set V) ∪ (B : Set V) = (U : Set V) ∧
  Disjoint (A : Set V) (B : Set V) ∧
  (G.induce (A : Set V)).IsTree ∧
  (G.induce (B : Set V)) = ⊥ ∧
  (∀ a ∈ A, ∀ b ∈ B, G.Adj a b) ∧
  B.card ≤ A.card ∧ A.card ≤ B.card + 2

@[simp] lemma bipyramidGraph_adj_left_left {l : ℕ} {i j : Fin l} :
    (bipyramidGraph l).Adj (.inl i) (.inl j) ↔ (SimpleGraph.cycleGraph l).Adj i j :=
  Iff.rfl

@[simp] lemma bipyramidGraph_adj_left_right {l : ℕ} {i : Fin l} {b : Bool} :
    (bipyramidGraph l).Adj (.inl i) (.inr b) :=
  trivial

@[simp] lemma bipyramidGraph_adj_right_left {l : ℕ} {b : Bool} {i : Fin l} :
    (bipyramidGraph l).Adj (.inr b) (.inl i) :=
  trivial

@[simp] lemma not_bipyramidGraph_adj_right_right {l : ℕ} {b c : Bool} :
    ¬(bipyramidGraph l).Adj (.inr b) (.inr c) :=
  id

lemma bipyramidGraph_degree_apex {l : ℕ} (b : Bool) :
    (bipyramidGraph l).degree (Sum.inr b) = l := by
  classical
  let e : (bipyramidGraph l).neighborSet (Sum.inr b) ≃ Fin l :=
    { toFun := fun y ↦ match h : y.1 with
        | .inl i => i
        | .inr c => False.elim (by
            have hy := y.2
            rw [h] at hy
            exact hy)
      invFun := fun i ↦ ⟨Sum.inl i, by simp⟩
      left_inv := by
        intro y
        rcases y with ⟨i | c, hi⟩
        · rfl
        · exact False.elim hi
      right_inv := by intro i; rfl }
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  exact (Fintype.card_congr e).trans (Fintype.card_fin l)

lemma bipyramidGraph_degree_equator {l : ℕ} (hl : 3 ≤ l) (i : Fin l) :
    (bipyramidGraph l).degree (Sum.inl i) = 4 := by
  classical
  let e : (bipyramidGraph l).neighborSet (Sum.inl i) ≃
      (SimpleGraph.cycleGraph l).neighborSet i ⊕ Bool :=
    { toFun := fun y ↦ match h : y.1 with
        | .inl j => Sum.inl ⟨j, by
            have hy := y.2
            rw [h] at hy
            exact hy⟩
        | .inr b => Sum.inr b
      invFun := fun y ↦ match y with
        | .inl j => ⟨Sum.inl j.1, j.2⟩
        | .inr b => ⟨Sum.inr b, by simp⟩
      left_inv := by
        intro y
        rcases y with ⟨j | b, hj⟩ <;> rfl
      right_inv := by
        intro y
        rcases y with j | b <;> rfl }
  have hcycle : (SimpleGraph.cycleGraph l).degree i = 2 := by
    obtain ⟨k, rfl⟩ : ∃ k, l = k + 3 := by
      exact ⟨l - 3, by omega⟩
    exact SimpleGraph.cycleGraph_degree_three_le
  rw [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_congr e,
    Fintype.card_sum, Fintype.card_bool]
  rw [SimpleGraph.card_neighborSet_eq_degree, hcycle]

lemma bipyramidGraph_card_edges {l : ℕ} (hl : 3 ≤ l) :
    #(bipyramidGraph l).edgeFinset = 3 * l := by
  classical
  have hsum := (bipyramidGraph l).sum_degrees_eq_twice_card_edges
  simp only [Fintype.sum_sum_type, bipyramidGraph_degree_equator hl,
    bipyramidGraph_degree_apex, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul] at hsum
  nlinarith

/-- A proof-relevant planar certificate specialized to the two spherical triangulations appearing
in Simonovits's theorem.  The TeX proof records their explicit sphere embeddings. -/
def CanonicalPlanarTriangulationModel {W : Type*} (H : SimpleGraph W) : Prop :=
  Nonempty (H ≃g (⊤ : SimpleGraph (Fin 4))) ∨
    ∃ l : ℕ, 3 ≤ l ∧ Nonempty (H ≃g bipyramidGraph l)

/-- A certified planar triangulation on more than three vertices, with the saturated Euler edge
count `3v-6`. -/
def IsCertifiedSaturatedPlanar {W : Type*} [Fintype W]
    (H : SimpleGraph W) : Prop :=
  CanonicalPlanarTriangulationModel H ∧
    3 < Fintype.card W ∧
    H.edgeSet.ncard = 3 * Fintype.card W - 6

lemma top_four_isCertifiedSaturatedPlanar :
    IsCertifiedSaturatedPlanar (⊤ : SimpleGraph (Fin 4)) := by
  refine ⟨Or.inl ⟨SimpleGraph.Iso.refl⟩, by simp, ?_⟩
  rw [edgeSet_ncard_eq_card_edgeFinset,
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  norm_num [Nat.choose]

lemma bipyramidGraph_isCertifiedSaturatedPlanar (l : ℕ) (hl : 3 ≤ l) :
    IsCertifiedSaturatedPlanar (bipyramidGraph l) := by
  refine ⟨Or.inr ⟨l, hl, ⟨SimpleGraph.Iso.refl⟩⟩, ?_, ?_⟩
  · simp
    omega
  · rw [edgeSet_ncard_eq_card_edgeFinset, bipyramidGraph_card_edges hl]
    simp
    omega

/-- An explicit saturated planar subgraph on more than three vertices, together with its copy in
the host graph.  `W` lives in the small universe because both canonical witness families do. -/
structure SaturatedPlanarSubgraph (V : Type*) (G : SimpleGraph V) where
  W : Type
  fintypeW : Fintype W
  H : SimpleGraph W
  certified : @IsCertifiedSaturatedPlanar W fintypeW H
  copy : H ⊑ G

def ContainsSaturatedPlanarBeyondTriangle {V : Type*} (G : SimpleGraph V) : Prop :=
  Nonempty (SaturatedPlanarSubgraph V G)

lemma HasTarget.to_saturatedPlanarSubgraph {V : Type*} {G : SimpleGraph V}
    (h : HasTarget G) : ContainsSaturatedPlanarBeyondTriangle G := by
  rcases h with h4 | ⟨l, hl, hb⟩
  · exact ⟨{
      W := Fin 4
      fintypeW := inferInstance
      H := ⊤
      certified := top_four_isCertifiedSaturatedPlanar
      copy := h4 }⟩
  · exact ⟨{
      W := Fin l ⊕ Bool
      fintypeW := inferInstance
      H := bipyramidGraph l
      certified := bipyramidGraph_isCertifiedSaturatedPlanar l hl
      copy := hb }⟩

lemma HasTarget.mono {V : Type*} {G H : SimpleGraph V} (hGH : G ≤ H)
    (hG : HasTarget G) : HasTarget H := by
  rcases hG with h4 | ⟨l, hl, hb⟩
  · exact Or.inl (h4.trans_le hGH)
  · exact Or.inr ⟨l, hl, hb.trans_le hGH⟩

lemma HasTarget.of_induce {V : Type*} (G : SimpleGraph V) (s : Set V)
    (h : HasTarget (G.induce s)) : HasTarget G := by
  rcases h with h4 | ⟨l, hl, hb⟩
  · exact Or.inl (h4.trans ⟨SimpleGraph.Copy.induce G s⟩)
  · exact Or.inr ⟨l, hl, hb.trans ⟨SimpleGraph.Copy.induce G s⟩⟩

/-- Four distinct, pairwise adjacent vertices give a copy of `K₄`. -/
lemma top_four_isContained_of_pairwise_adj {V : Type*} {G : SimpleGraph V}
    (f : Fin 4 → V) (hf : Function.Injective f)
    (hadj : ∀ i j : Fin 4, i ≠ j → G.Adj (f i) (f j)) :
    (⊤ : SimpleGraph (Fin 4)) ⊑ G := by
  refine ⟨⟨{ toFun := f, map_rel' := ?_ }, hf⟩⟩
  intro i j hij
  exact hadj i j (by simpa using hij)

lemma HasTarget.of_four_clique {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {a b c d : V} (hab : G.Adj a b) (hac : G.Adj a c) (had : G.Adj a d)
    (hbc : G.Adj b c) (hbd : G.Adj b d) (hcd : G.Adj c d) : HasTarget G := by
  apply Or.inl
  rw [← SimpleGraph.not_cliqueFree_iff_top_isContained 4]
  apply SimpleGraph.IsNClique.not_cliqueFree (s := {a, b, c, d})
  rw [SimpleGraph.isNClique_iff]
  constructor
  · simp [hab, hac, had, hbc, hbd, hcd, hab.ne, hac.ne, had.ne,
      hbc.ne, hbd.ne, hcd.ne]
  · simp [hab.ne, hac.ne, had.ne, hbc.ne, hbd.ne, hcd.ne]

/-- Removing one vertex removes exactly its degree inside the induced graph.  This is the
finite-set form used by the induction. -/
lemma edgeCountOn_erase {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    {x : V} (hx : x ∈ U) :
    edgeCountOn G (U.erase x) =
      edgeCountOn G U - (G.induce (U : Set V)).degree ⟨x, hx⟩ := by
  classical
  let xu : (U : Set V) := ⟨x, hx⟩
  let e : {y : (U : Set V) // y ∈ ({xu}ᶜ : Set (U : Set V))} ≃
      (U.erase x : Set V) :=
    { toFun := fun y ↦ ⟨y.1.1, Finset.mem_erase.mpr ⟨by
          intro h
          exact y.2 (Set.mem_singleton_iff.mpr (Subtype.ext h)), y.1.2⟩⟩
      invFun := fun y ↦ ⟨⟨y.1, Finset.mem_of_mem_erase y.2⟩, by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          intro h
          exact (Finset.ne_of_mem_erase y.2) (congrArg Subtype.val h)⟩
      left_inv := by intro y; rfl
      right_inv := by intro y; rfl }
  let iso : (G.induce (U : Set V)).induce ({xu}ᶜ : Set (U : Set V)) ≃g
      G.induce (U.erase x : Set V) :=
    { toEquiv := e
      map_rel_iff' := by intro a b; rfl }
  have hi := iso.card_edgeFinset_eq
  have hd := (G.induce (U : Set V)).card_edgeFinset_induce_compl_singleton xu
  have hr := (G.induce (U : Set V)).card_edgeFinset_deleteIncidenceSet xu
  rw [edgeCountOn_eq_card_edgeFinset, edgeCountOn_eq_card_edgeFinset]
  simpa only [xu] using hi.symm.trans (hd.trans hr)

lemma degree_induce_eq_card_filter {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    {x : V} (hx : x ∈ U) :
    (G.induce (U : Set V)).degree ⟨x, hx⟩ = #(U.filter (G.Adj x)) := by
  classical
  let e : (G.induce (U : Set V)).neighborSet (⟨x, hx⟩ : (U : Set V)) ≃
      (U.filter (G.Adj x) : Set V) :=
    { toFun := fun y ↦ ⟨y.1.1, Finset.mem_filter.mpr ⟨y.1.2, y.2⟩⟩
      invFun := fun y ↦ ⟨⟨y.1, (Finset.mem_filter.mp y.2).1⟩,
        (Finset.mem_filter.mp y.2).2⟩
      left_inv := by intro y; rfl
      right_inv := by intro y; rfl }
  calc
    (G.induce (U : Set V)).degree ⟨x, hx⟩ =
        Fintype.card ((G.induce (U : Set V)).neighborSet ⟨x, hx⟩) :=
      (SimpleGraph.card_neighborSet_eq_degree _ _).symm
    _ = Fintype.card (U.filter (G.Adj x) : Set V) := Fintype.card_congr e
    _ = #(U.filter (G.Adj x)) := Fintype.card_coe _

/-- Extend a copied equatorial cycle by two external universal vertices. -/
lemma bipyramid_isContained_of_cycle_copy {V : Type*} {G : SimpleGraph V} {l : ℕ}
    (f : (SimpleGraph.cycleGraph l).Copy G) (north south : V)
    (hns : north ≠ south) (hn : north ∉ Set.range f) (hs : south ∉ Set.range f)
    (hun : ∀ i : Fin l, G.Adj north (f i) ∧ G.Adj south (f i)) :
    bipyramidGraph l ⊑ G := by
  let F : Fin l ⊕ Bool → V := fun z ↦ match z with
    | .inl i => f i
    | .inr false => north
    | .inr true => south
  let hFhom : bipyramidGraph l →g G := {
    toFun := F
    map_rel' := by
      intro u v huv
      rcases u with i | b <;> rcases v with j | c
      · change G.Adj (f i) (f j)
        exact f.toHom.map_rel huv
      · cases c
        · change G.Adj (f i) north
          exact (hun i).1.symm
        · change G.Adj (f i) south
          exact (hun i).2.symm
      · cases b
        · change G.Adj north (f j)
          exact (hun j).1
        · change G.Adj south (f j)
          exact (hun j).2
      · exact False.elim huv }
  have hFinj : Function.Injective F := by
    intro u v huv
    rcases u with i | b <;> rcases v with j | c
    · change f i = f j at huv
      exact congrArg Sum.inl (f.injective huv)
    · exfalso
      cases c
      · change f i = north at huv
        exact hn ⟨i, huv⟩
      · change f i = south at huv
        exact hs ⟨i, huv⟩
    · exfalso
      cases b
      · change north = f j at huv
        exact hn ⟨j, huv.symm⟩
      · change south = f j at huv
        exact hs ⟨j, huv.symm⟩
    · cases b <;> cases c
      · rfl
      · change north = south at huv
        exact (hns huv).elim
      · change south = north at huv
        exact (hns huv.symm).elim
      · rfl
  exact ⟨⟨hFhom, hFinj⟩⟩

/-- A tree together with a new vertex joined to two tree vertices contains a cycle. -/
lemma not_isAcyclic_tree_insert_two_neighbors {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A : Finset V) (x u v : V)
    (hT : (G.induce (A : Set V)).IsTree) (hxA : x ∉ A)
    (hu : u ∈ A) (hv : v ∈ A) (huv : u ≠ v)
    (hxu : G.Adj x u) (hxv : G.Adj x v) :
    ¬(G.induce ((insert x A : Finset V) : Set V)).IsAcyclic := by
  classical
  let C := insert x A
  let HC := G.induce (C : Set V)
  let inc : G.induce (A : Set V) →g HC :=
    { toFun := fun y ↦ ⟨y.1, by simp [C, y.2]⟩
      map_rel' := by intro a b hab; exact hab }
  have hinc : Function.Injective inc := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun z : (C : Set V) ↦ z.1) h
  let uA : (A : Set V) := ⟨u, hu⟩
  let vA : (A : Set V) := ⟨v, hv⟩
  let uC : (C : Set V) := inc uA
  let vC : (C : Set V) := inc vA
  let xC : (C : Set V) := ⟨x, by simp [C]⟩
  obtain ⟨p, hp⟩ := hT.connected.exists_isPath uA vA
  let pC := p.map inc
  have hpC : pC.IsPath := hp.map hinc
  have hxuC : HC.Adj xC uC := hxu
  have hxvC : HC.Adj xC vC := hxv
  let q : HC.Walk uC vC := .cons hxuC.symm (.cons hxvC .nil)
  have hxv_ne : xC ≠ vC := by
    intro h
    apply hxA
    have : x = v := congrArg Subtype.val h
    simpa [this] using hv
  have huvC : uC ≠ vC := by
    intro h
    exact huv (congrArg Subtype.val h)
  have hux_ne : uC ≠ xC := by
    intro h
    apply hxA
    have : u = x := congrArg Subtype.val h
    simpa [← this] using hu
  have hq : q.IsPath := by
    apply SimpleGraph.Walk.IsPath.cons
    · apply SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil
      simp [hxv_ne]
    · simp [huvC, hux_ne]
  intro hac
  change HC.IsAcyclic at hac
  have heq := hac.subsingleton_path uC vC |>.elim
      (⟨pC, hpC⟩ : HC.Path uC vC) (⟨q, hq⟩ : HC.Path uC vC)
  have hwalk : pC = q := congrArg Subtype.val heq
  have hxq : xC ∈ q.support := by simp [q]
  rw [← hwalk, SimpleGraph.Walk.support_map] at hxq
  rcases List.mem_map.mp hxq with ⟨y, hy, hey⟩
  apply hxA
  have hval : y.1 = x := congrArg Subtype.val hey
  simpa [hval] using y.2

/-- Two external universal vertices turn any cycle in `C` into a bipyramid. -/
lemma hasTarget_of_not_isAcyclic_two_apices {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V) (north south : V)
    (hacyc : ¬(G.induce (C : Set V)).IsAcyclic)
    (hnC : north ∉ C) (hsC : south ∉ C) (hns : north ≠ south)
    (hun : ∀ z ∈ C, G.Adj north z ∧ G.Adj south z) : HasTarget G := by
  classical
  have hcycle : ∃ l : ℕ, 3 ≤ l ∧
      SimpleGraph.cycleGraph l ⊑ G.induce (C : Set V) := by
    by_contra h
    apply hacyc
    rw [SimpleGraph.isAcyclic_iff_free_cycleGraph]
    intro l hl hcopy
    exact h ⟨l, hl, hcopy⟩
  obtain ⟨l, hl, ⟨f⟩⟩ := hcycle
  let fG : (SimpleGraph.cycleGraph l).Copy G :=
    (SimpleGraph.Copy.induce G (C : Set V)).comp f
  have hnrange : north ∉ Set.range fG := by
    rintro ⟨i, hi⟩
    apply hnC
    have : north = (f i).1 := hi.symm
    simpa [this] using (f i).2
  have hsrange : south ∉ Set.range fG := by
    rintro ⟨i, hi⟩
    apply hsC
    have : south = (f i).1 := hi.symm
    simpa [this] using (f i).2
  refine Or.inr ⟨l, hl, bipyramid_isContained_of_cycle_copy fG north south hns
    hnrange hsrange ?_⟩
  intro i
  exact hun (f i).1 (f i).2

/-- In the induction, two neighbours on each side immediately give a bipyramid. -/
lemma hasTarget_of_two_neighbors_on_both_sides {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (x : V)
    (hT : (G.induce (A : Set V)).IsTree)
    (hdisj : Disjoint (A : Set V) (B : Set V))
    (hcross : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hxA : x ∉ A) (hxB : x ∉ B)
    (hSA : 2 ≤ #(A.filter (G.Adj x)))
    (hSB : 2 ≤ #(B.filter (G.Adj x))) : HasTarget G := by
  classical
  have hSA' : 1 < #(A.filter (G.Adj x)) := by omega
  obtain ⟨u, huS, v, hvS, huv⟩ := Finset.one_lt_card.mp hSA'
  have hSB' : 1 < #(B.filter (G.Adj x)) := by omega
  obtain ⟨north, hnS, south, hsS, hns⟩ := Finset.one_lt_card.mp hSB'
  have hu := (Finset.mem_filter.mp huS).1
  have hv := (Finset.mem_filter.mp hvS).1
  have hxu := (Finset.mem_filter.mp huS).2
  have hxv := (Finset.mem_filter.mp hvS).2
  have hnB := (Finset.mem_filter.mp hnS).1
  have hsB := (Finset.mem_filter.mp hsS).1
  have hxn := (Finset.mem_filter.mp hnS).2
  have hxs := (Finset.mem_filter.mp hsS).2
  have hacyc := not_isAcyclic_tree_insert_two_neighbors G A x u v hT hxA hu hv huv hxu hxv
  apply hasTarget_of_not_isAcyclic_two_apices G (insert x A) north south hacyc
  · simp only [Finset.mem_insert]
    intro h
    rcases h with rfl | hnA
    · exact hxB hnB
    · exact hdisj.le_bot ⟨hnA, hnB⟩
  · simp only [Finset.mem_insert]
    intro h
    rcases h with rfl | hsA
    · exact hxB hsB
    · exact hdisj.le_bot ⟨hsA, hsB⟩
  · exact hns
  · intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hzA
    · exact ⟨hxn.symm, hxs.symm⟩
    · exact ⟨(hcross z hzA north hnB).symm, (hcross z hzA south hsB).symm⟩

/-- Adding a new vertex with exactly one neighbour to a finite tree again gives a tree. -/
lemma isTree_induce_insert_of_one_neighbor {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (x u : V) (hT : (G.induce (A : Set V)).IsTree)
    (hxA : x ∉ A) (hu : u ∈ A) (hxu : G.Adj x u)
    (hone : #(A.filter (G.Adj x)) = 1) :
    (G.induce ((insert x A : Finset V) : Set V)).IsTree := by
  classical
  let C : Finset V := insert x A
  let HC := G.induce (C : Set V)
  let inc : G.induce (A : Set V) →g HC :=
    { toFun := fun y ↦ ⟨y.1, by simp [C, y.2]⟩
      map_rel' := by intro a b hab; exact hab }
  let xC : (C : Set V) := ⟨x, by simp [C]⟩
  let uA : (A : Set V) := ⟨u, hu⟩
  let uC : (C : Set V) := inc uA
  have hxuC : HC.Adj xC uC := hxu
  have hconn : HC.Connected := by
    refine { preconnected := ?_, nonempty := ⟨xC⟩ }
    intro y z
    have hy : y.1 = x ∨ y.1 ∈ A := by simpa [C] using y.2
    have hz : z.1 = x ∨ z.1 ∈ A := by simpa [C] using z.2
    rcases hy with hy | hy <;> rcases hz with hz | hz
    · have hy' : y = xC := Subtype.ext hy
      have hz' : z = xC := Subtype.ext hz
      rw [hy', hz']
    · have hy' : y = xC := Subtype.ext hy
      rw [hy']
      let zA : (A : Set V) := ⟨z.1, hz⟩
      have hz' : inc zA = z := Subtype.ext rfl
      rw [← hz']
      exact hxuC.reachable.trans (hT.connected uA zA |>.map inc)
    · have hz' : z = xC := Subtype.ext hz
      rw [hz']
      let yA : (A : Set V) := ⟨y.1, hy⟩
      have hy' : inc yA = y := Subtype.ext rfl
      rw [← hy']
      exact (hT.connected yA uA |>.map inc).trans hxuC.symm.reachable
    · let yA : (A : Set V) := ⟨y.1, hy⟩
      let zA : (A : Set V) := ⟨z.1, hz⟩
      have hy' : inc yA = y := Subtype.ext rfl
      have hz' : inc zA = z := Subtype.ext rfl
      rw [← hy', ← hz']
      exact hT.connected yA zA |>.map inc
  have hdeg : HC.degree xC = 1 := by
    rw [degree_induce_eq_card_filter]
    have hloop : ¬G.Adj x x := G.loopless.irrefl x
    simp only [C, Finset.filter_insert, if_neg hloop]
    exact hone
  have herase := edgeCountOn_erase G C xC.2
  have hOld : edgeCountOn G A + 1 = A.card := by
    rw [edgeCountOn_eq_card_edgeFinset]
    simpa using hT.card_edgeFinset
  have hpos : 1 ≤ edgeCountOn G C := by
    have := HC.degree_le_card_edgeFinset xC
    rw [edgeCountOn_eq_card_edgeFinset]
    simpa [HC, hdeg] using this
  have hE : edgeCountOn G C + 1 = C.card := by
    have hEraseSet : C.erase x = A := by simp [C, hxA]
    rw [hEraseSet, hdeg] at herase
    have hCcard : C.card = A.card + 1 := by simp [C, hxA]
    omega
  change HC.IsTree
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨hconn, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    ← SimpleGraph.edgeFinset_card]
  rw [edgeCountOn_eq_card_edgeFinset] at hE
  simpa [HC] using hE

/-- A centre joined to every vertex of an independent set is a tree. -/
lemma isTree_induce_star {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset V) (u : V)
    (huB : u ∉ B)
    (hB : ∀ b₁ ∈ B, ∀ b₂ ∈ B, ¬G.Adj b₁ b₂)
    (hu : ∀ b ∈ B, G.Adj u b) :
    (G.induce ((insert u B : Finset V) : Set V)).IsTree := by
  classical
  induction B using Finset.induction_on with
  | empty =>
      have hsingle : (G.induce (({u} : Finset V) : Set V)).IsTree := by
        letI : Nonempty (({u} : Finset V) : Set V) := ⟨⟨u, by simp⟩⟩
        letI : Subsingleton (({u} : Finset V) : Set V) := ⟨by
          intro a b
          apply Subtype.ext
          have ha : a.1 = u := by simpa using a.2
          have hb : b.1 = u := by simpa using b.2
          exact ha.trans hb.symm⟩
        exact SimpleGraph.IsTree.of_subsingleton
      simpa using hsingle
  | @insert b B hb ih =>
      have hub : u ≠ b := by
        intro h
        apply huB
        simp [h]
      have huB' : u ∉ B := by
        intro h
        exact huB (Finset.mem_insert_of_mem h)
      have hB' : ∀ b₁ ∈ B, ∀ b₂ ∈ B, ¬G.Adj b₁ b₂ := by
        intro b₁ hb₁ b₂ hb₂
        exact hB b₁ (Finset.mem_insert_of_mem hb₁) b₂ (Finset.mem_insert_of_mem hb₂)
      have hu' : ∀ z ∈ B, G.Adj u z := by
        intro z hz
        exact hu z (Finset.mem_insert_of_mem hz)
      have ihT := ih huB' hB' hu'
      have hbA : b ∉ insert u B := by simp [hb, hub.symm]
      have hbu : G.Adj b u := (hu b (by simp)).symm
      have hone : #((insert u B).filter (G.Adj b)) = 1 := by
        have heq : (insert u B).filter (G.Adj b) = {u} := by
          ext z
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨rfl | hz, hadj⟩
            · rfl
            · exact False.elim (hB b (by simp) z (by simp [hz]) hadj)
          · rintro rfl
            exact ⟨Or.inl rfl, hbu⟩
        rw [heq]
        simp
      have hleaf := isTree_induce_insert_of_one_neighbor G (insert u B) b u
        ihT hbA (by simp) hbu hone
      have heq : insert b (insert u B) = insert u (insert b B) := by
        ext z
        simp [or_left_comm]
      rw [← heq]
      exact hleaf

/-- The rearranged exceptional configuration is the broom-shaped tree used in the proof. -/
lemma isTree_induce_broom {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset V) (u x p : V)
    (huB : u ∉ B) (hxB : x ∉ B) (hxu : x ≠ u) (hp : p ∈ B)
    (hB : ∀ b₁ ∈ B, ∀ b₂ ∈ B, ¬G.Adj b₁ b₂)
    (hu : ∀ b ∈ B, G.Adj u b)
    (hxp : G.Adj x p) (hxu_not : ¬G.Adj x u)
    (hxonly : ∀ b ∈ B, G.Adj x b → b = p) :
    (G.induce ((insert x (insert u B) : Finset V) : Set V)).IsTree := by
  classical
  have hstar := isTree_induce_star G B u huB hB hu
  have hxD : x ∉ insert u B := by simp [hxB, hxu]
  have hone : #((insert u B).filter (G.Adj x)) = 1 := by
    have heq : (insert u B).filter (G.Adj x) = {p} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | hz, hadj⟩
        · exact False.elim (hxu_not hadj)
        · exact hxonly z hz hadj
      · rintro rfl
        exact ⟨Or.inr hp, hxp⟩
    rw [heq]
    simp
  exact isTree_induce_insert_of_one_neighbor G (insert u B) x p hstar hxD
    (by simp [hp]) hxp hone

/-- If deleting `u` leaves no edges in a tree, then every other vertex is adjacent to `u`. -/
lemma tree_center_of_independent_erase {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A : Finset V) (u : V)
    (hT : (G.induce (A : Set V)).IsTree) (hu : u ∈ A)
    (hno : ∀ y ∈ A.erase u, ∀ z ∈ A.erase u, ¬G.Adj y z) :
    ∀ z ∈ A.erase u, G.Adj u z := by
  classical
  intro z hz
  let uA : (A : Set V) := ⟨u, hu⟩
  let zA : (A : Set V) := ⟨z, Finset.mem_of_mem_erase hz⟩
  obtain ⟨p, hp⟩ := hT.connected.exists_isPath uA zA
  have huz : u ≠ z := (Finset.ne_of_mem_erase hz).symm
  have hnil : ¬p.Nil := by
    intro h
    exact huz (congrArg Subtype.val (hp.nil_iff_eq.mp h))
  have hadj := p.adj_penultimate hnil
  by_cases heq : p.penultimate = uA
  · simpa [heq] using hadj
  · exfalso
    have hpA : p.penultimate.1 ∈ A.erase u := Finset.mem_erase.mpr ⟨by
      intro h
      apply heq
      exact Subtype.ext h, p.penultimate.2⟩
    exact hno p.penultimate.1 hpA z hz hadj

/-- The extension step in Simonovits's sharp induction. -/
lemma extend_balanced_tree_join {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U A B : Finset V) (x : V) (hxU : x ∉ U)
    (hjoin : IsBalancedTreeJoinOn G U A B)
    (hdeg : #(A.filter (G.Adj x)) + #(B.filter (G.Adj x)) =
      stepDegree (U.card + 1)) :
    HasTarget G ∨ ∃ A' B', IsBalancedTreeJoinOn G (insert x U) A' B' := by
  classical
  rcases hjoin with ⟨hpart, hdisj, hT, hBind, hcross, hBA, hAB⟩
  have hpartF : A ∪ B = U := by
    ext z
    have hz := Set.ext_iff.mp hpart z
    simpa only [Finset.mem_union, Finset.mem_coe, Set.mem_union] using hz
  have hdisjF : Disjoint A B := by simpa only [Finset.disjoint_coe] using hdisj
  have hxA : x ∉ A := by
    intro hx
    apply hxU
    rw [← hpartF]
    exact Finset.mem_union_left B hx
  have hxB : x ∉ B := by
    intro hx
    apply hxU
    rw [← hpartF]
    exact Finset.mem_union_right A hx
  have hUcard : U.card = A.card + B.card := by
    rw [← hpartF, Finset.card_union_of_disjoint hdisjF]
  let SA := A.filter (G.Adj x)
  let SB := B.filter (G.Adj x)
  have hSAle : SA.card ≤ A.card := Finset.card_filter_le _ _
  have hSBle : SB.card ≤ B.card := Finset.card_filter_le _ _
  change SA.card + SB.card = stepDegree (U.card + 1) at hdeg
  by_cases htwo : 2 ≤ SA.card ∧ 2 ≤ SB.card
  · exact Or.inl (hasTarget_of_two_neighbors_on_both_sides G A B x hT hdisj
      hcross hxA hxB htwo.1 htwo.2)
  have hsmall : SA.card ≤ 1 ∨ SB.card ≤ 1 := by omega
  by_cases hleaf : SA.card = 1 ∧ SB.card = B.card
  · rcases hleaf with ⟨hSA1, hSBcard⟩
    obtain ⟨u, hSAeq⟩ := Finset.card_eq_one.mp hSA1
    have huS : u ∈ SA := by simp [hSAeq]
    have huA : u ∈ A := (Finset.mem_filter.mp huS).1
    have hxu : G.Adj x u := (Finset.mem_filter.mp huS).2
    have hSBeq : SB = B :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
    have hnewT := isTree_induce_insert_of_one_neighbor G A x u hT hxA huA hxu hSA1
    refine Or.inr ⟨insert x A, B, ?_⟩
    refine ⟨?_, ?_, hnewT, hBind, ?_, ?_, ?_⟩
    · have heq : insert x A ∪ B = insert x U := by
        rw [insert_union, hpartF]
      simpa only [Finset.coe_union, Finset.coe_insert] using
        congrArg (fun s : Finset V ↦ (s : Set V)) heq
    · rw [Set.disjoint_left]
      intro z hz hzB
      rcases Finset.mem_insert.mp hz with rfl | hzA
      · exact hxB hzB
      · exact hdisj.le_bot ⟨hzA, hzB⟩
    · intro a ha b hb
      rcases Finset.mem_insert.mp ha with rfl | haA
      · have : b ∈ SB := by rw [hSBeq]; exact hb
        exact (Finset.mem_filter.mp this).2
      · exact hcross a haA b hb
    · simp [hxA]
      omega
    · simp [hxA]
      unfold stepDegree at hdeg
      omega
  by_cases hind : SB.card = 0 ∧ SA.card = A.card
  · rcases hind with ⟨hSB0, hSAcard⟩
    have hSAeq : SA = A :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
    have hxBnone : ∀ b ∈ B, ¬G.Adj x b := by
      intro b hb hadj
      have : b ∈ SB := Finset.mem_filter.mpr ⟨hb, hadj⟩
      have : 0 < SB.card := Finset.card_pos.mpr ⟨b, this⟩
      omega
    have hBno : ∀ b₁ ∈ B, ∀ b₂ ∈ B, ¬G.Adj b₁ b₂ := by
      intro b₁ hb₁ b₂ hb₂ hadj
      have h : (G.induce (B : Set V)).Adj ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩ := hadj
      rw [hBind] at h
      exact h
    have hnewB : G.induce ((insert x B : Finset V) : Set V) = ⊥ := by
      ext y z
      simp only [SimpleGraph.induce_adj, SimpleGraph.bot_adj, iff_false]
      intro hadj
      have hy : y.1 = x ∨ y.1 ∈ B := by simpa using y.2
      have hz : z.1 = x ∨ z.1 ∈ B := by simpa using z.2
      rcases hy with hy | hy <;> rcases hz with hz | hz
      · exact G.loopless.irrefl x (by simpa [hy, hz] using hadj)
      · exact hxBnone z hz (by simpa [hy] using hadj)
      · exact hxBnone y hy (by simpa [hz] using hadj.symm)
      · exact hBno y hy z hz hadj
    refine Or.inr ⟨A, insert x B, ?_⟩
    refine ⟨?_, ?_, hT, hnewB, ?_, ?_, ?_⟩
    · have heq : A ∪ insert x B = insert x U := by
        rw [Finset.union_insert, hpartF]
      simpa only [Finset.coe_union, Finset.coe_insert] using
        congrArg (fun s : Finset V ↦ (s : Set V)) heq
    · rw [Set.disjoint_left]
      intro z hzA hz
      rcases Finset.mem_insert.mp hz with rfl | hzB
      · exact hxA hzA
      · exact hdisj.le_bot ⟨hzA, hzB⟩
    · intro a ha b hb
      rcases Finset.mem_insert.mp hb with rfl | hbB
      · have : a ∈ SA := by rw [hSAeq]; exact ha
        exact (Finset.mem_filter.mp this).2.symm
      · exact hcross a ha b hbB
    · simp [hxB]
      unfold stepDegree at hdeg
      omega
    · simp [hxB]
      omega
  by_cases heqcard : A.card = B.card
  · have hSAcard : SA.card = A.card := by
      unfold stepDegree at hdeg
      omega
    have hSB1 : SB.card = 1 := by
      unfold stepDegree at hdeg
      omega
    have hAge2 : 2 ≤ A.card := by
      by_contra h
      have : A.card ≤ 1 := by omega
      have hleaf' : SA.card = 1 ∧ SB.card = B.card := by omega
      exact hleaf hleaf'
    have hSAeq : SA = A :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
    obtain ⟨p, hSBeq⟩ := Finset.card_eq_one.mp hSB1
    have hpS : p ∈ SB := by simp [hSBeq]
    have hpB : p ∈ B := (Finset.mem_filter.mp hpS).1
    have hxp : G.Adj x p := (Finset.mem_filter.mp hpS).2
    have hEnonempty : (G.induce (A : Set V)).edgeFinset.Nonempty := by
      rw [← Finset.card_pos]
      have hcardT := hT.card_edgeFinset
      have hcardA : Fintype.card (A : Set V) = A.card := Fintype.card_coe _
      omega
    obtain ⟨e, he⟩ := hEnonempty
    rw [SimpleGraph.mem_edgeFinset] at he
    induction e using Sym2.inductionOn with
    | _ y z =>
      have hyS : y.1 ∈ SA := by rw [hSAeq]; exact y.2
      have hzS : z.1 ∈ SA := by rw [hSAeq]; exact z.2
      exact Or.inl (HasTarget.of_four_clique hxp (Finset.mem_filter.mp hyS).2
        (Finset.mem_filter.mp hzS).2 (hcross y y.2 p hpB).symm
        (hcross z z.2 p hpB).symm he)
  · have hdiff : A.card = B.card + 1 ∨ A.card = B.card + 2 := by omega
    have hSB1 : SB.card = 1 := by
      unfold stepDegree at hdeg
      omega
    have hSApred : SA.card + 1 = A.card := by
      unfold stepDegree at hdeg
      omega
    obtain ⟨p, hSBeq⟩ := Finset.card_eq_one.mp hSB1
    have hpS : p ∈ SB := by simp [hSBeq]
    have hpB : p ∈ B := (Finset.mem_filter.mp hpS).1
    have hxp : G.Adj x p := (Finset.mem_filter.mp hpS).2
    have hSAssub : SA ⊂ A := by
      rw [Finset.ssubset_iff_subset_ne]
      exact ⟨Finset.filter_subset _ _, fun h ↦ by
        have := congrArg Finset.card h
        omega⟩
    obtain ⟨u, huA, huS⟩ := Finset.exists_of_ssubset hSAssub
    have hSAerase : SA = A.erase u := by
      apply Finset.eq_of_subset_of_card_le
      · intro z hz
        exact Finset.mem_erase.mpr ⟨fun h ↦ huS (h ▸ hz), (Finset.mem_filter.mp hz).1⟩
      · simp [huA]
        omega
    by_cases hedge : ∃ y ∈ A.erase u, ∃ z ∈ A.erase u, G.Adj y z
    · obtain ⟨y, hy, z, hz, hyz⟩ := hedge
      have hyS : y ∈ SA := by rw [hSAerase]; exact hy
      have hzS : z ∈ SA := by rw [hSAerase]; exact hz
      exact Or.inl (HasTarget.of_four_clique hxp (Finset.mem_filter.mp hyS).2
        (Finset.mem_filter.mp hzS).2
        (hcross y (Finset.mem_of_mem_erase hy) p hpB).symm
        (hcross z (Finset.mem_of_mem_erase hz) p hpB).symm hyz)
    · push_neg at hedge
      have hBno : ∀ b₁ ∈ B, ∀ b₂ ∈ B, ¬G.Adj b₁ b₂ := by
        intro b₁ hb₁ b₂ hb₂ hadj
        have h : (G.induce (B : Set V)).Adj ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩ := hadj
        rw [hBind] at h
        exact h
      have huB : u ∉ B := by
        intro hu
        exact hdisj.le_bot ⟨huA, hu⟩
      have hxu_not : ¬G.Adj x u := by
        intro hadj
        exact huS (Finset.mem_filter.mpr ⟨huA, hadj⟩)
      have hxonly : ∀ b ∈ B, G.Adj x b → b = p := by
        intro b hb hadj
        have : b ∈ SB := Finset.mem_filter.mpr ⟨hb, hadj⟩
        rw [hSBeq] at this
        simpa using this
      have huall : ∀ b ∈ B, G.Adj u b := fun b hb ↦ hcross u huA b hb
      have hxu_ne : x ≠ u := fun h ↦ hxA (h ▸ huA)
      have hbroom := isTree_induce_broom G B u x p huB hxB
        hxu_ne hpB hBno huall hxp hxu_not hxonly
      have hcenter := tree_center_of_independent_erase G A u hT huA hedge
      have hnewInd : G.induce ((A.erase u : Finset V) : Set V) = ⊥ := by
        ext y z
        simp only [SimpleGraph.induce_adj, SimpleGraph.bot_adj, iff_false]
        exact hedge y y.2 z z.2
      refine Or.inr ⟨insert x (insert u B), A.erase u, ?_⟩
      refine ⟨?_, ?_, hbroom, hnewInd, ?_, ?_, ?_⟩
      · have heq : insert x (insert u B) ∪ A.erase u = insert x U := by
          ext z
          rw [← hpartF]
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro ((rfl | rfl | hzB) | ⟨_, hzA⟩)
            · exact Or.inl rfl
            · exact Or.inr (Or.inl huA)
            · exact Or.inr (Or.inr hzB)
            · exact Or.inr (Or.inl hzA)
          · rintro (rfl | hzA | hzB)
            · exact Or.inl (Or.inl rfl)
            · by_cases hzu : z = u
              · exact Or.inl (Or.inr (Or.inl hzu))
              · exact Or.inr ⟨hzu, hzA⟩
            · exact Or.inl (Or.inr (Or.inr hzB))
        simpa only [Finset.coe_union, Finset.coe_insert] using
          congrArg (fun s : Finset V ↦ (s : Set V)) heq
      · rw [Set.disjoint_left]
        intro z hz hze
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact hxA (Finset.mem_of_mem_erase hze)
        · rcases Finset.mem_insert.mp hz with rfl | hzB
          · exact (Finset.ne_of_mem_erase hze) rfl
          · exact hdisj.le_bot ⟨Finset.mem_of_mem_erase hze, hzB⟩
      · intro a ha z hz
        rcases Finset.mem_insert.mp ha with rfl | ha
        · have : z ∈ SA := by rw [hSAerase]; exact hz
          exact (Finset.mem_filter.mp this).2
        · rcases Finset.mem_insert.mp ha with rfl | haB
          · exact hcenter z hz
          · exact (hcross z (Finset.mem_of_mem_erase hz) a haB).symm
      · have htreecard : #(insert x (insert u B)) = B.card + 2 := by
          simp [hxB, huB, hxu_ne]
        have hindcard : #(A.erase u) = A.card - 1 := by simp [huA]
        rw [htreecard, hindcard]
        omega
      · have htreecard : #(insert x (insert u B)) = B.card + 2 := by
          simp [hxB, huB, hxu_ne]
        have hindcard : #(A.erase u) = A.card - 1 := by simp [huA]
        rw [htreecard, hindcard]
        omega

/-- Adding a missing chord to a spanning tree creates a cycle. -/
lemma not_isAcyclic_of_tree_le_extra_edge {V : Type*} [DecidableEq V]
    (H G : SimpleGraph V) (A : Finset V) (hHG : H ≤ G)
    (hT : (H.induce (A : Set V)).IsTree) {u v : V}
    (hu : u ∈ A) (hv : v ∈ A) (hGuv : G.Adj u v) (hHuv : ¬H.Adj u v) :
    ¬(G.induce (A : Set V)).IsAcyclic := by
  let uA : (A : Set V) := ⟨u, hu⟩
  let vA : (A : Set V) := ⟨v, hv⟩
  intro hacyc
  have hleTree : H.induce (A : Set V) ≤ G.induce (A : Set V) := fun _ _ h ↦ hHG h
  have hleEdge : SimpleGraph.edge uA vA ≤ G.induce (A : Set V) := by
    rw [SimpleGraph.edge_le_iff]
    exact Or.inr hGuv
  have hsup : H.induce (A : Set V) ⊔ SimpleGraph.edge uA vA ≤
      G.induce (A : Set V) := sup_le hleTree hleEdge
  have hs := hacyc.anti hsup
  rw [SimpleGraph.isAcyclic_sup_fromEdgeSet_iff] at hs
  rcases hs.2 (hT.connected uA vA) with huv | hadj
  · exact hGuv.ne (congrArg Subtype.val huv)
  · exact hHuv hadj

/-- One additional edge over a balanced tree join forces one of the two target graphs. -/
lemma augment_balanced_tree_join {V : Type*} [Fintype V] [DecidableEq V]
    (H G : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel G.Adj]
    (U A B : Finset V) (hU4 : 4 ≤ U.card) (hHG : H ≤ G)
    (hjoin : IsBalancedTreeJoinOn H U A B)
    {u v : V} (huU : u ∈ U) (hvU : v ∈ U)
    (hGuv : G.Adj u v) (hHuv : ¬H.Adj u v) : HasTarget G := by
  classical
  rcases hjoin with ⟨hpart, hdisj, hT, hBind, hcross, hBA, hAB⟩
  have hpartF : A ∪ B = U := by
    ext z
    have hz := Set.ext_iff.mp hpart z
    simpa only [Finset.mem_union, Finset.mem_coe, Set.mem_union] using hz
  have hdisjF : Disjoint A B := by simpa only [Finset.disjoint_coe] using hdisj
  have hUcard : U.card = A.card + B.card := by
    rw [← hpartF, Finset.card_union_of_disjoint hdisjF]
  have hu : u ∈ A ∨ u ∈ B := by
    rw [← Finset.mem_union, hpartF]
    exact huU
  have hv : v ∈ A ∨ v ∈ B := by
    rw [← Finset.mem_union, hpartF]
    exact hvU
  rcases hu with huA | huB <;> rcases hv with hvA | hvB
  · have hacyc := not_isAcyclic_of_tree_le_extra_edge H G A hHG hT huA hvA hGuv hHuv
    by_cases hB2 : 2 ≤ B.card
    · have hB1 : 1 < B.card := by omega
      obtain ⟨north, hnB, south, hsB, hns⟩ := Finset.one_lt_card.mp hB1
      apply hasTarget_of_not_isAcyclic_two_apices G A north south hacyc
      · intro hnA
        exact hdisj.le_bot ⟨hnA, hnB⟩
      · intro hsA
        exact hdisj.le_bot ⟨hsA, hsB⟩
      · exact hns
      · intro z hz
        exact ⟨hHG (hcross z hz north hnB).symm,
          hHG (hcross z hz south hsB).symm⟩
    · have hBcard : B.card = 1 := by omega
      have hAcard : A.card = 3 := by omega
      obtain ⟨b, hBeq⟩ := Finset.card_eq_one.mp hBcard
      have hbB : b ∈ B := by simp [hBeq]
      have hcycle : ∃ l : ℕ, 3 ≤ l ∧
          SimpleGraph.cycleGraph l ⊑ G.induce (A : Set V) := by
        by_contra h
        apply hacyc
        rw [SimpleGraph.isAcyclic_iff_free_cycleGraph]
        intro l hl hc
        exact h ⟨l, hl, hc⟩
      obtain ⟨l, hl, ⟨f⟩⟩ := hcycle
      have hle : l ≤ 3 := by
        rw [← hAcard, ← Fintype.card_coe, ← Fintype.card_fin l]
        exact Fintype.card_le_of_injective f f.injective
      have hl3 : l = 3 := by omega
      subst l
      let fG : (SimpleGraph.cycleGraph 3).Copy G :=
        (SimpleGraph.Copy.induce G (A : Set V)).comp f
      have h01 : G.Adj (fG 0) (fG 1) := fG.toHom.map_rel (by
        rw [SimpleGraph.cycleGraph_three_eq_top]
        simp)
      have h02 : G.Adj (fG 0) (fG 2) := fG.toHom.map_rel (by
        rw [SimpleGraph.cycleGraph_three_eq_top]
        simp)
      have h12 : G.Adj (fG 1) (fG 2) := fG.toHom.map_rel (by
        rw [SimpleGraph.cycleGraph_three_eq_top]
        simp)
      exact HasTarget.of_four_clique
        (hHG (hcross (f 0).1 (f 0).2 b hbB).symm)
        (hHG (hcross (f 1).1 (f 1).2 b hbB).symm)
        (hHG (hcross (f 2).1 (f 2).2 b hbB).symm) h01 h02 h12
  · exact False.elim (hHuv (hcross u huA v hvB))
  · exact False.elim (hHuv (hcross v hvA u huB).symm)
  · have huv : u ≠ v := hGuv.ne
    have hB2 : 2 ≤ B.card := by
      have : 1 < B.card := Finset.one_lt_card.mpr ⟨u, huB, v, hvB, huv⟩
      omega
    have hA2 : 2 ≤ A.card := by omega
    have hEnonempty : (H.induce (A : Set V)).edgeFinset.Nonempty := by
      rw [← Finset.card_pos]
      have hcardT := hT.card_edgeFinset
      have hcardA : Fintype.card (A : Set V) = A.card := Fintype.card_coe _
      omega
    obtain ⟨e, he⟩ := hEnonempty
    rw [SimpleGraph.mem_edgeFinset] at he
    induction e using Sym2.inductionOn with
    | _ y z =>
      exact HasTarget.of_four_clique hGuv
        (hHG (hcross y y.2 u huB).symm) (hHG (hcross z z.2 u huB).symm)
        (hHG (hcross y y.2 v hvB).symm) (hHG (hcross z z.2 v hvB).symm)
        (hHG he)

/-- Keep any prescribed number of the edges induced on `U`, and discard all other edges. -/
lemma exists_subgraph_edgeCountOn_eq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) {m : ℕ}
    (hm : m ≤ edgeCountOn G U) :
    ∃ H : SimpleGraph V, H ≤ G ∧ edgeCountOn H U = m := by
  classical
  let E := G.edgeFinset.filter fun e ↦ e.toFinset ⊆ U
  have hEm : m ≤ E.card := by
    rw [edgeCountOn_eq_card_edgeFinset] at hm
    rw [SimpleGraph.card_filter_edgeFinset_toFinset_subset]
    exact hm
  obtain ⟨K, hKE, hKcard⟩ := Finset.exists_subset_card_eq hEm
  let H : SimpleGraph V := SimpleGraph.fromEdgeSet (K : Set (Sym2 V))
  refine ⟨H, ?_, ?_⟩
  · rw [SimpleGraph.fromEdgeSet_le]
    intro e he
    have heK : e ∈ K := he.1
    have heE : e ∈ E := hKE heK
    exact SimpleGraph.mem_edgeFinset.mp (Finset.mem_filter.mp heE).1
  · have hsupp : H.support ⊆ (U : Set V) := by
      intro x hx
      rw [SimpleGraph.mem_support] at hx
      obtain ⟨y, hxy⟩ := hx
      have heK : s(x, y) ∈ K :=
        ((SimpleGraph.fromEdgeSet_adj (K : Set (Sym2 V))).mp hxy).1
      have heE : s(x, y) ∈ E := hKE heK
      have hsub := (Finset.mem_filter.mp heE).2
      exact hsub (by simp)
    have hKEdiag : Disjoint (K : Set (Sym2 V)) Sym2.diagSet := by
      rw [Set.disjoint_left]
      intro e heK hediag
      have heE : e ∈ E := hKE heK
      exact G.not_isDiag_of_mem_edgeFinset (Finset.mem_filter.mp heE).1 hediag
    have hedge : H.edgeSet = (K : Set (Sym2 V)) := by
      rw [SimpleGraph.edgeSet_fromEdgeSet, sdiff_eq_left]
      exact hKEdiag
    let inc : (U : Set V) ↪ V := Function.Embedding.subtype _
    let F : Sym2 (U : Set V) → Sym2 V := inc.sym2Map
    have himage : F '' (H.induce (U : Set V)).edgeSet = H.edgeSet := by
      apply Set.Subset.antisymm
      · intro e he
        obtain ⟨d, hd, rfl⟩ := he
        induction d using Sym2.inductionOn with
        | _ a b => exact hd
      · intro e he
        induction e using Sym2.inductionOn with
        | _ a b =>
          have hab : H.Adj a b := he
          have ha : a ∈ H.support := ⟨b, hab⟩
          have hb : b ∈ H.support := ⟨a, hab.symm⟩
          refine ⟨s(⟨a, hsupp ha⟩, ⟨b, hsupp hb⟩), hab, ?_⟩
          rfl
    unfold edgeCountOn
    calc
      (H.induce (U : Set V)).edgeSet.ncard =
          (F '' (H.induce (U : Set V)).edgeSet).ncard :=
        (Set.ncard_image_of_injective _ inc.sym2Map.injective).symm
      _ = H.edgeSet.ncard := congrArg Set.ncard himage
      _ = (K : Set (Sym2 V)).ncard := by rw [hedge]
      _ = K.card := Set.ncard_coe_finset K
      _ = m := hKcard

/-- If `H ≤ G` and `G` has more edges on `U`, one of those induced edges is absent from `H`. -/
lemma exists_extra_adj_on {V : Type*} [Fintype V] [DecidableEq V]
    {H G : SimpleGraph V} (U : Finset V) (hHG : H ≤ G)
    (hlt : edgeCountOn H U < edgeCountOn G U) :
    ∃ u ∈ U, ∃ v ∈ U, G.Adj u v ∧ ¬H.Adj u v := by
  by_contra hno
  have hall : ∀ u ∈ U, ∀ v ∈ U, G.Adj u v → H.Adj u v := by
    intro u hu v hv huv
    by_contra hn
    exact hno ⟨u, hu, v, hv, huv, hn⟩
  have hGH : G.induce (U : Set V) ≤ H.induce (U : Set V) := by
    intro u v huv
    exact hall u.1 u.2 v.1 v.2 huv
  have hHG' : H.induce (U : Set V) ≤ G.induce (U : Set V) := by
    intro u v huv
    exact hHG huv
  have heq : G.induce (U : Set V) = H.induce (U : Set V) :=
    le_antisymm hGH hHG'
  unfold edgeCountOn at hlt
  rw [heq] at hlt
  exact (Nat.lt_irrefl _ hlt)

lemma lowerThreshold_even (s : ℕ) :
    lowerThreshold (2 * s) = s * s + s - 1 := by
  cases s with
  | zero => simp [lowerThreshold]
  | succ s =>
      unfold lowerThreshold
      rw [show (2 * (s + 1)) * (2 * (s + 1)) = 4 * ((s + 1) * (s + 1)) by ring]
      simp
      omega

lemma lowerThreshold_odd (s : ℕ) :
    lowerThreshold (2 * s + 1) = s * s + 2 * s := by
  unfold lowerThreshold
  rw [show (2 * s + 1) * (2 * s + 1) = 4 * (s * s + s) + 1 by ring]
  simp
  omega

lemma problemThreshold_eq_lowerThreshold_add_one {n : ℕ} (hn : 1 ≤ n) :
    problemThreshold n = lowerThreshold n + 1 := by
  simp [problemThreshold, lowerThreshold]
  omega

lemma lowerThreshold_succ (n : ℕ) (hn : 0 < n) :
    lowerThreshold (n + 1) = lowerThreshold n + stepDegree (n + 1) := by
  rcases n.even_or_odd with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · rw [← two_mul s] at hn ⊢
    have hs : 0 < s := by omega
    rw [lowerThreshold_even, lowerThreshold_odd]
    unfold stepDegree
    have hh : (2 * s + 1 + 1) / 2 = s + 1 := by omega
    rw [hh]
    omega
  · rw [show 2 * s + 1 + 1 = 2 * (s + 1) by omega]
    rw [lowerThreshold_even, lowerThreshold_odd]
    unfold stepDegree
    have hh : (2 * (s + 1) + 1) / 2 = s + 1 := by omega
    rw [hh]
    have he : (s + 1) * (s + 1) + (s + 1) - 1 =
        (s + 1) * (s + 1) + s := by omega
    rw [he]
    ring

lemma twice_lowerThreshold_lt (n : ℕ) (hn : 0 < n) :
    2 * lowerThreshold n < n * (stepDegree n + 1) := by
  rcases n.even_or_odd with ⟨s, hs⟩ | ⟨s, hs⟩
  · subst n
    have hs0 : 0 < s := by omega
    rw [← two_mul s]
    rw [lowerThreshold_even]
    unfold stepDegree
    have hh : (2 * s + 1) / 2 = s := by omega
    rw [hh]
    have hsub : s * s + s - 1 + 1 = s * s + s := by omega
    nlinarith
  · subst n
    rw [lowerThreshold_odd]
    unfold stepDegree
    have hh : (2 * s + 1 + 1) / 2 = s + 1 := by omega
    rw [hh]
    nlinarith

/-- At the one-edge-lower extremal value there is a vertex of at most the induction degree. -/
lemma exists_degree_le_stepDegree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) (hU : U.Nonempty)
    (hcard : edgeCountOn G U = lowerThreshold U.card) :
    ∃ (x : V) (hx : x ∈ U),
      (G.induce (U : Set V)).degree ⟨x, hx⟩ ≤ stepDegree U.card := by
  classical
  let H := G.induce (U : Set V)
  letI : Nonempty (U : Set V) := Set.nonempty_coe_sort.mpr (by simpa using hU)
  obtain ⟨x, hx⟩ := H.exists_minimal_degree_vertex
  by_cases hle : H.degree x ≤ stepDegree U.card
  · exact ⟨x.1, x.2, hle⟩
  · have hall : ∀ v : (U : Set V), stepDegree U.card + 1 ≤ H.degree v := by
      intro v
      have hmin := H.minDegree_le_degree v
      rw [hx] at hmin
      omega
    have hsum : U.card * (stepDegree U.card + 1) ≤ ∑ v, H.degree v := by
      calc
        U.card * (stepDegree U.card + 1) =
            ∑ _v : (U : Set V), (stepDegree U.card + 1) := by simp
        _ ≤ ∑ v, H.degree v := Finset.sum_le_sum fun v _ ↦ hall v
    rw [H.sum_degrees_eq_twice_card_edges] at hsum
    have hpos : 0 < U.card := Finset.card_pos.mpr hU
    have hlt := twice_lowerThreshold_lt U.card hpos
    have hedge : #H.edgeFinset = lowerThreshold U.card := by
      rw [edgeCountOn_eq_card_edgeFinset] at hcard
      simpa [H] using hcard
    rw [hedge] at hsum
    omega

/-- The simultaneous sharp induction.  Its first component classifies every target-free graph at
the one-edge-lower bound; its second component is Simonovits's forcing theorem. -/
theorem sharp_simonovits_induction {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset V) (hU : U.Nonempty) :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      edgeCountOn G U = lowerThreshold U.card →
        HasTarget G ∨ ∃ A B, IsBalancedTreeJoinOn G U A B) ∧
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      lowerThreshold U.card + 1 ≤ edgeCountOn G U → HasTarget G) := by
  induction hn : U.card using Nat.strong_induction_on generalizing U with
  | h n ih =>
    have hnpos : 0 < n := by
      rw [← hn]
      exact Finset.card_pos.mpr hU
    have hp : ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
        edgeCountOn G U = lowerThreshold n →
          HasTarget G ∨ ∃ A B, IsBalancedTreeJoinOn G U A B := by
      intro G instG hcard
      by_cases hn1 : n = 1
      · have hUcard : U.card = 1 := hn.trans hn1
        obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hUcard
        refine Or.inr ⟨{a}, ∅, ?_⟩
        refine ⟨by simp, by simp, ?_, ?_, by simp, by simp, by simp⟩
        · exact isTree_induce_star G ∅ a (by simp) (by simp) (by simp)
        · ext x y
          simp only [SimpleGraph.induce_adj, SimpleGraph.bot_adj, iff_false]
          intro _
          simpa using x.2
      · have hn2 : 2 ≤ n := by omega
        have hcardU : edgeCountOn G U = lowerThreshold U.card := by
          rw [hn]
          exact hcard
        obtain ⟨x, hxU, hxdeg⟩ := exists_degree_le_stepDegree G U hU hcardU
        let U' := U.erase x
        have hU'card : U'.card + 1 = U.card := by
          rw [show U' = U.erase x by rfl, Finset.card_erase_of_mem hxU]
          omega
        have hU'pos : 0 < U'.card := by omega
        have hU'nonempty : U'.Nonempty := Finset.card_pos.mp hU'pos
        have hU'lt : U'.card < n := by omega
        have hi := ih U'.card hU'lt U' hU'nonempty rfl
        have herase := edgeCountOn_erase G U hxU
        have hq : lowerThreshold U.card =
            lowerThreshold U'.card + stepDegree U.card := by
          have h := lowerThreshold_succ U'.card hU'pos
          rw [hU'card] at h
          exact h
        have hOldGe : lowerThreshold U'.card ≤ edgeCountOn G U' := by
          rw [show U.erase x = U' by rfl] at herase
          omega
        by_cases hOldHigh : lowerThreshold U'.card + 1 ≤ edgeCountOn G U'
        · exact Or.inl (hi.2 G hOldHigh)
        · have hOldEq : edgeCountOn G U' = lowerThreshold U'.card := by omega
          rcases hi.1 G hOldEq with htarget | ⟨A, B, hjoin⟩
          · exact Or.inl htarget
          · have hdegree :
                (G.induce (U : Set V)).degree ⟨x, hxU⟩ = stepDegree U.card := by
              rw [show U.erase x = U' by rfl] at herase
              omega
            have hpartF : A ∪ B = U' := by
              ext z
              have hz := Set.ext_iff.mp hjoin.1 z
              simpa only [Finset.mem_union, Finset.mem_coe, Set.mem_union] using hz
            have hdisjF : Disjoint A B := by
              simpa only [Finset.disjoint_coe] using hjoin.2.1
            have hfilterErase : U.filter (G.Adj x) = U'.filter (G.Adj x) := by
              ext z
              simp only [U', Finset.mem_filter, Finset.mem_erase]
              constructor
              · rintro ⟨hzU, hxz⟩
                exact ⟨⟨fun hzx ↦ G.loopless.irrefl x (hzx ▸ hxz), hzU⟩, hxz⟩
              · rintro ⟨⟨_, hzU⟩, hxz⟩
                exact ⟨hzU, hxz⟩
            have hfilterCard : #(U.filter (G.Adj x)) =
                #(A.filter (G.Adj x)) + #(B.filter (G.Adj x)) := by
              rw [hfilterErase, ← hpartF, Finset.filter_union]
              rw [Finset.card_union_of_disjoint
                (hdisjF.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
            have hdegFilters : #(A.filter (G.Adj x)) + #(B.filter (G.Adj x)) =
                stepDegree (U'.card + 1) := by
              have hdcard := degree_induce_eq_card_filter G U hxU
              rw [hdegree, hfilterCard] at hdcard
              rw [hU'card]
              exact hdcard.symm
            rcases extend_balanced_tree_join G U' A B x (by simp [U']) hjoin hdegFilters with
              htarget | ⟨A', B', hjoin'⟩
            · exact Or.inl htarget
            · refine Or.inr ⟨A', B', ?_⟩
              simpa [U', hxU] using hjoin'
    refine ⟨hp, ?_⟩
    intro G instG hcard
    by_cases hn4 : 4 ≤ n
    · have hm : lowerThreshold n ≤ edgeCountOn G U := by omega
      obtain ⟨H, hHG, hHcard⟩ := exists_subgraph_edgeCountOn_eq G U hm
      letI : DecidableRel H.Adj := Classical.decRel H.Adj
      rcases hp H hHcard with htarget | ⟨A, B, hjoin⟩
      · exact htarget.mono hHG
      · have hlt : edgeCountOn H U < edgeCountOn G U := by omega
        obtain ⟨u, hu, v, hv, hGuv, hHuv⟩ := exists_extra_adj_on U hHG hlt
        apply augment_balanced_tree_join H G U A B
        · omega
        · exact hHG
        · exact hjoin
        · exact hu
        · exact hv
        · exact hGuv
        · exact hHuv
    · have hmax : edgeCountOn G U ≤ U.card.choose 2 := by
        rw [edgeCountOn_eq_card_edgeFinset, ← Fintype.card_coe U]
        exact SimpleGraph.card_edgeFinset_le_card_choose_two
      rw [hn] at hmax
      have hcases : n = 1 ∨ n = 2 ∨ n = 3 := by omega
      rcases hcases with rfl | rfl | rfl <;>
        norm_num [lowerThreshold] at hcard hmax hn <;> omega

/-- Simonovits's stronger resolution of Erdős Problem 1019: at the stated threshold, the host
contains either `K₄` or a bipyramid over a cycle. -/
theorem erdos_1019_sharp {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hE : #G.edgeFinset = problemThreshold (Fintype.card V)) :
    HasTarget G := by
  have hne : (Finset.univ : Finset V).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    exact Fintype.card_pos_iff.mp (Fintype.card_pos)
  apply (sharp_simonovits_induction (Finset.univ : Finset V) hne).2 G
  have hthreshold := problemThreshold_eq_lowerThreshold_add_one (n := Fintype.card V)
    (Fintype.card_pos)
  rw [hthreshold] at hE
  have hcount : edgeCountOn G (Finset.univ : Finset V) = #G.edgeFinset := by
    rw [edgeCountOn_eq_edgeSet_ncard_of_support_subset G Finset.univ (by simp),
      edgeSet_ncard_eq_card_edgeFinset]
  simpa [hcount] using hE.ge

/-- Erdős Problem 1019, in its original saturated-planar formulation.  The returned structure
contains a finite graph on more than three vertices, its `3v-6` edge certificate, an explicit
spherical-triangulation model (`K₄` or a bipyramid), and a copy inside `G`. -/
theorem erdos_1019 {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hE : #G.edgeFinset = problemThreshold (Fintype.card V)) :
    ContainsSaturatedPlanarBeyondTriangle G :=
  (erdos_1019_sharp G hE).to_saturatedPlanarSubgraph

end Erdos1019

#print axioms Erdos1019.erdos_1019
