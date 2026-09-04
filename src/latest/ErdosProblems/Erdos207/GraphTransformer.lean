/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AbsorberBank
import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Edge-bijective transformers

This formalizes the simpler (degeneracy-six) transformer described after
Lemma 3.4 of Barber--Glock--Kühn--Lo--Montgomery--Osthus, *Minimalist
designs*.  The degeneracy bound is irrelevant for the bounded cycle-cover
roots in KSSS; the explicit two decompositions are what is needed here.
-/

namespace Erdos207

open Finset

noncomputable section

/-- A graph homomorphism that induces a bijection on graph edges. -/
structure EdgeBijectiveHom {V W : Type*} (G : SimpleGraph V)
    (H : SimpleGraph W) where
  hom : G →g H
  edge_bijective : Function.Bijective hom.mapEdgeSet

namespace EdgeBijectiveHom

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

def edgeEquiv (φ : EdgeBijectiveHom G H) : G.edgeSet ≃ H.edgeSet :=
  Equiv.ofBijective φ.hom.mapEdgeSet φ.edge_bijective

@[simp]
lemma edgeEquiv_val (φ : EdgeBijectiveHom G H) (e : G.edgeSet) :
    (φ.edgeEquiv e : Sym2 W) = (e : Sym2 V).map φ.hom := by
  rfl

end EdgeBijectiveHom

lemma even_ncard_neighborSet {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : ∀ x, Even (G.degree x)) (x : V) :
    Even (G.neighborSet x).ncard := by
  rw [Set.ncard_eq_toFinset_card]
  have hfinset : (G.neighborSet x).toFinite.toFinset = G.neighborFinset x := by
    ext y
    simp
  rw [hfinset, SimpleGraph.card_neighborFinset_eq_degree]
  exact heven x

/-- A perfect matching on the neighbors of `x`, regarded as a subgraph of
the complete graph on the same ambient vertex type. -/
def incidentMatching {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : ∀ x, Even (G.degree x)) (x : V) :
    (SimpleGraph.completeGraph V).Subgraph := by
  let U : Set V := G.neighborSet x
  have hfinite : U.Finite := Set.toFinite U
  have hcard : Even U.ncard := even_ncard_neighborSet G heven x
  have hclique : (SimpleGraph.completeGraph V).IsClique U := by
    rw [SimpleGraph.isClique_iff]
    intro u hu v hv huv
    simpa using huv
  exact Classical.choose
    ((hclique.even_iff_exists_isMatching hfinite).mp hcard)

lemma incidentMatching_verts {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : ∀ x, Even (G.degree x)) (x : V) :
    (incidentMatching G heven x).verts = G.neighborSet x := by
  exact (Classical.choose_spec
    (((show (SimpleGraph.completeGraph V).IsClique (G.neighborSet x) by
        rw [SimpleGraph.isClique_iff]
        intro u hu v hv huv
        simpa using huv).even_iff_exists_isMatching (Set.toFinite _)).mp
          (even_ncard_neighborSet G heven x))).1

lemma incidentMatching_isMatching {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : ∀ x, Even (G.degree x)) (x : V) :
    (incidentMatching G heven x).IsMatching := by
  exact (Classical.choose_spec
    (((show (SimpleGraph.completeGraph V).IsClique (G.neighborSet x) by
        rw [SimpleGraph.isClique_iff]
        intro u hu v hv huv
        simpa using huv).even_iff_exists_isMatching (Set.toFinite _)).mp
          (even_ncard_neighborSet G heven x))).2

/-- Vertices used by the simple transformer: the two root graphs and one
new vertex for every source edge. -/
inductive TransformerVertex {V : Type*} (G : SimpleGraph V) (W : Type*) where
  | source (x : V)
  | target (y : W)
  | edge (e : G.edgeSet)
  deriving DecidableEq

def transformerVertexEquiv {V W : Type*} (G : SimpleGraph V) :
    V ⊕ W ⊕ G.edgeSet ≃ TransformerVertex G W where
  toFun
    | Sum.inl x => .source x
    | Sum.inr (Sum.inl y) => .target y
    | Sum.inr (Sum.inr e) => .edge e
  invFun
    | .source x => Sum.inl x
    | .target y => Sum.inr (Sum.inl y)
    | .edge e => Sum.inr (Sum.inr e)
  left_inv x := by cases x with
    | inl x => rfl
    | inr x => cases x <;> rfl
  right_inv x := by cases x <;> rfl

noncomputable instance transformerVertexFintype
    {V W : Type*} [Fintype V] [Fintype W] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    Fintype (TransformerVertex G W) :=
  Fintype.ofEquiv (V ⊕ W ⊕ G.edgeSet) (transformerVertexEquiv G)

def transformerSourceEmbedding {V W : Type*} (G : SimpleGraph V) :
    V ↪ TransformerVertex G W :=
  ⟨TransformerVertex.source, by intro x y h; simpa using h⟩

def transformerTargetEmbedding {V W : Type*} (G : SimpleGraph V) :
    W ↪ TransformerVertex G W :=
  ⟨TransformerVertex.target, by intro x y h; simpa using h⟩

lemma edge_out_ne {V : Type*} {G : SimpleGraph V} (e : G.edgeSet) :
    e.1.out.1 ≠ e.1.out.2 := by
  intro h
  apply G.not_isDiag_of_mem_edgeSet e.2
  rw [← e.1.out_eq, Sym2.mk_isDiag_iff]
  exact h

/-- A convenient constructor for a triple from three pairwise distinct
vertices. -/
def tripleOfThree {V : Type*} [DecidableEq V] (a b c : V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : TripleOn V :=
  ⟨{a, b, c}, by simp [hab, hac, hbc]⟩

/-- Triangle on a source edge and its new edge-vertex. -/
def transformerSourceEdgeTriple {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} (e : G.edgeSet) : TripleOn (TransformerVertex G W) :=
  tripleOfThree (.source e.1.out.1) (.source e.1.out.2) (.edge e)
    (by simpa using edge_out_ne e) (by simp) (by simp)

/-- Triangle on the corresponding target edge and the same new
edge-vertex. -/
def transformerTargetEdgeTriple {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (φ : EdgeBijectiveHom G H)
    (e : G.edgeSet) : TripleOn (TransformerVertex G W) :=
  let e' := φ.edgeEquiv e
  tripleOfThree (.target e'.1.out.1) (.target e'.1.out.2) (.edge e)
    (by simpa using edge_out_ne e') (by simp) (by simp)

/-- The source edge joining `x` to a neighbor `y`. -/
def edgeAtNeighbor {V : Type*} {G : SimpleGraph V} (x : V)
    (y : G.neighborSet x) : G.edgeSet :=
  ⟨s(x, y.1), y.2⟩

lemma edgeAtNeighbor_injective {V : Type*} {G : SimpleGraph V} (x : V) :
    Function.Injective (edgeAtNeighbor (G := G) x) := by
  intro y z h
  apply Subtype.ext
  exact Sym2.congr_right.mp (congrArg Subtype.val h)

lemma edge_out_adj {V : Type*} {G : SimpleGraph V} (e : G.edgeSet) :
    G.Adj e.1.out.1 e.1.out.2 := by
  rw [← SimpleGraph.mem_edgeSet]
  have hout : s(e.1.out.1, e.1.out.2) = e.1 := by
    change Quot.mk _ e.1.out = e.1
    exact e.1.out_eq
  rw [hout]
  exact e.2

/-- If `x` is an endpoint of `e`, the edge `e` is the edge from `x` to
one of its neighbors. -/
lemma exists_edgeAtNeighbor_eq
    {V : Type*} {G : SimpleGraph V} (e : G.edgeSet) {x : V}
    (hx : x ∈ e.1) :
    ∃ y : G.neighborSet x, edgeAtNeighbor x y = e := by
  have hxout : x = e.1.out.1 ∨ x = e.1.out.2 := by
    rw [← e.1.out_eq, Sym2.mem_iff] at hx
    exact hx
  rcases hxout with rfl | rfl
  · let y : G.neighborSet e.1.out.1 := ⟨e.1.out.2, edge_out_adj e⟩
    refine ⟨y, ?_⟩
    apply Subtype.ext
    change s(e.1.out.1, e.1.out.2) = e.1
    change Quot.mk _ e.1.out = e.1
    exact e.1.out_eq
  · let y : G.neighborSet e.1.out.2 := ⟨e.1.out.1, by
      change G.Adj e.1.out.2 e.1.out.1
      exact (edge_out_adj e).symm⟩
    refine ⟨y, ?_⟩
    apply Subtype.ext
    change s(e.1.out.2, e.1.out.1) = e.1
    rw [Sym2.eq_swap]
    change Quot.mk _ e.1.out = e.1
    exact e.1.out_eq

def matchingNeighborLeft {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : ∀ x, Even (G.degree x)) (x : V)
    (p : (incidentMatching G heven x).edgeSet) : G.neighborSet x :=
  ⟨p.1.out.1, by
    rw [← incidentMatching_verts G heven x]
    exact (incidentMatching G heven x).mem_verts_of_mem_edge p.2
      (Sym2.out_fst_mem p.1)⟩

def matchingNeighborRight {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : ∀ x, Even (G.degree x)) (x : V)
    (p : (incidentMatching G heven x).edgeSet) : G.neighborSet x :=
  ⟨p.1.out.2, by
    rw [← incidentMatching_verts G heven x]
    exact (incidentMatching G heven x).mem_verts_of_mem_edge p.2
      (Sym2.out_snd_mem p.1)⟩

lemma matchingNeighborLeft_ne_right
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : ∀ x, Even (G.degree x)) (x : V)
    (p : (incidentMatching G heven x).edgeSet) :
    matchingNeighborLeft G heven x p ≠ matchingNeighborRight G heven x p := by
  intro h
  have hp : p.1 ∈ (incidentMatching G heven x).spanningCoe.edgeSet := by
    rw [SimpleGraph.Subgraph.edgeSet_spanningCoe]
    exact p.2
  apply (incidentMatching G heven x).spanningCoe.not_isDiag_of_mem_edgeSet hp
  rw [← p.1.out_eq, Sym2.mk_isDiag_iff]
  exact congrArg Subtype.val h

/-- Matching triangle rooted at the source vertex `x`. -/
def transformerSourceMatchingTriple
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : ∀ x, Even (G.degree x)) (x : V)
    (p : (incidentMatching G heven x).edgeSet) :
    TripleOn (TransformerVertex G W) :=
  let e₁ := edgeAtNeighbor x (matchingNeighborLeft G heven x p)
  let e₂ := edgeAtNeighbor x (matchingNeighborRight G heven x p)
  tripleOfThree (.source x) (.edge e₁) (.edge e₂)
    (by simp) (by simp) (by
      intro h
      apply matchingNeighborLeft_ne_right G heven x p
      apply edgeAtNeighbor_injective x
      simpa [e₁, e₂] using h)

/-- The corresponding matching triangle rooted at the target image of
`x`. -/
def transformerTargetMatchingTriple
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    (φ : EdgeBijectiveHom G H)
    (heven : ∀ x, Even (G.degree x)) (x : V)
    (p : (incidentMatching G heven x).edgeSet) :
    TripleOn (TransformerVertex G W) :=
  let e₁ := edgeAtNeighbor x (matchingNeighborLeft G heven x p)
  let e₂ := edgeAtNeighbor x (matchingNeighborRight G heven x p)
  tripleOfThree (.target (φ.hom x)) (.edge e₁) (.edge e₂)
    (by simp) (by simp) (by
      intro h
      apply matchingNeighborLeft_ne_right G heven x p
      apply edgeAtNeighbor_injective x
      simpa [e₁, e₂] using h)

def transformerSourceEdgeTriples
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    TripleSystemOn (TransformerVertex G W) :=
  univ.image transformerSourceEdgeTriple

def transformerTargetEdgeTriples
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] (φ : EdgeBijectiveHom G H) :
    TripleSystemOn (TransformerVertex G W) :=
  univ.image (transformerTargetEdgeTriple φ)

def transformerSourceMatchingTriples
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : ∀ x, Even (G.degree x)) :
    TripleSystemOn (TransformerVertex G W) :=
  univ.biUnion fun x ↦
    letI : Fintype (incidentMatching G heven x).edgeSet := Fintype.ofFinite _
    univ.image (transformerSourceMatchingTriple G heven x)

def transformerTargetMatchingTriples
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    (φ : EdgeBijectiveHom G H)
    (heven : ∀ x, Even (G.degree x)) :
    TripleSystemOn (TransformerVertex G W) :=
  univ.biUnion fun x ↦
    letI : Fintype (incidentMatching G heven x).edgeSet := Fintype.ofFinite _
    univ.image (transformerTargetMatchingTriple φ heven x)

/-- Decomposition candidate for the transformer together with the source
root graph. -/
def transformerSourceSide
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    (φ : EdgeBijectiveHom G H)
    (heven : ∀ x, Even (G.degree x)) :
    TripleSystemOn (TransformerVertex G W) :=
  transformerSourceEdgeTriples G ∪ transformerTargetMatchingTriples φ heven

/-- Decomposition candidate for the transformer together with the target
root graph. -/
def transformerTargetSide
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    (φ : EdgeBijectiveHom G H)
    (heven : ∀ x, Even (G.degree x)) :
    TripleSystemOn (TransformerVertex G W) :=
  transformerTargetEdgeTriples φ ∪ transformerSourceMatchingTriples G heven

@[simp]
lemma mem_transformerSourceEdgeTriples_iff
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {T : TripleOn (TransformerVertex G W)} :
    T ∈ transformerSourceEdgeTriples G ↔
      ∃ e : G.edgeSet, T = transformerSourceEdgeTriple e := by
  simp [transformerSourceEdgeTriples, eq_comm]

@[simp]
lemma mem_transformerTargetEdgeTriples_iff
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    (φ : EdgeBijectiveHom G H) {T : TripleOn (TransformerVertex G W)} :
    T ∈ transformerTargetEdgeTriples φ ↔
      ∃ e : G.edgeSet, T = transformerTargetEdgeTriple φ e := by
  simp [transformerTargetEdgeTriples, eq_comm]

@[simp]
lemma mem_transformerSourceMatchingTriples_iff
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : ∀ x, Even (G.degree x))
    {T : TripleOn (TransformerVertex G W)} :
    T ∈ transformerSourceMatchingTriples (W := W) G heven ↔
      ∃ x : V, ∃ p : (incidentMatching G heven x).edgeSet,
        T = transformerSourceMatchingTriple G heven x p := by
  classical
  simp only [transformerSourceMatchingTriples, mem_biUnion, mem_univ,
    true_and]
  constructor
  · rintro ⟨x, hx⟩
    let : Fintype (incidentMatching G heven x).edgeSet := Fintype.ofFinite _
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨x, p, rfl⟩
  · rintro ⟨x, p, rfl⟩
    refine ⟨x, ?_⟩
    let : Fintype (incidentMatching G heven x).edgeSet := Fintype.ofFinite _
    exact Finset.mem_image.mpr ⟨p, mem_univ p, rfl⟩

@[simp]
lemma mem_transformerTargetMatchingTriples_iff
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    (φ : EdgeBijectiveHom G H)
    (heven : ∀ x, Even (G.degree x))
    {T : TripleOn (TransformerVertex G W)} :
    T ∈ transformerTargetMatchingTriples φ heven ↔
      ∃ x : V, ∃ p : (incidentMatching G heven x).edgeSet,
        T = transformerTargetMatchingTriple φ heven x p := by
  classical
  simp only [transformerTargetMatchingTriples, mem_biUnion, mem_univ,
    true_and]
  constructor
  · rintro ⟨x, hx⟩
    let : Fintype (incidentMatching G heven x).edgeSet := Fintype.ofFinite _
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨x, p, rfl⟩
  · rintro ⟨x, p, rfl⟩
    refine ⟨x, ?_⟩
    let : Fintype (incidentMatching G heven x).edgeSet := Fintype.ofFinite _
    exact Finset.mem_image.mpr ⟨p, mem_univ p, rfl⟩

/-- Every neighbor belongs to a unique matching edge in its incident
matching. -/
lemma existsUnique_incidentMatching_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : ∀ x, Even (G.degree x)) (x : V) (y : G.neighborSet x) :
    ∃! p : (incidentMatching G heven x).edgeSet, y.1 ∈ p.1 := by
  have hyverts : y.1 ∈ (incidentMatching G heven x).verts := by
    rw [incidentMatching_verts G heven x]
    exact y.2
  obtain ⟨z, hyz, hunique⟩ :=
    incidentMatching_isMatching G heven x hyverts
  let p : (incidentMatching G heven x).edgeSet := ⟨s(y.1, z), hyz⟩
  refine ⟨p, Sym2.mem_mk_left _ _, ?_⟩
  intro q hyq
  apply Subtype.ext
  obtain ⟨w, hqw⟩ := Sym2.mem_iff_exists.mp hyq
  rw [hqw]
  have hqadj : (incidentMatching G heven x).Adj y.1 w := by
    change s(y.1, w) ∈ (incidentMatching G heven x).edgeSet
    rw [← hqw]
    exact q.2
  have hwz : w = z := hunique w hqadj
  subst w
  rfl

/-- The matching triangle at `x` which contains the spoke associated to a
specified neighbor. -/
lemma exists_sourceMatchingTriple_spoke
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : ∀ x, Even (G.degree x)) (x : V) (y : G.neighborSet x) :
    ∃ p : (incidentMatching G heven x).edgeSet,
      TransformerVertex.source x ∈
        (transformerSourceMatchingTriple (W := W) G heven x p).1 ∧
      TransformerVertex.edge (edgeAtNeighbor x y) ∈
        (transformerSourceMatchingTriple (W := W) G heven x p).1 := by
  obtain ⟨p, hyp, hpunique⟩ := existsUnique_incidentMatching_edge G heven x y
  refine ⟨p, by simp [transformerSourceMatchingTriple, tripleOfThree], ?_⟩
  have hyout : y.1 = p.1.out.1 ∨ y.1 = p.1.out.2 := by
    rw [← p.1.out_eq, Sym2.mem_iff] at hyp
    exact hyp
  rcases hyout with hy | hy
  · have heq : edgeAtNeighbor x y =
        edgeAtNeighbor x (matchingNeighborLeft G heven x p) := by
      apply Subtype.ext
      exact congrArg (s(x, ·)) hy
    simp [transformerSourceMatchingTriple, tripleOfThree, heq]
  · have heq : edgeAtNeighbor x y =
        edgeAtNeighbor x (matchingNeighborRight G heven x p) := by
      apply Subtype.ext
      exact congrArg (s(x, ·)) hy
    simp [transformerSourceMatchingTriple, tripleOfThree, heq]

lemma exists_targetMatchingTriple_spoke
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    (φ : EdgeBijectiveHom G H)
    (heven : ∀ x, Even (G.degree x)) (x : V) (y : G.neighborSet x) :
    ∃ p : (incidentMatching G heven x).edgeSet,
      TransformerVertex.target (φ.hom x) ∈
        (transformerTargetMatchingTriple φ heven x p).1 ∧
      TransformerVertex.edge (edgeAtNeighbor x y) ∈
        (transformerTargetMatchingTriple φ heven x p).1 := by
  obtain ⟨p, hsource, hedge⟩ :=
    exists_sourceMatchingTriple_spoke (W := W) G heven x y
  refine ⟨p, by simp [transformerTargetMatchingTriple, tripleOfThree], ?_⟩
  simpa [transformerSourceMatchingTriple, transformerTargetMatchingTriple,
    tripleOfThree] using hedge

lemma exists_sourceMatchingTriple_spoke_edge
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : ∀ x, Even (G.degree x)) (e : G.edgeSet) {x : V}
    (hx : x ∈ e.1) :
    ∃ p : (incidentMatching G heven x).edgeSet,
      TransformerVertex.source x ∈
        (transformerSourceMatchingTriple (W := W) G heven x p).1 ∧
      TransformerVertex.edge e ∈
        (transformerSourceMatchingTriple (W := W) G heven x p).1 := by
  obtain ⟨y, hy⟩ := exists_edgeAtNeighbor_eq e hx
  obtain ⟨p, hsource, hedge⟩ :=
    exists_sourceMatchingTriple_spoke (W := W) G heven x y
  exact ⟨p, hsource, by simpa [hy] using hedge⟩

lemma exists_targetMatchingTriple_spoke_edge
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    (phi : EdgeBijectiveHom G H)
    (heven : ∀ x, Even (G.degree x)) (e : G.edgeSet) {x : V}
    (hx : x ∈ e.1) :
    ∃ p : (incidentMatching G heven x).edgeSet,
      TransformerVertex.target (phi.hom x) ∈
        (transformerTargetMatchingTriple phi heven x p).1 ∧
      TransformerVertex.edge e ∈
        (transformerTargetMatchingTriple phi heven x p).1 := by
  obtain ⟨y, hy⟩ := exists_edgeAtNeighbor_eq e hx
  obtain ⟨p, htarget, hedge⟩ :=
    exists_targetMatchingTriple_spoke phi heven x y
  exact ⟨p, htarget, by simpa [hy] using hedge⟩

lemma exists_targetMatchingTriple_mapped_spoke
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    (phi : EdgeBijectiveHom G H)
    (heven : ∀ x, Even (G.degree x)) (e : G.edgeSet) {y : W}
    (hy : y ∈ (phi.edgeEquiv e).1) :
    ∃ x : V, ∃ p : (incidentMatching G heven x).edgeSet,
      phi.hom x = y ∧
      TransformerVertex.target y ∈
        (transformerTargetMatchingTriple phi heven x p).1 ∧
      TransformerVertex.edge e ∈
        (transformerTargetMatchingTriple phi heven x p).1 := by
  rw [EdgeBijectiveHom.edgeEquiv_val, Sym2.mem_map] at hy
  obtain ⟨x, hx, hxy⟩ := hy
  obtain ⟨p, htarget, hedge⟩ :=
    exists_targetMatchingTriple_spoke_edge phi heven e hx
  refine ⟨x, p, hxy, ?_, hedge⟩
  simpa [hxy] using htarget

lemma source_mem_sourceEdgeTriple_of_mem
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} (e : G.edgeSet) {x : V} (hx : x ∈ e.1) :
    TransformerVertex.source x ∈
      (transformerSourceEdgeTriple (W := W) e).1 := by
  have hxout : x = e.1.out.1 ∨ x = e.1.out.2 := by
    rw [← e.1.out_eq, Sym2.mem_iff] at hx
    exact hx
  rcases hxout with rfl | rfl <;>
    simp [transformerSourceEdgeTriple, tripleOfThree]

@[simp]
lemma edge_mem_sourceEdgeTriple
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} (e : G.edgeSet) :
    TransformerVertex.edge e ∈
      (transformerSourceEdgeTriple (W := W) e).1 := by
  simp [transformerSourceEdgeTriple, tripleOfThree]

lemma target_mem_targetEdgeTriple_of_mem
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : EdgeBijectiveHom G H) (e : G.edgeSet) {x : V} (hx : x ∈ e.1) :
    TransformerVertex.target (φ.hom x) ∈
      (transformerTargetEdgeTriple φ e).1 := by
  let e' := φ.edgeEquiv e
  have hx' : φ.hom x ∈ e'.1 := by
    rw [EdgeBijectiveHom.edgeEquiv_val, Sym2.mem_map]
    exact ⟨x, hx, rfl⟩
  have hxout : φ.hom x = e'.1.out.1 ∨ φ.hom x = e'.1.out.2 := by
    rw [← e'.1.out_eq, Sym2.mem_iff] at hx'
    exact hx'
  rcases hxout with hxout | hxout <;>
    simp [transformerTargetEdgeTriple, tripleOfThree, e', hxout]

@[simp]
lemma edge_mem_targetEdgeTriple
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : EdgeBijectiveHom G H) (e : G.edgeSet) :
    TransformerVertex.edge e ∈
      (transformerTargetEdgeTriple φ e).1 := by
  simp [transformerTargetEdgeTriple, tripleOfThree]

@[simp]
lemma source_mem_sourceEdgeTriple_iff
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} (e : G.edgeSet) (x : V) :
    TransformerVertex.source x ∈
        (transformerSourceEdgeTriple (W := W) e).1 ↔
      x ∈ e.1 := by
  constructor
  · intro hx
    simp [transformerSourceEdgeTriple, tripleOfThree] at hx
    rcases hx with hx | hx
    · subst x
      exact Sym2.out_fst_mem e.1
    · subst x
      exact Sym2.out_snd_mem e.1
  · intro hx
    have hxout : x = e.1.out.1 ∨ x = e.1.out.2 := by
      rw [← e.1.out_eq, Sym2.mem_iff] at hx
      exact hx
    rcases hxout with rfl | rfl <;>
      simp [transformerSourceEdgeTriple, tripleOfThree]

@[simp]
lemma target_not_mem_sourceEdgeTriple
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} (e : G.edgeSet) (y : W) :
    TransformerVertex.target y ∉
      (transformerSourceEdgeTriple (W := W) e).1 := by
  simp [transformerSourceEdgeTriple, tripleOfThree]

@[simp]
lemma edge_mem_sourceEdgeTriple_iff
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} (e f : G.edgeSet) :
    TransformerVertex.edge f ∈
        (transformerSourceEdgeTriple (W := W) e).1 ↔
      f = e := by
  simp [transformerSourceEdgeTriple, tripleOfThree]

@[simp]
lemma target_mem_targetEdgeTriple_iff
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (phi : EdgeBijectiveHom G H) (e : G.edgeSet) (y : W) :
    TransformerVertex.target y ∈
        (transformerTargetEdgeTriple phi e).1 ↔
      y ∈ (phi.edgeEquiv e).1 := by
  let e' := phi.edgeEquiv e
  constructor
  · intro hy
    have hyout :
        y = (phi.edgeEquiv e).1.out.1 ∨ y = (phi.edgeEquiv e).1.out.2 := by
      simpa [transformerTargetEdgeTriple, tripleOfThree] using hy
    rcases hyout with hy | hy
    · subst y
      exact Sym2.out_fst_mem e'.1
    · subst y
      exact Sym2.out_snd_mem e'.1
  · intro hy
    have hyout : y = e'.1.out.1 ∨ y = e'.1.out.2 := by
      rw [← e'.1.out_eq, Sym2.mem_iff] at hy
      exact hy
    rcases hyout with hy | hy <;>
      simp [transformerTargetEdgeTriple, tripleOfThree, e', hy]

@[simp]
lemma source_not_mem_targetEdgeTriple
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (phi : EdgeBijectiveHom G H) (e : G.edgeSet) (x : V) :
    TransformerVertex.source x ∉
      (transformerTargetEdgeTriple phi e).1 := by
  simp [transformerTargetEdgeTriple, tripleOfThree]

@[simp]
lemma edge_mem_targetEdgeTriple_iff
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (phi : EdgeBijectiveHom G H) (e f : G.edgeSet) :
    TransformerVertex.edge f ∈
        (transformerTargetEdgeTriple phi e).1 ↔
      f = e := by
  simp [transformerTargetEdgeTriple, tripleOfThree]

@[simp]
lemma source_mem_sourceMatchingTriple_iff
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : ∀ x, Even (G.degree x)) (x x' : V)
    (p : (incidentMatching G heven x).edgeSet) :
    TransformerVertex.source x' ∈
        (transformerSourceMatchingTriple (W := W) G heven x p).1 ↔
      x' = x := by
  simp [transformerSourceMatchingTriple, tripleOfThree]

@[simp]
lemma target_not_mem_sourceMatchingTriple
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : ∀ x, Even (G.degree x)) (x : V)
    (p : (incidentMatching G heven x).edgeSet) (y : W) :
    TransformerVertex.target y ∉
      (transformerSourceMatchingTriple (W := W) G heven x p).1 := by
  simp [transformerSourceMatchingTriple, tripleOfThree]

@[simp]
lemma edge_mem_sourceMatchingTriple_iff
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : ∀ x, Even (G.degree x)) (x : V)
    (p : (incidentMatching G heven x).edgeSet) (e : G.edgeSet) :
    TransformerVertex.edge e ∈
        (transformerSourceMatchingTriple (W := W) G heven x p).1 ↔
      e = edgeAtNeighbor x (matchingNeighborLeft G heven x p) ∨
      e = edgeAtNeighbor x (matchingNeighborRight G heven x p) := by
  simp [transformerSourceMatchingTriple, tripleOfThree]

@[simp]
lemma target_mem_targetMatchingTriple_iff
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    (phi : EdgeBijectiveHom G H)
    (heven : ∀ x, Even (G.degree x)) (x : V)
    (p : (incidentMatching G heven x).edgeSet) (y : W) :
    TransformerVertex.target y ∈
        (transformerTargetMatchingTriple phi heven x p).1 ↔
      y = phi.hom x := by
  simp [transformerTargetMatchingTriple, tripleOfThree]

@[simp]
lemma source_not_mem_targetMatchingTriple
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    (phi : EdgeBijectiveHom G H)
    (heven : ∀ x, Even (G.degree x)) (x : V)
    (p : (incidentMatching G heven x).edgeSet) (x' : V) :
    TransformerVertex.source x' ∉
      (transformerTargetMatchingTriple phi heven x p).1 := by
  simp [transformerTargetMatchingTriple, tripleOfThree]

@[simp]
lemma edge_mem_targetMatchingTriple_iff
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    (phi : EdgeBijectiveHom G H)
    (heven : ∀ x, Even (G.degree x)) (x : V)
    (p : (incidentMatching G heven x).edgeSet) (e : G.edgeSet) :
    TransformerVertex.edge e ∈
        (transformerTargetMatchingTriple phi heven x p).1 ↔
      e = edgeAtNeighbor x (matchingNeighborLeft G heven x p) ∨
      e = edgeAtNeighbor x (matchingNeighborRight G heven x p) := by
  simp [transformerTargetMatchingTriple, tripleOfThree]

lemma edgeSubtype_eq_of_two_endpoints
    {V : Type*} {G : SimpleGraph V} (e f : G.edgeSet) {x y : V}
    (hxy : x ≠ y) (hxe : x ∈ e.1) (hye : y ∈ e.1)
    (hxf : x ∈ f.1) (hyf : y ∈ f.1) : e = f := by
  apply Subtype.ext
  exact Sym2.eq_of_ne_mem hxy hxe hye hxf hyf

theorem transformerSourceEdgeTriples_isPacking
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    IsPackingOn (transformerSourceEdgeTriples (W := W) G) := by
  intro u v huv T hT huT hvT U hU huU hvU
  obtain ⟨e, rfl⟩ := mem_transformerSourceEdgeTriples_iff.mp hT
  obtain ⟨f, rfl⟩ := mem_transformerSourceEdgeTriples_iff.mp hU
  cases u with
  | source x =>
      cases v with
      | source y =>
          have hxy : x ≠ y := by simpa using huv
          have hef := edgeSubtype_eq_of_two_endpoints e f hxy
            (source_mem_sourceEdgeTriple_iff e x |>.mp huT)
            (source_mem_sourceEdgeTriple_iff e y |>.mp hvT)
            (source_mem_sourceEdgeTriple_iff f x |>.mp huU)
            (source_mem_sourceEdgeTriple_iff f y |>.mp hvU)
          subst f
          rfl
      | target y => exact (target_not_mem_sourceEdgeTriple e y hvT).elim
      | edge k =>
          have hke := edge_mem_sourceEdgeTriple_iff e k |>.mp hvT
          have hkf := edge_mem_sourceEdgeTriple_iff f k |>.mp hvU
          subst e
          subst f
          rfl
  | target x => exact (target_not_mem_sourceEdgeTriple e x huT).elim
  | edge k =>
      cases v with
      | source y =>
          have hke := edge_mem_sourceEdgeTriple_iff e k |>.mp huT
          have hkf := edge_mem_sourceEdgeTriple_iff f k |>.mp huU
          subst e
          subst f
          rfl
      | target y => exact (target_not_mem_sourceEdgeTriple e y hvT).elim
      | edge l =>
          have hke := edge_mem_sourceEdgeTriple_iff e k |>.mp huT
          have hle := edge_mem_sourceEdgeTriple_iff e l |>.mp hvT
          exact (huv (by simpa [hke, hle])).elim

theorem transformerTargetEdgeTriples_isPacking
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    (phi : EdgeBijectiveHom G H) :
    IsPackingOn (transformerTargetEdgeTriples phi) := by
  intro u v huv T hT huT hvT U hU huU hvU
  obtain ⟨e, rfl⟩ := mem_transformerTargetEdgeTriples_iff phi |>.mp hT
  obtain ⟨f, rfl⟩ := mem_transformerTargetEdgeTriples_iff phi |>.mp hU
  cases u with
  | source x => exact (source_not_mem_targetEdgeTriple phi e x huT).elim
  | target x =>
      cases v with
      | source y => exact (source_not_mem_targetEdgeTriple phi e y hvT).elim
      | target y =>
          have hxy : x ≠ y := by simpa using huv
          have hef' : phi.edgeEquiv e = phi.edgeEquiv f := by
            apply Subtype.ext
            exact Sym2.eq_of_ne_mem hxy
              (target_mem_targetEdgeTriple_iff phi e x |>.mp huT)
              (target_mem_targetEdgeTriple_iff phi e y |>.mp hvT)
              (target_mem_targetEdgeTriple_iff phi f x |>.mp huU)
              (target_mem_targetEdgeTriple_iff phi f y |>.mp hvU)
          have hef : e = f := phi.edgeEquiv.injective hef'
          subst f
          rfl
      | edge k =>
          have hke := edge_mem_targetEdgeTriple_iff phi e k |>.mp hvT
          have hkf := edge_mem_targetEdgeTriple_iff phi f k |>.mp hvU
          subst e
          subst f
          rfl
  | edge k =>
      cases v with
      | source y => exact (source_not_mem_targetEdgeTriple phi e y hvT).elim
      | target y =>
          have hke := edge_mem_targetEdgeTriple_iff phi e k |>.mp huT
          have hkf := edge_mem_targetEdgeTriple_iff phi f k |>.mp huU
          subst e
          subst f
          rfl
      | edge l =>
          have hke := edge_mem_targetEdgeTriple_iff phi e k |>.mp huT
          have hle := edge_mem_targetEdgeTriple_iff phi e l |>.mp hvT
          exact (huv (by simpa [hke, hle])).elim

lemma incidentMatching_edge_eq_of_neighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : ∀ x, Even (G.degree x)) (x : V)
    (p q : (incidentMatching G heven x).edgeSet)
    (a b : G.neighborSet x) (hap : a.1 ∈ p.1) (hbq : b.1 ∈ q.1)
    (hab : edgeAtNeighbor x a = edgeAtNeighbor x b) : p = q := by
  have hab' : a = b := edgeAtNeighbor_injective x hab
  subst b
  exact (existsUnique_incidentMatching_edge G heven x a).unique hap hbq

lemma incidentMatching_edge_eq_of_common_spoke
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : ∀ x, Even (G.degree x)) (x : V)
    (p q : (incidentMatching G heven x).edgeSet) (e : G.edgeSet)
    (hep : TransformerVertex.edge e ∈
      (transformerSourceMatchingTriple (W := W) G heven x p).1)
    (heq : TransformerVertex.edge e ∈
      (transformerSourceMatchingTriple (W := W) G heven x q).1) :
    p = q := by
  rw [edge_mem_sourceMatchingTriple_iff] at hep heq
  rcases hep with hep | hep <;> rcases heq with heq | heq
  · exact incidentMatching_edge_eq_of_neighbors G heven x p q
      (matchingNeighborLeft G heven x p) (matchingNeighborLeft G heven x q)
      (Sym2.out_fst_mem p.1) (Sym2.out_fst_mem q.1) (hep.symm.trans heq)
  · exact incidentMatching_edge_eq_of_neighbors G heven x p q
      (matchingNeighborLeft G heven x p) (matchingNeighborRight G heven x q)
      (Sym2.out_fst_mem p.1) (Sym2.out_snd_mem q.1) (hep.symm.trans heq)
  · exact incidentMatching_edge_eq_of_neighbors G heven x p q
      (matchingNeighborRight G heven x p) (matchingNeighborLeft G heven x q)
      (Sym2.out_snd_mem p.1) (Sym2.out_fst_mem q.1) (hep.symm.trans heq)
  · exact incidentMatching_edge_eq_of_neighbors G heven x p q
      (matchingNeighborRight G heven x p) (matchingNeighborRight G heven x q)
      (Sym2.out_snd_mem p.1) (Sym2.out_snd_mem q.1) (hep.symm.trans heq)

lemma sourceEndpoint_mem_of_edge_mem_sourceMatchingTriple
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : ∀ x, Even (G.degree x)) (x : V)
    (p : (incidentMatching G heven x).edgeSet) (e : G.edgeSet)
    (he : TransformerVertex.edge e ∈
      (transformerSourceMatchingTriple (W := W) G heven x p).1) :
    x ∈ e.1 := by
  rw [edge_mem_sourceMatchingTriple_iff] at he
  rcases he with rfl | rfl <;> exact Sym2.mem_mk_left _ _

lemma sourceEndpoint_mem_of_edge_mem_targetMatchingTriple
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    (phi : EdgeBijectiveHom G H)
    (heven : ∀ x, Even (G.degree x)) (x : V)
    (p : (incidentMatching G heven x).edgeSet) (e : G.edgeSet)
    (he : TransformerVertex.edge e ∈
      (transformerTargetMatchingTriple phi heven x p).1) :
    x ∈ e.1 := by
  rw [edge_mem_targetMatchingTriple_iff] at he
  rcases he with rfl | rfl <;> exact Sym2.mem_mk_left _ _

lemma edge_eq_of_common_distinct_endpoints
    {V : Type*} {G : SimpleGraph V} (e f : G.edgeSet) {x y : V}
    (hxy : x ≠ y) (hxe : x ∈ e.1) (hye : y ∈ e.1)
    (hxf : x ∈ f.1) (hyf : y ∈ f.1) : e = f :=
  edgeSubtype_eq_of_two_endpoints e f hxy hxe hye hxf hyf

lemma adj_of_mem_edge_endpoints
    {V : Type*} {G : SimpleGraph V} (e : G.edgeSet) {x y : V}
    (hxy : x ≠ y) (hx : x ∈ e.1) (hy : y ∈ e.1) :
    G.Adj x y := by
  rw [← SimpleGraph.mem_edgeSet]
  have heq : e.1 = s(x, y) := (Sym2.mem_and_mem_iff hxy).mp ⟨hx, hy⟩
  rw [← heq]
  exact e.2

lemma incidentMatching_edge_eq_of_common_targetSpoke
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    (phi : EdgeBijectiveHom G H)
    (heven : ∀ x, Even (G.degree x)) (x : V)
    (p q : (incidentMatching G heven x).edgeSet) (e : G.edgeSet)
    (hep : TransformerVertex.edge e ∈
      (transformerTargetMatchingTriple phi heven x p).1)
    (heq : TransformerVertex.edge e ∈
      (transformerTargetMatchingTriple phi heven x q).1) :
    p = q := by
  apply incidentMatching_edge_eq_of_common_spoke (W := W) G heven x p q e
  · simpa [transformerSourceMatchingTriple, transformerTargetMatchingTriple,
      tripleOfThree] using hep
  · simpa [transformerSourceMatchingTriple, transformerTargetMatchingTriple,
      tripleOfThree] using heq

theorem transformerSourceMatchingTriples_isPacking
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : ∀ x, Even (G.degree x)) :
    IsPackingOn (transformerSourceMatchingTriples (W := W) G heven) := by
  intro u v huv T hT huT hvT U hU huU hvU
  obtain ⟨x, p, rfl⟩ :=
    mem_transformerSourceMatchingTriples_iff G heven |>.mp hT
  obtain ⟨z, q, rfl⟩ :=
    mem_transformerSourceMatchingTriples_iff G heven |>.mp hU
  cases u with
  | source a =>
      cases v with
      | source b =>
          have hax := source_mem_sourceMatchingTriple_iff G heven x a p |>.mp huT
          have hbx := source_mem_sourceMatchingTriple_iff G heven x b p |>.mp hvT
          exact (huv (by simpa [hax, hbx])).elim
      | target b => exact (target_not_mem_sourceMatchingTriple G heven x p b hvT).elim
      | edge e =>
          have hax := source_mem_sourceMatchingTriple_iff G heven x a p |>.mp huT
          have haz := source_mem_sourceMatchingTriple_iff G heven z a q |>.mp huU
          subst a
          have hxz : x = z := haz
          subst z
          have hpq := incidentMatching_edge_eq_of_common_spoke
            (W := W) G heven x p q e hvT hvU
          subst q
          rfl
  | target a => exact (target_not_mem_sourceMatchingTriple G heven x p a huT).elim
  | edge e =>
      cases v with
      | source b =>
          have hbx := source_mem_sourceMatchingTriple_iff G heven x b p |>.mp hvT
          have hbz := source_mem_sourceMatchingTriple_iff G heven z b q |>.mp hvU
          subst b
          have hxz : x = z := hbz
          subst z
          have hpq := incidentMatching_edge_eq_of_common_spoke
            (W := W) G heven x p q e huT huU
          subst q
          rfl
      | target b => exact (target_not_mem_sourceMatchingTriple G heven x p b hvT).elim
      | edge f =>
          by_cases hxz : x = z
          · subst z
            have hpq := incidentMatching_edge_eq_of_common_spoke
              (W := W) G heven x p q e huT huU
            subst q
            rfl
          · have hxe := sourceEndpoint_mem_of_edge_mem_sourceMatchingTriple
              (W := W) G heven x p e huT
            have hze := sourceEndpoint_mem_of_edge_mem_sourceMatchingTriple
              (W := W) G heven z q e huU
            have hxf := sourceEndpoint_mem_of_edge_mem_sourceMatchingTriple
              (W := W) G heven x p f hvT
            have hzf := sourceEndpoint_mem_of_edge_mem_sourceMatchingTriple
              (W := W) G heven z q f hvU
            have hef := edge_eq_of_common_distinct_endpoints e f hxz hxe hze hxf hzf
            exact (huv (congrArg TransformerVertex.edge hef)).elim

theorem transformerTargetMatchingTriples_isPacking
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    (phi : EdgeBijectiveHom G H)
    (heven : ∀ x, Even (G.degree x)) :
    IsPackingOn (transformerTargetMatchingTriples phi heven) := by
  intro u v huv T hT huT hvT U hU huU hvU
  obtain ⟨x, p, rfl⟩ :=
    mem_transformerTargetMatchingTriples_iff phi heven |>.mp hT
  obtain ⟨z, q, rfl⟩ :=
    mem_transformerTargetMatchingTriples_iff phi heven |>.mp hU
  cases u with
  | source a => exact (source_not_mem_targetMatchingTriple phi heven x p a huT).elim
  | target a =>
      cases v with
      | source b => exact (source_not_mem_targetMatchingTriple phi heven x p b hvT).elim
      | target b =>
          have hax := target_mem_targetMatchingTriple_iff phi heven x p a |>.mp huT
          have hbx := target_mem_targetMatchingTriple_iff phi heven x p b |>.mp hvT
          exact (huv (by simpa [hax, hbx])).elim
      | edge e =>
          have hax := target_mem_targetMatchingTriple_iff phi heven x p a |>.mp huT
          have haz := target_mem_targetMatchingTriple_iff phi heven z q a |>.mp huU
          have himage : phi.hom x = phi.hom z := hax.symm.trans haz
          have hxe := sourceEndpoint_mem_of_edge_mem_targetMatchingTriple
            phi heven x p e hvT
          have hze := sourceEndpoint_mem_of_edge_mem_targetMatchingTriple
            phi heven z q e hvU
          have hxz : x = z := by
            by_contra hxz
            have hadj := adj_of_mem_edge_endpoints e hxz hxe hze
            exact (phi.hom.map_rel hadj).ne himage
          subst z
          have hpq := incidentMatching_edge_eq_of_common_targetSpoke
            phi heven x p q e hvT hvU
          subst q
          rfl
  | edge e =>
      cases v with
      | source b => exact (source_not_mem_targetMatchingTriple phi heven x p b hvT).elim
      | target b =>
          have hbx := target_mem_targetMatchingTriple_iff phi heven x p b |>.mp hvT
          have hbz := target_mem_targetMatchingTriple_iff phi heven z q b |>.mp hvU
          have himage : phi.hom x = phi.hom z := hbx.symm.trans hbz
          have hxe := sourceEndpoint_mem_of_edge_mem_targetMatchingTriple
            phi heven x p e huT
          have hze := sourceEndpoint_mem_of_edge_mem_targetMatchingTriple
            phi heven z q e huU
          have hxz : x = z := by
            by_contra hxz
            have hadj := adj_of_mem_edge_endpoints e hxz hxe hze
            exact (phi.hom.map_rel hadj).ne himage
          subst z
          have hpq := incidentMatching_edge_eq_of_common_targetSpoke
            phi heven x p q e huT huU
          subst q
          rfl
      | edge f =>
          by_cases hxz : x = z
          · subst z
            have hpq := incidentMatching_edge_eq_of_common_targetSpoke
              phi heven x p q e huT huU
            subst q
            rfl
          · have hxe := sourceEndpoint_mem_of_edge_mem_targetMatchingTriple
              phi heven x p e huT
            have hze := sourceEndpoint_mem_of_edge_mem_targetMatchingTriple
              phi heven z q e huU
            have hxf := sourceEndpoint_mem_of_edge_mem_targetMatchingTriple
              phi heven x p f hvT
            have hzf := sourceEndpoint_mem_of_edge_mem_targetMatchingTriple
              phi heven z q f hvU
            have hef := edge_eq_of_common_distinct_endpoints e f hxz hxe hze hxf hzf
            exact (huv (congrArg TransformerVertex.edge hef)).elim

lemma IsPackingOn.union_of_cross
    {X : Type*} [DecidableEq X]
    {C D : TripleSystemOn X} (hC : IsPackingOn C) (hD : IsPackingOn D)
    (hcross : ∀ u v : X, u ≠ v →
      ∀ T ∈ C, u ∈ T.1 → v ∈ T.1 →
      ∀ U ∈ D, u ∈ U.1 → v ∈ U.1 → False) :
    IsPackingOn (C ∪ D) := by
  intro u v huv T hT huT hvT U hU huU hvU
  rcases mem_union.mp hT with hTC | hTD <;>
    rcases mem_union.mp hU with hUC | hUD
  · exact hC u v huv T hTC huT hvT U hUC huU hvU
  · exact (hcross u v huv T hTC huT hvT U hUD huU hvU).elim
  · exact (hcross u v huv U hUC huU hvU T hTD huT hvT).elim
  · exact hD u v huv T hTD huT hvT U hUD huU hvU

lemma sourceEdge_targetMatching_cross
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    (phi : EdgeBijectiveHom G H) (heven : ∀ x, Even (G.degree x))
    (u v : TransformerVertex G W) (huv : u ≠ v)
    (e : G.edgeSet)
    (huE : u ∈ (transformerSourceEdgeTriple (W := W) e).1)
    (hvE : v ∈ (transformerSourceEdgeTriple (W := W) e).1)
    (x : V) (p : (incidentMatching G heven x).edgeSet)
    (huM : u ∈ (transformerTargetMatchingTriple phi heven x p).1)
    (hvM : v ∈ (transformerTargetMatchingTriple phi heven x p).1) : False := by
  cases u with
  | source a => exact source_not_mem_targetMatchingTriple phi heven x p a huM
  | target a => exact target_not_mem_sourceEdgeTriple e a huE
  | edge k =>
      cases v with
      | source b => exact source_not_mem_targetMatchingTriple phi heven x p b hvM
      | target b => exact target_not_mem_sourceEdgeTriple e b hvE
      | edge l =>
          have hke := edge_mem_sourceEdgeTriple_iff e k |>.mp huE
          have hle := edge_mem_sourceEdgeTriple_iff e l |>.mp hvE
          exact huv (by simpa [hke, hle])

lemma targetEdge_sourceMatching_cross
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    (phi : EdgeBijectiveHom G H) (heven : ∀ x, Even (G.degree x))
    (u v : TransformerVertex G W) (huv : u ≠ v)
    (e : G.edgeSet)
    (huE : u ∈ (transformerTargetEdgeTriple phi e).1)
    (hvE : v ∈ (transformerTargetEdgeTriple phi e).1)
    (x : V) (p : (incidentMatching G heven x).edgeSet)
    (huM : u ∈ (transformerSourceMatchingTriple (W := W) G heven x p).1)
    (hvM : v ∈ (transformerSourceMatchingTriple (W := W) G heven x p).1) : False := by
  cases u with
  | source a => exact source_not_mem_targetEdgeTriple phi e a huE
  | target a => exact target_not_mem_sourceMatchingTriple G heven x p a huM
  | edge k =>
      cases v with
      | source b => exact source_not_mem_targetEdgeTriple phi e b hvE
      | target b => exact target_not_mem_sourceMatchingTriple G heven x p b hvM
      | edge l =>
          have hke := edge_mem_targetEdgeTriple_iff phi e k |>.mp huE
          have hle := edge_mem_targetEdgeTriple_iff phi e l |>.mp hvE
          exact huv (by simpa [hke, hle])

theorem transformerSourceSide_isPacking
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    (phi : EdgeBijectiveHom G H) (heven : ∀ x, Even (G.degree x)) :
    IsPackingOn (transformerSourceSide phi heven) := by
  apply IsPackingOn.union_of_cross
    (transformerSourceEdgeTriples_isPacking (W := W) G)
    (transformerTargetMatchingTriples_isPacking phi heven)
  intro u v huv T hTE huT hvT U hUM huU hvU
  obtain ⟨e, rfl⟩ := mem_transformerSourceEdgeTriples_iff.mp hTE
  obtain ⟨x, p, rfl⟩ :=
    mem_transformerTargetMatchingTriples_iff phi heven |>.mp hUM
  exact sourceEdge_targetMatching_cross phi heven u v huv e huT hvT x p huU hvU

theorem transformerTargetSide_isPacking
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    (phi : EdgeBijectiveHom G H) (heven : ∀ x, Even (G.degree x)) :
    IsPackingOn (transformerTargetSide phi heven) := by
  apply IsPackingOn.union_of_cross
    (transformerTargetEdgeTriples_isPacking phi)
    (transformerSourceMatchingTriples_isPacking (W := W) G heven)
  intro u v huv T hTE huT hvT U hUM huU hvU
  obtain ⟨e, rfl⟩ := mem_transformerTargetEdgeTriples_iff phi |>.mp hTE
  obtain ⟨x, p, rfl⟩ :=
    mem_transformerSourceMatchingTriples_iff G heven |>.mp hUM
  exact targetEdge_sourceMatching_cross phi heven u v huv e huT hvT x p huU hvU

def transformerSourceRoot
    {V W : Type*} (G : SimpleGraph V) :
    SimpleGraph (TransformerVertex G W) :=
  G.map (transformerSourceEmbedding G)

def transformerTargetRoot
    {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) :
    SimpleGraph (TransformerVertex G W) :=
  H.map (transformerTargetEmbedding G)

/-- Every source-root edge is covered on the source side. -/
lemma transformerSourceRoot_le_coveredGraph
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    (φ : EdgeBijectiveHom G H)
    (heven : ∀ x, Even (G.degree x)) :
    transformerSourceRoot (W := W) G ≤
      coveredGraph (transformerSourceSide φ heven) := by
  intro u v huv
  rw [transformerSourceRoot, SimpleGraph.map_adj] at huv
  obtain ⟨x, y, hxy, rfl, rfl⟩ := huv
  let e : G.edgeSet := ⟨s(x, y), hxy⟩
  refine ⟨transformerSourceEdgeTriple e, ?_, ?_, ?_, ?_⟩
  · apply mem_union_left
    exact mem_transformerSourceEdgeTriples_iff.mpr ⟨e, rfl⟩
  · exact source_mem_sourceEdgeTriple_of_mem e (Sym2.mem_mk_left x y)
  · exact source_mem_sourceEdgeTriple_of_mem e (Sym2.mem_mk_right x y)
  · simpa using G.ne_of_adj hxy

/-- Every target-root edge is covered on the target side. -/
lemma transformerTargetRoot_le_coveredGraph
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    (φ : EdgeBijectiveHom G H)
    (heven : ∀ x, Even (G.degree x)) :
    transformerTargetRoot G H ≤
      coveredGraph (transformerTargetSide φ heven) := by
  intro u v huv
  rw [transformerTargetRoot, SimpleGraph.map_adj] at huv
  obtain ⟨x, y, hxy, rfl, rfl⟩ := huv
  obtain ⟨e, he⟩ := φ.edge_bijective.2 ⟨s(x, y), hxy⟩
  have he' : φ.edgeEquiv e = ⟨s(x, y), hxy⟩ := by
    change φ.hom.mapEdgeSet e = ⟨s(x, y), hxy⟩
    exact he
  refine ⟨transformerTargetEdgeTriple φ e, ?_, ?_, ?_, ?_⟩
  · apply mem_union_left
    exact mem_transformerTargetEdgeTriples_iff φ |>.mpr ⟨e, rfl⟩
  · have hx : x ∈ (φ.edgeEquiv e).1 := by
      rw [he']
      exact Sym2.mem_mk_left x y
    have hxout : x = (φ.edgeEquiv e).1.out.1 ∨
        x = (φ.edgeEquiv e).1.out.2 := by
      rw [← (φ.edgeEquiv e).1.out_eq, Sym2.mem_iff] at hx
      exact hx
    simp only [transformerTargetEdgeTriple, tripleOfThree,
      transformerTargetEmbedding, mem_insert, mem_singleton]
    rcases hxout with hx | hx
    · left
      change TransformerVertex.target x =
        TransformerVertex.target (φ.edgeEquiv e).1.out.1
      exact congrArg TransformerVertex.target hx
    · right
      left
      change TransformerVertex.target x =
        TransformerVertex.target (φ.edgeEquiv e).1.out.2
      exact congrArg TransformerVertex.target hx
  · have hy : y ∈ (φ.edgeEquiv e).1 := by
      rw [he']
      exact Sym2.mem_mk_right x y
    have hyout : y = (φ.edgeEquiv e).1.out.1 ∨
        y = (φ.edgeEquiv e).1.out.2 := by
      rw [← (φ.edgeEquiv e).1.out_eq, Sym2.mem_iff] at hy
      exact hy
    simp only [transformerTargetEdgeTriple, tripleOfThree,
      transformerTargetEmbedding, mem_insert, mem_singleton]
    rcases hyout with hy | hy
    · left
      change TransformerVertex.target y =
        TransformerVertex.target (φ.edgeEquiv e).1.out.1
      exact congrArg TransformerVertex.target hy
    · right
      left
      change TransformerVertex.target y =
        TransformerVertex.target (φ.edgeEquiv e).1.out.2
      exact congrArg TransformerVertex.target hy
  · exact (transformerTargetEmbedding G).injective.ne (H.ne_of_adj hxy)

lemma transformerSourceRoot_adj_of_adj
    {V W : Type*} {G : SimpleGraph V} {x y : V} (hxy : G.Adj x y) :
    (transformerSourceRoot (W := W) G).Adj
      (.source x) (.source y) := by
  rw [transformerSourceRoot, SimpleGraph.map_adj]
  exact ⟨x, y, hxy, rfl, rfl⟩

lemma transformerTargetRoot_adj_of_adj
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {x y : W} (hxy : H.Adj x y) :
    (transformerTargetRoot G H).Adj (.target x) (.target y) := by
  rw [transformerTargetRoot, SimpleGraph.map_adj]
  exact ⟨x, y, hxy, rfl, rfl⟩

/-- Each triangle of the source decomposition uses only pairs occurring in
the target decomposition or in the source root. -/
lemma sourceEdgeTriple_pair_targetSide_or_sourceRoot
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    (phi : EdgeBijectiveHom G H) (heven : ∀ x, Even (G.degree x))
    (e : G.edgeSet) {u v : TransformerVertex G W}
    (hu : u ∈ (transformerSourceEdgeTriple (W := W) e).1)
    (hv : v ∈ (transformerSourceEdgeTriple (W := W) e).1)
    (huv : u ≠ v) :
    (coveredGraph (transformerTargetSide phi heven) ⊔
      transformerSourceRoot (W := W) G).Adj u v := by
  have headj : G.Adj e.1.out.1 e.1.out.2 := by
    rw [← SimpleGraph.mem_edgeSet]
    have hout : s(e.1.out.1, e.1.out.2) = e.1 := by
      change Quot.mk _ e.1.out = e.1
      exact e.1.out_eq
    rw [hout]
    exact e.2
  have heleft : edgeAtNeighbor e.1.out.1
        (⟨e.1.out.2, headj⟩ : G.neighborSet e.1.out.1) = e := by
    apply Subtype.ext
    change s(e.1.out.1, e.1.out.2) = e.1
    change Quot.mk _ e.1.out = e.1
    exact e.1.out_eq
  have heright : edgeAtNeighbor e.1.out.2
        (⟨e.1.out.1, by
          change G.Adj e.1.out.2 e.1.out.1
          exact headj.symm⟩ : G.neighborSet e.1.out.2) = e := by
    apply Subtype.ext
    change s(e.1.out.2, e.1.out.1) = e.1
    rw [Sym2.eq_swap]
    change Quot.mk _ e.1.out = e.1
    exact e.1.out_eq
  simp only [transformerSourceEdgeTriple, tripleOfThree, mem_insert,
    mem_singleton] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  · exact (huv rfl).elim

  · rw [SimpleGraph.sup_adj]
    right
    exact transformerSourceRoot_adj_of_adj headj
  · rw [SimpleGraph.sup_adj]
    left
    let y : G.neighborSet e.1.out.1 := ⟨e.1.out.2, headj⟩
    obtain ⟨p, hroot, hedge⟩ :=
      exists_sourceMatchingTriple_spoke (W := W) G heven e.1.out.1 y
    refine ⟨transformerSourceMatchingTriple G heven e.1.out.1 p,
      ?_, hroot, ?_, by simp⟩
    · apply mem_union_right
      exact mem_transformerSourceMatchingTriples_iff G heven |>.mpr
        ⟨e.1.out.1, p, rfl⟩
    · simpa [y, heleft] using hedge
  · rw [SimpleGraph.sup_adj]
    right
    exact (transformerSourceRoot_adj_of_adj headj).symm
  · exact (huv rfl).elim
  · rw [SimpleGraph.sup_adj]
    left
    let y : G.neighborSet e.1.out.2 := ⟨e.1.out.1, by
      change G.Adj e.1.out.2 e.1.out.1
      exact headj.symm⟩
    obtain ⟨p, hroot, hedge⟩ :=
      exists_sourceMatchingTriple_spoke (W := W) G heven e.1.out.2 y
    refine ⟨transformerSourceMatchingTriple G heven e.1.out.2 p,
      ?_, hroot, ?_, by simp⟩
    · apply mem_union_right
      exact mem_transformerSourceMatchingTriples_iff G heven |>.mpr
        ⟨e.1.out.2, p, rfl⟩
    · simpa [y, heright] using hedge
  · rw [SimpleGraph.sup_adj]
    left
    let y : G.neighborSet e.1.out.1 := ⟨e.1.out.2, headj⟩
    obtain ⟨p, hroot, hedge⟩ :=
      exists_sourceMatchingTriple_spoke (W := W) G heven e.1.out.1 y
    refine ⟨transformerSourceMatchingTriple G heven e.1.out.1 p,
      ?_, ?_, hroot, by simp⟩
    · apply mem_union_right
      exact mem_transformerSourceMatchingTriples_iff G heven |>.mpr
        ⟨e.1.out.1, p, rfl⟩
    · simpa [y, heleft] using hedge
  · rw [SimpleGraph.sup_adj]
    left
    let y : G.neighborSet e.1.out.2 := ⟨e.1.out.1, by
      change G.Adj e.1.out.2 e.1.out.1
      exact headj.symm⟩
    obtain ⟨p, hroot, hedge⟩ :=
      exists_sourceMatchingTriple_spoke (W := W) G heven e.1.out.2 y
    refine ⟨transformerSourceMatchingTriple G heven e.1.out.2 p,
      ?_, ?_, hroot, by simp⟩
    · apply mem_union_right
      exact mem_transformerSourceMatchingTriples_iff G heven |>.mpr
        ⟨e.1.out.2, p, rfl⟩
    · simpa [y, heright] using hedge
  · exact (huv rfl).elim

lemma targetMatchingTriple_pair_targetSide_or_sourceRoot
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    (phi : EdgeBijectiveHom G H) (heven : ∀ x, Even (G.degree x))
    (x : V) (p : (incidentMatching G heven x).edgeSet)
    {u v : TransformerVertex G W}
    (hu : u ∈ (transformerTargetMatchingTriple phi heven x p).1)
    (hv : v ∈ (transformerTargetMatchingTriple phi heven x p).1)
    (huv : u ≠ v) :
    (coveredGraph (transformerTargetSide phi heven) ⊔
      transformerSourceRoot (W := W) G).Adj u v := by
  let y₁ := matchingNeighborLeft G heven x p
  let y₂ := matchingNeighborRight G heven x p
  let e₁ := edgeAtNeighbor x y₁
  let e₂ := edgeAtNeighbor x y₂
  have hx₁ : x ∈ e₁.1 := Sym2.mem_mk_left x y₁.1
  have hx₂ : x ∈ e₂.1 := Sym2.mem_mk_left x y₂.1
  have he₁ : TransformerVertex.edge e₁ ∈
      (transformerSourceMatchingTriple (W := W) G heven x p).1 := by
    simp [transformerSourceMatchingTriple, tripleOfThree, e₁, e₂, y₁, y₂]
  have he₂ : TransformerVertex.edge e₂ ∈
      (transformerSourceMatchingTriple (W := W) G heven x p).1 := by
    simp [transformerSourceMatchingTriple, tripleOfThree, e₁, e₂, y₁, y₂]
  simp only [transformerTargetMatchingTriple, tripleOfThree, mem_insert,
    mem_singleton] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  · exact (huv rfl).elim

  · rw [SimpleGraph.sup_adj]
    left
    refine ⟨transformerTargetEdgeTriple phi e₁, ?_, ?_,
      edge_mem_targetEdgeTriple phi e₁, by simp⟩
    · apply mem_union_left
      exact mem_transformerTargetEdgeTriples_iff phi |>.mpr ⟨e₁, rfl⟩
    · exact target_mem_targetEdgeTriple_of_mem phi e₁ hx₁
  · rw [SimpleGraph.sup_adj]
    left
    refine ⟨transformerTargetEdgeTriple phi e₂, ?_, ?_,
      edge_mem_targetEdgeTriple phi e₂, by simp⟩
    · apply mem_union_left
      exact mem_transformerTargetEdgeTriples_iff phi |>.mpr ⟨e₂, rfl⟩
    · exact target_mem_targetEdgeTriple_of_mem phi e₂ hx₂
  · rw [SimpleGraph.sup_adj]
    left
    refine ⟨transformerTargetEdgeTriple phi e₁, ?_,
      edge_mem_targetEdgeTriple phi e₁, ?_, by simp⟩
    · apply mem_union_left
      exact mem_transformerTargetEdgeTriples_iff phi |>.mpr ⟨e₁, rfl⟩
    · exact target_mem_targetEdgeTriple_of_mem phi e₁ hx₁
  · exact (huv rfl).elim
  · rw [SimpleGraph.sup_adj]
    left
    refine ⟨transformerSourceMatchingTriple G heven x p, ?_, he₁, he₂,
      by simpa using huv⟩
    apply mem_union_right
    exact mem_transformerSourceMatchingTriples_iff G heven |>.mpr ⟨x, p, rfl⟩
  · rw [SimpleGraph.sup_adj]
    left
    refine ⟨transformerTargetEdgeTriple phi e₂, ?_,
      edge_mem_targetEdgeTriple phi e₂, ?_, by simp⟩
    · apply mem_union_left
      exact mem_transformerTargetEdgeTriples_iff phi |>.mpr ⟨e₂, rfl⟩
    · exact target_mem_targetEdgeTriple_of_mem phi e₂ hx₂
  · rw [SimpleGraph.sup_adj]
    left
    refine ⟨transformerSourceMatchingTriple G heven x p, ?_, he₂, he₁,
      by simpa using huv⟩
    apply mem_union_right
    exact mem_transformerSourceMatchingTriples_iff G heven |>.mpr ⟨x, p, rfl⟩
  · exact (huv rfl).elim

lemma sourceMatchingTriple_pair_sourceSide_or_targetRoot
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    (phi : EdgeBijectiveHom G H) (heven : ∀ x, Even (G.degree x))
    (x : V) (p : (incidentMatching G heven x).edgeSet)
    {u v : TransformerVertex G W}
    (hu : u ∈ (transformerSourceMatchingTriple (W := W) G heven x p).1)
    (hv : v ∈ (transformerSourceMatchingTriple (W := W) G heven x p).1)
    (huv : u ≠ v) :
    (coveredGraph (transformerSourceSide phi heven) ⊔
      transformerTargetRoot G H).Adj u v := by
  let y₁ := matchingNeighborLeft G heven x p
  let y₂ := matchingNeighborRight G heven x p
  let e₁ := edgeAtNeighbor x y₁
  let e₂ := edgeAtNeighbor x y₂
  have hx₁ : x ∈ e₁.1 := Sym2.mem_mk_left x y₁.1
  have hx₂ : x ∈ e₂.1 := Sym2.mem_mk_left x y₂.1
  have he₁ : TransformerVertex.edge e₁ ∈
      (transformerTargetMatchingTriple phi heven x p).1 := by
    simp [transformerTargetMatchingTriple, tripleOfThree, e₁, y₁]
  have he₂ : TransformerVertex.edge e₂ ∈
      (transformerTargetMatchingTriple phi heven x p).1 := by
    simp [transformerTargetMatchingTriple, tripleOfThree, e₂, y₂]
  simp only [transformerSourceMatchingTriple, tripleOfThree, mem_insert,
    mem_singleton] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  · exact (huv rfl).elim
  · rw [SimpleGraph.sup_adj]
    left
    refine ⟨transformerSourceEdgeTriple e₁, ?_, ?_,
      edge_mem_sourceEdgeTriple e₁, by simp⟩
    · apply mem_union_left
      exact mem_transformerSourceEdgeTriples_iff.mpr ⟨e₁, rfl⟩
    · exact source_mem_sourceEdgeTriple_of_mem e₁ hx₁
  · rw [SimpleGraph.sup_adj]
    left
    refine ⟨transformerSourceEdgeTriple e₂, ?_, ?_,
      edge_mem_sourceEdgeTriple e₂, by simp⟩
    · apply mem_union_left
      exact mem_transformerSourceEdgeTriples_iff.mpr ⟨e₂, rfl⟩
    · exact source_mem_sourceEdgeTriple_of_mem e₂ hx₂
  · rw [SimpleGraph.sup_adj]
    left
    refine ⟨transformerSourceEdgeTriple e₁, ?_,
      edge_mem_sourceEdgeTriple e₁, ?_, by simp⟩
    · apply mem_union_left
      exact mem_transformerSourceEdgeTriples_iff.mpr ⟨e₁, rfl⟩
    · exact source_mem_sourceEdgeTriple_of_mem e₁ hx₁
  · exact (huv rfl).elim
  · rw [SimpleGraph.sup_adj]
    left
    refine ⟨transformerTargetMatchingTriple phi heven x p, ?_, he₁, he₂,
      by simpa using huv⟩
    apply mem_union_right
    exact mem_transformerTargetMatchingTriples_iff phi heven |>.mpr ⟨x, p, rfl⟩
  · rw [SimpleGraph.sup_adj]
    left
    refine ⟨transformerSourceEdgeTriple e₂, ?_,
      edge_mem_sourceEdgeTriple e₂, ?_, by simp⟩
    · apply mem_union_left
      exact mem_transformerSourceEdgeTriples_iff.mpr ⟨e₂, rfl⟩
    · exact source_mem_sourceEdgeTriple_of_mem e₂ hx₂
  · rw [SimpleGraph.sup_adj]
    left
    refine ⟨transformerTargetMatchingTriple phi heven x p, ?_, he₂, he₁,
      by simpa using huv⟩
    apply mem_union_right
    exact mem_transformerTargetMatchingTriples_iff phi heven |>.mpr ⟨x, p, rfl⟩
  · exact (huv rfl).elim

lemma targetEdgeTriple_pair_sourceSide_or_targetRoot
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    (phi : EdgeBijectiveHom G H) (heven : ∀ x, Even (G.degree x))
    (e : G.edgeSet) {u v : TransformerVertex G W}
    (hu : u ∈ (transformerTargetEdgeTriple phi e).1)
    (hv : v ∈ (transformerTargetEdgeTriple phi e).1)
    (huv : u ≠ v) :
    (coveredGraph (transformerSourceSide phi heven) ⊔
      transformerTargetRoot G H).Adj u v := by
  let e' := phi.edgeEquiv e
  have hy₁ : e'.1.out.1 ∈ e'.1 := by
    exact Sym2.out_fst_mem e'.1
  have hy₂ : e'.1.out.2 ∈ e'.1 := by
    exact Sym2.out_snd_mem e'.1
  obtain ⟨x₁, p₁, hx₁, ht₁, he₁⟩ :=
    exists_targetMatchingTriple_mapped_spoke phi heven e hy₁
  obtain ⟨x₂, p₂, hx₂, ht₂, he₂⟩ :=
    exists_targetMatchingTriple_mapped_spoke phi heven e hy₂
  simp only [transformerTargetEdgeTriple, tripleOfThree, mem_insert,
    mem_singleton] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  · exact (huv rfl).elim

  · rw [SimpleGraph.sup_adj]
    right
    exact transformerTargetRoot_adj_of_adj (edge_out_adj e')
  · rw [SimpleGraph.sup_adj]
    left
    refine ⟨transformerTargetMatchingTriple phi heven x₁ p₁, ?_, ?_, he₁,
      by simp⟩
    · apply mem_union_right
      exact mem_transformerTargetMatchingTriples_iff phi heven |>.mpr
        ⟨x₁, p₁, rfl⟩
    · simpa [e', hx₁] using ht₁
  · rw [SimpleGraph.sup_adj]
    right
    exact (transformerTargetRoot_adj_of_adj (edge_out_adj e')).symm
  · exact (huv rfl).elim
  · rw [SimpleGraph.sup_adj]
    left
    refine ⟨transformerTargetMatchingTriple phi heven x₂ p₂, ?_, ?_, he₂,
      by simp⟩
    · apply mem_union_right
      exact mem_transformerTargetMatchingTriples_iff phi heven |>.mpr
        ⟨x₂, p₂, rfl⟩
    · simpa [e', hx₂] using ht₂
  · rw [SimpleGraph.sup_adj]
    left
    refine ⟨transformerTargetMatchingTriple phi heven x₁ p₁, ?_, he₁, ?_,
      by simp⟩
    · apply mem_union_right
      exact mem_transformerTargetMatchingTriples_iff phi heven |>.mpr
        ⟨x₁, p₁, rfl⟩
    · simpa [e', hx₁] using ht₁
  · rw [SimpleGraph.sup_adj]
    left
    refine ⟨transformerTargetMatchingTriple phi heven x₂ p₂, ?_, he₂, ?_,
      by simp⟩
    · apply mem_union_right
      exact mem_transformerTargetMatchingTriples_iff phi heven |>.mpr
        ⟨x₂, p₂, rfl⟩
    · simpa [e', hx₂] using ht₂
  · exact (huv rfl).elim

lemma coveredGraph_transformerSourceSide_le
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    (phi : EdgeBijectiveHom G H) (heven : ∀ x, Even (G.degree x)) :
    coveredGraph (transformerSourceSide phi heven) ≤
      coveredGraph (transformerTargetSide phi heven) ⊔
        transformerSourceRoot (W := W) G := by
  intro u v huv
  obtain ⟨T, hT, hu, hv, hne⟩ := huv
  rcases mem_union.mp hT with hEdge | hMatching
  · obtain ⟨e, rfl⟩ := mem_transformerSourceEdgeTriples_iff.mp hEdge
    exact sourceEdgeTriple_pair_targetSide_or_sourceRoot phi heven e hu hv hne
  · obtain ⟨x, p, rfl⟩ :=
      mem_transformerTargetMatchingTriples_iff phi heven |>.mp hMatching
    exact targetMatchingTriple_pair_targetSide_or_sourceRoot
      phi heven x p hu hv hne

lemma coveredGraph_transformerTargetSide_le
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    (phi : EdgeBijectiveHom G H) (heven : ∀ x, Even (G.degree x)) :
    coveredGraph (transformerTargetSide phi heven) ≤
      coveredGraph (transformerSourceSide phi heven) ⊔
        transformerTargetRoot G H := by
  intro u v huv
  obtain ⟨T, hT, hu, hv, hne⟩ := huv
  rcases mem_union.mp hT with hEdge | hMatching
  · obtain ⟨e, rfl⟩ :=
      mem_transformerTargetEdgeTriples_iff phi |>.mp hEdge
    exact targetEdgeTriple_pair_sourceSide_or_targetRoot phi heven e hu hv hne
  · obtain ⟨x, p, rfl⟩ :=
      mem_transformerSourceMatchingTriples_iff G heven |>.mp hMatching
    exact sourceMatchingTriple_pair_sourceSide_or_targetRoot
      phi heven x p hu hv hne

/-- Adjoining the opposite root to either decomposition produces the same
graph. -/
theorem coveredGraph_transformerSides_sup_roots
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    (phi : EdgeBijectiveHom G H) (heven : ∀ x, Even (G.degree x)) :
    coveredGraph (transformerSourceSide phi heven) ⊔ transformerTargetRoot G H =
      coveredGraph (transformerTargetSide phi heven) ⊔
        transformerSourceRoot (W := W) G := by
  apply le_antisymm
  · rw [sup_le_iff]
    exact ⟨coveredGraph_transformerSourceSide_le phi heven,
      (transformerTargetRoot_le_coveredGraph phi heven).trans le_sup_left⟩
  · rw [sup_le_iff]
    exact ⟨coveredGraph_transformerTargetSide_le phi heven,
      (transformerSourceRoot_le_coveredGraph phi heven).trans le_sup_left⟩

lemma transformerTargetSide_disjoint_sourceRoot
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    (phi : EdgeBijectiveHom G H) (heven : ∀ x, Even (G.degree x)) :
    Disjoint (coveredGraph (transformerTargetSide phi heven))
      (transformerSourceRoot (W := W) G) := by
  rw [← SimpleGraph.disjoint_edgeSet, Set.disjoint_left]
  intro e heSide heRoot
  induction e using Sym2.ind with
  | h u v =>
      rw [SimpleGraph.mem_edgeSet, transformerSourceRoot,
        SimpleGraph.map_adj] at heRoot
      obtain ⟨x, y, hxy, rfl, rfl⟩ := heRoot
      rw [SimpleGraph.mem_edgeSet, coveredGraph_adj] at heSide
      obtain ⟨T, hT, hxT, hyT, hxy'⟩ := heSide
      rcases mem_union.mp hT with hEdge | hMatching
      · obtain ⟨a, rfl⟩ :=
          mem_transformerTargetEdgeTriples_iff phi |>.mp hEdge
        exact source_not_mem_targetEdgeTriple phi a x hxT
      · obtain ⟨a, p, rfl⟩ :=
          mem_transformerSourceMatchingTriples_iff G heven |>.mp hMatching
        have hxa := source_mem_sourceMatchingTriple_iff G heven a x p |>.mp hxT
        have hya := source_mem_sourceMatchingTriple_iff G heven a y p |>.mp hyT
        exact (G.ne_of_adj hxy) (hxa.trans hya.symm)

lemma transformerSourceSide_disjoint_targetRoot
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    (phi : EdgeBijectiveHom G H) (heven : ∀ x, Even (G.degree x)) :
    Disjoint (coveredGraph (transformerSourceSide phi heven))
      (transformerTargetRoot G H) := by
  rw [← SimpleGraph.disjoint_edgeSet, Set.disjoint_left]
  intro e heSide heRoot
  induction e using Sym2.ind with
  | h u v =>
      rw [SimpleGraph.mem_edgeSet, transformerTargetRoot,
        SimpleGraph.map_adj] at heRoot
      obtain ⟨x, y, hxy, rfl, rfl⟩ := heRoot
      rw [SimpleGraph.mem_edgeSet, coveredGraph_adj] at heSide
      obtain ⟨T, hT, hxT, hyT, hxy'⟩ := heSide
      rcases mem_union.mp hT with hEdge | hMatching
      · obtain ⟨a, rfl⟩ := mem_transformerSourceEdgeTriples_iff.mp hEdge
        exact target_not_mem_sourceEdgeTriple a x hxT
      · obtain ⟨a, p, rfl⟩ :=
          mem_transformerTargetMatchingTriples_iff phi heven |>.mp hMatching
        have hxa := target_mem_targetMatchingTriple_iff phi heven a p x |>.mp hxT
        have hya := target_mem_targetMatchingTriple_iff phi heven a p y |>.mp hyT
        exact (H.ne_of_adj hxy) (hxa.trans hya.symm)

/-- The edges common to the two sides are precisely the auxiliary
transformer edges; the two roots live only on their respective sides. -/
def transformerGraph
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    (phi : EdgeBijectiveHom G H) (heven : ∀ x, Even (G.degree x)) :
    SimpleGraph (TransformerVertex G W) :=
  coveredGraph (transformerSourceSide phi heven) ⊓
    coveredGraph (transformerTargetSide phi heven)

lemma coveredGraph_transformerSourceSide_eq
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    (phi : EdgeBijectiveHom G H) (heven : ∀ x, Even (G.degree x)) :
    coveredGraph (transformerSourceSide phi heven) =
      transformerGraph phi heven ⊔ transformerSourceRoot (W := W) G := by
  apply le_antisymm
  · intro u v huv
    have h := coveredGraph_transformerSourceSide_le phi heven huv
    rw [SimpleGraph.sup_adj] at h ⊢
    rcases h with htarget | hroot
    · left
      rw [transformerGraph, SimpleGraph.inf_adj]
      exact ⟨huv, htarget⟩
    · exact Or.inr hroot
  · rw [sup_le_iff]
    exact ⟨inf_le_left, transformerSourceRoot_le_coveredGraph phi heven⟩

lemma coveredGraph_transformerTargetSide_eq
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    (phi : EdgeBijectiveHom G H) (heven : ∀ x, Even (G.degree x)) :
    coveredGraph (transformerTargetSide phi heven) =
      transformerGraph phi heven ⊔ transformerTargetRoot G H := by
  apply le_antisymm
  · intro u v huv
    have h := coveredGraph_transformerTargetSide_le phi heven huv
    rw [SimpleGraph.sup_adj] at h ⊢
    rcases h with hsource | hroot
    · left
      rw [transformerGraph, SimpleGraph.inf_adj]
      exact ⟨hsource, huv⟩
    · exact Or.inr hroot
  · rw [sup_le_iff]
    exact ⟨inf_le_right, transformerTargetRoot_le_coveredGraph phi heven⟩

lemma transformerGraph_disjoint_sourceRoot
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    (phi : EdgeBijectiveHom G H) (heven : ∀ x, Even (G.degree x)) :
    Disjoint (transformerGraph phi heven) (transformerSourceRoot (W := W) G) :=
  (transformerTargetSide_disjoint_sourceRoot phi heven).mono inf_le_right le_rfl

lemma transformerGraph_disjoint_targetRoot
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    (phi : EdgeBijectiveHom G H) (heven : ∀ x, Even (G.degree x)) :
    Disjoint (transformerGraph phi heven) (transformerTargetRoot G H) :=
  (transformerSourceSide_disjoint_targetRoot phi heven).mono inf_le_left le_rfl

/-- Exact finite transformer interface: `sourceSide` decomposes the
auxiliary graph plus the source root, while `targetSide` decomposes the same
auxiliary graph plus the target root. -/
def IsGraphTransformerOn {X : Type*} [DecidableEq X]
    (sourceRoot targetRoot auxiliary : SimpleGraph X)
    (sourceSide targetSide : TripleSystemOn X) : Prop :=
  IsPackingOn sourceSide ∧ IsPackingOn targetSide ∧
    Disjoint auxiliary sourceRoot ∧ Disjoint auxiliary targetRoot ∧
    coveredGraph sourceSide = auxiliary ⊔ sourceRoot ∧
    coveredGraph targetSide = auxiliary ⊔ targetRoot

/-- The simple edge-bijective construction is a genuine graph transformer. -/
theorem edgeBijectiveHom_isGraphTransformer
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    (phi : EdgeBijectiveHom G H) (heven : ∀ x, Even (G.degree x)) :
    IsGraphTransformerOn
      (transformerSourceRoot (W := W) G) (transformerTargetRoot G H)
      (transformerGraph phi heven) (transformerSourceSide phi heven)
      (transformerTargetSide phi heven) := by
  exact ⟨transformerSourceSide_isPacking phi heven,
    transformerTargetSide_isPacking phi heven,
    transformerGraph_disjoint_sourceRoot phi heven,
    transformerGraph_disjoint_targetRoot phi heven,
    coveredGraph_transformerSourceSide_eq phi heven,
    coveredGraph_transformerTargetSide_eq phi heven⟩

theorem IsGraphTransformerOn.map
    {X Z : Type*} [Fintype X] [Fintype Z] [DecidableEq X] [DecidableEq Z]
    {sourceRoot targetRoot auxiliary : SimpleGraph X}
    {sourceSide targetSide : TripleSystemOn X}
    (h : IsGraphTransformerOn sourceRoot targetRoot auxiliary
      sourceSide targetSide) (f : X ↪ Z) :
    IsGraphTransformerOn (sourceRoot.map f) (targetRoot.map f)
      (auxiliary.map f) (mapTripleSystem f sourceSide)
      (mapTripleSystem f targetSide) := by
  rcases h with ⟨hSource, hTarget, hAuxSource, hAuxTarget,
    hSourceCover, hTargetCover⟩
  refine ⟨hSource.map f, hTarget.map f,
    SimpleGraph.disjoint_map_embedding f hAuxSource,
    SimpleGraph.disjoint_map_embedding f hAuxTarget, ?_, ?_⟩
  · rw [coveredGraph_mapTripleSystem, ← SimpleGraph.map_sup_embedding]
    exact congrArg (SimpleGraph.map f) hSourceCover
  · rw [coveredGraph_mapTripleSystem, ← SimpleGraph.map_sup_embedding]
    exact congrArg (SimpleGraph.map f) hTargetCover

lemma IsTriangleDecomposition.isPackingOn
    {X : Type*} [DecidableEq X] {G : SimpleGraph X}
    {C : TripleSystemOn X} (hC : IsTriangleDecomposition G C) :
    IsPackingOn C := by
  intro u v huv T hT huT hvT U hU huU hvU
  have huvG := hC.1 T hT u huT v hvT huv
  exact (hC.2 u v huvG).unique ⟨hT, huT, hvT⟩ ⟨hU, huU, hvU⟩

lemma IsTriangleDecomposition.coveredGraph_eq
    {X : Type*} [DecidableEq X] {G : SimpleGraph X}
    {C : TripleSystemOn X} (hC : IsTriangleDecomposition G C) :
    coveredGraph C = G := by
  apply le_antisymm
  · intro u v huv
    obtain ⟨T, hT, huT, hvT, huvne⟩ := huv
    exact hC.1 T hT u huT v hvT huvne
  · intro u v huv
    obtain ⟨T, hT, huT, hvT⟩ := (hC.2 u v huv).exists
    exact ⟨T, hT, huT, hvT, G.ne_of_adj huv⟩

/-- Compose an exclusive absorber for the source root with a transformer
from the source root to the target root.  The source root is retained as an
auxiliary part of the resulting target absorber. -/
theorem IsExclusiveGraphAbsorberOn.compose_transformer
    {X : Type*} [Fintype X] [DecidableEq X]
    {sourceRoot targetRoot auxiliary absorberGraph : SimpleGraph X}
    {absorberOut absorberIn sourceSide targetSide : TripleSystemOn X}
    (habs : IsExclusiveGraphAbsorberOn sourceRoot absorberOut absorberIn)
    (htrans : IsGraphTransformerOn sourceRoot targetRoot auxiliary
      sourceSide targetSide)
    (hOutDisj : Disjoint absorberGraph (auxiliary ⊔ sourceRoot))
    (hInDisj : Disjoint (absorberGraph ⊔ sourceRoot)
      (auxiliary ⊔ targetRoot))
    (hAbsGraph : coveredGraph absorberOut = absorberGraph)
    (hRootDisj : Disjoint (absorberGraph ⊔ (auxiliary ⊔ sourceRoot))
      targetRoot) :
    IsExclusiveGraphAbsorberOn targetRoot
      (absorberOut ∪ sourceSide) (absorberIn ∪ targetSide) := by
  rcases htrans with ⟨hSourcePacking, hTargetPacking, hAuxSource,
    hAuxTarget, hSourceCover, hTargetCover⟩
  have hSourceDec : IsTriangleDecomposition
      (auxiliary ⊔ sourceRoot) sourceSide := by
    rw [← hSourceCover]
    exact hSourcePacking.isTriangleDecomposition
  have hTargetDec : IsTriangleDecomposition
      (auxiliary ⊔ targetRoot) targetSide := by
    rw [← hTargetCover]
    exact hTargetPacking.isTriangleDecomposition
  have hOutDec : IsTriangleDecomposition
      (absorberGraph ⊔ (auxiliary ⊔ sourceRoot))
      (absorberOut ∪ sourceSide) := by
    have hAbsOut : IsTriangleDecomposition absorberGraph absorberOut := by
      rw [← hAbsGraph]
      exact habs.out_decomposition
    exact hAbsOut.union hSourceDec hOutDisj
  have hInDec : IsTriangleDecomposition
      ((absorberGraph ⊔ sourceRoot) ⊔ (auxiliary ⊔ targetRoot))
      (absorberIn ∪ targetSide) := by
    have hAbsIn : IsTriangleDecomposition
        (absorberGraph ⊔ sourceRoot) absorberIn := by
      rw [← hAbsGraph]
      exact habs.in_decomposition
    exact hAbsIn.union hTargetDec hInDisj
  refine ⟨hOutDec.isPackingOn, hInDec.isPackingOn, ?_, ?_⟩
  · rw [hOutDec.coveredGraph_eq]
    exact hRootDisj
  · rw [hInDec.coveredGraph_eq, hOutDec.coveredGraph_eq]
    ac_rfl

end

end Erdos207
