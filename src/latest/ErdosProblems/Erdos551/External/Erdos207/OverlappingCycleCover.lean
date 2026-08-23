/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos551.External.Erdos207.GraphTransformer
import ErdosProblems.Erdos551.External.Erdos207.CycleCoverBank

/-!
# Cycle-cover absorbers with overlapping roots

KSSS Definition 4.4 allows the cycles in a grouped root graph to share
vertices, although their edges remain distinct.  Such a root is an
edge-bijective quotient of the corresponding vertex-disjoint template.  This
module composes the explicit template absorbers with the edge-bijective
transformer, and then tags all non-root vertices by the bank copy.
-/

namespace Erdos207

open Finset

noncomputable section

def c4c5TemplateEdges : Finset (Sym2 (Fin 9)) :=
  {s(0, 1), s(1, 2), s(2, 3), s(0, 3),
   s(4, 5), s(5, 6), s(6, 7), s(7, 8), s(4, 8)}

def c4c5TemplateGraph : SimpleGraph (Fin 9) :=
  SimpleGraph.fromEdgeSet (c4c5TemplateEdges : Set (Sym2 (Fin 9)))

def threeC4TemplateEdges : Finset (Sym2 (Fin 12)) :=
  {s(0, 1), s(1, 2), s(2, 3), s(0, 3),
   s(4, 5), s(5, 6), s(6, 7), s(4, 7),
   s(8, 9), s(9, 10), s(10, 11), s(8, 11)}

def threeC4TemplateGraph : SimpleGraph (Fin 12) :=
  SimpleGraph.fromEdgeSet (threeC4TemplateEdges : Set (Sym2 (Fin 12)))

instance : DecidableRel c4c5TemplateGraph.Adj := by
  unfold c4c5TemplateGraph
  infer_instance

instance : DecidableRel threeC4TemplateGraph.Adj := by
  unfold threeC4TemplateGraph
  infer_instance

lemma c4c5Template_even_degree :
    ∀ x, Even (c4c5TemplateGraph.degree x) := by
  decide

lemma threeC4Template_even_degree :
    ∀ x, Even (threeC4TemplateGraph.degree x) := by
  decide

/-- A vertex map which neither collapses nor identifies two template edges.
It may identify nonadjacent vertices, exactly as overlapping cycles require. -/
def EdgeFaithfulMap {V Y : Type*} (G : SimpleGraph V) (f : V → Y) : Prop :=
  (∀ x y, G.Adj x y → f x ≠ f y) ∧
    Function.Injective (fun e : G.edgeSet ↦ e.1.map f)

/-- An injective vertex map is automatically edge-faithful.  Quotient maps
need the weaker notion above, but path-cover cycles will usually enter the
bank through this convenient constructor. -/
lemma edgeFaithfulMap_of_injective
    {V Y : Type*} {G : SimpleGraph V} {f : V → Y}
    (hf : Function.Injective f) : EdgeFaithfulMap G f := by
  constructor
  · intro x y hxy heq
    exact G.ne_of_adj hxy (hf heq)
  · intro e₁ e₂ heq
    apply Subtype.ext
    exact Sym2.map.injective hf heq

lemma edgeFaithfulMap_mappedEdge_mem
    {V Y : Type*} {G : SimpleGraph V} {f : V → Y}
    (hf : EdgeFaithfulMap G f) (e : G.edgeSet) :
    e.1.map f ∈ (G.map f).edgeSet := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | h x y =>
      change G.Adj x y at he
      change (G.map f).Adj (f x) (f y)
      exact SimpleGraph.map_adj_apply' he (hf.1 x y he)

/-- Edge-faithful realizations glue over an edge-disjoint supremum.  This is
the semantic tool used to combine three realized four-cycles, or one realized
four-cycle and one realized five-cycle, into a bank root. -/
lemma edgeFaithfulMap_sup
    {V Y : Type*} {G H : SimpleGraph V} {f : V → Y}
    (hG : EdgeFaithfulMap G f) (hH : EdgeFaithfulMap H f)
    (hdisjoint : Disjoint (G.map f) (H.map f)) :
    EdgeFaithfulMap (G ⊔ H) f := by
  constructor
  · intro x y hxy
    rw [SimpleGraph.sup_adj] at hxy
    exact hxy.elim (hG.1 x y) (hH.1 x y)
  · intro e₁ e₂ heq
    have he₁ : e₁.1 ∈ G.edgeSet ∨ e₁.1 ∈ H.edgeSet := by
      simpa only [SimpleGraph.edgeSet_sup, Set.mem_union] using e₁.2
    have he₂ : e₂.1 ∈ G.edgeSet ∨ e₂.1 ∈ H.edgeSet := by
      simpa only [SimpleGraph.edgeSet_sup, Set.mem_union] using e₂.2
    have heq' : Sym2.map f e₁.1 = Sym2.map f e₂.1 := heq
    rcases he₁ with he₁G | he₁H <;> rcases he₂ with he₂G | he₂H
    · let a : G.edgeSet := ⟨e₁.1, he₁G⟩
      let b : G.edgeSet := ⟨e₂.1, he₂G⟩
      have hab : a = b := hG.2 heq'
      have habval : (a : Sym2 V) = b :=
        congrArg (fun z : G.edgeSet => z.1) hab
      exact Subtype.ext habval
    · have hm₁ := edgeFaithfulMap_mappedEdge_mem hG ⟨e₁.1, he₁G⟩
      have hm₂ := edgeFaithfulMap_mappedEdge_mem hH ⟨e₂.1, he₂H⟩
      change Sym2.map f e₂.1 ∈ (H.map f).edgeSet at hm₂
      rw [← heq'] at hm₂
      exact (Set.disjoint_left.mp
        (SimpleGraph.disjoint_edgeSet.mpr hdisjoint) hm₁ hm₂).elim
    · have hm₁ := edgeFaithfulMap_mappedEdge_mem hH ⟨e₁.1, he₁H⟩
      have hm₂ := edgeFaithfulMap_mappedEdge_mem hG ⟨e₂.1, he₂G⟩
      change Sym2.map f e₁.1 ∈ (H.map f).edgeSet at hm₁
      rw [heq'] at hm₁
      exact (Set.disjoint_left.mp
        (SimpleGraph.disjoint_edgeSet.mpr hdisjoint) hm₂ hm₁).elim
    · let a : H.edgeSet := ⟨e₁.1, he₁H⟩
      let b : H.edgeSet := ⟨e₂.1, he₂H⟩
      have hab : a = b := hH.2 heq'
      have habval : (a : Sym2 V) = b :=
        congrArg (fun z : H.edgeSet => z.1) hab
      exact Subtype.ext habval

/-- Transport edge-faithfulness from a graph to its image under a vertex
embedding.  The ambient map only has to agree with the original realization
on the embedded source vertices. -/
lemma edgeFaithfulMap_map_embedding
    {V W Y : Type*} (G : SimpleGraph V) (q : V ↪ W)
    (F : W → Y) (f : V → Y)
    (hF : ∀ v, F (q v) = f v) (hf : EdgeFaithfulMap G f) :
    EdgeFaithfulMap (G.map q) F := by
  constructor
  · intro x y hxy hEq
    rw [SimpleGraph.map_adj] at hxy
    obtain ⟨a, b, hab, rfl, rfl⟩ := hxy
    apply hf.1 a b hab
    rw [← hF a, ← hF b]
    exact hEq
  · intro e₁ e₂ heq
    have he₁ : e₁.1 ∈ q.sym2Map '' G.edgeSet := by
      simpa only [SimpleGraph.edgeSet_map] using e₁.2
    have he₂ : e₂.1 ∈ q.sym2Map '' G.edgeSet := by
      simpa only [SimpleGraph.edgeSet_map] using e₂.2
    obtain ⟨a₁, ha₁, ha₁e⟩ := he₁
    obtain ⟨a₂, ha₂, ha₂e⟩ := he₂
    let a₁' : G.edgeSet := ⟨a₁, ha₁⟩
    let a₂' : G.edgeSet := ⟨a₂, ha₂⟩
    have hfun : F ∘ q = f := funext hF
    have hmap₁ : Sym2.map F e₁.1 = Sym2.map f a₁ := by
      rw [← ha₁e]
      change Sym2.map F (Sym2.map q a₁) = Sym2.map f a₁
      rw [Sym2.map_map, hfun]
    have hmap₂ : Sym2.map F e₂.1 = Sym2.map f a₂ := by
      rw [← ha₂e]
      change Sym2.map F (Sym2.map q a₂) = Sym2.map f a₂
      rw [Sym2.map_map, hfun]
    have haeq : a₁' = a₂' := by
      apply hf.2
      change Sym2.map f a₁ = Sym2.map f a₂
      rw [← hmap₁, ← hmap₂]
      exact heq
    apply Subtype.ext
    rw [← ha₁e, ← ha₂e]
    exact congrArg (fun z : G.edgeSet => z.1.map q)
      haeq

lemma SimpleGraph.map_sup_function
    {V Y : Type*} (G H : SimpleGraph V) (f : V → Y) :
    (G ⊔ H).map f = G.map f ⊔ H.map f := by
  ext x y
  simp only [SimpleGraph.map_adj', SimpleGraph.sup_adj]
  aesop

abbrev C4C5QuotientMap (Y : Type*) :=
  {f : Fin 9 → Y // EdgeFaithfulMap c4c5TemplateGraph f}

abbrev ThreeC4QuotientMap (Y : Type*) :=
  {f : Fin 12 → Y // EdgeFaithfulMap threeC4TemplateGraph f}

noncomputable instance c4c5QuotientMapFintype
    {Y : Type*} [Fintype Y] : Fintype (C4C5QuotientMap Y) :=
  Fintype.ofFinite _

noncomputable instance threeC4QuotientMapFintype
    {Y : Type*} [Fintype Y] : Fintype (ThreeC4QuotientMap Y) :=
  Fintype.ofFinite _

/-- An edge-faithful quotient map induces an edge-bijective homomorphism to
the graph-theoretic image. -/
def edgeFaithfulMap_edgeBijectiveHom
    {V Y : Type*} [DecidableEq V] [DecidableEq Y]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → Y)
    (hf : EdgeFaithfulMap G f) : EdgeBijectiveHom G (G.map f) := by
  let hom : G →g G.map f :=
    SimpleGraph.Hom.map f G (fun {_ _} h ↦ hf.1 _ _ h)
  refine ⟨hom, ?_⟩
  constructor
  · intro e₁ e₂ heq
    apply hf.2
    change Sym2.map f e₁.1 = Sym2.map f e₂.1
    exact congrArg Subtype.val heq
  · intro q
    rcases q with ⟨q, hq⟩
    induction q using Sym2.ind with
    | h y z =>
        rw [SimpleGraph.mem_edgeSet, SimpleGraph.map_adj'] at hq
        obtain ⟨hyz, x, w, hxw, hxy, hwz⟩ := hq
        subst y
        subst z
        let e : G.edgeSet := ⟨s(x, w), hxw⟩
        refine ⟨e, ?_⟩
        apply Subtype.ext
        change Sym2.map f e.1 = s(f x, f w)
        simp [e]

def c4c5RootEmbedding : Fin 9 ↪ Fin 15 :=
  Function.Embedding.inl.trans
    (finSumFinEquiv (m := 9) (n := 6)).toEmbedding

def threeC4RootEmbedding : Fin 12 ↪ Fin 18 :=
  Function.Embedding.inl.trans
    (finSumFinEquiv (m := 12) (n := 6)).toEmbedding

lemma c4c5RootGraph_eq_template_map :
    c4c5RootGraph = c4c5TemplateGraph.map c4c5RootEmbedding := by
  ext u v
  simp only [c4c5RootGraph, c4c5TemplateGraph,
    SimpleGraph.fromEdgeSet_adj, SimpleGraph.map_adj]
  fin_cases u <;> fin_cases v <;> decide

lemma threeC4RootGraph_eq_template_map :
    threeC4RootGraph = threeC4TemplateGraph.map threeC4RootEmbedding := by
  ext u v
  simp only [threeC4RootGraph, threeC4TemplateGraph,
    SimpleGraph.fromEdgeSet_adj, SimpleGraph.map_adj]
  fin_cases u <;> fin_cases v <;> decide

abbrev C4C5LocalVertex (Y : Type*) :=
  TransformerVertex c4c5TemplateGraph Y ⊕ Fin 6

def c4c5LocalTransformerEmbedding {Y : Type*} :
    TransformerVertex c4c5TemplateGraph Y ↪ C4C5LocalVertex Y :=
  Function.Embedding.inl

def c4c5LocalAbsorberEmbedding {Y : Type*} :
    Fin 15 ↪ C4C5LocalVertex Y :=
  (finSumFinEquiv (m := 9) (n := 6)).symm.toEmbedding |>.trans <|
    Function.Embedding.sumMap
      (transformerSourceEmbedding c4c5TemplateGraph)
      (Function.Embedding.refl (Fin 6))

lemma c4c5Local_sourceRoot_eq {Y : Type*} :
    c4c5RootGraph.map (c4c5LocalAbsorberEmbedding (Y := Y)) =
      (transformerSourceRoot (W := Y) c4c5TemplateGraph).map
        c4c5LocalTransformerEmbedding := by
  rw [c4c5RootGraph_eq_template_map, SimpleGraph.map_map,
    transformerSourceRoot, SimpleGraph.map_map]
  congr 1
  funext x
  simp [c4c5RootEmbedding, c4c5LocalAbsorberEmbedding,
    c4c5LocalTransformerEmbedding, transformerSourceEmbedding]

def c4c5QuotientHom {Y : Type*} [DecidableEq Y]
    (f : C4C5QuotientMap Y) :
    EdgeBijectiveHom c4c5TemplateGraph (c4c5TemplateGraph.map f.1) :=
  edgeFaithfulMap_edgeBijectiveHom c4c5TemplateGraph f.1 f.2

def c4c5LocalSourceRoot {Y : Type*} [DecidableEq Y] :
    SimpleGraph (C4C5LocalVertex Y) :=
  (transformerSourceRoot (W := Y) c4c5TemplateGraph).map
    c4c5LocalTransformerEmbedding

def c4c5LocalTargetRoot {Y : Type*} [DecidableEq Y]
    (f : C4C5QuotientMap Y) : SimpleGraph (C4C5LocalVertex Y) :=
  (transformerTargetRoot c4c5TemplateGraph
    (c4c5TemplateGraph.map f.1)).map c4c5LocalTransformerEmbedding

def c4c5LocalAuxiliary {Y : Type*} [Fintype Y] [DecidableEq Y]
    (f : C4C5QuotientMap Y) : SimpleGraph (C4C5LocalVertex Y) :=
  (transformerGraph (c4c5QuotientHom f) c4c5Template_even_degree).map
    c4c5LocalTransformerEmbedding

def c4c5LocalSourceSide {Y : Type*} [Fintype Y] [DecidableEq Y]
    (f : C4C5QuotientMap Y) : TripleSystemOn (C4C5LocalVertex Y) :=
  mapTripleSystem c4c5LocalTransformerEmbedding
    (transformerSourceSide (c4c5QuotientHom f) c4c5Template_even_degree)

def c4c5LocalTargetSide {Y : Type*} [Fintype Y] [DecidableEq Y]
    (f : C4C5QuotientMap Y) : TripleSystemOn (C4C5LocalVertex Y) :=
  mapTripleSystem c4c5LocalTransformerEmbedding
    (transformerTargetSide (c4c5QuotientHom f) c4c5Template_even_degree)

def c4c5LocalAbsorberOut {Y : Type*} [DecidableEq Y] :
    TripleSystemOn (C4C5LocalVertex Y) :=
  mapTripleSystem c4c5LocalAbsorberEmbedding c4c5Out

def c4c5LocalAbsorberIn {Y : Type*} [DecidableEq Y] :
    TripleSystemOn (C4C5LocalVertex Y) :=
  mapTripleSystem c4c5LocalAbsorberEmbedding c4c5In

def c4c5LocalOut {Y : Type*} [Fintype Y] [DecidableEq Y]
    (f : C4C5QuotientMap Y) : TripleSystemOn (C4C5LocalVertex Y) :=
  c4c5LocalAbsorberOut ∪ c4c5LocalSourceSide f

def c4c5LocalIn {Y : Type*} [Fintype Y] [DecidableEq Y]
    (f : C4C5QuotientMap Y) : TripleSystemOn (C4C5LocalVertex Y) :=
  c4c5LocalAbsorberIn ∪ c4c5LocalTargetSide f

lemma transformerSourceRoot_disjoint_targetRoot
    {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) :
    Disjoint (transformerSourceRoot (W := W) G)
      (transformerTargetRoot G H) := by
  rw [← SimpleGraph.disjoint_edgeSet, Set.disjoint_left]
  intro e heSource heTarget
  induction e using Sym2.ind with
  | h u v =>
      rw [SimpleGraph.mem_edgeSet, transformerSourceRoot,
        SimpleGraph.map_adj] at heSource
      obtain ⟨x, y, hxy, rfl, rfl⟩ := heSource
      rw [SimpleGraph.mem_edgeSet, transformerTargetRoot,
        SimpleGraph.map_adj] at heTarget
      simpa [transformerSourceEmbedding, transformerTargetEmbedding] using heTarget

def IsTransformerNonTarget {V W : Type*} {G : SimpleGraph V} :
    TransformerVertex G W → Prop
  | .source _ => True
  | .target _ => False
  | .edge _ => True

lemma transformerSourceSide_edge_has_nonTarget
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    (phi : EdgeBijectiveHom G H) (heven : ∀ x, Even (G.degree x))
    {u v : TransformerVertex G W}
    (huv : (coveredGraph (transformerSourceSide phi heven)).Adj u v) :
    IsTransformerNonTarget u ∨ IsTransformerNonTarget v := by
  obtain ⟨T, hT, huT, hvT, huvne⟩ := huv
  rcases mem_union.mp hT with hEdge | hMatching
  · obtain ⟨e, rfl⟩ := mem_transformerSourceEdgeTriples_iff.mp hEdge
    cases u with
    | source x => exact Or.inl trivial
    | edge e' => exact Or.inl trivial
    | target y => exact (target_not_mem_sourceEdgeTriple e y huT).elim
  · obtain ⟨x, p, rfl⟩ :=
      mem_transformerTargetMatchingTriples_iff phi heven |>.mp hMatching
    cases u with
    | source x' => exact Or.inl trivial
    | edge e => exact Or.inl trivial
    | target y =>
        cases v with
        | source z => exact Or.inr trivial
        | edge e => exact Or.inr trivial
        | target z =>
            exfalso
            apply huvne
            have hy :=
              target_mem_targetMatchingTriple_iff phi heven x p y |>.mp huT
            have hz :=
              target_mem_targetMatchingTriple_iff phi heven x p z |>.mp hvT
            simpa [hy, hz]

/-- Every absorber-out edge uses one of the six private vertices, whereas a
graph mapped through the transformer embedding only uses transformer
vertices. -/
lemma c4c5LocalAbsorberOut_disjoint_leftMap
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (G : SimpleGraph (TransformerVertex c4c5TemplateGraph Y)) :
    Disjoint (coveredGraph (c4c5LocalAbsorberOut (Y := Y)))
      (G.map c4c5LocalTransformerEmbedding) := by
  rw [← SimpleGraph.disjoint_edgeSet, Set.disjoint_left]
  intro e heAbs heLeft
  induction e using Sym2.ind with
  | h u v =>
      change (coveredGraph (mapTripleSystem c4c5LocalAbsorberEmbedding
        c4c5Out)).Adj u v at heAbs
      rw [coveredGraph_mapTripleSystem, SimpleGraph.map_adj] at heAbs
      obtain ⟨a, b, hab, rfl, rfl⟩ := heAbs
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.map_adj] at heLeft
      obtain ⟨x, y, hxy, hx, hy⟩ := heLeft
      rcases c4c5Out_edge_has_private_source a b hab with
        ⟨k, hk⟩ | ⟨k, hk⟩
      · rw [← (finSumFinEquiv (m := 9) (n := 6)).apply_symm_apply a, hk] at hx
        simp [c4c5LocalAbsorberEmbedding,
          c4c5LocalTransformerEmbedding] at hx
      · rw [← (finSumFinEquiv (m := 9) (n := 6)).apply_symm_apply b, hk] at hy
        simp [c4c5LocalAbsorberEmbedding,
          c4c5LocalTransformerEmbedding] at hy

theorem c4c5Local_isExclusiveGraphAbsorber
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (f : C4C5QuotientMap Y) :
    IsExclusiveGraphAbsorberOn (c4c5LocalTargetRoot f)
      (c4c5LocalOut f) (c4c5LocalIn f) := by
  let sourceRoot := c4c5LocalSourceRoot (Y := Y)
  let targetRoot := c4c5LocalTargetRoot f
  let auxiliary := c4c5LocalAuxiliary f
  let absorberGraph := coveredGraph (c4c5LocalAbsorberOut (Y := Y))
  have habs : IsExclusiveGraphAbsorberOn sourceRoot
      (c4c5LocalAbsorberOut (Y := Y))
      (c4c5LocalAbsorberIn (Y := Y)) := by
    dsimp only [sourceRoot]
    unfold c4c5LocalSourceRoot
    rw [← c4c5Local_sourceRoot_eq]
    exact c4c5_isExclusiveGraphAbsorber.map
      (c4c5LocalAbsorberEmbedding (Y := Y))
  have htrans : IsGraphTransformerOn sourceRoot targetRoot auxiliary
      (c4c5LocalSourceSide f) (c4c5LocalTargetSide f) :=
    (edgeBijectiveHom_isGraphTransformer (c4c5QuotientHom f)
      c4c5Template_even_degree).map c4c5LocalTransformerEmbedding
  have hAbsLeft (G : SimpleGraph (TransformerVertex c4c5TemplateGraph Y)) :
      Disjoint absorberGraph (G.map c4c5LocalTransformerEmbedding) :=
    c4c5LocalAbsorberOut_disjoint_leftMap G
  have hSourceTarget : Disjoint sourceRoot targetRoot := by
    exact SimpleGraph.disjoint_map_embedding c4c5LocalTransformerEmbedding
      (transformerSourceRoot_disjoint_targetRoot c4c5TemplateGraph
        (c4c5TemplateGraph.map f.1))
  apply habs.compose_transformer htrans
      (absorberGraph := absorberGraph)
  · exact Disjoint.sup_right (hAbsLeft _) (hAbsLeft _)
  · apply Disjoint.sup_left
    · exact Disjoint.sup_right (hAbsLeft _) (hAbsLeft _)
    · exact Disjoint.sup_right htrans.2.2.1.symm hSourceTarget
  · rfl
  · apply Disjoint.sup_left
    · dsimp [targetRoot]
      exact hAbsLeft _
    · exact Disjoint.sup_left htrans.2.2.2.1 hSourceTarget

def IsC4C5LocalPrivate {Y : Type*} : C4C5LocalVertex Y → Prop
  | Sum.inl x => IsTransformerNonTarget x
  | Sum.inr _ => True

lemma c4c5LocalOut_edge_has_private
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (f : C4C5QuotientMap Y) {u v : C4C5LocalVertex Y}
    (huv : (coveredGraph (c4c5LocalOut f)).Adj u v) :
    IsC4C5LocalPrivate u ∨ IsC4C5LocalPrivate v := by
  obtain ⟨T, hT, huT, hvT, huvne⟩ := huv
  rcases mem_union.mp hT with hAbs | hSource
  · have hab : (coveredGraph (c4c5LocalAbsorberOut (Y := Y))).Adj u v :=
      ⟨T, hAbs, huT, hvT, huvne⟩
    change (coveredGraph (mapTripleSystem c4c5LocalAbsorberEmbedding
      c4c5Out)).Adj u v at hab
    rw [coveredGraph_mapTripleSystem, SimpleGraph.map_adj] at hab
    obtain ⟨a, b, hab, rfl, rfl⟩ := hab
    rcases c4c5Out_edge_has_private_source a b hab with
      ⟨k, hk⟩ | ⟨k, hk⟩
    · left
      rw [← (finSumFinEquiv (m := 9) (n := 6)).apply_symm_apply a, hk]
      simp [IsC4C5LocalPrivate, c4c5LocalAbsorberEmbedding]
    · right
      rw [← (finSumFinEquiv (m := 9) (n := 6)).apply_symm_apply b, hk]
      simp [IsC4C5LocalPrivate, c4c5LocalAbsorberEmbedding]
  · have hsource :
        (coveredGraph (c4c5LocalSourceSide f)).Adj u v :=
      ⟨T, hSource, huT, hvT, huvne⟩
    change (coveredGraph (mapTripleSystem c4c5LocalTransformerEmbedding
      (transformerSourceSide (c4c5QuotientHom f)
        c4c5Template_even_degree))).Adj u v at hsource
    rw [coveredGraph_mapTripleSystem, SimpleGraph.map_adj] at hsource
    obtain ⟨a, b, hab, rfl, rfl⟩ := hsource
    simpa [IsC4C5LocalPrivate, c4c5LocalTransformerEmbedding] using
      transformerSourceSide_edge_has_nonTarget
        (c4c5QuotientHom f) c4c5Template_even_degree hab

abbrev ThreeC4LocalVertex (Y : Type*) :=
  TransformerVertex threeC4TemplateGraph Y ⊕ Fin 6

def threeC4LocalTransformerEmbedding {Y : Type*} :
    TransformerVertex threeC4TemplateGraph Y ↪ ThreeC4LocalVertex Y :=
  Function.Embedding.inl

def threeC4LocalAbsorberEmbedding {Y : Type*} :
    Fin 18 ↪ ThreeC4LocalVertex Y :=
  (finSumFinEquiv (m := 12) (n := 6)).symm.toEmbedding |>.trans <|
    Function.Embedding.sumMap
      (transformerSourceEmbedding threeC4TemplateGraph)
      (Function.Embedding.refl (Fin 6))

lemma threeC4Local_sourceRoot_eq {Y : Type*} :
    threeC4RootGraph.map (threeC4LocalAbsorberEmbedding (Y := Y)) =
      (transformerSourceRoot (W := Y) threeC4TemplateGraph).map
        threeC4LocalTransformerEmbedding := by
  rw [threeC4RootGraph_eq_template_map, SimpleGraph.map_map,
    transformerSourceRoot, SimpleGraph.map_map]
  congr 1
  funext x
  simp [threeC4RootEmbedding, threeC4LocalAbsorberEmbedding,
    threeC4LocalTransformerEmbedding, transformerSourceEmbedding]

def threeC4QuotientHom {Y : Type*} [DecidableEq Y]
    (f : ThreeC4QuotientMap Y) :
    EdgeBijectiveHom threeC4TemplateGraph
      (threeC4TemplateGraph.map f.1) :=
  edgeFaithfulMap_edgeBijectiveHom threeC4TemplateGraph f.1 f.2

def threeC4LocalSourceRoot {Y : Type*} [DecidableEq Y] :
    SimpleGraph (ThreeC4LocalVertex Y) :=
  (transformerSourceRoot (W := Y) threeC4TemplateGraph).map
    threeC4LocalTransformerEmbedding

def threeC4LocalTargetRoot {Y : Type*} [DecidableEq Y]
    (f : ThreeC4QuotientMap Y) : SimpleGraph (ThreeC4LocalVertex Y) :=
  (transformerTargetRoot threeC4TemplateGraph
    (threeC4TemplateGraph.map f.1)).map threeC4LocalTransformerEmbedding

def threeC4LocalAuxiliary {Y : Type*} [Fintype Y] [DecidableEq Y]
    (f : ThreeC4QuotientMap Y) : SimpleGraph (ThreeC4LocalVertex Y) :=
  (transformerGraph (threeC4QuotientHom f) threeC4Template_even_degree).map
    threeC4LocalTransformerEmbedding

def threeC4LocalSourceSide {Y : Type*} [Fintype Y] [DecidableEq Y]
    (f : ThreeC4QuotientMap Y) : TripleSystemOn (ThreeC4LocalVertex Y) :=
  mapTripleSystem threeC4LocalTransformerEmbedding
    (transformerSourceSide (threeC4QuotientHom f)
      threeC4Template_even_degree)

def threeC4LocalTargetSide {Y : Type*} [Fintype Y] [DecidableEq Y]
    (f : ThreeC4QuotientMap Y) : TripleSystemOn (ThreeC4LocalVertex Y) :=
  mapTripleSystem threeC4LocalTransformerEmbedding
    (transformerTargetSide (threeC4QuotientHom f)
      threeC4Template_even_degree)

def threeC4LocalAbsorberOut {Y : Type*} [DecidableEq Y] :
    TripleSystemOn (ThreeC4LocalVertex Y) :=
  mapTripleSystem threeC4LocalAbsorberEmbedding threeC4Out

def threeC4LocalAbsorberIn {Y : Type*} [DecidableEq Y] :
    TripleSystemOn (ThreeC4LocalVertex Y) :=
  mapTripleSystem threeC4LocalAbsorberEmbedding threeC4In

def threeC4LocalOut {Y : Type*} [Fintype Y] [DecidableEq Y]
    (f : ThreeC4QuotientMap Y) : TripleSystemOn (ThreeC4LocalVertex Y) :=
  threeC4LocalAbsorberOut ∪ threeC4LocalSourceSide f

def threeC4LocalIn {Y : Type*} [Fintype Y] [DecidableEq Y]
    (f : ThreeC4QuotientMap Y) : TripleSystemOn (ThreeC4LocalVertex Y) :=
  threeC4LocalAbsorberIn ∪ threeC4LocalTargetSide f

lemma threeC4LocalAbsorberOut_disjoint_leftMap
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (G : SimpleGraph (TransformerVertex threeC4TemplateGraph Y)) :
    Disjoint (coveredGraph (threeC4LocalAbsorberOut (Y := Y)))
      (G.map threeC4LocalTransformerEmbedding) := by
  rw [← SimpleGraph.disjoint_edgeSet, Set.disjoint_left]
  intro e heAbs heLeft
  induction e using Sym2.ind with
  | h u v =>
      change (coveredGraph (mapTripleSystem threeC4LocalAbsorberEmbedding
        threeC4Out)).Adj u v at heAbs
      rw [coveredGraph_mapTripleSystem, SimpleGraph.map_adj] at heAbs
      obtain ⟨a, b, hab, rfl, rfl⟩ := heAbs
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.map_adj] at heLeft
      obtain ⟨x, y, hxy, hx, hy⟩ := heLeft
      rcases threeC4Out_edge_has_private_source a b hab with
        ⟨k, hk⟩ | ⟨k, hk⟩
      · rw [← (finSumFinEquiv (m := 12) (n := 6)).apply_symm_apply a, hk] at hx
        simp [threeC4LocalAbsorberEmbedding,
          threeC4LocalTransformerEmbedding] at hx
      · rw [← (finSumFinEquiv (m := 12) (n := 6)).apply_symm_apply b, hk] at hy
        simp [threeC4LocalAbsorberEmbedding,
          threeC4LocalTransformerEmbedding] at hy

theorem threeC4Local_isExclusiveGraphAbsorber
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (f : ThreeC4QuotientMap Y) :
    IsExclusiveGraphAbsorberOn (threeC4LocalTargetRoot f)
      (threeC4LocalOut f) (threeC4LocalIn f) := by
  let sourceRoot := threeC4LocalSourceRoot (Y := Y)
  let targetRoot := threeC4LocalTargetRoot f
  let auxiliary := threeC4LocalAuxiliary f
  let absorberGraph := coveredGraph (threeC4LocalAbsorberOut (Y := Y))
  have habs : IsExclusiveGraphAbsorberOn sourceRoot
      (threeC4LocalAbsorberOut (Y := Y))
      (threeC4LocalAbsorberIn (Y := Y)) := by
    dsimp only [sourceRoot]
    unfold threeC4LocalSourceRoot
    rw [← threeC4Local_sourceRoot_eq]
    exact threeC4_isExclusiveGraphAbsorber.map
      (threeC4LocalAbsorberEmbedding (Y := Y))
  have htrans : IsGraphTransformerOn sourceRoot targetRoot auxiliary
      (threeC4LocalSourceSide f) (threeC4LocalTargetSide f) :=
    (edgeBijectiveHom_isGraphTransformer (threeC4QuotientHom f)
      threeC4Template_even_degree).map threeC4LocalTransformerEmbedding
  have hAbsLeft
      (G : SimpleGraph (TransformerVertex threeC4TemplateGraph Y)) :
      Disjoint absorberGraph (G.map threeC4LocalTransformerEmbedding) :=
    threeC4LocalAbsorberOut_disjoint_leftMap G
  have hSourceTarget : Disjoint sourceRoot targetRoot := by
    exact SimpleGraph.disjoint_map_embedding threeC4LocalTransformerEmbedding
      (transformerSourceRoot_disjoint_targetRoot threeC4TemplateGraph
        (threeC4TemplateGraph.map f.1))
  apply habs.compose_transformer htrans
      (absorberGraph := absorberGraph)
  · exact Disjoint.sup_right (hAbsLeft _) (hAbsLeft _)
  · apply Disjoint.sup_left
    · exact Disjoint.sup_right (hAbsLeft _) (hAbsLeft _)
    · exact Disjoint.sup_right htrans.2.2.1.symm hSourceTarget
  · rfl
  · apply Disjoint.sup_left
    · dsimp [targetRoot]
      exact hAbsLeft _
    · exact Disjoint.sup_left htrans.2.2.2.1 hSourceTarget

def IsThreeC4LocalPrivate {Y : Type*} : ThreeC4LocalVertex Y → Prop
  | Sum.inl x => IsTransformerNonTarget x
  | Sum.inr _ => True

lemma threeC4LocalOut_edge_has_private
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (f : ThreeC4QuotientMap Y) {u v : ThreeC4LocalVertex Y}
    (huv : (coveredGraph (threeC4LocalOut f)).Adj u v) :
    IsThreeC4LocalPrivate u ∨ IsThreeC4LocalPrivate v := by
  obtain ⟨T, hT, huT, hvT, huvne⟩ := huv
  rcases mem_union.mp hT with hAbs | hSource
  · have hab : (coveredGraph (threeC4LocalAbsorberOut (Y := Y))).Adj u v :=
      ⟨T, hAbs, huT, hvT, huvne⟩
    change (coveredGraph (mapTripleSystem threeC4LocalAbsorberEmbedding
      threeC4Out)).Adj u v at hab
    rw [coveredGraph_mapTripleSystem, SimpleGraph.map_adj] at hab
    obtain ⟨a, b, hab, rfl, rfl⟩ := hab
    rcases threeC4Out_edge_has_private_source a b hab with
      ⟨k, hk⟩ | ⟨k, hk⟩
    · left
      rw [← (finSumFinEquiv (m := 12) (n := 6)).apply_symm_apply a, hk]
      simp [IsThreeC4LocalPrivate, threeC4LocalAbsorberEmbedding]
    · right
      rw [← (finSumFinEquiv (m := 12) (n := 6)).apply_symm_apply b, hk]
      simp [IsThreeC4LocalPrivate, threeC4LocalAbsorberEmbedding]
  · have hsource :
        (coveredGraph (threeC4LocalSourceSide f)).Adj u v :=
      ⟨T, hSource, huT, hvT, huvne⟩
    change (coveredGraph (mapTripleSystem threeC4LocalTransformerEmbedding
      (transformerSourceSide (threeC4QuotientHom f)
        threeC4Template_even_degree))).Adj u v at hsource
    rw [coveredGraph_mapTripleSystem, SimpleGraph.map_adj] at hsource
    obtain ⟨a, b, hab, rfl, rfl⟩ := hsource
    simpa [IsThreeC4LocalPrivate, threeC4LocalTransformerEmbedding] using
      transformerSourceSide_edge_has_nonTarget
        (threeC4QuotientHom f) threeC4Template_even_degree hab

end

end Erdos207
