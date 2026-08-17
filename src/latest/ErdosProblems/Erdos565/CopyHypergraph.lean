/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Formalization Project
-/
module

public import ErdosProblems.Erdos565.Graph
public import ErdosProblems.Erdos565.Hypergraph

/-!
# Hypergraphs of induced graph copies

This file packages the copy hypergraph used in the proof of Erdős Problem 565.  Its vertices are
the vertices of an ambient graph `G`.  A finite set `L` is a hyperedge precisely when the graph
induced by a designated subgraph `G'` on `L` is isomorphic to the target `F`, and all ambient edges
inside `L` already belong to `G'`.
-/

@[expose] public section

open scoped SimpleGraph

namespace Erdos565

/-- The vertex sets of copies of `F` that lie in `G'` and are induced in the ambient graph `G`.

The equality of induced graphs is essential: when `G'` is one color class of an edge-coloring of
`G`, it says that every ambient edge inside the copy has that color, while the isomorphism with
`G'[L]` also ensures that nonedges of `F` map to genuine nonedges of `G`.
-/
noncomputable def copyHypergraph {U V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph U) (G' G : SimpleGraph V) : Hypergraph V := by
  classical
  exact ((Finset.univ : Finset V).powerset).filter fun L ↦
    Nonempty (F ≃g G'.induce (↑L : Set V)) ∧
      G'.induce (↑L : Set V) = G.induce (↑L : Set V)

@[simp]
theorem mem_copyHypergraph {U V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph U) (G' G : SimpleGraph V) (L : Finset V) :
    L ∈ copyHypergraph F G' G ↔
      Nonempty (F ≃g G'.induce (↑L : Set V)) ∧
        G'.induce (↑L : Set V) = G.induce (↑L : Set V) := by
  classical
  simp [copyHypergraph]

/-- Every edge of the copy hypergraph has the target order. -/
theorem card_eq_of_mem_copyHypergraph {U V : Type*} [Fintype U] [Fintype V]
    [DecidableEq V] (F : SimpleGraph U) (G' G : SimpleGraph V) {L : Finset V}
    (hL : L ∈ copyHypergraph F G' G) : L.card = Fintype.card U := by
  obtain ⟨e⟩ := (mem_copyHypergraph F G' G L).mp hL |>.1
  have hcard := Fintype.card_congr e.toEquiv
  rw [← Fintype.card_coe L]
  simpa only [Finset.coe_sort_coe] using hcard.symm

/-- The copy hypergraph is uniform, with rank equal to the number of vertices of the target. -/
theorem copyHypergraph_isUniform {U V : Type*} [Fintype U] [Fintype V]
    [DecidableEq V] (F : SimpleGraph U) (G' G : SimpleGraph V) :
    Hypergraph.IsUniform (copyHypergraph F G' G) (Fintype.card U) := by
  intro L hL
  exact card_eq_of_mem_copyHypergraph F G' G hL

/-- Restricting a color class to `S` gives the whole ambient induced graph exactly when every
ambient edge with both endpoints in `S` has the chosen color. -/
theorem labelGraph_induce_eq_induce_iff {V K : Type*} {G : SimpleGraph V}
    (coloring : G.EdgeLabeling K) (color : K) (S : Set V) :
    (coloring.labelGraph color).induce S = G.induce S ↔
      ∀ x ∈ S, ∀ y ∈ S, ∀ hxy : G.Adj x y,
        coloring.get x y hxy = color := by
  constructor
  · intro h x hx y hy hxy
    have hcolorAdj : (coloring.labelGraph color).Adj x y := by
      have hxy' : (G.induce S).Adj ⟨x, hx⟩ ⟨y, hy⟩ := hxy
      rw [← h] at hxy'
      exact hxy'
    obtain ⟨_, hc⟩ :=
      (SimpleGraph.EdgeLabeling.labelGraph_adj (C := coloring) (k := color) x y).mp hcolorAdj
    exact hc
  · intro h
    apply SimpleGraph.ext
    funext x y
    apply propext
    rcases x with ⟨x, hx⟩
    rcases y with ⟨y, hy⟩
    change (coloring.labelGraph color).Adj x y ↔ G.Adj x y
    constructor
    · intro hxy
      exact SimpleGraph.EdgeLabeling.labelGraph_le coloring (k := color) hxy
    · intro hxy
      exact (SimpleGraph.EdgeLabeling.labelGraph_adj (C := coloring) (k := color) x y).mpr
        ⟨hxy, h x hx y hy hxy⟩

/-- Membership in a color-class copy hypergraph, with the image of the witnessing embedding
recorded exactly.  This range-sensitive form is the convenient interface for restriction and
relabeling arguments. -/
theorem mem_copyHypergraph_labelGraph_iff {U V K : Type*}
    [Fintype U] [Fintype V] [DecidableEq V]
    (F : SimpleGraph U) (G : SimpleGraph V) (coloring : G.EdgeLabeling K)
    (color : K) (L : Finset V) :
    L ∈ copyHypergraph F (coloring.labelGraph color) G ↔
      ∃ f : F ↪g G, Finset.univ.map f.toEmbedding = L ∧
        ∀ e : F.edgeSet, coloring (f.mapEdgeSet e) = color := by
  classical
  constructor
  · intro hL
    obtain ⟨⟨e⟩, heq⟩ :=
      (mem_copyHypergraph F (coloring.labelGraph color) G L).mp hL
    have eG : F ≃g G.induce (↑L : Set V) := by
      rw [← heq]
      exact e
    let f : F ↪g G := (SimpleGraph.Embedding.induce (↑L : Set V)).comp eG.toEmbedding
    have hRange : Finset.univ.map f.toEmbedding = L := by
      apply Finset.ext
      intro v
      constructor
      · intro hv
        obtain ⟨x, _, hx⟩ := Finset.mem_map.mp hv
        rw [← hx]
        exact (eG x).property
      · intro hv
        obtain ⟨x, hx⟩ := eG.surjective ⟨v, hv⟩
        apply Finset.mem_map.mpr
        refine ⟨x, Finset.mem_univ x, ?_⟩
        exact congrArg Subtype.val hx
    refine ⟨f, hRange, ?_⟩
    have hcolor :=
      (labelGraph_induce_eq_induce_iff coloring color (↑L : Set V)).mp heq
    rintro ⟨edge, hedge⟩
    induction edge using Sym2.inductionOn with
    | _ x y =>
      change coloring.get (f x) (f y) (f.toHom.map_adj hedge) = color
      exact hcolor (f x) (eG x).property (f y) (eG y).property (f.toHom.map_adj hedge)
  · rintro ⟨f, hRange, hf⟩
    have hLset : (↑L : Set V) = Set.range f := by
      rw [← hRange]
      simp [Finset.coe_map]
    have heq : (coloring.labelGraph color).induce (↑L : Set V) =
        G.induce (↑L : Set V) := by
      apply (labelGraph_induce_eq_induce_iff coloring color (↑L : Set V)).mpr
      intro x hx y hy hxy
      rw [hLset] at hx hy
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      have hab : F.Adj a b := f.map_adj_iff.mp hxy
      have hfab := hf ⟨s(a, b), hab⟩
      change coloring.get (f a) (f b) (f.toHom.map_adj hab) = color at hfab
      exact hfab
    refine (mem_copyHypergraph F (coloring.labelGraph color) G L).mpr ⟨?_, heq⟩
    have eG : F ≃g G.induce (↑L : Set V) := by
      rw [hLset]
      exact f.isoInduceRange
    rw [heq]
    exact ⟨eG⟩

/-- Copy hypergraphs commute with restricting the host to a finite induced vertex set.  The
left-hand side lives on the subtype `W`; mapping by subtype coercion identifies it with precisely
the edges of the ambient copy hypergraph that are contained in `W`. -/
theorem map_copyHypergraph_pullback_induce_eq_restrict {U V K : Type*}
    [Fintype U] [Fintype V] [DecidableEq V]
    (F : SimpleGraph U) (G : SimpleGraph V) (coloring : G.EdgeLabeling K)
    (color : K) (W : Finset V) :
    (copyHypergraph F
        ((coloring.pullback
          (SimpleGraph.Embedding.induce (G := G) (↑W : Set V)).toHom).labelGraph color)
        (G.induce (↑W : Set V))).map (fun x : (↑W : Set V) ↦ x.1) =
      (copyHypergraph F (coloring.labelGraph color) G).restrict W := by
  classical
  let j : G.induce (↑W : Set V) ↪g G :=
    SimpleGraph.Embedding.induce (G := G) (↑W : Set V)
  ext L
  constructor
  · intro hL
    obtain ⟨T, hT, rfl⟩ := Hypergraph.mem_map.mp hL
    obtain ⟨f, hfRange, hfMono⟩ :=
      (mem_copyHypergraph_labelGraph_iff F (G.induce (↑W : Set V))
        (coloring.pullback j.toHom) color T).mp hT
    let fg : F ↪g G := j.comp f
    have hfgRange : Finset.univ.map fg.toEmbedding =
        T.image (fun x : (↑W : Set V) ↦ x.1) := by
      rw [← hfRange]
      simp only [Finset.map_eq_image, Finset.image_image]
      apply Finset.image_congr
      intro x _
      rfl
    have hfgMono : ∀ e : F.edgeSet, coloring (fg.mapEdgeSet e) = color := by
      intro e
      have hmap : fg.mapEdgeSet e = j.toHom.mapEdgeSet (f.mapEdgeSet e) := by
        apply Subtype.ext
        simp only [SimpleGraph.Embedding.mapEdgeSet_apply, SimpleGraph.Hom.mapEdgeSet]
        rw [Sym2.map_map]
        rfl
      calc
        coloring (fg.mapEdgeSet e) =
            coloring (j.toHom.mapEdgeSet (f.mapEdgeSet e)) := congrArg coloring hmap
        _ = color := hfMono e
    apply Hypergraph.mem_restrict.mpr
    refine ⟨(mem_copyHypergraph_labelGraph_iff F G coloring color _).mpr
      ⟨fg, hfgRange, hfgMono⟩, ?_⟩
    intro v hv
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hv
    exact x.property
  · intro hL
    obtain ⟨hcopy, hLW⟩ := Hypergraph.mem_restrict.mp hL
    obtain ⟨f, hfRange, hfMono⟩ :=
      (mem_copyHypergraph_labelGraph_iff F G coloring color L).mp hcopy
    have hfW : ∀ x : U, f x ∈ W := by
      intro x
      apply hLW
      rw [← hfRange]
      exact Finset.mem_map.mpr ⟨x, Finset.mem_univ x, rfl⟩
    let fW : F ↪g G.induce (↑W : Set V) :=
      { toFun := fun x ↦ ⟨f x, hfW x⟩
        inj' := fun _ _ h ↦ f.injective (congrArg Subtype.val h)
        map_rel_iff' := by
          intro x y
          exact f.map_adj_iff }
    have hfWMono : ∀ e : F.edgeSet,
        (coloring.pullback j.toHom) (fW.mapEdgeSet e) = color := by
      intro e
      have hmap : j.toHom.mapEdgeSet (fW.mapEdgeSet e) = f.mapEdgeSet e := by
        apply Subtype.ext
        simp only [SimpleGraph.Embedding.mapEdgeSet_apply, SimpleGraph.Hom.mapEdgeSet]
        rw [Sym2.map_map]
        rfl
      change coloring (j.toHom.mapEdgeSet (fW.mapEdgeSet e)) = color
      rw [hmap]
      exact hfMono e
    let T : Finset (↑W : Set V) := Finset.univ.map fW.toEmbedding
    have hT : T ∈ copyHypergraph F
        ((coloring.pullback j.toHom).labelGraph color) (G.induce (↑W : Set V)) :=
      (mem_copyHypergraph_labelGraph_iff F (G.induce (↑W : Set V))
        (coloring.pullback j.toHom) color T).mpr ⟨fW, rfl, hfWMono⟩
    apply Hypergraph.mem_map.mpr
    refine ⟨T, hT, ?_⟩
    rw [← hfRange]
    simp only [T, Finset.map_eq_image, Finset.image_image]
    apply Finset.image_congr
    intro x _
    rfl

/-- The restriction/relabeling identity for an arbitrary finite induced graph embedding.  The
finite-set equality `range_e` records that the image of `e` is exactly the ambient vertex set
`W`; no particular subtype presentation of that image is required. -/
theorem map_copyHypergraph_pullback_embedding_eq_restrict
    {U X V KColor : Type*} [Fintype U] [Fintype X] [Fintype V]
    [DecidableEq X] [DecidableEq V]
    (F : SimpleGraph U) (K : SimpleGraph X) (G : SimpleGraph V)
    (coloring : G.EdgeLabeling KColor) (color : KColor)
    (e : K ↪g G) (W : Finset V)
    (range_e : Finset.univ.map e.toEmbedding = W) :
    (copyHypergraph F ((coloring.pullback e.toHom).labelGraph color) K).map
        (fun x ↦ e x) =
      (copyHypergraph F (coloring.labelGraph color) G).restrict W := by
  classical
  ext L
  constructor
  · intro hL
    obtain ⟨T, hT, rfl⟩ := Hypergraph.mem_map.mp hL
    obtain ⟨f, hfRange, hfMono⟩ :=
      (mem_copyHypergraph_labelGraph_iff F K (coloring.pullback e.toHom) color T).mp hT
    let ef : F ↪g G := e.comp f
    have hefRange : Finset.univ.map ef.toEmbedding = T.image (fun x ↦ e x) := by
      rw [← hfRange]
      simp only [Finset.map_eq_image, Finset.image_image]
      apply Finset.image_congr
      intro x _
      rfl
    have hefMono : ∀ a : F.edgeSet, coloring (ef.mapEdgeSet a) = color := by
      intro a
      have hmap : ef.mapEdgeSet a = e.toHom.mapEdgeSet (f.mapEdgeSet a) := by
        apply Subtype.ext
        simp only [SimpleGraph.Embedding.mapEdgeSet_apply, SimpleGraph.Hom.mapEdgeSet]
        rw [Sym2.map_map]
        rfl
      calc
        coloring (ef.mapEdgeSet a) =
            coloring (e.toHom.mapEdgeSet (f.mapEdgeSet a)) := congrArg coloring hmap
        _ = color := hfMono a
    apply Hypergraph.mem_restrict.mpr
    refine ⟨(mem_copyHypergraph_labelGraph_iff F G coloring color _).mpr
      ⟨ef, hefRange, hefMono⟩, ?_⟩
    intro v hv
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hv
    rw [← range_e]
    exact Finset.mem_map.mpr ⟨x, Finset.mem_univ x, rfl⟩
  · intro hL
    obtain ⟨hcopy, hLW⟩ := Hypergraph.mem_restrict.mp hL
    obtain ⟨f, hfRange, hfMono⟩ :=
      (mem_copyHypergraph_labelGraph_iff F G coloring color L).mp hcopy
    have hpre : ∀ a : U, ∃ x : X, e x = f a := by
      intro a
      have hfaL : f a ∈ L := by
        rw [← hfRange]
        exact Finset.mem_map.mpr ⟨a, Finset.mem_univ a, rfl⟩
      have hfaW := hLW hfaL
      rw [← range_e] at hfaW
      obtain ⟨x, _, hx⟩ := Finset.mem_map.mp hfaW
      exact ⟨x, hx⟩
    choose pre hpre_eq using hpre
    let fK : F ↪g K :=
      { toFun := pre
        inj' := by
          intro a b hab
          apply f.injective
          rw [← hpre_eq a, ← hpre_eq b, hab]
        map_rel_iff' := by
          intro a b
          calc
            K.Adj (pre a) (pre b) ↔ G.Adj (e (pre a)) (e (pre b)) := e.map_adj_iff.symm
            _ ↔ G.Adj (f a) (f b) := by rw [hpre_eq a, hpre_eq b]
            _ ↔ F.Adj a b := f.map_adj_iff }
    have hfKMono : ∀ a : F.edgeSet,
        (coloring.pullback e.toHom) (fK.mapEdgeSet a) = color := by
      intro a
      have hmap : e.toHom.mapEdgeSet (fK.mapEdgeSet a) = f.mapEdgeSet a := by
        apply Subtype.ext
        simp only [SimpleGraph.Embedding.mapEdgeSet_apply, SimpleGraph.Hom.mapEdgeSet]
        rw [Sym2.map_map]
        have hfun : (⇑e.toHom ∘ ⇑fK.toHom) = ⇑f.toHom := by
          funext x
          exact hpre_eq x
        rw [hfun]
      change coloring (e.toHom.mapEdgeSet (fK.mapEdgeSet a)) = color
      rw [hmap]
      exact hfMono a
    let T : Finset X := Finset.univ.map fK.toEmbedding
    have hT : T ∈ copyHypergraph F
        ((coloring.pullback e.toHom).labelGraph color) K :=
      (mem_copyHypergraph_labelGraph_iff F K (coloring.pullback e.toHom) color T).mpr
        ⟨fK, rfl, hfKMono⟩
    apply Hypergraph.mem_map.mpr
    refine ⟨T, hT, ?_⟩
    rw [← hfRange]
    simp only [T, Finset.map_eq_image, Finset.image_image]
    apply Finset.image_congr
    intro x _
    exact hpre_eq x

/-- A fixed color has a hyperedge in the copy hypergraph exactly when there is an induced
embedding of the target into the host whose target edges all have that color. -/
theorem copyHypergraph_nonempty_iff_isMonochromaticEmbedding {n m : ℕ}
    (F : SimpleGraph (Fin n)) (G : SimpleGraph (Fin m))
    (coloring : G.EdgeLabeling (Fin 2)) (color : Fin 2) :
    (copyHypergraph F (coloring.labelGraph color) G).Nonempty ↔
      ∃ f : F ↪g G, IsMonochromaticEmbedding F G coloring color f := by
  classical
  constructor
  · rintro ⟨L, hL⟩
    obtain ⟨⟨e⟩, heq⟩ := (mem_copyHypergraph F (coloring.labelGraph color) G L).mp hL
    have eG : F ≃g G.induce (↑L : Set (Fin m)) := by
      rw [← heq]
      exact e
    let f : F ↪g G := (SimpleGraph.Embedding.induce (↑L : Set (Fin m))).comp eG.toEmbedding
    refine ⟨f, ?_⟩
    have hcolor :=
      (labelGraph_induce_eq_induce_iff coloring color (↑L : Set (Fin m))).mp heq
    rintro ⟨edge, hedge⟩
    induction edge using Sym2.inductionOn with
    | _ x y =>
      change coloring.get (f x) (f y) (f.toHom.map_adj hedge) = color
      exact hcolor (f x) (eG x).property (f y) (eG y).property (f.toHom.map_adj hedge)
  · rintro ⟨f, hf⟩
    let L : Finset (Fin m) := Finset.univ.map f.toEmbedding
    have hLset : (↑L : Set (Fin m)) = Set.range f := by
      simp [L, Finset.coe_map]
    have heq : (coloring.labelGraph color).induce (↑L : Set (Fin m)) =
        G.induce (↑L : Set (Fin m)) := by
      apply (labelGraph_induce_eq_induce_iff coloring color (↑L : Set (Fin m))).mpr
      intro x hx y hy hxy
      rw [hLset] at hx hy
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      have hab : F.Adj a b := f.map_adj_iff.mp hxy
      have hfab := hf ⟨s(a, b), hab⟩
      change coloring.get (f a) (f b) (f.toHom.map_adj hab) = color at hfab
      exact hfab
    refine ⟨L, (mem_copyHypergraph F (coloring.labelGraph color) G L).mpr ⟨?_, heq⟩⟩
    have eG : F ≃g G.induce (↑L : Set (Fin m)) := by
      rw [hLset]
      exact f.isoInduceRange
    rw [heq]
    exact ⟨eG⟩

/-- The copy-hypergraph formulation is equivalent to the graph-theoretic definition of a
monochromatic induced copy. -/
theorem monochromaticInducedCopy_iff_exists_copyHypergraph_nonempty {n m : ℕ}
    (F : SimpleGraph (Fin n)) (G : SimpleGraph (Fin m))
    (coloring : G.EdgeLabeling (Fin 2)) :
    MonochromaticInducedCopy F G coloring ↔
      ∃ color : Fin 2, (copyHypergraph F (coloring.labelGraph color) G).Nonempty := by
  simp only [MonochromaticInducedCopy, copyHypergraph_nonempty_iff_isMonochromaticEmbedding]

end Erdos565
