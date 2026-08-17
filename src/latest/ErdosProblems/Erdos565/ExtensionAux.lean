/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Formalization Project
-/
module

public import ErdosProblems.Erdos565.CopyHypergraph
public import Mathlib.Data.Finset.Prod
public import Mathlib.Tactic

/-!
# The two-layer extension hypergraph

This file formalizes the deterministic gadget used in the extension lemma for
Erdős problem 565.  An old host vertex `u` has two auxiliary copies:

* `(u, 0)` records that the new host vertex is not adjacent to `u` in the
  ambient graph;
* `(u, 1)` records that it is adjacent to `u` in the chosen colour graph.

An auxiliary edge is attached to an *embedding* of the target with its
distinguished vertex deleted.  Keeping the embedding, rather than only its
image, matters when the deleted target has automorphisms which do not preserve
the neighbourhood of the distinguished vertex.
-/

@[expose] public section

open scoped SimpleGraph

namespace Erdos565

variable {A U : Type*} [Fintype A] [DecidableEq A]
  [Fintype U] [DecidableEq U]

/-- The vertices left after deleting `root` from a target graph. -/
abbrev DeletedVertices (root : A) := {x : A // x ≠ root}

/-- The target graph obtained by deleting its distinguished vertex. -/
abbrev deleteVertex (F : SimpleGraph A) (root : A) :
    SimpleGraph (DeletedVertices root) :=
  F.induce {x | x ≠ root}

/-- The two possible requirements placed on an old host vertex. -/
noncomputable def requiredBit (F : SimpleGraph A) (root x : A) : Fin 2 := by
  classical
  exact if F.Adj root x then 1 else 0

/-- The canonical injection from old host vertices into a host with one new
vertex.  The new vertex itself is `none`. -/
def oldVertex : U → Option U := some

/-- Extend an injection of the deleted target by sending the distinguished
target vertex to the new host vertex `none`. -/
def extensionVertexEmbedding (root : A) (e : DeletedVertices root ↪ U) :
    A ↪ Option U where
  toFun x := if hx : x = root then none else some (e ⟨x, hx⟩)
  inj' := by
    intro x y hxy
    by_cases hx : x = root
    · subst x
      by_cases hy : y = root
      · exact hy.symm
      · simp [hy] at hxy
    · by_cases hy : y = root
      · subst y
        simp [hx] at hxy
      · have he : e ⟨x, hx⟩ = e ⟨y, hy⟩ := by
          simpa [hx, hy] using hxy
        exact congrArg Subtype.val (e.injective he)

@[simp]
theorem extensionVertexEmbedding_root (root : A) (e : DeletedVertices root ↪ U) :
    extensionVertexEmbedding root e root = none := by
  simp [extensionVertexEmbedding]

@[simp]
theorem extensionVertexEmbedding_of_ne (root : A) (e : DeletedVertices root ↪ U)
    {x : A} (hx : x ≠ root) :
    extensionVertexEmbedding root e x = some (e ⟨x, hx⟩) := by
  simp [extensionVertexEmbedding, hx]

/-- The required pair attached to a vertex of the deleted target. -/
noncomputable def requiredPairEmbedding (F : SimpleGraph A) (root : A)
    (e : DeletedVertices root ↪ U) : DeletedVertices root ↪ U × Fin 2 where
  toFun x := (e x, requiredBit F root x)
  inj' := by
    intro x y hxy
    exact e.injective (congrArg Prod.fst hxy)

/-- The auxiliary edge corresponding to an embedded copy of the deleted
target. -/
noncomputable def extensionEdge (F : SimpleGraph A) (root : A)
    (e : DeletedVertices root ↪ U) : Finset (U × Fin 2) :=
  Finset.univ.map (requiredPairEmbedding F root e)

@[simp]
theorem mem_extensionEdge (F : SimpleGraph A) (root : A)
    (e : DeletedVertices root ↪ U) (p : U × Fin 2) :
    p ∈ extensionEdge F root e ↔
      ∃ x : DeletedVertices root,
        e x = p.1 ∧ requiredBit F root x = p.2 := by
  classical
  constructor
  · intro hp
    obtain ⟨x, -, hxp⟩ := Finset.mem_map.1 hp
    exact ⟨x, congrArg Prod.fst hxp, congrArg Prod.snd hxp⟩
  · rintro ⟨x, hx, hb⟩
    apply Finset.mem_map.2
    refine ⟨x, Finset.mem_univ _, ?_⟩
    exact Prod.ext hx hb

@[simp]
theorem card_extensionEdge (F : SimpleGraph A) (root : A)
    (e : DeletedVertices root ↪ U) :
    (extensionEdge F root e).card = Fintype.card (DeletedVertices root) := by
  simp [extensionEdge]

/-- Forget the layer of a set in the two-layer auxiliary vertex set. -/
def layerProjection (E : Finset (U × Fin 2)) : Finset U :=
  E.image Prod.fst

/-- The image of the embedded deleted target in the old host. -/
def embeddingImage (root : A) (e : DeletedVertices root ↪ U) : Finset U :=
  Finset.univ.map e

@[simp]
theorem layerProjection_extensionEdge (F : SimpleGraph A) (root : A)
    (e : DeletedVertices root ↪ U) :
    layerProjection (extensionEdge F root e) = embeddingImage root e := by
  ext u
  simp [layerProjection, extensionEdge, embeddingImage, requiredPairEmbedding]

/-- The graph induced by a one-new-vertex graph on its old vertices. -/
abbrev oldPart (G : SimpleGraph (Option U)) : SimpleGraph U :=
  G.comap some

/-- The subset of the two-layer vertex set exposed by a pair `G' ≤ G` of
graphs on the old host plus one new vertex. -/
noncomputable def extensionIota (G' G : SimpleGraph (Option U)) : Finset (U × Fin 2) := by
  classical
  exact Finset.univ.filter fun p ↦
    (p.2 = 0 ∧ ¬ G.Adj (some p.1) none) ∨
      (p.2 = 1 ∧ G'.Adj (some p.1) none)

@[simp]
theorem mem_extensionIota (G' G : SimpleGraph (Option U)) (u : U) (b : Fin 2) :
    (u, b) ∈ extensionIota G' G ↔
      (b = 0 ∧ ¬ G.Adj (some u) none) ∨
        (b = 1 ∧ G'.Adj (some u) none) := by
  simp [extensionIota]

@[simp]
theorem mem_extensionIota_zero (G' G : SimpleGraph (Option U)) (u : U) :
    (u, 0) ∈ extensionIota G' G ↔ ¬ G.Adj (some u) none := by
  simp [extensionIota]

@[simp]
theorem mem_extensionIota_one (G' G : SimpleGraph (Option U)) (u : U) :
    (u, 1) ∈ extensionIota G' G ↔ G'.Adj (some u) none := by
  simp [extensionIota]

/-- An embedded copy of the deleted target whose old edges lie in `G'`
projects to an edge of the ordinary copy hypergraph on the old host. -/
theorem embeddingImage_mem_copyHypergraph (F : SimpleGraph A) (root : A)
    (G' G : SimpleGraph (Option U)) (hG : G' ≤ G)
    (e : deleteVertex F root ↪g oldPart G)
    (hMono : ∀ {x y : DeletedVertices root},
      (deleteVertex F root).Adj x y → G'.Adj (some (e x)) (some (e y))) :
    embeddingImage root e.toEmbedding ∈
      copyHypergraph (deleteVertex F root) (oldPart G') (oldPart G) := by
  classical
  let L := embeddingImage root e.toEmbedding
  have hLset : (↑L : Set U) = Set.range e := by
    simp [L, embeddingImage, Finset.coe_map]
  have heq : (oldPart G').induce (↑L : Set U) =
      (oldPart G).induce (↑L : Set U) := by
    apply SimpleGraph.ext
    funext x y
    apply propext
    rcases x with ⟨u, hu⟩
    rcases y with ⟨w, hw⟩
    change (oldPart G').Adj u w ↔ (oldPart G).Adj u w
    constructor
    · intro huw
      exact hG huw
    · intro huw
      rw [hLset] at hu hw
      obtain ⟨x, rfl⟩ := hu
      obtain ⟨y, rfl⟩ := hw
      exact hMono (e.map_adj_iff.mp huw)
  apply (mem_copyHypergraph (deleteVertex F root) (oldPart G') (oldPart G) L).2
  refine ⟨?_, heq⟩
  have eG : deleteVertex F root ≃g (oldPart G).induce (↑L : Set U) := by
    rw [hLset]
    exact e.isoInduceRange
  rw [heq]
  exact ⟨eG⟩

/-- The finite auxiliary hypergraph.  Its edges retain every possible
embedding of a projected old copy, rather than choosing one representative
for each image. -/
noncomputable def extensionAuxHypergraph (F : SimpleGraph A) (root : A)
    (G' G : SimpleGraph (Option U)) : Finset (Finset (U × Fin 2)) := by
  classical
  exact (Finset.univ : Finset (Finset (U × Fin 2))).filter fun E ↦
    ∃ e : deleteVertex F root ↪g oldPart G,
      (∀ {x y : DeletedVertices root},
        (deleteVertex F root).Adj x y →
          G'.Adj (some (e x)) (some (e y))) ∧
        E = extensionEdge F root e.toEmbedding

@[simp]
theorem mem_extensionAuxHypergraph (F : SimpleGraph A) (root : A)
    (G' G : SimpleGraph (Option U)) (E : Finset (U × Fin 2)) :
    E ∈ extensionAuxHypergraph F root G' G ↔
      ∃ e : deleteVertex F root ↪g oldPart G,
        (∀ {x y : DeletedVertices root},
          (deleteVertex F root).Adj x y →
            G'.Adj (some (e x)) (some (e y))) ∧
          E = extensionEdge F root e.toEmbedding := by
  classical
  simp [extensionAuxHypergraph]

theorem extensionEdge_mem_extensionAuxHypergraph (F : SimpleGraph A) (root : A)
    (G' G : SimpleGraph (Option U))
    (e : deleteVertex F root ↪g oldPart G)
    (hMono : ∀ {x y : DeletedVertices root},
      (deleteVertex F root).Adj x y → G'.Adj (some (e x)) (some (e y))) :
    extensionEdge F root e.toEmbedding ∈ extensionAuxHypergraph F root G' G := by
  exact (mem_extensionAuxHypergraph F root G' G _).2 ⟨e, hMono, rfl⟩

/-- Every edge of the auxiliary hypergraph projects to an induced
monochromatic deleted-target copy. -/
theorem layerProjection_mem_copyHypergraph_of_mem_extensionAuxHypergraph
    (F : SimpleGraph A) (root : A) (G' G : SimpleGraph (Option U)) (hG : G' ≤ G)
    {E : Finset (U × Fin 2)} (hE : E ∈ extensionAuxHypergraph F root G' G) :
    layerProjection E ∈
      copyHypergraph (deleteVertex F root) (oldPart G') (oldPart G) := by
  obtain ⟨e, hMono, rfl⟩ :=
    (mem_extensionAuxHypergraph F root G' G E).1 hE
  rw [layerProjection_extensionEdge]
  exact embeddingImage_mem_copyHypergraph F root G' G hG e hMono

/-- The auxiliary hypergraph is uniform of the order of the deleted target. -/
theorem card_eq_of_mem_extensionAuxHypergraph
    (F : SimpleGraph A) (root : A) (G' G : SimpleGraph (Option U))
    {E : Finset (U × Fin 2)} (hE : E ∈ extensionAuxHypergraph F root G' G) :
    E.card = Fintype.card (DeletedVertices root) := by
  obtain ⟨e, _, rfl⟩ := (mem_extensionAuxHypergraph F root G' G E).1 hE
  exact card_extensionEdge F root e.toEmbedding

/-- The canonical extension map preserves and reflects all ambient adjacencies,
and sends every target edge to the chosen colour graph. -/
def IsInducedMonochromaticExtension (F : SimpleGraph A) (root : A)
    (G' G : SimpleGraph (Option U)) (e : DeletedVertices root ↪ U) : Prop :=
  (∀ x y, F.Adj x y ↔
      G.Adj (extensionVertexEmbedding root e x)
        (extensionVertexEmbedding root e y)) ∧
    ∀ {x y}, F.Adj x y →
      G'.Adj (extensionVertexEmbedding root e x)
        (extensionVertexEmbedding root e y)

/-- Turn the adjacency part of `IsInducedMonochromaticExtension` into the
corresponding graph embedding. -/
def inducedExtensionEmbedding (F : SimpleGraph A) (root : A)
    (G : SimpleGraph (Option U)) (e : DeletedVertices root ↪ U)
    (hAdj : ∀ x y, F.Adj x y ↔
      G.Adj (extensionVertexEmbedding root e x)
        (extensionVertexEmbedding root e y)) : F ↪g G where
  __ := extensionVertexEmbedding root e
  map_rel_iff' := (hAdj _ _).symm

/-- Membership of a required pair says exactly that the adjacency prescribed
by the target is realized at the new vertex, and that a prescribed edge lies
in the chosen colour graph. -/
theorem requiredPair_mem_iota_iff (F : SimpleGraph A) (root : A)
    (G' G : SimpleGraph (Option U)) (hG : G' ≤ G)
    (e : DeletedVertices root ↪ U) (x : DeletedVertices root) :
    (e x, requiredBit F root x) ∈ extensionIota G' G ↔
      (F.Adj root x ↔ G.Adj none (some (e x))) ∧
        (F.Adj root x → G'.Adj none (some (e x))) := by
  by_cases hx : F.Adj root x
  · rw [show requiredBit F root x = 1 by simp [requiredBit, hx],
      mem_extensionIota_one]
    simp only [hx, true_iff]
    constructor
    · intro h
      have h' : G'.Adj none (some (e x)) := by
        simpa [SimpleGraph.adj_comm] using h
      exact ⟨hG h', fun _ ↦ h'⟩
    · rintro ⟨_, h'⟩
      simpa [SimpleGraph.adj_comm] using h' trivial
  · simp [requiredBit, hx, SimpleGraph.adj_comm]

/-- The central deterministic equivalence of the extension construction.

The embedding `e` is an induced copy of the deleted target in the ambient
old-host graph `G.comap some`, and `hMono` says that its old edges already
belong to `G'`.  The auxiliary edge is exposed by `extensionIota G' G` exactly
when adjoining the new vertex gives an induced copy of all of `F`, with every
edge in `G'`.
-/
theorem extensionEdge_subset_iota_iff (F : SimpleGraph A) (root : A)
    (G' G : SimpleGraph (Option U)) (hG : G' ≤ G)
    (e : deleteVertex F root ↪g G.comap some)
    (hMono : ∀ {x y : DeletedVertices root},
      (deleteVertex F root).Adj x y → G'.Adj (some (e x)) (some (e y))) :
    extensionEdge F root e.toEmbedding ⊆ extensionIota G' G ↔
      IsInducedMonochromaticExtension F root G' G e.toEmbedding := by
  constructor
  · intro hsub
    have hnew (x : DeletedVertices root) :
        (F.Adj root x ↔ G.Adj none (some (e.toEmbedding x))) ∧
          (F.Adj root x → G'.Adj none (some (e.toEmbedding x))) := by
      have hm : (e.toEmbedding x, requiredBit F root x) ∈ extensionIota G' G := by
        apply hsub
        exact (mem_extensionEdge F root e.toEmbedding _).2 ⟨x, rfl, rfl⟩
      exact (requiredPair_mem_iota_iff F root G' G hG e.toEmbedding x).1 hm
    constructor
    · intro x y
      by_cases hx : x = root
      · subst x
        by_cases hy : y = root
        · subst y
          simp
        · simpa [extensionVertexEmbedding, hy] using (hnew ⟨y, hy⟩).1
      · by_cases hy : y = root
        · subst y
          simpa [extensionVertexEmbedding, hx, SimpleGraph.adj_comm] using
            (hnew ⟨x, hx⟩).1
        · have he : (deleteVertex F root).Adj ⟨x, hx⟩ ⟨y, hy⟩ ↔
              (G.comap some).Adj (e ⟨x, hx⟩) (e ⟨y, hy⟩) :=
            e.map_adj_iff.symm
          simpa [extensionVertexEmbedding, hx, hy] using he
    · intro x y hxy
      by_cases hx : x = root
      · subst x
        have hy : y ≠ root := by
          intro hy
          subst y
          exact F.loopless.irrefl root hxy
        simpa [extensionVertexEmbedding, hy] using (hnew ⟨y, hy⟩).2 hxy
      · by_cases hy : y = root
        · subst y
          have h := (hnew ⟨x, hx⟩).2 (by simpa [SimpleGraph.adj_comm] using hxy)
          simpa [extensionVertexEmbedding, hx, SimpleGraph.adj_comm] using h
        · simpa [extensionVertexEmbedding, hx, hy] using
            hMono (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) hxy
  · rintro ⟨hAdj, hMonoAll⟩ p hp
    obtain ⟨x, hx, hb⟩ := (mem_extensionEdge F root e.toEmbedding p).1 hp
    have hpEq : (e.toEmbedding x, requiredBit F root x) = p := Prod.ext hx hb
    rw [← hpEq]
    apply (requiredPair_mem_iota_iff F root G' G hG e.toEmbedding x).2
    constructor
    · simpa [extensionVertexEmbedding, x.property] using hAdj root x
    · intro hx
      simpa [extensionVertexEmbedding, x.property] using hMonoAll hx

/-- In embedding language, the right side of
`extensionEdge_subset_iota_iff` supplies the canonical induced embedding of
the full target and certifies that all of its edges lie in `G'`. -/
theorem extensionEdge_subset_iota_iff_exists_embedding (F : SimpleGraph A) (root : A)
    (G' G : SimpleGraph (Option U)) (hG : G' ≤ G)
    (e : deleteVertex F root ↪g G.comap some)
    (hMono : ∀ {x y : DeletedVertices root},
      (deleteVertex F root).Adj x y → G'.Adj (some (e x)) (some (e y))) :
    extensionEdge F root e.toEmbedding ⊆ extensionIota G' G ↔
      ∃ f : F ↪g G,
        (∀ x, f x = extensionVertexEmbedding root e.toEmbedding x) ∧
          ∀ {x y}, F.Adj x y → G'.Adj (f x) (f y) := by
  rw [extensionEdge_subset_iota_iff F root G' G hG e hMono]
  constructor
  · rintro ⟨hAdj, hAll⟩
    let f := inducedExtensionEmbedding F root G e.toEmbedding hAdj
    refine ⟨f, ?_, ?_⟩
    · intro x
      rfl
    · exact hAll
  · rintro ⟨f, hf, hAll⟩
    constructor
    · intro x y
      rw [← hf x, ← hf y]
      exact f.map_adj_iff.symm
    · intro x y hxy
      simpa [hf x, hf y] using hAll hxy

/-! ## Set-level bridges used by the extension lemma -/

/-- The vertex set of the image of a graph embedding. -/
noncomputable def graphEmbeddingImage {B C : Type*} [Fintype B] [DecidableEq C]
    {H : SimpleGraph B} {K : SimpleGraph C} (f : H ↪g K) : Finset C :=
  Finset.univ.map f.toEmbedding

theorem graphEmbeddingImage_mem_copyHypergraph
    {B C : Type*} [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (H : SimpleGraph B) (K' K : SimpleGraph C) (hK : K' ≤ K)
    (f : H ↪g K)
    (hMono : ∀ {x y : B}, H.Adj x y → K'.Adj (f x) (f y)) :
    graphEmbeddingImage f ∈ copyHypergraph H K' K := by
  classical
  let L := graphEmbeddingImage f
  have hLset : (↑L : Set C) = Set.range f := by
    simp [L, graphEmbeddingImage, Finset.coe_map]
  have heq : K'.induce (↑L : Set C) = K.induce (↑L : Set C) := by
    apply SimpleGraph.ext
    funext x y
    apply propext
    rcases x with ⟨u, hu⟩
    rcases y with ⟨w, hw⟩
    change K'.Adj u w ↔ K.Adj u w
    constructor
    · intro huw
      exact hK huw
    · intro huw
      rw [hLset] at hu hw
      obtain ⟨x, rfl⟩ := hu
      obtain ⟨y, rfl⟩ := hw
      exact hMono (f.map_adj_iff.mp huw)
  apply (mem_copyHypergraph H K' K L).2
  refine ⟨?_, heq⟩
  have eK : H ≃g K.induce (↑L : Set C) := by
    rw [hLset]
    exact f.isoInduceRange
  rw [heq]
  exact ⟨eK⟩

/-- The image of the canonical extension embedding is the old image together
with the new vertex. -/
theorem graphEmbeddingImage_inducedExtensionEmbedding
    (F : SimpleGraph A) (root : A) (G : SimpleGraph (Option U))
    (e : DeletedVertices root ↪ U)
    (hAdj : ∀ x y, F.Adj x y ↔
      G.Adj (extensionVertexEmbedding root e x)
        (extensionVertexEmbedding root e y)) :
    graphEmbeddingImage (inducedExtensionEmbedding F root G e hAdj) =
      insert none ((embeddingImage root e).image some) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨x, -, hxz⟩ := Finset.mem_map.1 hz
    rw [← hxz, Finset.mem_insert]
    change extensionVertexEmbedding root e x = none ∨
      extensionVertexEmbedding root e x ∈ (embeddingImage root e).image some
    by_cases hx : x = root
    · left
      subst x
      exact extensionVertexEmbedding_root root e
    · right
      rw [extensionVertexEmbedding_of_ne root e hx]
      simp [embeddingImage, hx]
  · intro hz
    rw [Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · apply Finset.mem_map.2
      exact ⟨root, Finset.mem_univ _, by simp [inducedExtensionEmbedding]⟩
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hz
      obtain ⟨x, -, rfl⟩ := Finset.mem_map.1 hu
      apply Finset.mem_map.2
      refine ⟨x, Finset.mem_univ _, ?_⟩
      simp [inducedExtensionEmbedding, extensionVertexEmbedding, x.property]

/-- Projecting an auxiliary edge directly to the one-new-vertex host agrees
with first forgetting its layer and then injecting old vertices by `some`. -/
theorem image_some_fst_eq_image_some_layerProjection (E : Finset (U × Fin 2)) :
    E.image (fun z ↦ some z.1) = (layerProjection E).image some := by
  rw [layerProjection, Finset.image_image]
  rfl

/-- An exposed auxiliary edge cones to a full induced monochromatic copy. -/
theorem cone_layerProjection_mem_copyHypergraph_of_subset_iota
    (F : SimpleGraph A) (root : A) (G' G : SimpleGraph (Option U)) (hG : G' ≤ G)
    {E : Finset (U × Fin 2)} (hE : E ∈ extensionAuxHypergraph F root G' G)
    (hEI : E ⊆ extensionIota G' G) :
    insert none ((layerProjection E).image some) ∈ copyHypergraph F G' G := by
  obtain ⟨e, hMono, rfl⟩ :=
    (mem_extensionAuxHypergraph F root G' G E).1 hE
  have hext :=
    (extensionEdge_subset_iota_iff F root G' G hG e hMono).1 hEI
  rcases hext with ⟨hAdj, hAll⟩
  let f := inducedExtensionEmbedding F root G e.toEmbedding hAdj
  have hcopy : graphEmbeddingImage f ∈ copyHypergraph F G' G :=
    graphEmbeddingImage_mem_copyHypergraph F G' G hG f hAll
  rw [show f = inducedExtensionEmbedding F root G e.toEmbedding hAdj from rfl,
    graphEmbeddingImage_inducedExtensionEmbedding] at hcopy
  simpa only [layerProjection_extensionEdge] using hcopy

/-- The version of the coning bridge in precisely the projection form used by
`SpecialContainer.projectedExtension`. -/
theorem cone_image_mem_copyHypergraph_of_subset_iota
    (F : SimpleGraph A) (root : A) (G' G : SimpleGraph (Option U)) (hG : G' ≤ G)
    {E : Finset (U × Fin 2)} (hE : E ∈ extensionAuxHypergraph F root G' G)
    (hEI : E ⊆ extensionIota G' G) :
    insert none (E.image (fun z ↦ some z.1)) ∈ copyHypergraph F G' G := by
  rw [image_some_fst_eq_image_some_layerProjection]
  exact cone_layerProjection_mem_copyHypergraph_of_subset_iota F root G' G hG hE hEI

/-- Vertices occurring in layer `b` of a two-layer set. -/
noncomputable def layerVertices (b : Fin 2) (Y : Finset (U × Fin 2)) : Finset U := by
  classical
  exact Finset.univ.filter fun u ↦ (u, b) ∈ Y

@[simp]
theorem mem_layerVertices (b : Fin 2) (Y : Finset (U × Fin 2)) (u : U) :
    u ∈ layerVertices b Y ↔ (u, b) ∈ Y := by
  classical
  simp [layerVertices]

/-- Recover a concrete induced embedding from an edge of the old copy
hypergraph.  The returned embedding has exactly the prescribed image and all
of its target edges lie in the old part of `G'`. -/
theorem exists_embedding_of_mem_copyHypergraph_delete
    (F : SimpleGraph A) (root : A) (G' G : SimpleGraph (Option U))
    {L : Finset U}
    (hL : L ∈ copyHypergraph (deleteVertex F root) (oldPart G') (oldPart G)) :
    ∃ e : deleteVertex F root ↪g oldPart G,
      (∀ {x y : DeletedVertices root},
        (deleteVertex F root).Adj x y →
          G'.Adj (some (e x)) (some (e y))) ∧
      embeddingImage root e.toEmbedding = L := by
  classical
  obtain ⟨⟨iso'⟩, heq⟩ :=
    (mem_copyHypergraph (deleteVertex F root) (oldPart G') (oldPart G) L).1 hL
  let emb : DeletedVertices root ↪ U :=
    iso'.toEquiv.toEmbedding.trans (Function.Embedding.subtype _)
  let e : deleteVertex F root ↪g oldPart G :=
    { __ := emb
      map_rel_iff' := by
        intro x y
        have hi : ((oldPart G).induce (↑L : Set U)).Adj (iso' x) (iso' y) ↔
            (deleteVertex F root).Adj x y := by
          rw [← heq]
          exact iso'.map_adj_iff
        exact hi }
  refine ⟨e, ?_, ?_⟩
  · intro x y hxy
    change (oldPart G').Adj (iso' x).1 (iso' y).1
    exact iso'.toEmbedding.toHom.map_adj hxy
  · ext u
    constructor
    · intro hu
      obtain ⟨x, -, hxu⟩ := Finset.mem_map.1 hu
      rw [← hxu]
      exact (iso' x).property
    · intro hu
      let x : DeletedVertices root := iso'.symm ⟨u, hu⟩
      apply Finset.mem_map.2
      refine ⟨x, Finset.mem_univ _, ?_⟩
      change (iso' x).1 = u
      exact congrArg Subtype.val (iso'.apply_symm_apply ⟨u, hu⟩)

/-- Every deleted-target copy supported in both layers lifts to an auxiliary
edge contained in `Y`. -/
theorem exists_extensionEdge_subset_of_copy_subset_layerIntersection
    (F : SimpleGraph A) (root : A) (G' G : SimpleGraph (Option U))
    (Y : Finset (U × Fin 2)) {L : Finset U}
    (hL : L ∈ copyHypergraph (deleteVertex F root) (oldPart G') (oldPart G))
    (hLW : L ⊆ layerVertices 0 Y ∩ layerVertices 1 Y) :
    ∃ E ∈ extensionAuxHypergraph F root G' G,
      E ⊆ Y ∧ layerProjection E = L := by
  obtain ⟨e, hMono, himage⟩ :=
    exists_embedding_of_mem_copyHypergraph_delete F root G' G hL
  let E := extensionEdge F root e.toEmbedding
  refine ⟨E, extensionEdge_mem_extensionAuxHypergraph F root G' G e hMono, ?_, ?_⟩
  · intro z hz
    obtain ⟨x, hx, hb⟩ := (mem_extensionEdge F root e.toEmbedding z).1 hz
    have hxeL : e.toEmbedding x ∈ L := by
      rw [← himage]
      simp [embeddingImage]
    have hxeW := hLW hxeL
    have hzero : (e.toEmbedding x, (0 : Fin 2)) ∈ Y :=
      (mem_layerVertices 0 Y _).1 (Finset.mem_inter.1 hxeW).1
    have hone : (e.toEmbedding x, (1 : Fin 2)) ∈ Y :=
      (mem_layerVertices 1 Y _).1 (Finset.mem_inter.1 hxeW).2
    have hzEq : (e.toEmbedding x, requiredBit F root x) = z := Prod.ext hx hb
    rw [← hzEq]
    have hbit : requiredBit F root x = 0 ∨ requiredBit F root x = 1 := by
      have hb := (requiredBit F root x).isLt
      omega
    rcases hbit with hbit | hbit
    · simpa [hbit] using hzero
    · simpa [hbit] using hone
  · rw [layerProjection_extensionEdge, himage]

/-- Restricting to the intersection of the two layers preserves every old
deleted-target copy after projection through the auxiliary hypergraph. -/
theorem map_restrict_copyHypergraph_subset_map_restrict_extensionAuxHypergraph
    (F : SimpleGraph A) (root : A) (G' G : SimpleGraph (Option U))
    (Y : Finset (U × Fin 2)) :
    Hypergraph.map some
        (Hypergraph.restrict
          (copyHypergraph (deleteVertex F root) (oldPart G') (oldPart G))
          (layerVertices 0 Y ∩ layerVertices 1 Y)) ⊆
      Hypergraph.map (fun z ↦ some z.1)
        (Hypergraph.restrict (extensionAuxHypergraph F root G' G) Y) := by
  intro T hT
  obtain ⟨L, hLr, rfl⟩ := Hypergraph.mem_map.1 hT
  obtain ⟨hL, hLW⟩ := Hypergraph.mem_restrict.1 hLr
  obtain ⟨E, hEAux, hEY, hproj⟩ :=
    exists_extensionEdge_subset_of_copy_subset_layerIntersection
      F root G' G Y hL hLW
  apply Hypergraph.mem_map.2
  refine ⟨E, Hypergraph.mem_restrict.2 ⟨hEAux, hEY⟩, ?_⟩
  rw [image_some_fst_eq_image_some_layerProjection, hproj]

end Erdos565
