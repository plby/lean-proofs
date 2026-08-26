-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.Reduce

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Structural infrastructure: Berge cycles, bridges, the class `B`, expansions

This file provides the definitional infrastructure of the paper needed to state
the classification of obligatory triple systems and the exact-spectrum results:
Berge cycles, Levi bridges and bridge selectors, the intrinsic obligatoriness
condition, the private-vertex expansion `J⁺`, disjoint union and one-point
amalgamation of finite triple systems, and the target class `B`.
-/

open Cardinal

namespace Erdos1177

universe u

/-! ### Berge cycles and bridges -/

/-- A *Berge cycle* of length `m ≥ 2` in a triple system: an alternating cyclic
sequence of distinct point-nodes and hyperedge-nodes with consecutive
incidences (`v i, v (i+1) ∈ e i`). -/
structure BergeCycle (F : FTS) where
  m : ℕ
  hm : 2 ≤ m
  v : ZMod m → F.V
  e : ZMod m → {e : Finset F.V // e ∈ F.edges}
  vinj : Function.Injective v
  einj : Function.Injective e
  mem_left : ∀ i, v i ∈ (e i).1
  mem_right : ∀ i, v (i + 1) ∈ (e i).1

/-- The Levi incidence `(w, ed)` (with `w ∈ ed`) lies on a Berge cycle. -/
def OnBergeCycle (F : FTS) (w : F.V) (ed : {e : Finset F.V // e ∈ F.edges}) : Prop :=
  ∃ (c : BergeCycle F) (i : ZMod c.m), c.e i = ed ∧ (c.v i = w ∨ c.v (i + 1) = w)

/-- A Levi incidence `(w, ed)` is a *bridge* if `w ∈ ed` and it lies on no Berge
cycle.  (A finite-graph edge is a bridge iff it lies on no cycle; this is the
characterization the paper uses.) -/
def IsBridgeInc (F : FTS) (w : F.V) (ed : {e : Finset F.V // e ∈ F.edges}) : Prop :=
  w ∈ ed.1 ∧ ¬ OnBergeCycle F w ed

/-- A *bridge selector*: a choice at each edge of an incident bridge point. -/
structure BridgeSelector (F : FTS) where
  p : {e : Finset F.V // e ∈ F.edges} → F.V
  isBridge : ∀ ed, IsBridgeInc F (p ed) ed

/-- The intrinsic condition (iii) of the classification: linear, every
hyperedge-node incident with a bridge, and every Berge cycle of even length.
(These three properties are unaffected by isolated vertices, so we phrase them on
`F` directly.) -/
def FTS.IntrinsicObligatory (F : FTS) : Prop :=
  F.Linear ∧
  (∀ ed : {e : Finset F.V // e ∈ F.edges}, ∃ w ∈ ed.1, IsBridgeInc F w ed) ∧
  (∀ c : BergeCycle F, Even c.m)

/-! ### The class `B` -/

/-- Disjoint union of two finite triple systems. -/
def FTS.disjUnion (F G : FTS) : FTS where
  V := F.V ⊕ G.V
  edges := F.edges.image (Finset.map Function.Embedding.inl) ∪
           G.edges.image (Finset.map Function.Embedding.inr)
  card3 := by
    intro e he
    simp only [Finset.mem_union, Finset.mem_image] at he
    rcases he with ⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩ <;>
      rw [Finset.card_map] <;> [exact F.card3 d hd; exact G.card3 d hd]

/-- One-point amalgamation identifying `x ∈ V(F)` with `y ∈ V(G)`.  Realized on
the glue type `F.V ⊕ {b : G.V // b ≠ y}`, sending `y` to `x`. -/
noncomputable def FTS.amalgamate (F G : FTS) (x : F.V) (y : G.V) : FTS where
  V := F.V ⊕ {b : G.V // b ≠ y}
  edges :=
    F.edges.image (Finset.map Function.Embedding.inl) ∪
    G.edges.image (Finset.map ⟨fun b => if h : b = y then Sum.inl x else Sum.inr ⟨b, h⟩, by
      intro a b hab
      by_cases ha : a = y <;> by_cases hb : b = y <;> simp_all⟩)
  card3 := by
    intro e he
    simp only [Finset.mem_union, Finset.mem_image] at he
    rcases he with ⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩ <;>
      rw [Finset.card_map] <;> [exact F.card3 d hd; exact G.card3 d hd]

/-- The private-vertex expansion `J⁺` of a finite graph `J`: core vertices of `J`
plus one private vertex per edge, with edges `{x, y, p_{xy}}`. -/
noncomputable def graphExpansion {VJ : Type} [Fintype VJ] [DecidableEq VJ]
    (J : SimpleGraph VJ) [DecidableRel J.Adj] : FTS where
  V := VJ ⊕ {e : Sym2 VJ // e ∈ J.edgeFinset}
  edges := J.edgeFinset.attach.image (fun e =>
    {Sum.inl (Quot.out e.1).1, Sum.inl (Quot.out e.1).2, Sum.inr e})
  card3 := by
    classical
    intro s hs
    simp only [Finset.mem_image, Finset.mem_attach, true_and] at hs
    obtain ⟨e, rfl⟩ := hs
    have hmem : e.1 ∈ J.edgeSet := SimpleGraph.mem_edgeFinset.mp e.2
    rw [← Quot.out_eq e.1] at hmem
    have hadj : J.Adj (Quot.out e.1).1 (Quot.out e.1).2 := hmem
    have hne : (Quot.out e.1).1 ≠ (Quot.out e.1).2 := hadj.ne
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton]; exact fun h => Sum.inl_ne_inr h
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨fun h => hne (Sum.inl_injective h), fun h => Sum.inl_ne_inr h⟩

/-- Isomorphism of finite triple systems: a vertex bijection preserving edges. -/
def FTS.Iso (F G : FTS) : Prop :=
  ∃ φ : F.V ≃ G.V, ∀ e : Finset F.V, e ∈ F.edges ↔ e.map φ.toEmbedding ∈ G.edges

/-- **The class `B`** (`Bclass`): the smallest class of finite triple systems
containing every private-vertex expansion `J⁺` of a finite bipartite graph `J`,
containing every edgeless system, and closed under isomorphism, disjoint union
and one-point amalgamation. -/
inductive Bclass : FTS → Prop
  | edgeless (F : FTS) (h : F.edges = ∅) : Bclass F
  | expansion {VJ : Type} [Fintype VJ] [DecidableEq VJ] (J : SimpleGraph VJ)
      [DecidableRel J.Adj] (hJ : J.Colorable 2) : Bclass (graphExpansion J)
  | iso {F G : FTS} (h : FTS.Iso F G) : Bclass F → Bclass G
  | union {F G : FTS} : Bclass F → Bclass G → Bclass (F.disjUnion G)
  | amalg {F G : FTS} (x : F.V) (y : G.V) : Bclass F → Bclass G → Bclass (F.amalgamate G x y)

/-! ### Linearity for hosts -/

/-- A host hypergraph is *linear* if any two distinct edges meet in at most one
vertex. -/
def Hypergraph.Linear {W : Type*} (H : Hypergraph W) : Prop :=
  ∀ e₁ ∈ H.edges, ∀ e₂ ∈ H.edges, e₁ ≠ e₂ → (e₁ ∩ e₂).Subsingleton

/-! ### Obligatoriness transfers across isomorphism -/

/-- Obligatoriness transfers across isomorphism. -/
theorem obligatory_iso {F G : FTS} (h : FTS.Iso F G) (ih : FTS.Obligatory.{u} F) :
    FTS.Obligatory.{u} G := by
  intro W H htri huc;
  obtain ⟨ φ, hφ ⟩ := h;
  obtain ⟨ f, hf, hfe ⟩ := ih H htri huc;
  use fun x => f ( φ.symm x );
  refine' ⟨ hf.comp φ.symm.injective, _ ⟩;
  intro e he; specialize hφ ( Finset.map φ.symm.toEmbedding e ) ; simp_all +decide [ Finset.map_map ] ;
  convert! hfe _ hφ using 1 ; ext ; aesop

end Erdos1177
