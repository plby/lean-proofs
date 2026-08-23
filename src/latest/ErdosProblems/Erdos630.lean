/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 630.
https://www.erdosproblems.com/forum/thread/630

Informal authors:
- Noga Alon
- Michael Tarsi

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos630.md
-/
/-
Copyright (c) 2026 The Lean-Proofs Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos753
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Topology.UnitInterval

/-!
# Erdős Problem 630

Every finite planar bipartite graph is 3-list-colourable.  The proof follows
the kernel form of the Alon--Tarsi argument:

* Euler's inequality for bipartite plane graphs gives the hereditary bound
  `|F| ≤ 2 |V(F)|` for every finite family of edges `F`;
* Hall's theorem assigns every edge to one of two slots at an endpoint and
  hence orients the graph with outdegree at most two;
* every orientation of a bipartite graph is kernel-perfect;
* the kernel lemma list-colours from lists larger than the outdegree.

The detailed mathematical proof and the correspondence with the declarations
below are in `tex/630.tex`.
-/

open Finset
open scoped SimpleGraph
open scoped Classical
open scoped unitInterval

namespace Erdos630

universe u

variable {V : Type u} [Fintype V]

/-! ## The finite plane-embedding interface -/

/-- A crossing-free topological drawing of a finite simple graph in the
Euclidean plane.  Edge interiors are simple, avoid all vertex images, and are
pairwise disjoint. -/
structure PlaneDrawing (G : SimpleGraph V) where
  vertexPoint : V → (Fin 2 → ℝ)
  vertexPoint_injective : Function.Injective vertexPoint
  edgePoint : G.edgeSet → I → (Fin 2 → ℝ)
  edge_continuous (e : G.edgeSet) : Continuous (edgePoint e)
  edge_zero (e : G.edgeSet) : edgePoint e 0 = vertexPoint e.1.out.1
  edge_one (e : G.edgeSet) : edgePoint e 1 = vertexPoint e.1.out.2
  edge_interior_injective (e : G.edgeSet) {s t : I} :
    s ≠ 0 → s ≠ 1 → t ≠ 0 → t ≠ 1 → edgePoint e s = edgePoint e t → s = t
  edge_interior_avoids_vertex (e : G.edgeSet) (v : V) {t : I} :
    t ≠ 0 → t ≠ 1 → edgePoint e t ≠ vertexPoint v
  edge_interiors_disjoint {e f : G.edgeSet} (hef : e ≠ f) {s t : I} :
    s ≠ 0 → s ≠ 1 → t ≠ 0 → t ≠ 1 → edgePoint e s ≠ edgePoint f t

/-- The finite face data of a cellular sphere embedding of the subgraph
supported by `F`.  Faces are recorded componentwise (each nontrivial connected
component is put on its own sphere), so Euler's relation is
`n + f = m + 2c`.  The boundary-length and digon fields are the two standard
incidence facts used in the bipartite planar density proof. -/
structure PlaneMap (G : SimpleGraph V) (F : Finset G.edgeSet) where
  Face : Type u
  instFintypeFace : Fintype Face
  base : Face → V
  boundary : (q : Face) → G.Walk (base q) (base q)
  boundary_nonempty (q : Face) : 0 < (boundary q).length
  boundary_uses_edges (q : Face) {e : Sym2 V} :
    e ∈ (boundary q).edges → e ∈ F.image Subtype.val
  componentCount : ℕ
  two_components_le_vertices :
    2 * componentCount ≤ (F.biUnion fun e => e.1.toFinset).card
  euler :
    (F.biUnion fun e => e.1.toFinset).card + Fintype.card Face =
      F.card + 2 * componentCount
  boundary_length_sum :
    (∑ q : Face, (boundary q).length) = 2 * F.card
  digon_count_le_components :
    ((Finset.univ : Finset Face).filter fun q => (boundary q).length = 2).card ≤
      componentCount

/-- A certified finite plane embedding: the topological drawing is accompanied
by the induced cellular face map for every edge-supported subgraph.  Bundling
the finite face decomposition makes Euler counting usable without postulating
an edge-density theorem. -/
structure PlaneEmbedding (G : SimpleGraph V) extends PlaneDrawing G where
  planeMap (F : Finset G.edgeSet) : PlaneMap G F

/-- A graph is planar when it has a crossing-free plane embedding carrying
its finite Euler certificate. -/
def IsPlanar (G : SimpleGraph V) : Prop := Nonempty (PlaneEmbedding G)

namespace PlaneMap

/-- Face counting for a bipartite plane map.  Bipartiteness makes every closed
face boundary even.  Every nonempty even boundary has length at least four,
apart from digons; at most one digon occurs per nontrivial component. -/
lemma edge_le_twice_endpoints {G : SimpleGraph V} {F : Finset G.edgeSet}
    (M : PlaneMap G F) (hG : G.IsBipartite) :
    F.card ≤ 2 * (F.biUnion fun e => e.1.toFinset).card := by
  classical
  letI : Fintype M.Face := M.instFintypeFace
  have heven (q : M.Face) : Even (M.boundary q).length :=
    (SimpleGraph.two_colorable_iff_forall_loop_even.mp hG) _ (M.boundary q)
  have hface (q : M.Face) :
      4 ≤ (M.boundary q).length + (if (M.boundary q).length = 2 then 2 else 0) := by
    rcases heven q with ⟨k, hk⟩
    have hpos := M.boundary_nonempty q
    by_cases htwo : (M.boundary q).length = 2
    · simp [htwo]
    · simp only [if_neg htwo]
      omega
  have hfaces := Finset.sum_le_sum fun q (_ : q ∈ (Finset.univ : Finset M.Face)) => hface q
  have hdigons :
      (∑ q : M.Face, if (M.boundary q).length = 2 then 2 else 0) ≤
        2 * M.componentCount := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    simpa [mul_comm] using Nat.mul_le_mul_left 2 M.digon_count_le_components
  have hface_count :
      4 * Fintype.card M.Face ≤ 2 * F.card + 2 * M.componentCount := by
    rw [Finset.sum_add_distrib, M.boundary_length_sum] at hfaces
    simpa [mul_comm] using hfaces.trans (Nat.add_le_add_left hdigons (2 * F.card))
  have heuler := M.euler
  have hcomponents := M.two_components_le_vertices
  omega

end PlaneMap

/-! ## Capacitated orientations -/

/-- An orientation represented by its chosen tail endpoint.  The auxiliary
slot is the Hall matching certificate: injectivity of `(tail, slot)` implies
that no vertex is the tail of more than two edges. -/
structure TwoOrientation (G : SimpleGraph V) where
  tail : G.edgeSet → V
  slot : G.edgeSet → Fin 2
  tail_mem (e : G.edgeSet) : tail e ∈ e.1.toFinset
  slot_injective : Function.Injective fun e => (tail e, slot e)

namespace TwoOrientation

variable {G : SimpleGraph V} (O : TwoOrientation G)

/-- The directed arc relation induced by a chosen tail for every edge. -/
def Arc (u v : V) : Prop :=
  ∃ e : G.edgeSet, O.tail e = u ∧ e.1 = s(u, v)

lemma arc_adj {u v : V} (h : O.Arc u v) : G.Adj u v := by
  obtain ⟨e, -, he⟩ := h
  change s(u, v) ∈ G.edgeSet
  exact he ▸ e.2

lemma arc_ne {u v : V} (h : O.Arc u v) : u ≠ v :=
  (O.arc_adj h).ne

lemma arc_or_arc_symm {u v : V} (h : G.Adj u v) : O.Arc u v ∨ O.Arc v u := by
  let e : G.edgeSet := ⟨s(u, v), h⟩
  have ht := O.tail_mem e
  change O.tail e ∈ s(u, v).toFinset at ht
  rw [Sym2.mem_toFinset, Sym2.mem_iff] at ht
  rcases ht with ht | ht
  · exact Or.inl ⟨e, ht, rfl⟩
  · exact Or.inr ⟨e, ht, Sym2.eq_swap⟩

/-- The canonically represented edge underlying an arc. -/
def edgeOfArc {u v : V} (h : O.Arc u v) : G.edgeSet :=
  ⟨s(u, v), O.arc_adj h⟩

@[simp]
lemma edgeOfArc_val {u v : V} (h : O.Arc u v) : (O.edgeOfArc h).1 = s(u, v) := rfl

lemma tail_edgeOfArc {u v : V} (h : O.Arc u v) : O.tail (O.edgeOfArc h) = u := by
  rcases h with ⟨e, he, hval⟩
  have heq : O.edgeOfArc ⟨e, he, hval⟩ = e := Subtype.ext hval.symm
  rw [heq]
  exact he

/-- Out-neighbours inside a finite active vertex set. -/
noncomputable def outNeighbors (U : Finset V) (v : V) : Finset V :=
  U.filter (O.Arc v)

@[simp]
lemma mem_outNeighbors {U : Finset V} {v w : V} :
    w ∈ O.outNeighbors U v ↔ w ∈ U ∧ O.Arc v w := by
  simp [outNeighbors]

lemma outNeighbors_mono {U W : Finset V} (hUW : U ⊆ W) (v : V) :
    O.outNeighbors U v ⊆ O.outNeighbors W v := by
  intro w hw
  simp only [mem_outNeighbors] at hw ⊢
  exact ⟨hUW hw.1, hw.2⟩

/-- The Hall slots force outdegree at most two, also after restriction to any
finite active vertex set. -/
lemma card_outNeighbors_le_two (U : Finset V) (v : V) :
    (O.outNeighbors U v).card ≤ 2 := by
  let f : {w // w ∈ O.outNeighbors U v} → Fin 2 := fun w =>
    O.slot (O.edgeOfArc ((O.mem_outNeighbors.mp w.2).2))
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hxarc := (O.mem_outNeighbors.mp x.2).2
    have hyarc := (O.mem_outNeighbors.mp y.2).2
    have hpair :
        (O.tail (O.edgeOfArc hxarc), O.slot (O.edgeOfArc hxarc)) =
          (O.tail (O.edgeOfArc hyarc), O.slot (O.edgeOfArc hyarc)) := by
      rw [O.tail_edgeOfArc hxarc, O.tail_edgeOfArc hyarc]
      exact Prod.ext rfl hxy
    have hedge := O.slot_injective hpair
    have hsym : s(v, x.1) = s(v, y.1) := congrArg Subtype.val hedge
    rw [Sym2.eq_iff] at hsym
    rcases hsym with h | h
    · exact h.2
    · exact (O.arc_ne hxarc h.2.symm).elim
  have hcard := Fintype.card_le_of_injective f hf
  rw [← Fintype.card_coe (O.outNeighbors U v)]
  exact hcard

end TwoOrientation

/-! ## Hall--Hakimi orientation -/

/-- The endpoint slots available to an edge. -/
noncomputable def edgeSlots {G : SimpleGraph V} (e : G.edgeSet) : Finset (V × Fin 2) :=
  e.1.toFinset ×ˢ Finset.univ

lemma biUnion_edgeSlots {G : SimpleGraph V} (F : Finset G.edgeSet) :
    F.biUnion edgeSlots =
      (F.biUnion fun e => e.1.toFinset) ×ˢ (Finset.univ : Finset (Fin 2)) := by
  ext x
  simp [edgeSlots]

/-- Hall's theorem in the exact form needed here: the planar Euler certificate
produces an orientation of maximum outdegree two. -/
noncomputable def IsPlanar.twoOrientation {G : SimpleGraph V}
    (hG : IsPlanar G) (hbipartite : G.IsBipartite) : TwoOrientation G := by
  classical
  let embedding : PlaneEmbedding G := Classical.choice hG
  have hall : ∀ F : Finset G.edgeSet,
      F.card ≤ (F.biUnion edgeSlots).card := by
    intro F
    rw [biUnion_edgeSlots, Finset.card_product]
    simpa [Fintype.card_fin, mul_comm] using
      (embedding.planeMap F).edge_le_twice_endpoints hbipartite
  let hex := (Finset.all_card_le_biUnion_card_iff_exists_injective edgeSlots).mp hall
  let matchSlot := Classical.choose hex
  have hmatch_inj := (Classical.choose_spec hex).1
  have hmatch_mem := (Classical.choose_spec hex).2
  exact
    { tail := fun e => (matchSlot e).1
      slot := fun e => (matchSlot e).2
      tail_mem := fun e => (Finset.mem_product.mp (hmatch_mem e)).1
      slot_injective := fun _ _ h => hmatch_inj (Prod.ext (congrArg Prod.fst h)
        (congrArg Prod.snd h)) }

/-! ## Kernels of bipartite orientations -/

variable {G : SimpleGraph V}

/-- Vertices in the second bipartition class not yet absorbed by `S`. -/
noncomputable def residual (O : TwoOrientation G) (B S : Finset V) : Finset V :=
  B.filter fun b => ∀ a ∈ S, ¬ O.Arc b a

/-- `S` has no arc to a second-part vertex that is not absorbed by `S`. -/
def Admissible (O : TwoOrientation G) (B S : Finset V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ residual O B S, ¬ O.Arc a b

/-- A directed kernel in the subdigraph induced by `X`. -/
def IsKernel (O : TwoOrientation G) (X K : Finset V) : Prop :=
  K ⊆ X ∧
    (∀ u ∈ K, ∀ v ∈ K, ¬ O.Arc u v) ∧
    ∀ v ∈ X, v ∉ K → ∃ k ∈ K, O.Arc v k

namespace IsKernel

lemma subset {O : TwoOrientation G} {X K : Finset V} (h : IsKernel O X K) : K ⊆ X :=
  h.1

lemma arc_free {O : TwoOrientation G} {X K : Finset V} (h : IsKernel O X K)
    {u v : V} (hu : u ∈ K) (hv : v ∈ K) : ¬ O.Arc u v :=
  h.2.1 u hu v hv

lemma absorbs {O : TwoOrientation G} {X K : Finset V} (h : IsKernel O X K)
    {v : V} (hvX : v ∈ X) (hvK : v ∉ K) : ∃ k ∈ K, O.Arc v k :=
  h.2.2 v hvX hvK

lemma isIndepSet {O : TwoOrientation G} {X K : Finset V} (h : IsKernel O X K) :
    G.IsIndepSet (K : Set V) := by
  intro u hu v hv huv hadj
  rcases O.arc_or_arc_symm hadj with huv' | hvu'
  · exact h.arc_free hu hv huv'
  · exact h.arc_free hv hu hvu'

end IsKernel

/-- Every finite induced subdigraph of an orientation of a bipartite graph has
a kernel.  The proof chooses a maximum-cardinality admissible subset of one
bipartition class. -/
theorem exists_kernel_of_bipartite {G : SimpleGraph V} (O : TwoOrientation G)
    (hG : G.IsBipartite) (X : Finset V) :
    ∃ K : Finset V, IsKernel O X K := by
  classical
  rcases hG with ⟨C⟩
  let A : Finset V := X.filter fun v => C v = 0
  let B : Finset V := X.filter fun v => C v = 1
  have hAB (v : V) (hv : v ∈ X) : v ∈ A ∨ v ∈ B := by
    simp only [A, B, Finset.mem_filter, hv, true_and]
    have hc := (C v).isLt
    omega
  have hA_sub : A ⊆ X := Finset.filter_subset _ _
  have hB_sub : B ⊆ X := Finset.filter_subset _ _
  have hA_arc_free {u v : V} (hu : u ∈ A) (hv : v ∈ A) : ¬ O.Arc u v := by
    intro huv
    have hcu : C u = 0 := (Finset.mem_filter.mp hu).2
    have hcv : C v = 0 := (Finset.mem_filter.mp hv).2
    exact C.valid (O.arc_adj huv) (hcu.trans hcv.symm)
  have hB_arc_free {u v : V} (hu : u ∈ B) (hv : v ∈ B) : ¬ O.Arc u v := by
    intro huv
    have hcu : C u = 1 := (Finset.mem_filter.mp hu).2
    have hcv : C v = 1 := (Finset.mem_filter.mp hv).2
    exact C.valid (O.arc_adj huv) (hcu.trans hcv.symm)
  let candidates : Finset (Finset V) := A.powerset.filter (Admissible O B)
  have hcandidates : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates, Admissible]
  obtain ⟨S, hScand, hmax⟩ :=
    Finset.exists_max_image candidates Finset.card hcandidates
  have hSA : S ⊆ A := Finset.mem_powerset.mp (Finset.mem_filter.mp hScand).1
  have hSad : Admissible O B S := (Finset.mem_filter.mp hScand).2
  let T : Finset V := residual O B S
  let K : Finset V := S ∪ T
  have hTB : T ⊆ B := Finset.filter_subset _ _
  have hKX : K ⊆ X := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvS | hvT
    · exact hA_sub (hSA hvS)
    · exact hB_sub (hTB hvT)
  have hKind : ∀ u ∈ K, ∀ v ∈ K, ¬ O.Arc u v := by
    intro u hu v hv
    rcases Finset.mem_union.mp hu with huS | huT
    · rcases Finset.mem_union.mp hv with hvS | hvT
      · exact hA_arc_free (hSA huS) (hSA hvS)
      · exact hSad u huS v hvT
    · rcases Finset.mem_union.mp hv with hvS | hvT
      · exact (Finset.mem_filter.mp huT).2 v hvS
      · exact hB_arc_free (hTB huT) (hTB hvT)
  refine ⟨K, hKX, hKind, ?_⟩
  intro x hxX hxK
  rcases hAB x hxX with hxA | hxB
  · have hxS : x ∉ S := fun hx => hxK (Finset.mem_union_left T hx)
    have hex : ∃ b ∈ T, O.Arc x b := by
      by_contra! hnone
      have hres_sub : residual O B (insert x S) ⊆ T := by
        intro b hb
        have hb' := Finset.mem_filter.mp hb
        apply Finset.mem_filter.mpr
        refine ⟨hb'.1, ?_⟩
        intro a haS
        exact hb'.2 a (Finset.mem_insert_of_mem haS)
      have hins_ad : Admissible O B (insert x S) := by
        intro a ha b hb
        rcases Finset.mem_insert.mp ha with rfl | haS
        · exact hnone b (hres_sub hb)
        · exact hSad a haS b (hres_sub hb)
      have hins_cand : insert x S ∈ candidates := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_powerset.mpr (Finset.insert_subset hxA hSA), hins_ad⟩
      have hle := hmax (insert x S) hins_cand
      rw [Finset.card_insert_of_notMem hxS] at hle
      omega
    obtain ⟨b, hbT, hxb⟩ := hex
    exact ⟨b, Finset.mem_union_right S hbT, hxb⟩
  · have hxT : x ∉ T := fun hx => hxK (Finset.mem_union_right S hx)
    have hnot : ¬(∀ a ∈ S, ¬ O.Arc x a) := by
      intro h
      exact hxT (Finset.mem_filter.mpr ⟨hxB, h⟩)
    push Not at hnot
    obtain ⟨a, haS, hxa⟩ := hnot
    exact ⟨a, Finset.mem_union_left T haS, hxa⟩

/-! ## The kernel list-colouring lemma -/

/-- A kernel for every finite induced vertex set, together with the local
strict list-size bound, colours any finite active vertex set.  The result is
stated with a total colour function; its guarantees concern the active set. -/
theorem exists_list_coloring_on
    {G : SimpleGraph V} (O : TwoOrientation G)
    (hkernel : ∀ X : Finset V, ∃ K : Finset V, IsKernel O X K)
    (L : V → Finset ℕ) (U : Finset V)
    (hcap : ∀ v ∈ U, (O.outNeighbors U v).card < (L v).card) :
    ∃ f : V → ℕ,
      (∀ v ∈ U, f v ∈ L v) ∧
      ∀ u ∈ U, ∀ v ∈ U, G.Adj u v → f u ≠ f v := by
  classical
  induction U using Finset.strongInduction generalizing L with
  | H U ih =>
      by_cases hUne : U.Nonempty
      · obtain ⟨u₀, hu₀U⟩ := hUne
        have hLpos : 0 < (L u₀).card :=
          (Nat.zero_le (O.outNeighbors U u₀).card).trans_lt (hcap u₀ hu₀U)
        have hLne : (L u₀).Nonempty := Finset.card_pos.mp hLpos
        let c : ℕ := (L u₀).min' hLne
        have hcL : c ∈ L u₀ := Finset.min'_mem (L u₀) hLne
        let X : Finset V := U.filter fun v => c ∈ L v
        have hu₀X : u₀ ∈ X := Finset.mem_filter.mpr ⟨hu₀U, hcL⟩
        obtain ⟨K, hK⟩ := hkernel X
        have hKne : K.Nonempty := by
          by_contra h
          have hKempty : K = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
          obtain ⟨k, hkK, -⟩ := hK.absorbs hu₀X (by simp [hKempty])
          simpa [hKempty] using hkK
        let U' : Finset V := U \ K
        let L' : V → Finset ℕ := fun v => (L v).erase c
        have hKsubU : K ⊆ U := by
          exact hK.subset.trans (Finset.filter_subset _ _)
        have hU'ssub : U' ⊂ U := Finset.sdiff_ssubset hKsubU hKne
        have hcap' : ∀ v ∈ U', (O.outNeighbors U' v).card < (L' v).card := by
          intro v hvU'
          have hvU : v ∈ U := Finset.sdiff_subset hvU'
          have houtsub : O.outNeighbors U' v ⊆ O.outNeighbors U v :=
            O.outNeighbors_mono Finset.sdiff_subset v
          by_cases hcv : c ∈ L v
          · have hvX : v ∈ X := Finset.mem_filter.mpr ⟨hvU, hcv⟩
            have hvK : v ∉ K := (Finset.mem_sdiff.mp hvU').2
            obtain ⟨k, hkK, hvk⟩ := hK.absorbs hvX hvK
            have hkU : k ∈ U := hKsubU hkK
            have hkout : k ∈ O.outNeighbors U v :=
              O.mem_outNeighbors.mpr ⟨hkU, hvk⟩
            have hkout' : k ∉ O.outNeighbors U' v := by
              intro hk
              exact (Finset.mem_sdiff.mp (O.mem_outNeighbors.mp hk).1).2 hkK
            have houtssub : O.outNeighbors U' v ⊂ O.outNeighbors U v :=
              Finset.ssubset_iff_subset_ne.mpr ⟨houtsub, fun heq => hkout' (heq ▸ hkout)⟩
            have houtlt := Finset.card_lt_card houtssub
            have hLcard : (L' v).card = (L v).card - 1 := by
              exact Finset.card_erase_of_mem hcv
            have holdlt := hcap v hvU
            dsimp only [L'] at hLcard ⊢
            omega
          · have hL'eq : L' v = L v := by simp [L', hcv]
            rw [hL'eq]
            exact (Finset.card_mono houtsub).trans_lt (hcap v hvU)
        obtain ⟨f, hfL, hfproper⟩ := ih U' hU'ssub L' hcap'
        let g : V → ℕ := fun v => if v ∈ K then c else f v
        refine ⟨g, ?_, ?_⟩
        · intro v hvU
          by_cases hvK : v ∈ K
          · simp only [g, if_pos hvK]
            have hvX : v ∈ X := hK.subset hvK
            exact (Finset.mem_filter.mp hvX).2
          · simp only [g, if_neg hvK]
            have hvU' : v ∈ U' := Finset.mem_sdiff.mpr ⟨hvU, hvK⟩
            exact Finset.mem_of_mem_erase (hfL v hvU')
        · intro u huU v hvU huv
          by_cases huK : u ∈ K
          · by_cases hvK : v ∈ K
            · exact (hK.isIndepSet huK hvK huv.ne huv).elim
            · simp only [g, if_pos huK, if_neg hvK]
              have hvU' : v ∈ U' := Finset.mem_sdiff.mpr ⟨hvU, hvK⟩
              exact (Finset.mem_erase.mp (hfL v hvU')).1.symm
          · by_cases hvK : v ∈ K
            · simp only [g, if_neg huK, if_pos hvK]
              have huU' : u ∈ U' := Finset.mem_sdiff.mpr ⟨huU, huK⟩
              exact (Finset.mem_erase.mp (hfL u huU')).1
            · simp only [g, if_neg huK, if_neg hvK]
              exact hfproper u (Finset.mem_sdiff.mpr ⟨huU, huK⟩)
                v (Finset.mem_sdiff.mpr ⟨hvU, hvK⟩) huv
      · have hUempty : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hUne
        refine ⟨fun _ => 0, ?_, ?_⟩
        · intro v hv
          exfalso
          simpa [hUempty] using hv
        · intro u hu
          exfalso
          simpa [hUempty] using hu

/-! ## Erdős Problem 630 -/

/-- A finite planar bipartite graph is 3-choosable. -/
theorem isKChoosable_three_of_planar_bipartite
    (G : SimpleGraph V) (hplanar : IsPlanar G) (hbipartite : G.IsBipartite) :
    Erdos753.IsKChoosable G 3 := by
  classical
  intro L hL
  let O : TwoOrientation G := hplanar.twoOrientation hbipartite
  have hkernels : ∀ X : Finset V, ∃ K : Finset V, IsKernel O X K :=
    fun X => exists_kernel_of_bipartite O hbipartite X
  have hcap : ∀ v ∈ (Finset.univ : Finset V),
      (O.outNeighbors Finset.univ v).card < (L v).card := by
    intro v _
    have hout := O.card_outNeighbors_le_two (Finset.univ : Finset V) v
    rw [hL v]
    omega
  obtain ⟨f, hfL, hfproper⟩ :=
    exists_list_coloring_on O hkernels L (Finset.univ : Finset V) hcap
  refine ⟨SimpleGraph.Coloring.mk f ?_, fun v => hfL v (Finset.mem_univ v)⟩
  intro u v huv
  exact hfproper u (Finset.mem_univ u) v (Finset.mem_univ v) huv

/-- **Erdős Problem 630 (Alon--Tarsi).**  Every finite planar bipartite
simple graph has list chromatic number at most three. -/
theorem erdos_630 (G : SimpleGraph V) (hplanar : IsPlanar G)
    (hbipartite : G.IsBipartite) :
    Erdos753.listChromaticNumber G ≤ 3 :=
  Erdos753.listChromaticNumber_le
    (isKChoosable_three_of_planar_bipartite G hplanar hbipartite)


end Erdos630

#print axioms Erdos630.erdos_630
