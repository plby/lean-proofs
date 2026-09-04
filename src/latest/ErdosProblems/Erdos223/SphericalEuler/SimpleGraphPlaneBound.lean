import ErdosProblems.Erdos223.SphericalEuler.GeneralPlaneBound
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.Graph.Maps

open Metric Set Schoenflies unitInterval
open scoped Graph

namespace Graph

variable {α α' β : Type*} {G : Graph α β}

/-- Injectively mapping the vertices of a simple multigraph preserves simplicity. -/
theorem Simple.map_of_injective [G.Simple] (f : α → α') (hf : Function.Injective f) :
    (G.map f).Simple where
  not_isLoopAt e x := by
    rintro ⟨u, v, huv, hux, hvx⟩
    have huv' : u = v := hf (hux.trans hvx.symm)
    subst v
    exact G.not_isLoopAt e u huv
  eq_of_isLink e g x y he hg := by
    rcases he with ⟨u, v, huv, hux, hvy⟩
    rcases hg with ⟨p, q, hpq, hpx, hqy⟩
    have hup : u = p := hf (hux.trans hpx.symm)
    have hvq : v = q := hf (hvy.trans hqy.symm)
    subst p; subst q
    exact huv.eq hpq

/-- A walk maps to a walk with the same edge list. -/
theorem IsWalk.map_vertices (h : G.IsWalk u W v) (f : α → α') :
    (G.map f).IsWalk (f u) W (f v) := by
  induction h with
  | nil hu => exact .nil (Set.mem_image_of_mem f hu)
  | cons hlink _ ih => exact .cons (hlink.map f) ih

/-- Mapping the vertices of a connected multigraph preserves connectedness. -/
theorem Connected.map_vertices (h : G.Connected) (f : α → α') :
    (G.map f).Connected := by
  obtain ⟨u, hu⟩ := h.nonempty
  refine Connected.of_hub (Set.mem_image_of_mem f hu) ?_
  intro y hy
  change y ∈ f '' V(G) at hy
  obtain ⟨v, hv, rfl⟩ := hy
  obtain ⟨W, hW⟩ := h.reaches hu hv
  exact ⟨W, hW.map_vertices f⟩

/-- A Mathlib simple-graph walk is the corresponding edge-named multigraph walk. -/
theorem ofSimpleGraph_isWalk_of_walk {V : Type*} {F : SimpleGraph V} {u v : V}
    (p : F.Walk u v) : (Graph.ofSimpleGraph F).IsWalk u p.edges v := by
  induction p with
  | nil => exact .nil (by simp)
  | @cons u v w hadj p ih =>
      rw [SimpleGraph.Walk.edges_cons]
      exact .cons ⟨rfl, (SimpleGraph.mem_edgeSet F).2 hadj⟩ ih

/-- Mathlib connectedness agrees with connectedness of the edge-named multigraph. -/
theorem ofSimpleGraph_connected {V : Type*} {F : SimpleGraph V}
    (h : F.Connected) : (Graph.ofSimpleGraph F).Connected := by
  let : Nonempty V := h.nonempty
  refine ⟨by simp, ?_⟩
  intro u _ v _
  obtain ⟨p⟩ := h u v
  exact ⟨p.edges, ofSimpleGraph_isWalk_of_walk p⟩

/-- The edge-named multigraph of a simple graph is simple. -/
theorem simple_ofSimpleGraph {V : Type*} (F : SimpleGraph V) :
    (Graph.ofSimpleGraph F).Simple where
  not_isLoopAt e x := by
    intro h
    exact F.loopless.irrefl x ((ofSimpleGraph_adj_iff x x).mp ⟨e, h⟩)
  eq_of_isLink e f x y he hf := he.1.trans hf.1.symm

#print axioms Graph.Simple.map_of_injective
#print axioms Graph.ofSimpleGraph_connected

namespace WeightedFaces

/-- SimpleGraph-facing connected bipartite plane bound. -/
theorem simpleGraph_edge_add_four_le_two_vertices
    {V : Type*} [Fintype V] (F : SimpleGraph V) [Fintype F.edgeSet]
    (pos : V → Plane) (hpos : Function.Injective pos)
    (drawing : Sym2 V → ℝ → Plane)
    (hdraw : ((Graph.ofSimpleGraph F).map pos).IsDrawing drawing)
    (hconn : F.Connected) (hbi : F.IsBipartite)
    (hcard : 3 ≤ Fintype.card V) :
    F.edgeFinset.card + 4 ≤ 2 * Fintype.card V := by
  classical
  let : Nonempty V := hconn.nonempty
  let Q := (Graph.ofSimpleGraph F).map pos
  let : (Graph.ofSimpleGraph F).Simple := simple_ofSimpleGraph F
  let : Q.Simple := Graph.Simple.map_of_injective pos hpos
  let : Q.Finite := by
    refine ⟨?_, ?_⟩
    · change (pos '' (Set.univ : Set V)).Finite
      exact Set.finite_univ.image pos
    · change F.edgeSet.Finite
      exact Set.toFinite _
  have hQconn : Q.Connected := (ofSimpleGraph_connected hconn).map_vertices pos
  obtain ⟨s, t, hst⟩ := hbi.exists_isBipartiteWith
  let cV : V → Bool := fun x => decide (x ∈ s)
  let c : Plane → Bool := fun x => cV (Function.invFun pos x)
  have hc : Q.IsBicoloring c := by
    intro e x y hxy
    rcases hxy with ⟨u, v, huv, rfl, rfl⟩
    have hadj : F.Adj u v := (ofSimpleGraph_adj_iff u v).mp ⟨e, huv⟩
    have huinv : Function.invFun pos (pos u) = u := Function.leftInverse_invFun hpos u
    have hvinv : Function.invFun pos (pos v) = v := Function.leftInverse_invFun hpos v
    rcases hst.mem_of_adj hadj with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · have hv' : v ∉ s := fun hvS => Set.disjoint_left.1 hst.disjoint hvS hv
      simp [c, cV, huinv, hvinv, hu, hv']
    · have hu' : u ∉ s := fun huS => Set.disjoint_left.1 hst.disjoint huS hu
      simp [c, cV, huinv, hvinv, hu', hv]
  have hVcard : V(Q).ncard = Fintype.card V := by
    change (pos '' (Set.univ : Set V)).ncard = Fintype.card V
    rw [Set.ncard_image_of_injective _ hpos]
    simp [Nat.card_eq_fintype_card]
  have hEcard : E(Q).ncard = F.edgeFinset.card := by
    change F.edgeSet.ncard = F.edgeFinset.card
    simpa [SimpleGraph.edgeFinset] using Set.ncard_eq_toFinset_card' F.edgeSet
  have hbound := edge_add_four_le_two_vertices_of_connected_isDrawing_isBicoloring
    Q drawing hdraw hQconn (hVcard ▸ hcard) hc
  rwa [hVcard, hEcard] at hbound

#print axioms Graph.WeightedFaces.simpleGraph_edge_add_four_le_two_vertices

end WeightedFaces
end Graph

namespace Graph.WeightedFaces

/-- The exact callback expected by the Vázsonyi double-cover bridge. -/
theorem connectedSimpleGraphCallback
    (W : Type) [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (p : W → Plane) (D : Sym2 W → ℝ → Plane)
    (hconn : H.Connected) (hmin : ∀ w, 2 ≤ H.degree w)
    (hbi : H.IsBipartite) (hp : Function.Injective p)
    (hdraw : Graph.IsDrawing ((Graph.ofSimpleGraph H).map p) D) :
    H.edgeFinset.card + 4 ≤ 2 * Fintype.card W := by
  let w : W := Classical.choice hconn.nonempty
  have hcard : 3 ≤ Fintype.card W := by
    have hlt := H.degree_lt_card_verts w
    exact (hmin w).trans_lt hlt
  exact simpleGraph_edge_add_four_le_two_vertices H p hp D hdraw hconn hbi hcard

#print axioms connectedSimpleGraphCallback

end Graph.WeightedFaces
