/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.DisjointUnion
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Connected-component bookkeeping for Erdős Problem 570

The induction in the odd-cycle proof removes one connected component of the
target.  This file packages a component and its complementary union of
components as coded graphs, proves exact additivity of their edge counts, and
records that neither piece acquires isolated vertices.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

open Erdos79

/-- The finite vertex set of a connected component. -/
def componentVertices (H : GraphCode) (c : H.graph.ConnectedComponent) :
    Finset (Fin H.vertexCount) := by
  classical
  exact Finset.univ.filter fun v ↦ H.graph.connectedComponentMk v = c

/-- A connected component, canonically recoded on a finite interval. -/
def componentCode (H : GraphCode) (c : H.graph.ConnectedComponent) : GraphCode :=
  inducedCode H (componentVertices H c)

/-- The union of all components other than `c`. -/
def componentRemainderCode (H : GraphCode)
    (c : H.graph.ConnectedComponent) : GraphCode :=
  inducedCode H ((componentVertices H c)ᶜ)

@[simp] theorem mem_componentVertices {H : GraphCode}
    {c : H.graph.ConnectedComponent} {v : Fin H.vertexCount} :
    v ∈ componentVertices H c ↔ v ∈ c.supp := by
  simp [componentVertices, SimpleGraph.ConnectedComponent.mem_supp_iff]

@[simp] theorem mem_componentVertices_compl {H : GraphCode}
    {c : H.graph.ConnectedComponent} {v : Fin H.vertexCount} :
    v ∈ (componentVertices H c)ᶜ ↔ v ∉ c.supp := by
  simp [componentVertices, SimpleGraph.ConnectedComponent.mem_supp_iff]

/-- The graph on a component support is the same as its canonical code. -/
def componentCodeIso (H : GraphCode) (c : H.graph.ConnectedComponent) :
    c.toSimpleGraph ≃g (componentCode H c).graph := by
  have hS : (componentVertices H c : Set (Fin H.vertexCount)) = c.supp := by
    ext v
    simp
  change H.graph.induce c.supp ≃g (componentCode H c).graph
  exact hS ▸ inducedCodeIso H (componentVertices H c)

/-- No edge of a graph joins a component to its complement. -/
theorem component_no_cross {H : GraphCode}
    (c : H.graph.ConnectedComponent) {x y : Fin H.vertexCount}
    (hx : x ∈ componentVertices H c) (hy : y ∈ (componentVertices H c)ᶜ) :
    ¬ H.graph.Adj x y := by
  intro hxy
  have hyc : y ∈ c.supp :=
    c.mem_supp_of_adj_mem_supp (mem_componentVertices.mp hx) hxy
  exact (mem_componentVertices_compl.mp hy) hyc

/-- The original graph embeds into the disjoint union of one component and
the union of the remaining components. -/
theorem isContained_component_partition (H : GraphCode)
    (c : H.graph.ConnectedComponent) :
    IsContained H (disjointUnionCode (componentCode H c)
      (componentRemainderCode H c)) := by
  apply isContained_disjointUnionCode_induced_partition
  intro x hx y hy hxy
  exact component_no_cross c hx (by simpa using hy) hxy

/-- Conversely, the two induced pieces have disjoint copies in the original
graph. -/
theorem component_partition_isContained (H : GraphCode)
    (c : H.graph.ConnectedComponent) :
    IsContained (disjointUnionCode (componentCode H c)
      (componentRemainderCode H c)) H := by
  let S : Set (Fin H.vertexCount) := componentVertices H c
  let T : Set (Fin H.vertexCount) :=
    ((componentVertices H c)ᶜ : Finset (Fin H.vertexCount))
  have hST : Disjoint S T := by
    rw [Set.disjoint_left]
    intro x hxS hxT
    have hxnot : x ∉ componentVertices H c := by simpa [T] using hxT
    exact hxnot (by simpa [S] using hxS)
  have hleft : (componentCode H c).graph ⊑ H.graph.induce S := by
    let e := inducedCodeIso H (componentVertices H c)
    simpa [S, componentCode] using
      (show (componentCode H c).graph ⊑
        H.graph.induce (componentVertices H c : Set (Fin H.vertexCount)) from
          ⟨e.symm.toCopy⟩)
  have hright : (componentRemainderCode H c).graph ⊑ H.graph.induce T := by
    let e := inducedCodeIso H (componentVertices H c)ᶜ
    simpa [T, componentRemainderCode] using
      (show (inducedCode H ((componentVertices H c)ᶜ)).graph ⊑
        H.graph.induce (((componentVertices H c)ᶜ :
          Finset (Fin H.vertexCount)) : Set (Fin H.vertexCount)) from
          ⟨e.symm.toCopy⟩)
  exact disjointUnionCode_isContained_of_induced_copies hST hleft hright

/-- Removing a component gives an exact edge-count decomposition. -/
theorem componentCode_edgeCount_add_remainder (H : GraphCode)
    (c : H.graph.ConnectedComponent) :
    (componentCode H c).edgeCount + (componentRemainderCode H c).edgeCount =
      H.edgeCount := by
  apply Nat.le_antisymm
  · simpa using (component_partition_isContained H c).edgeCount_le
  · simpa using (isContained_component_partition H c).edgeCount_le

/-- The code of a connected component is connected. -/
theorem componentCode_connected (H : GraphCode)
    (c : H.graph.ConnectedComponent) :
    (componentCode H c).graph.Connected := by
  exact (componentCodeIso H c).connected_iff.mp c.connected_toSimpleGraph

/-- A positive-edge component has no isolated vertices. -/
theorem componentCode_noIsolated {H : GraphCode}
    (c : H.graph.ConnectedComponent) (hc : 0 < (componentCode H c).edgeCount) :
    NoIsolated (componentCode H c) := by
  classical
  let G := (componentCode H c).graph
  let : DecidableRel G.Adj := Classical.decRel G.Adj
  have hcard : 0 < G.edgeFinset.card := by
    simpa [G, GraphCode.edgeCount_eq_card_edgeFinset] using hc
  obtain ⟨e, he⟩ := Finset.card_pos.mp hcard
  have hadj : G.Adj e.out.1 e.out.2 := by
    rw [← G.mem_edgeSet, Sym2.mk, e.out_eq]
    exact SimpleGraph.mem_edgeFinset.mp he
  let : Nontrivial (Fin (componentCode H c).vertexCount) := hadj.nontrivial
  intro v
  exact (componentCode_connected H c).preconnected.not_isIsolated v

/-- If the original graph has no isolated vertices, the union of all
components other than `c` has no isolated vertices as well. -/
theorem componentRemainderCode_noIsolated {H : GraphCode}
    (hH : NoIsolated H) (c : H.graph.ConnectedComponent) :
    NoIsolated (componentRemainderCode H c) := by
  intro v
  apply (componentRemainderCode H c).graph.exists_adj_iff_not_isIsolated.mp
  change ∃ u, (inducedCode H ((componentVertices H c)ᶜ)).graph.Adj v u
  let S : Set (Fin H.vertexCount) :=
    ((componentVertices H c)ᶜ : Finset (Fin H.vertexCount))
  let e := inducedCodeIso H (componentVertices H c)ᶜ
  let x : S :=
    ⟨(e.symm v).1, by simpa [S] using (e.symm v).2⟩
  obtain ⟨y, hxy⟩ := H.graph.exists_adj_iff_not_isIsolated.mpr (hH x.1)
  have hy : y ∈ (componentVertices H c)ᶜ := by
    rw [mem_componentVertices_compl]
    intro hyc
    have hxc : x.1 ∈ c.supp :=
      c.mem_supp_of_adj_mem_supp hyc hxy.symm
    exact (mem_componentVertices_compl.mp x.2) hxc
  let y' : S := ⟨y, by simpa [S] using hy⟩
  refine ⟨e y', ?_⟩
  have hxy' : (H.graph.induce S).Adj x y' := hxy
  have hex : e x = v := by
    have hx : x = e.symm v := Subtype.ext rfl
    rw [hx]
    exact e.apply_symm_apply v
  rw [← hex]
  exact e.toHom.map_adj (by simpa [S] using hxy')

/-- A connected component with `q` edges has at most `q+1` vertices. -/
theorem componentCode_vertexCount_le_edgeCount_add_one (H : GraphCode)
    (c : H.graph.ConnectedComponent) :
    (componentCode H c).vertexCount ≤ (componentCode H c).edgeCount + 1 := by
  simpa [GraphCode.edgeCount] using
    (componentCode_connected H c).card_vert_le_card_edgeSet_add_one

/-- A copy between coded graphs with the same vertex and edge counts is an
isomorphism.  Equality of edge counts upgrades the bijective homomorphism to
reflection of adjacency. -/
theorem isomorphic_of_isContained_of_counts {F G : GraphCode}
    (hFG : IsContained F G) (hV : F.vertexCount = G.vertexCount)
    (hE : F.edgeCount = G.edgeCount) : Isomorphic F G := by
  classical
  obtain ⟨copy⟩ := hFG
  have hvertexBij : Function.Bijective copy :=
    (Fintype.bijective_iff_injective_and_card copy).mpr
      ⟨copy.injective, by simp [hV]⟩
  let ev : Fin F.vertexCount ≃ Fin G.vertexCount :=
    Equiv.ofBijective copy hvertexBij
  have hedgeBij : Function.Bijective copy.mapEdgeSet :=
    (Nat.bijective_iff_injective_and_card copy.mapEdgeSet).mpr
      ⟨copy.mapEdgeSet.injective, hE⟩
  refine ⟨{
    toEquiv := ev
    map_rel_iff' := ?_ }⟩
  intro u v
  constructor
  · intro huv
    let b : G.graph.edgeSet := ⟨s(ev u, ev v), by
      simpa [SimpleGraph.mem_edgeSet] using huv⟩
    obtain ⟨a, ha⟩ := hedgeBij.surjective b
    have hamap : a.1.map copy = s(ev u, ev v) :=
      congrArg Subtype.val ha
    have haeq : a.1 = s(u, v) := by
      apply Sym2.map.injective copy.injective
      simpa [ev] using hamap
    rw [← F.graph.mem_edgeSet, ← haeq]
    exact a.2
  · intro huv
    simpa [ev] using copy.toHom.map_adj huv

/-- Every connected component of an isolate-free graph contains an edge. -/
theorem componentCode_edgeCount_pos_of_noIsolated {H : GraphCode}
    (hH : NoIsolated H) (c : H.graph.ConnectedComponent) :
    0 < (componentCode H c).edgeCount := by
  classical
  let e := componentCodeIso H c
  let x : c.supp := ⟨c.out, c.out_eq⟩
  obtain ⟨y, hxy⟩ := H.graph.exists_adj_iff_not_isIsolated.mpr (hH x.1)
  have hy : y ∈ c.supp := c.mem_supp_of_adj_mem_supp x.2 hxy
  let y' : c.supp := ⟨y, hy⟩
  have hadj : (componentCode H c).graph.Adj (e x) (e y') :=
    e.toHom.map_adj hxy
  let : DecidableRel (componentCode H c).graph.Adj :=
    Classical.decRel (componentCode H c).graph.Adj
  rw [GraphCode.edgeCount_eq_card_edgeFinset, Finset.card_pos]
  refine ⟨s(e x, e y'), ?_⟩
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  exact hadj

/-- If one component contains every edge of an isolate-free graph, then it
contains every vertex and the graph is connected. -/
theorem connected_of_component_edgeCount_eq {H : GraphCode}
    (hH : NoIsolated H) (c : H.graph.ConnectedComponent)
    (hc : (componentCode H c).edgeCount = H.edgeCount) :
    H.graph.Connected := by
  have hall : ∀ v : Fin H.vertexCount, v ∈ c.supp := by
    intro v
    by_contra hv
    let d := H.graph.connectedComponentMk v
    have hdpos := componentCode_edgeCount_pos_of_noIsolated hH d
    have hdle : (componentCode H d).edgeCount ≤
        (componentRemainderCode H c).edgeCount := by
      apply IsContained.edgeCount_le
      let S : Set (Fin H.vertexCount) := componentVertices H c
      let T : Set (Fin H.vertexCount) :=
        ((componentVertices H c)ᶜ : Finset (Fin H.vertexCount))
      let ed := inducedCodeIso H (componentVertices H d)
      let er := inducedCodeIso H (componentVertices H c)ᶜ
      let hom : (componentCode H d).graph →g
          (componentRemainderCode H c).graph :=
        { toFun := fun x ↦ er ⟨(ed.symm x).1, by
              have hxd : (ed.symm x).1 ∈ d.supp :=
                mem_componentVertices.mp (ed.symm x).2
              have hxnot : (ed.symm x).1 ∉ c.supp := by
                intro hxc
                have hdc : d = c :=
                  SimpleGraph.ConnectedComponent.eq_of_common_vertex hxd hxc
                exact hv (by simpa [d, hdc] using hxd)
              simpa using hxnot⟩
          map_rel' := by
            intro x y hxy
            exact er.toHom.map_adj (ed.symm.toHom.map_adj hxy) }
      refine ⟨hom.toCopy ?_⟩
      intro x y hxy
      change er _ = er _ at hxy
      have hsub := er.injective hxy
      have hval : (ed.symm x).1 = (ed.symm y).1 :=
        congrArg (fun z ↦ z.1) hsub
      apply ed.symm.injective
      exact Subtype.ext hval
    have hsplit := componentCode_edgeCount_add_remainder H c
    have hremzero : (componentRemainderCode H c).edgeCount = 0 := by omega
    omega
  exact
    { preconnected := by
        intro u v
        exact c.reachable_of_mem_supp (hall u) (hall v)
      nonempty := ⟨c.out⟩ }

end Erdos570
