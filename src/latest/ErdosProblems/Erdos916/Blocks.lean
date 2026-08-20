import ErdosProblems.Erdos916.Core

/-!
# Cut vertices and end pieces for Erdős Problem 916

The Thomassen--Toft induction passes from a connected graph which is not
2-connected to an endblock avoiding the distinguished exceptional vertex.
For that induction one only needs the following concrete incarnation of an
endblock: choose a cut vertex `c` and a connected component of `G - c`, then
put `c` back.  Every vertex of the chosen component has all its neighbours in
this end piece, so its degree is unchanged in the induced graph.

This file also records finite definitions of nonseparable vertex sets, blocks,
and endblocks.  In accordance with the standard block convention, a bridge is
explicitly admitted as a two-vertex block.
-/

open Finset

attribute [local instance] Classical.propDecidable

namespace Erdos916

open SimpleGraph

universe u

variable {V : Type u} (G : SimpleGraph V)

/-! ## Cut vertices -/

/-- The graph obtained by deleting a vertex. -/
def deleteVertex (c : V) : SimpleGraph {v : V // v ≠ c} :=
  G.induce {v | v ≠ c}

@[simp] theorem deleteVertex_adj {c : V} {u v : {v : V // v ≠ c}} :
    (deleteVertex G c).Adj u v ↔ G.Adj u.1 v.1 :=
  Iff.rfl

/-- A cut vertex is a vertex whose deletion is not preconnected.  Using
`Preconnected` rather than `Connected` makes the definition correct for graphs
of order one: the empty and one-vertex graphs are preconnected.  In the uses
below the ambient graph is connected. -/
def IsCutVertex (c : V) : Prop := ¬(deleteVertex G c).Preconnected

theorem isCutVertex_iff_exists_not_reachable (c : V) :
    IsCutVertex G c ↔
      ∃ u v : {v : V // v ≠ c}, ¬(deleteVertex G c).Reachable u v := by
  simp only [IsCutVertex, SimpleGraph.Preconnected, not_forall]

/-! ## Nonseparable sets, blocks, and endblocks -/

/-- A vertex set is nonseparable when it induces a connected graph and remains
connected after any one of its vertices is deleted. -/
def NonseparableOn (S : Set V) : Prop :=
  (G.induce S).Connected ∧
    ∀ v, v ∈ S → (G.induce (S \ {v})).Connected

/-- A finite block.  The first alternative records the standard convention
that a bridge itself is a `K₂` block.  The second alternative is a maximal
nonseparable induced vertex set of order at least three. -/
def IsBlock [DecidableEq V] (B : Finset V) : Prop :=
  (∃ u v, G.IsBridge s(u, v) ∧ B = {u, v}) ∨
    (3 ≤ #B ∧ NonseparableOn G (B : Set V) ∧
      ∀ C : Finset V, 3 ≤ #C → NonseparableOn G (C : Set V) →
        B ⊆ C → C ⊆ B)

/-- An endblock has at most one vertex through which edges can leave it.  This
formulation is the useful one for the degree-preserving induction. -/
def IsEndBlock [DecidableEq V] (B : Finset V) : Prop :=
  IsBlock G B ∧
    ∃ c ∈ B, ∀ v ∈ B, v ≠ c → G.neighborSet v ⊆ (B : Set V)

theorem IsBridge.isBlock [DecidableEq V] {u v : V} (h : G.IsBridge s(u, v)) :
    IsBlock G {u, v} := by
  exact Or.inl ⟨u, v, h, rfl⟩

theorem IsEndBlock.neighborSet_subset [DecidableEq V] {B : Finset V}
    (hB : IsEndBlock G B) :
    ∃ c ∈ B, ∀ v ∈ B, v ≠ c → G.neighborSet v ⊆ (B : Set V) :=
  hB.2

/-! ## Component end pieces -/

namespace ComponentEndBlock

variable {G}

/-- The vertices in a connected component of `G - c`, regarded as vertices of
the original graph. -/
def side (c : V) (K : (deleteVertex G c).ConnectedComponent) : Set V :=
  {v | ∃ hvc : v ≠ c, (⟨v, hvc⟩ : {w : V // w ≠ c}) ∈ K.supp}

/-- Put the deleted cut vertex back into a component of `G - c`. -/
def verts (c : V) (K : (deleteVertex G c).ConnectedComponent) : Set V :=
  insert c (side c K)

@[simp] theorem mem_side_iff {c : V}
    {K : (deleteVertex G c).ConnectedComponent} {v : V} :
    v ∈ side c K ↔
      ∃ hvc : v ≠ c, (⟨v, hvc⟩ : {w : V // w ≠ c}) ∈ K.supp :=
  Iff.rfl

@[simp] theorem cut_not_mem_side (c : V)
    (K : (deleteVertex G c).ConnectedComponent) : c ∉ side c K := by
  rintro ⟨h, -⟩
  exact h rfl

theorem side_nonempty (c : V)
    (K : (deleteVertex G c).ConnectedComponent) : (side c K).Nonempty := by
  obtain ⟨⟨v, hvc⟩, hvK⟩ := K.nonempty_supp
  exact ⟨v, hvc, hvK⟩

private def sideHom (c : V) (K : (deleteVertex G c).ConnectedComponent) :
    K.toSimpleGraph →g G.induce (side c K) where
  toFun v := ⟨v.1.1, v.1.2, v.2⟩
  map_rel' h := h

private theorem sideHom_surjective (c : V)
    (K : (deleteVertex G c).ConnectedComponent) :
    Function.Surjective (sideHom c K) := by
  rintro ⟨v, hv⟩
  obtain ⟨hvc, hvK⟩ := hv
  exact ⟨⟨⟨v, hvc⟩, hvK⟩, rfl⟩

/-- A component side induces a connected graph in the original graph. -/
theorem side_connected (c : V)
    (K : (deleteVertex G c).ConnectedComponent) :
    (G.induce (side c K)).Connected :=
  K.connected_toSimpleGraph.map (sideHom c K) (sideHom_surjective c K)

/-- No edge can leave a component of `G - c` except through `c`. -/
theorem neighborSet_subset_verts {c : V}
    (K : (deleteVertex G c).ConnectedComponent) {v : V}
    (hv : v ∈ side c K) : G.neighborSet v ⊆ verts c K := by
  intro w hvw
  by_cases hwc : w = c
  · simp [verts, hwc]
  · have hvc : v ≠ c := by
      rintro rfl
      obtain ⟨h, -⟩ := hv
      exact h rfl
    have hadj : (deleteVertex G c).Adj ⟨v, hvc⟩ ⟨w, hwc⟩ := hvw
    have hvK : (⟨v, hvc⟩ : {x : V // x ≠ c}) ∈ K.supp := by
      obtain ⟨hvc', hvK⟩ := hv
      simpa only [Subtype.coe_eta] using hvK
    have hwK : (⟨w, hwc⟩ : {x : V // x ≠ c}) ∈ K.supp :=
      K.mem_supp_of_adj_mem_supp hvK hadj
    exact Set.mem_insert_iff.mpr <| Or.inr ⟨hwc, hwK⟩

private theorem exists_attachment (hG : G.Connected) {c : V}
    (K : (deleteVertex G c).ConnectedComponent) :
    ∃ v, v ∈ side c K ∧ G.Adj c v := by
  obtain ⟨⟨v, hvc⟩, hvK⟩ := K.nonempty_supp
  obtain ⟨p⟩ := hG v c
  let rec firstExit {w : V} (hwc : w ≠ c)
      (hwK : (⟨w, hwc⟩ : {x : V // x ≠ c}) ∈ K.supp)
      (q : G.Walk w c) : ∃ z, z ∈ side c K ∧ G.Adj c z := by
    cases q with
    | nil => exact False.elim (hwc rfl)
    | @cons _ z _ hwz q =>
        by_cases hzc : z = c
        · subst z
          exact ⟨w, ⟨hwc, hwK⟩, hwz.symm⟩
        · have hadj : (deleteVertex G c).Adj ⟨w, hwc⟩ ⟨z, hzc⟩ := hwz
          have hzK : (⟨z, hzc⟩ : {x : V // x ≠ c}) ∈ K.supp :=
            K.mem_supp_of_adj_mem_supp hwK hadj
          exact firstExit hzc hzK q
  termination_by q.length
  exact firstExit hvc hvK p

/-- Putting `c` back into any component of `G - c` gives a connected induced
subgraph. -/
theorem verts_connected (hG : G.Connected) {c : V}
    (K : (deleteVertex G c).ConnectedComponent) :
    (G.induce (verts c K)).Connected := by
  obtain ⟨v, hv, hcv⟩ := exists_attachment hG K
  rw [verts, Set.insert_eq]
  exact G.connected_induce_union (s := ({c} : Set V)) (t := side c K)
    (SimpleGraph.Preconnected.of_subsingleton)
    (side_connected c K).preconnected (by simp) hv hcv

/-- Vertices on the component side retain their ambient degree in the induced
end piece. -/
theorem degree_induce_verts [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {c v : V}
    (K : (deleteVertex G c).ConnectedComponent) (hv : v ∈ side c K) :
    (G.induce (verts c K)).degree ⟨v, Set.mem_insert_iff.mpr (Or.inr hv)⟩ =
      G.degree v := by
  classical
  exact G.degree_induce_of_neighborSet_subset
    (neighborSet_subset_verts (G := G) K hv)

/-- The distinguished exceptional vertex can be avoided on the component side
of some end piece.  If it is the cut vertex itself, this is automatic. -/
theorem exists_component_avoiding (c x₀ : V) (hc : IsCutVertex G c) :
    ∃ K : (deleteVertex G c).ConnectedComponent,
      x₀ = c ∨ x₀ ∉ side c K := by
  by_cases hxc : x₀ = c
  · obtain ⟨u, v, huv⟩ := (isCutVertex_iff_exists_not_reachable G c).mp hc
    exact ⟨(deleteVertex G c).connectedComponentMk u, Or.inl hxc⟩
  · obtain ⟨u, v, huv⟩ := (isCutVertex_iff_exists_not_reachable G c).mp hc
    let x' : {v : V // v ≠ c} := ⟨x₀, hxc⟩
    have huvcomp :
        (deleteVertex G c).connectedComponentMk u ≠
          (deleteVertex G c).connectedComponentMk v := by
      intro h
      exact huv (SimpleGraph.ConnectedComponent.exact h)
    by_cases hxu :
        (deleteVertex G c).connectedComponentMk x' =
          (deleteVertex G c).connectedComponentMk u
    · refine ⟨(deleteVertex G c).connectedComponentMk v, Or.inr ?_⟩
      rintro ⟨hxne, hxmem⟩
      have hxv :
          (deleteVertex G c).connectedComponentMk x' =
            (deleteVertex G c).connectedComponentMk v := by
        simpa [SimpleGraph.ConnectedComponent.mem_supp_iff] using hxmem
      exact huvcomp (hxu.symm.trans hxv)
    · refine ⟨(deleteVertex G c).connectedComponentMk u, Or.inr ?_⟩
      rintro ⟨hxne, hxmem⟩
      apply hxu
      simpa [SimpleGraph.ConnectedComponent.mem_supp_iff] using hxmem

/-- The component in `exists_component_avoiding` can be chosen so that putting
the cut vertex back still gives a proper vertex set. -/
theorem exists_component_avoiding_proper (c x₀ : V) (hc : IsCutVertex G c) :
    ∃ K : (deleteVertex G c).ConnectedComponent,
      (x₀ = c ∨ x₀ ∉ side c K) ∧ verts c K ≠ Set.univ := by
  by_cases hxc : x₀ = c
  · obtain ⟨u, v, huv⟩ := (isCutVertex_iff_exists_not_reachable G c).mp hc
    let K := (deleteVertex G c).connectedComponentMk u
    refine ⟨K, Or.inl hxc, ?_⟩
    intro hfull
    have hvverts : v.1 ∈ verts c K := by rw [hfull]; exact Set.mem_univ v.1
    rw [verts, Set.mem_insert_iff] at hvverts
    rcases hvverts with hvc | hvside
    · exact v.2 hvc
    · obtain ⟨hvc', hvK⟩ := hvside
      have hvK' :
          (⟨v.1, hvc'⟩ : {x : V // x ≠ c}) ∈ K.supp := hvK
      have hcomp :
          (deleteVertex G c).connectedComponentMk v =
            (deleteVertex G c).connectedComponentMk u := by
        simpa only [K, SimpleGraph.ConnectedComponent.mem_supp_iff,
          Subtype.coe_eta] using hvK'
      exact huv (SimpleGraph.ConnectedComponent.exact hcomp.symm)
  · obtain ⟨K, havoid⟩ := exists_component_avoiding (G := G) c x₀ hc
    have hxside : x₀ ∉ side c K := havoid.resolve_left hxc
    refine ⟨K, havoid, ?_⟩
    intro hfull
    apply hxside
    have hxverts : x₀ ∈ verts c K := by rw [hfull]; exact Set.mem_univ x₀
    rw [verts, Set.mem_insert_iff] at hxverts
    exact hxverts.resolve_left hxc

/-- In a finite graph, a proper component end piece has strictly fewer
vertices than the ambient graph. -/
theorem card_verts_lt [Fintype V] {c : V}
    (K : (deleteVertex G c).ConnectedComponent) (hproper : verts c K ≠ Set.univ) :
    Fintype.card {v // v ∈ verts c K} < Fintype.card V := by
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem (verts c K)).mp hproper
  exact Fintype.card_subtype_lt hx

/-- **Endblock reduction N1.**  In a connected graph, a cut vertex yields a
proper connected end piece whose component side avoids the distinguished
exceptional vertex and whose non-cut vertices have no neighbours outside the
piece. -/
theorem endblock_reduction_N1 (hG : G.Connected) (c x₀ : V)
    (hc : IsCutVertex G c) :
    ∃ K : (deleteVertex G c).ConnectedComponent,
      (x₀ = c ∨ x₀ ∉ side c K) ∧
      verts c K ≠ Set.univ ∧
      (G.induce (verts c K)).Connected ∧
      (∀ v, v ∈ side c K → G.neighborSet v ⊆ verts c K) := by
  obtain ⟨K, havoid, hproper⟩ := exists_component_avoiding_proper (G := G) c x₀ hc
  exact ⟨K, havoid, hproper, verts_connected hG K,
    fun _ hv ↦ neighborSet_subset_verts K hv⟩

end ComponentEndBlock

end Erdos916
