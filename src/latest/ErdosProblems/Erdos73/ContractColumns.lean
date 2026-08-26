/- Connected column images under one edge contraction. -/
import ErdosProblems.Erdos73.EdgeContraction

namespace Erdos73Infrastructure.SimpleGraph.TreewidthSparsifier
variable {V : Type*} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {a b : V}

theorem mem_edgeContractImageSet_iff {Q : Finset V} {z : EdgeContractVertex V a b} :
    z ∈ edgeContractImageSet (a := a) (b := b) Q ↔
      ∃ x ∈ Q, EdgeContractVertex.projection (u := a) (v := b) x = z := by
  classical
  simp only [edgeContractImageSet, Finset.mem_image, Finset.mem_attach,
    true_and, Subtype.exists, exists_prop]

theorem edgeContractImageSet_nonempty {Q : Finset V} (hQ : Q.Nonempty) :
    (edgeContractImageSet (a := a) (b := b) Q).Nonempty := by
  obtain ⟨x, hx⟩ := hQ
  exact ⟨_, mem_edgeContractImageSet_projection hx⟩

theorem edgeContractImageSet_mono {Q R : Finset V} (h : Q ⊆ R) :
    edgeContractImageSet (a := a) (b := b) Q ⊆
      edgeContractImageSet (a := a) (b := b) R := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := mem_edgeContractImageSet_iff.mp hz
  exact mem_edgeContractImageSet_projection (h hx)

/-- Contracting inside one column cannot merge two disjoint columns. -/
theorem edgeContractImageSet_pairwise_disjoint {I : Type*} (Q : I → Finset V)
    (hdis : Pairwise fun i j => Disjoint (Q i) (Q j)) (i₀ : I)
    (ha : a ∈ Q i₀) (hb : b ∈ Q i₀) :
    Pairwise fun i j => Disjoint
      (edgeContractImageSet (a := a) (b := b) (Q i))
      (edgeContractImageSet (a := a) (b := b) (Q j)) := by
  intro i j hij
  rw [Finset.disjoint_left]
  intro z hzi hzj
  obtain ⟨x, hx, hxz⟩ := mem_edgeContractImageSet_iff.mp hzi
  obtain ⟨y, hy, hyz⟩ := mem_edgeContractImageSet_iff.mp hzj
  rcases EdgeContractVertex.eq_or_endpoint_pair_of_projection_eq
      (hxz.trans hyz.symm) with hxy | ⟨hxend, hyend⟩
  · subst y
    exact Finset.disjoint_left.mp (hdis hij) hx hy
  · have hxi₀ : x ∈ Q i₀ := hxend.elim (fun h => h.symm ▸ ha) (fun h => h.symm ▸ hb)
    have hyi₀ : y ∈ Q i₀ := hyend.elim (fun h => h.symm ▸ ha) (fun h => h.symm ▸ hb)
    have hi : i = i₀ := by
      by_contra h
      exact Finset.disjoint_left.mp (hdis h) hx hxi₀
    have hj : j = i₀ := by
      by_contra h
      exact Finset.disjoint_left.mp (hdis h) hy hyi₀
    exact hij (hi.trans hj.symm)

/-- The finite image of a connected column is still connected. -/
theorem edgeContractImageSet_connected (hab : G.Adj a b) (Q : Finset V)
    (hQ : (G.induce {x | x ∈ Q}).Connected) :
    ((contractEdgeGraph G hab).induce
      {z | z ∈ edgeContractImageSet (a := a) (b := b) Q}).Connected := by
  classical
  let C := edgeContractImageSet (a := a) (b := b) Q
  obtain ⟨q⟩ := hQ.nonempty
  change ((contractEdgeGraph G hab).induce {z | z ∈ C}).Connected
  letI : Nonempty ↑({z | z ∈ C} : Set (EdgeContractVertex V a b)) :=
    ⟨⟨_, mem_edgeContractImageSet_projection q.property⟩⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨s, hs, hsx⟩ := mem_edgeContractImageSet_iff.mp x.property
  obtain ⟨t, ht, hty⟩ := mem_edgeContractImageSet_iff.mp y.property
  let R := GraphPath.ofConnectedInduce Q hQ s t hs ht
  let P := contractEdgeGraph.ProjectionWalk.toGraphPath (huv := hab) R
  have hPC : P.vertexSet ⊆ C := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ :=
      contractEdgeGraph.ProjectionWalk.toGraphPath_vertexSet_subset_projection
        (huv := hab) R z hz
    exact mem_edgeContractImageSet_projection
      (GraphPath.ofConnectedInduce_vertexSet_subset Q hQ s t hs ht hv)
  have hsource : (P.induce C hPC).source = x := Subtype.ext hsx
  have htarget : (P.induce C hPC).target = y := Subtype.ext hty
  exact ⟨(P.induce C hPC).walk.copy hsource htarget⟩

end Erdos73Infrastructure.SimpleGraph.TreewidthSparsifier
