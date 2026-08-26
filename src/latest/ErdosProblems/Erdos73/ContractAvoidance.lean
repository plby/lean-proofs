/- Lift a linkage avoiding a contracted column back to the original graph. -/
import ErdosProblems.Erdos73.ContractColumns
import ErdosProblems.Erdos73.MinorPathLifting

namespace Erdos73Infrastructure.SimpleGraph.TreewidthSparsifier
variable {V : Type*} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {a b : V}

theorem exists_preimage_mem_sdiff {A Q : Finset V} {z : EdgeContractVertex V a b}
    (hz : z ∈ edgeContractImageSet (a := a) (b := b) A \ edgeContractImageSet Q) :
    ∃ x ∈ A \ Q, EdgeContractVertex.projection (u := a) (v := b) x = z := by
  obtain ⟨hzA, hzQ⟩ := Finset.mem_sdiff.mp hz
  obtain ⟨x, hxA, hxz⟩ := mem_edgeContractImageSet_iff.mp hzA
  refine ⟨x, Finset.mem_sdiff.mpr ⟨hxA, ?_⟩, hxz⟩
  intro hxQ
  exact hzQ (hxz ▸ mem_edgeContractImageSet_projection hxQ)

/-- Avoiding paths lift with exactly the same cardinality; no closure
assumption on the deleted set under contraction fibers is needed. -/
theorem exists_lift_avoiding (hab : G.Adj a b) (A B Q : Finset V)
    (P : PathPacking (contractEdgeGraph G hab)
      (edgeContractImageSet (a := a) (b := b) A \ edgeContractImageSet Q)
      (edgeContractImageSet (a := a) (b := b) B \ edgeContractImageSet Q))
    (hP : ∀ i, Disjoint (P.path i).vertexSet (edgeContractImageSet Q)) :
    ∃ R : PathPacking G (A \ Q) (B \ Q), R.card = P.card ∧
      ∀ i, Disjoint (R.path i).vertexSet Q := by
  classical
  have hs : ∀ i : P.Index, ∃ x ∈ A \ Q,
      EdgeContractVertex.projection (u := a) (v := b) x = (P.orient.path i).source := by
    intro i
    exact exists_preimage_mem_sdiff
      (GraphPath.orient_source_mem (P.path i) (P.connects i))
  have ht : ∀ i : P.Index, ∃ x ∈ B \ Q,
      EdgeContractVertex.projection (u := a) (v := b) x = (P.orient.path i).target := by
    intro i
    exact exists_preimage_mem_sdiff
      (GraphPath.orient_target_mem (P.path i) (P.connects i))
  choose s hs hsproj using hs
  choose t ht htproj using ht
  let M := contractEdgeGraph.minorModel (G := G) (huv := hab)
  have hsbranch : ∀ i, s i ∈ M.branchSet (P.orient.path i).source := by
    intro i
    rw [← hsproj i]
    exact EdgeContractVertex.mem_branchSet_projection (s i)
  have htbranch : ∀ i, t i ∈ M.branchSet (P.orient.path i).target := by
    intro i
    rw [← htproj i]
    exact EdgeContractVertex.mem_branchSet_projection (t i)
  have hc : ∀ i, (s i ∈ A \ Q ∧ t i ∈ B \ Q) ∨ (s i ∈ B \ Q ∧ t i ∈ A \ Q) :=
    fun i => Or.inl ⟨hs i, ht i⟩
  refine ⟨M.liftPacking P.orient s t hsbranch htbranch hc, rfl, ?_⟩
  intro i
  rw [Finset.disjoint_left]
  intro x hx hxQ
  have hxproj := M.liftPacking_vertex_mem P.orient s t hsbranch htbranch hc i
    (EdgeContractVertex.mem_branchSet_projection x) hx
  have hxP : EdgeContractVertex.projection (u := a) (v := b) x ∈
      (P.path i).vertexSet := by
    change _ ∈ ((P.path i).orient (P.connects i)).vertexSet at hxproj
    rw [GraphPath.orient_vertexSet] at hxproj
    exact hxproj
  exact Finset.disjoint_left.mp (hP i) hxP (mem_edgeContractImageSet_projection hxQ)

end Erdos73Infrastructure.SimpleGraph.TreewidthSparsifier
