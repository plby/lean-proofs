import ErdosProblems.Erdos556.FiniteMatching
import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Correspondence with Mathlib subgraph matchings

The edge sets and supports are preserved. This allows the finite augmentation
tools to use Mathlib's alternating-cycle machinery without an assumed theorem.
-/

namespace Erdos556

open SimpleGraph Finset

def EdgeMatching.toSubgraph {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {M : Finset (Sym2 V)} (hM : EdgeMatching G M) : G.Subgraph where
  verts := matchingSupport M
  Adj u v := s(u, v) ∈ M
  adj_sub h := hM.1 _ h
  edge_vert h := matchingSupport_mem.mpr ⟨_, h, Sym2.mem_mk_left _ _⟩
  symm := ⟨fun _ _ h => by simpa only [Sym2.eq_swap] using h⟩

theorem EdgeMatching.toSubgraph_isMatching {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {M : Finset (Sym2 V)} (hM : EdgeMatching G M) :
    hM.toSubgraph.IsMatching := by
  intro u hu
  obtain ⟨e, he, hue⟩ := matchingSupport_mem.mp hu
  obtain ⟨v, rfl⟩ := Sym2.mem_iff_exists.mp hue
  refine ⟨v, he, ?_⟩
  intro w hw
  have heq : s(u, w) = s(u, v) := by
    by_contra hne
    exact Finset.disjoint_left.mp (hM.2 _ hw _ he hne)
      (Sym2.mem_toFinset.mpr (Sym2.mem_mk_left _ _))
      (Sym2.mem_toFinset.mpr (Sym2.mem_mk_left _ _))
  rcases Sym2.eq_iff.mp heq with h | h
  · exact h.2
  · exact h.2.trans h.1

theorem EdgeMatching.toSubgraph_edgeSet {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {M : Finset (Sym2 V)} (hM : EdgeMatching G M) :
    hM.toSubgraph.edgeSet = (M : Set (Sym2 V)) := by
  ext e
  exact Sym2.inductionOn e (fun _ _ => Iff.rfl)

open scoped Classical in
theorem EdgeMatching.toSubgraph_edgeFinset {V : Type*} [Fintype V]
    {G : SimpleGraph V} {M : Finset (Sym2 V)} (hM : EdgeMatching G M) :
    hM.toSubgraph.spanningCoe.edgeFinset = M := by
  ext e
  rw [mem_edgeFinset, Subgraph.edgeSet_spanningCoe, hM.toSubgraph_edgeSet]
  rfl

open scoped Classical in
theorem edgeMatching_of_subgraphMatching {V : Type*} [Fintype V]
    {G : SimpleGraph V} (M : G.Subgraph) (hM : M.IsMatching) :
    EdgeMatching G M.spanningCoe.edgeFinset := by
  classical
  constructor
  · intro e he
    exact M.edgeSet_subset (mem_edgeFinset.mp he)
  · intro e he f hf hne
    apply Finset.disjoint_left.mpr
    intro u hue huf
    obtain ⟨v, rfl⟩ := Sym2.mem_iff_exists.mp (Sym2.mem_toFinset.mp hue)
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp (Sym2.mem_toFinset.mp huf)
    have huv : M.Adj u v := mem_edgeFinset.mp he
    have huw : M.Adj u w := mem_edgeFinset.mp hf
    exact hne (congrArg (fun x => s(u, x)) (hM.eq_of_adj_left huv huw))

open scoped Classical in
theorem matchingSupport_of_subgraphMatching {V : Type*} [Fintype V]
    {G : SimpleGraph V} (M : G.Subgraph) (hM : M.IsMatching) :
    (matchingSupport M.spanningCoe.edgeFinset : Set V) = M.verts := by
  classical
  ext u
  constructor
  · intro hu
    obtain ⟨e, he, hue⟩ := matchingSupport_mem.mp hu
    exact M.mem_verts_of_mem_edge (mem_edgeFinset.mp he) hue
  · intro hu
    obtain ⟨v, huv, _⟩ := hM hu
    exact matchingSupport_mem.mpr ⟨s(u, v), mem_edgeFinset.mpr huv, Sym2.mem_mk_left _ _⟩

end Erdos556
