/-
Single-edge contraction of disjoint linkages. The projection argument follows
the independently proved contraction lemmas in the Apache-2.0 source
polynomial-grid-minor-theorem, commit fe2848173913a00d85c64d2a17af63f2cf0d4fbf,
PseudoGridReduction.lean. Here one no-split condition subsumes the same-path
and unused-endpoint cases, and perfectness follows from endpoint surjectivity.
-/
import ErdosProblems.Erdos73.EdgeContraction
import ErdosProblems.Erdos73.MinorPathLifting

namespace Erdos73Infrastructure.SimpleGraph
open TreewidthSparsifier
variable {V : Type*} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {A B : Finset V} {a b : V}

namespace PathPacking

/-- Contraction must not merge vertices of two different linkage members. -/
def NoSplitAcross (P : PathPacking G A B) (a b : V) : Prop :=
  ∀ i j, a ∈ (P.path i).vertexSet → b ∈ (P.path j).vertexSet → i = j

theorem noSplitAcross_of_samePath (P : PathPacking G A B) (i₀ : P.Index)
    (ha : a ∈ (P.path i₀).vertexSet) (hb : b ∈ (P.path i₀).vertexSet) :
    P.NoSplitAcross a b := by
  intro i j hi hj
  have hii : i = i₀ := by
    by_contra h
    exact Finset.disjoint_left.mp (P.node_disjoint h) hi ha
  have hji : j = i₀ := by
    by_contra h
    exact Finset.disjoint_left.mp (P.node_disjoint h) hj hb
  exact hii.trans hji.symm

theorem noSplitAcross_of_left_unused (P : PathPacking G A B)
    (ha : a ∉ P.vertexSet) : P.NoSplitAcross a b := by
  intro i j hi _
  exact (ha (P.mem_vertexSet.mpr ⟨i, hi⟩)).elim

theorem noSplitAcross_of_right_unused (P : PathPacking G A B)
    (hb : b ∉ P.vertexSet) : P.NoSplitAcross a b := by
  intro i j _ hj
  exact (hb (P.mem_vertexSet.mpr ⟨j, hj⟩)).elim

/-- Projection through an edge contraction with no collision between rows. -/
noncomputable def contractEdge (P : PathPacking G A B) (hab : G.Adj a b)
    (hP : P.NoSplitAcross a b) :
    PathPacking (contractEdgeGraph G hab)
      (edgeContractImageSet (a := a) (b := b) A)
      (edgeContractImageSet (a := a) (b := b) B) where
  Index := P.Index
  path i := contractEdgeGraph.ProjectionWalk.toGraphPath (huv := hab) (P.path i)
  connects := by
    intro i
    rcases P.connects i with h | h
    · exact Or.inl ⟨mem_edgeContractImageSet_projection h.1,
        mem_edgeContractImageSet_projection h.2⟩
    · exact Or.inr ⟨mem_edgeContractImageSet_projection h.1,
        mem_edgeContractImageSet_projection h.2⟩
  node_disjoint := by
    intro i j hij
    rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
    intro z hzi hzj
    obtain ⟨x, hx, hxz⟩ :=
      contractEdgeGraph.ProjectionWalk.toGraphPath_vertexSet_subset_projection
        (huv := hab) (P.path i) z hzi
    obtain ⟨y, hy, hyz⟩ :=
      contractEdgeGraph.ProjectionWalk.toGraphPath_vertexSet_subset_projection
        (huv := hab) (P.path j) z hzj
    rcases EdgeContractVertex.eq_or_endpoint_pair_of_projection_eq
        (hxz.trans hyz.symm) with hxy | ⟨hxend, hyend⟩
    · subst y
      exact Finset.disjoint_left.mp (P.node_disjoint hij) hx hy
    · rcases hxend with rfl | rfl <;> rcases hyend with rfl | rfl
      · exact Finset.disjoint_left.mp (P.node_disjoint hij) hx hy
      · exact hij (hP i j hx hy)
      · exact hij (hP j i hy hx).symm
      · exact Finset.disjoint_left.mp (P.node_disjoint hij) hx hy

@[simp] theorem contractEdge_card (P : PathPacking G A B) (hab : G.Adj a b)
    (hP : P.NoSplitAcross a b) : (P.contractEdge hab hP).card = P.card := rfl

theorem contractEdge_vertexSet_subset (P : PathPacking G A B) (hab : G.Adj a b)
    (hP : P.NoSplitAcross a b) (i : P.Index) :
    ((P.contractEdge hab hP).path i).vertexSet ⊆
      edgeContractImageSet (a := a) (b := b) (P.path i).vertexSet := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ :=
    contractEdgeGraph.ProjectionWalk.toGraphPath_vertexSet_subset_projection
      (huv := hab) (P.path i) z hz
  exact mem_edgeContractImageSet_projection hx

end PathPacking

namespace PerfectPathPacking

/-- A perfect linkage remains perfect under every no-split contraction. -/
noncomputable def contractEdge (P : PerfectPathPacking G A B) (hab : G.Adj a b)
    (hP : P.toPathPacking.NoSplitAcross a b) :
    PerfectPathPacking (contractEdgeGraph G hab)
      (edgeContractImageSet (a := a) (b := b) A)
      (edgeContractImageSet (a := a) (b := b) B) where
  toPathPacking := P.toPathPacking.contractEdge hab hP
  source_mem i := mem_edgeContractImageSet_projection (P.source_mem i)
  target_mem i := mem_edgeContractImageSet_projection (P.target_mem i)
  source_bijective := by
    constructor
    · intro i j hij
      by_contra hne
      have heq : ((P.toPathPacking.contractEdge hab hP).path i).source =
          ((P.toPathPacking.contractEdge hab hP).path j).source :=
        congrArg Subtype.val hij
      have hi := GraphPath.source_mem_vertexSet
        ((P.toPathPacking.contractEdge hab hP).path i)
      have hj := GraphPath.source_mem_vertexSet
        ((P.toPathPacking.contractEdge hab hP).path j)
      exact Finset.disjoint_left.mp
        ((P.toPathPacking.contractEdge hab hP).node_disjoint hne) hi (heq.symm ▸ hj)
    · intro z
      obtain ⟨x, _, hxz⟩ := Finset.mem_image.mp z.property
      obtain ⟨i, hi⟩ := P.source_bijective.2 x
      refine ⟨i, Subtype.ext ?_⟩
      exact (congrArg (EdgeContractVertex.projection (u := a) (v := b))
        (congrArg Subtype.val hi)).trans hxz
  target_bijective := by
    constructor
    · intro i j hij
      by_contra hne
      have heq : ((P.toPathPacking.contractEdge hab hP).path i).target =
          ((P.toPathPacking.contractEdge hab hP).path j).target :=
        congrArg Subtype.val hij
      have hi := GraphPath.target_mem_vertexSet
        ((P.toPathPacking.contractEdge hab hP).path i)
      have hj := GraphPath.target_mem_vertexSet
        ((P.toPathPacking.contractEdge hab hP).path j)
      exact Finset.disjoint_left.mp
        ((P.toPathPacking.contractEdge hab hP).node_disjoint hne) hi (heq.symm ▸ hj)
    · intro z
      obtain ⟨x, _, hxz⟩ := Finset.mem_image.mp z.property
      obtain ⟨i, hi⟩ := P.target_bijective.2 x
      refine ⟨i, Subtype.ext ?_⟩
      exact (congrArg (EdgeContractVertex.projection (u := a) (v := b))
        (congrArg Subtype.val hi)).trans hxz

@[simp] theorem contractEdge_card (P : PerfectPathPacking G A B) (hab : G.Adj a b)
    (hP : P.toPathPacking.NoSplitAcross a b) :
    (P.contractEdge hab hP).card = P.card := rfl

theorem contractEdge_left_card (P : PerfectPathPacking G A B) (hab : G.Adj a b)
    (hP : P.toPathPacking.NoSplitAcross a b) :
    (edgeContractImageSet (a := a) (b := b) A).card = A.card := by
  rw [← (P.contractEdge hab hP).card_eq_left_card, contractEdge_card,
    P.card_eq_left_card]

theorem contractEdge_right_card (P : PerfectPathPacking G A B) (hab : G.Adj a b)
    (hP : P.toPathPacking.NoSplitAcross a b) :
    (edgeContractImageSet (a := a) (b := b) B).card = B.card := by
  rw [← (P.contractEdge hab hP).card_eq_right_card, contractEdge_card,
    P.card_eq_right_card]

end PerfectPathPacking
end Erdos73Infrastructure.SimpleGraph
