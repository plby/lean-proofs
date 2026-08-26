/-
Adapted from the Apache-2.0-licensed polynomial-grid-minor-theorem development,
https://github.com/EdouardBonnet/polynomial-grid-minor-theorem,
commit fe2848173913a00d85c64d2a17af63f2cf0d4fbf,
proofs/Lax17Proofs/Source/Paths.lean.
Local changes: split graph-path and packing helpers; Lean 4.33 compatibility.
-/
import ErdosProblems.Erdos73.GraphPaths

namespace Erdos73Infrastructure

universe u v w

namespace SimpleGraph

/-- A finite indexed family of node-disjoint paths connecting two vertex sets. -/
structure PathPacking {V : Type*} [DecidableEq V]
    (G : _root_.SimpleGraph V) (S T : Finset V) where
  /-- The finite index type for the paths in the packing. -/
  Index : Type
  /-- The index type is finite. -/
  [indexFintype : Fintype Index]
  /-- The index type has decidable equality. -/
  [indexDecidableEq : DecidableEq Index]
  /-- The path assigned to each index. -/
  path : Index → GraphPath G
  /-- Every path connects the two specified vertex sets. -/
  connects : ∀ i : Index, (path i).Connects S T
  /-- Distinct indexed paths are vertex-disjoint. -/
  node_disjoint : Pairwise fun i j => GraphPath.NodeDisjoint (path i) (path j)

namespace PathPacking

variable {V : Type*} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {S T : Finset V}

/-- The image of a finite set in a subtype determined by a larger finite set. -/
noncomputable def subtypeFinset (S U : Finset V) (hS : S ⊆ U) :
    Finset {v : V // v ∈ U} :=
  S.attach.map
    ⟨fun v => ⟨v.1, hS v.2⟩,
      by
        intro a b h
        have hval : a.1 = b.1 :=
          congrArg (fun x : {v : V // v ∈ U} => x.1) h
        exact Subtype.ext hval⟩

omit [DecidableEq V] in
@[simp] theorem mem_subtypeFinset {S U : Finset V} (hS : S ⊆ U)
    (v : {x : V // x ∈ U}) :
    v ∈ subtypeFinset S U hS ↔ v.1 ∈ S := by
  classical
  constructor
  · intro hv
    rcases Finset.mem_map.mp hv with ⟨x, hx, hxv⟩
    have hxval : x.1 = v.1 := congrArg Subtype.val hxv
    simpa [hxval] using x.2
  · intro hv
    exact Finset.mem_map.mpr
      ⟨⟨v.1, hv⟩, by simp, by
        apply Subtype.ext
        rfl⟩

instance (P : PathPacking G S T) : Fintype P.Index := P.indexFintype
instance (P : PathPacking G S T) : DecidableEq P.Index := P.indexDecidableEq

/-- The number of paths in a packing. -/
noncomputable def card (P : PathPacking G S T) : ℕ :=
  Fintype.card P.Index

/-- Reindex a path packing by an equivalent finite index type. -/
noncomputable def reindex {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : PathPacking G S T) (e : ι ≃ P.Index) :
    PathPacking G S T where
  Index := ι
  path := fun i => P.path (e i)
  connects := fun i => P.connects (e i)
  node_disjoint := by
    intro i j hij
    exact P.node_disjoint (fun h => hij (e.injective h))

@[simp] theorem reindex_card {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : PathPacking G S T) (e : ι ≃ P.Index) :
    (P.reindex e).card = P.card := by
  dsimp [reindex, card]
  exact Fintype.card_congr e

@[simp] theorem reindex_path_vertexSet
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : PathPacking G S T) (e : ι ≃ P.Index) (i : ι) :
    ((P.reindex e).path i).vertexSet = (P.path (e i)).vertexSet := rfl

@[simp] theorem reindex_path_edgeSet
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : PathPacking G S T) (e : ι ≃ P.Index) (i : ι) :
    ((P.reindex e).path i).edgeSet = (P.path (e i)).edgeSet := rfl

/-- The canonical equivalence from `Fin P.card` to the index type of a path
packing. -/
noncomputable def finIndexEquiv (P : PathPacking G S T) :
    Fin P.card ≃ P.Index := by
  simpa [card] using (Fintype.equivFin P.Index).symm

/-- Reindex a path packing by `Fin P.card`. -/
noncomputable def finReindex (P : PathPacking G S T) : PathPacking G S T :=
  P.reindex P.finIndexEquiv

@[simp] theorem finReindex_card (P : PathPacking G S T) :
    P.finReindex.card = P.card := by
  simp [finReindex]

/-- Restrict a path packing to a finite set of path indices. -/
noncomputable def restrictIndexSet (P : PathPacking G S T)
    (I : Finset P.Index) : PathPacking G S T where
  Index := {i : P.Index // i ∈ I}
  path := fun i => P.path i.1
  connects := fun i => P.connects i.1
  node_disjoint := by
    intro i j hij
    exact P.node_disjoint (fun h => hij (Subtype.ext h))

@[simp] theorem restrictIndexSet_card (P : PathPacking G S T)
    (I : Finset P.Index) :
    (P.restrictIndexSet I).card = I.card := by
  classical
  exact Fintype.card_coe I

@[simp] theorem restrictIndexSet_path_vertexSet
    (P : PathPacking G S T) (I : Finset P.Index)
    (i : (P.restrictIndexSet I).Index) :
    ((P.restrictIndexSet I).path i).vertexSet = (P.path i.1).vertexSet := rfl

/-- Choose exactly `n` paths from a packing of size at least `n`. -/
theorem exists_indexSet_card_eq (P : PathPacking G S T)
    {n : ℕ} (hn : n ≤ P.card) :
    ∃ I : Finset P.Index, I.card = n ∧
      (P.restrictIndexSet I).card = n := by
  classical
  have hn_univ : n ≤ (Finset.univ : Finset P.Index).card := by
    simpa [card] using hn
  rcases Finset.exists_subset_card_eq hn_univ with ⟨I, _hI, hIcard⟩
  exact ⟨I, hIcard, by simp [hIcard]⟩

/-- Transfer every path in a packing to another graph on the same vertex type,
given edge-containment proofs for each path. -/
def transfer (P : PathPacking G S T) (H : _root_.SimpleGraph V)
    (h : ∀ i : P.Index, ∀ e, e ∈ (P.path i).walk.edges → e ∈ H.edgeSet) :
    PathPacking H S T where
  Index := P.Index
  path := fun i => (P.path i).transfer H (h i)
  connects := by
    intro i
    simpa [GraphPath.transfer, GraphPath.Connects] using P.connects i
  node_disjoint := by
    intro i j hij
    simpa [GraphPath.NodeDisjoint] using P.node_disjoint hij

/-- Every path in the packing has all vertices contained in `U`. -/
def StaysIn (P : PathPacking G S T) (U : Finset V) : Prop :=
  ∀ i : P.Index, (P.path i).vertexSet ⊆ U

/-- Lift a path packing that stays inside a finite vertex set to the induced
graph on that set.  The terminal sets are the corresponding subtype images. -/
noncomputable def induce (P : PathPacking G S T) (U : Finset V)
    (hP : P.StaysIn U) (hS : S ⊆ U) (hT : T ⊆ U) :
    PathPacking (G.induce {v : V | v ∈ U})
      (subtypeFinset S U hS) (subtypeFinset T U hT) where
  Index := P.Index
  path := fun i => (P.path i).induce U (hP i)
  connects := by
    intro i
    rcases P.connects i with h | h
    · exact Or.inl ⟨by
        rw [GraphPath.induce_source]
        exact (mem_subtypeFinset hS _).2 h.1,
        by
        rw [GraphPath.induce_target]
        exact (mem_subtypeFinset hT _).2 h.2⟩
    · exact Or.inr ⟨by
        rw [GraphPath.induce_source]
        exact (mem_subtypeFinset hT _).2 h.1,
        by
        rw [GraphPath.induce_target]
        exact (mem_subtypeFinset hS _).2 h.2⟩
  node_disjoint := by
    intro i j hij
    rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
    intro v hv_i hv_j
    have hvi : v.1 ∈ (P.path i).vertexSet := by
      have hv_support :
          v ∈ ((P.path i).induce U (hP i)).walk.support := by
        exact List.mem_toFinset.mp (by
          simpa [GraphPath.vertexSet] using hv_i)
      change
        v ∈ (_root_.SimpleGraph.Walk.induce (↑U : Set V)
          (P.path i).walk _).support at hv_support
      rw [_root_.SimpleGraph.Walk.support_induce] at hv_support
      simpa [GraphPath.vertexSet] using hv_support
    have hvj : v.1 ∈ (P.path j).vertexSet := by
      have hv_support :
          v ∈ ((P.path j).induce U (hP j)).walk.support := by
        exact List.mem_toFinset.mp (by
          simpa [GraphPath.vertexSet] using hv_j)
      change
        v ∈ (_root_.SimpleGraph.Walk.induce (↑U : Set V)
          (P.path j).walk _).support at hv_support
      rw [_root_.SimpleGraph.Walk.support_induce] at hv_support
      simpa [GraphPath.vertexSet] using hv_support
    exact Finset.disjoint_left.mp (P.node_disjoint hij) hvi hvj

/-- Every path in the packing is internally disjoint from `U`. -/
def InternallyDisjointFromSet (P : PathPacking G S T) (U : Finset V) : Prop :=
  ∀ i : P.Index, (P.path i).InternallyDisjointFromSet U

/-- The union of all vertices used by paths in the packing. -/
noncomputable def vertexSet (P : PathPacking G S T) : Finset V :=
  Finset.univ.biUnion fun i : P.Index => (P.path i).vertexSet

/-- Membership in the vertex set of a path packing is membership in one of its
indexed path vertex sets. -/
theorem mem_vertexSet (P : PathPacking G S T) {v : V} :
    v ∈ P.vertexSet ↔ ∃ i : P.Index, v ∈ (P.path i).vertexSet := by
  classical
  simp [vertexSet]

/-- The vertex set of each indexed path is contained in the packing vertex
set. -/
theorem path_vertexSet_subset_vertexSet (P : PathPacking G S T)
    (i : P.Index) :
    (P.path i).vertexSet ⊆ P.vertexSet := by
  intro v hv
  exact (P.mem_vertexSet).2 ⟨i, hv⟩

/-- Internal disjointness from `A` extends to `A ∪ B` when the whole packing is
disjoint from `B`. -/
theorem internallyDisjointFromSet_union_of_disjoint_vertexSet
    (P : PathPacking G S T) {A B : Finset V}
    (hA : P.InternallyDisjointFromSet A)
    (hB : Disjoint P.vertexSet B) :
    P.InternallyDisjointFromSet (A ∪ B) := by
  intro i v hv hvUnion
  rcases Finset.mem_union.mp hvUnion with hvA | hvB
  · exact hA i hv hvA
  · exact False.elim
      (Finset.disjoint_left.mp hB (P.path_vertexSet_subset_vertexSet i hv) hvB)

/-- If every path in a packing stays in `U`, then the whole packing vertex set is
contained in `U`. -/
theorem vertexSet_subset_of_staysIn {P : PathPacking G S T} {U : Finset V}
    (h : P.StaysIn U) :
    P.vertexSet ⊆ U := by
  classical
  intro v hv
  have hv' :
      v ∈ Finset.univ.biUnion fun i : P.Index => (P.path i).vertexSet := by
    simpa [vertexSet] using hv
  rcases Finset.mem_biUnion.mp hv' with ⟨i, _hi, hvi⟩
  exact h i hvi

/-- A bridge path from one indexed path of a packing to another, internally
disjoint from the whole packing.  This is the bridge object returned by
Chekuri--Chuzhoy Theorem 3.1. -/
structure BridgeBetween (P : PathPacking G S T) (i j : P.Index) where
  /-- The bridge path. -/
  path : GraphPath G
  /-- The bridge starts on path `i` and ends on path `j`, up to orientation. -/
  connects : path.Connects (P.path i).vertexSet (P.path j).vertexSet
  /-- Internal vertices of the bridge avoid every path in the packing. -/
  internallyDisjoint : path.InternallyDisjointFromSet P.vertexSet

namespace BridgeBetween

variable {P : PathPacking G S T} {i j : P.Index}

/-- Orient a bridge from the first indexed path to the second indexed path. -/
noncomputable def orientedPath (β : P.BridgeBetween i j) : GraphPath G :=
  β.path.orient β.connects

@[simp] theorem orientedPath_vertexSet (β : P.BridgeBetween i j) :
    β.orientedPath.vertexSet = β.path.vertexSet := by
  simp [orientedPath]

theorem orientedPath_source_mem_left (β : P.BridgeBetween i j) :
    β.orientedPath.source ∈ (P.path i).vertexSet :=
  GraphPath.orient_source_mem β.path β.connects

theorem orientedPath_target_mem_right (β : P.BridgeBetween i j) :
    β.orientedPath.target ∈ (P.path j).vertexSet :=
  GraphPath.orient_target_mem β.path β.connects

theorem orientedPath_internallyDisjoint (β : P.BridgeBetween i j) :
    β.orientedPath.InternallyDisjointFromSet P.vertexSet := by
  intro v hv hP
  exact (GraphPath.orient_isEndpoint β.path β.connects).2
    (β.internallyDisjoint (by simpa [orientedPath] using hv) hP)

end BridgeBetween

/-- A path whose endpoints lie on two indexed paths of a packing, and whose
internal vertices avoid the whole packing, is a bridge between those two
indexed paths.  This is the standard way that a clean transversal segment
creates an edge in the linkage auxiliary graph. -/
def BridgeBetween.of_orientedPath (P : PathPacking G S T)
    {i j : P.Index} (R : GraphPath G)
    (hsource : R.source ∈ (P.path i).vertexSet)
    (htarget : R.target ∈ (P.path j).vertexSet)
    (hinternal : R.InternallyDisjointFromSet P.vertexSet) :
    P.BridgeBetween i j where
  path := R
  connects := Or.inl ⟨hsource, htarget⟩
  internallyDisjoint := hinternal

/-- A packing has pairwise bridges if every pair of distinct indexed paths is
connected by a bridge internally disjoint from the entire packing. -/
def HasPairwiseBridges (P : PathPacking G S T) : Prop :=
  ∀ ⦃i j : P.Index⦄, i ≠ j → Nonempty (P.BridgeBetween i j)

/-- A localized version of pairwise bridges: each bridge is required to stay in
the finite region `U`. -/
def HasPairwiseBridgesIn (P : PathPacking G S T) (U : Finset V) : Prop :=
  ∀ ⦃i j : P.Index⦄, i ≠ j →
    ∃ β : P.BridgeBetween i j, β.path.vertexSet ⊆ U

/-- The union of all edges used by paths in the packing. -/
noncomputable def edgeSet (P : PathPacking G S T) : Finset (Sym2 V) :=
  Finset.univ.biUnion fun i : P.Index => (P.path i).edgeSet

/-- Membership in the edge set of a path packing is membership in one of its
indexed path edge sets. -/
theorem mem_edgeSet (P : PathPacking G S T) {e : Sym2 V} :
    e ∈ P.edgeSet ↔ ∃ i : P.Index, e ∈ (P.path i).edgeSet := by
  classical
  simp [edgeSet]

/-- The edge set of each indexed path is contained in the packing edge set. -/
theorem path_edgeSet_subset_edgeSet (P : PathPacking G S T) (i : P.Index) :
    (P.path i).edgeSet ⊆ P.edgeSet := by
  intro e he
  exact (P.mem_edgeSet).2 ⟨i, he⟩

/-- Every edge used by a path packing is an ambient graph edge. -/
theorem edgeSet_subset_edgeSet (P : PathPacking G S T) :
    ↑P.edgeSet ⊆ G.edgeSet := by
  classical
  intro e he
  have he' :
      e ∈ Finset.univ.biUnion fun i : P.Index => (P.path i).edgeSet := by
    simpa [edgeSet] using he
  rcases Finset.mem_biUnion.mp he' with ⟨i, _hi, hei⟩
  exact GraphPath.edgeSet_subset_edgeSet (P.path i) (by simpa using hei)

/-- The spanning subgraph consisting of exactly the path-packing edges. -/
noncomputable def spanningGraph (P : PathPacking G S T) : _root_.SimpleGraph V :=
  _root_.SimpleGraph.fromEdgeSet (↑P.edgeSet : Set (Sym2 V))

/-- The path-packing spanning graph is a subgraph of the ambient graph. -/
theorem spanningGraph_le (P : PathPacking G S T) :
    P.spanningGraph ≤ G := by
  intro u v huv
  rw [spanningGraph, _root_.SimpleGraph.fromEdgeSet_adj] at huv
  exact P.edgeSet_subset_edgeSet huv.1

/-- Adjacency in the graph spanned by a path packing comes from an edge of one
of the packed paths. -/
theorem spanningGraph_adj_iff_exists_path_edge (P : PathPacking G S T)
    {u v : V} :
    P.spanningGraph.Adj u v ↔
      (∃ i : P.Index, s(u, v) ∈ (P.path i).edgeSet) ∧ u ≠ v := by
  classical
  rw [spanningGraph, _root_.SimpleGraph.fromEdgeSet_adj]
  constructor
  · intro h
    constructor
    · have hedge : s(u, v) ∈ P.edgeSet := by
        simpa using h.1
      have hedge' :
          s(u, v) ∈ Finset.univ.biUnion fun i : P.Index =>
            (P.path i).edgeSet := by
        simpa [edgeSet] using hedge
      rcases Finset.mem_biUnion.mp hedge' with ⟨i, _hi, hpath⟩
      exact ⟨i, hpath⟩
    · exact h.2
  · rintro ⟨⟨i, hpath⟩, huv⟩
    constructor
    · have hedge :
          s(u, v) ∈ Finset.univ.biUnion fun i : P.Index =>
            (P.path i).edgeSet :=
        Finset.mem_biUnion.mpr ⟨i, by simp, hpath⟩
      simpa [edgeSet] using hedge
    · exact huv

/-- In the spanning graph of a node-disjoint packing, an edge incident with
one packed path stays on that same packed path. -/
theorem mem_path_vertexSet_of_spanningGraph_adj_of_mem_path_vertexSet
    (P : PathPacking G S T) {r : P.Index} {u v : V}
    (hu : u ∈ (P.path r).vertexSet) (huv : P.spanningGraph.Adj u v) :
    v ∈ (P.path r).vertexSet := by
  classical
  rcases (P.spanningGraph_adj_iff_exists_path_edge).1 huv with
    ⟨⟨i, he⟩, _hne⟩
  have heWalk : s(u, v) ∈ (P.path i).walk.edges := by
    simpa [GraphPath.edgeSet] using he
  have hu_i : u ∈ (P.path i).vertexSet := by
    simpa [GraphPath.vertexSet] using
      (P.path i).walk.fst_mem_support_of_mem_edges heWalk
  have hv_i : v ∈ (P.path i).vertexSet := by
    simpa [GraphPath.vertexSet] using
      (P.path i).walk.snd_mem_support_of_mem_edges heWalk
  by_cases hir : i = r
  · simpa [hir] using hv_i
  · exact False.elim
      (Finset.disjoint_left.mp (P.node_disjoint hir) hu_i hu)

/-- A walk in a packing's spanning graph that starts on one packed path never
leaves that path. -/
theorem spanningGraph_walk_support_subset_path
    (P : PathPacking G S T) (r : P.Index)
    {u v : V} (W : P.spanningGraph.Walk u v)
    (hu : u ∈ (P.path r).vertexSet) :
    ∀ x ∈ W.support, x ∈ (P.path r).vertexSet := by
  induction W with
  | nil =>
      intro x hx
      simp at hx
      subst x
      exact hu
  | @cons u v z huv W ih =>
      intro x hx
      simp only [_root_.SimpleGraph.Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hu
      · exact ih
          (P.mem_path_vertexSet_of_spanningGraph_adj_of_mem_path_vertexSet
            hu huv) x hx

/-- A graph path using only the edges of a node-disjoint packing and starting
on one packed path is wholly contained in that packed path. -/
theorem path_vertexSet_subset_of_edgeSet_subset_of_source_mem
    (P : PathPacking G S T) (Q : GraphPath G) (r : P.Index)
    (hQedge : Q.edgeSet ⊆ P.edgeSet)
    (hsource : Q.source ∈ (P.path r).vertexSet) :
    Q.vertexSet ⊆ (P.path r).vertexSet := by
  classical
  let Q' : GraphPath P.spanningGraph :=
    Q.transfer P.spanningGraph (by
      intro e he
      rw [spanningGraph, _root_.SimpleGraph.edgeSet_fromEdgeSet]
      constructor
      · apply hQedge
        simpa [GraphPath.edgeSet] using he
      · exact G.not_isDiag_of_mem_edgeSet
          (Q.walk.edges_subset_edgeSet he))
  intro x hx
  have hx' : x ∈ Q'.walk.support := by
    have hxQ' : x ∈ Q'.vertexSet := by
      simpa [Q'] using hx
    simpa [GraphPath.vertexSet] using hxQ'
  exact P.spanningGraph_walk_support_subset_path r Q'.walk
    hsource x hx'

/-- A path using only the edges of a node-disjoint packing and starting on one
packed path uses only the edges of that indexed path. -/
theorem path_edgeSet_subset_of_edgeSet_subset_of_source_mem
    (P : PathPacking G S T) (Q : GraphPath G) (r : P.Index)
    (hQedge : Q.edgeSet ⊆ P.edgeSet)
    (hsource : Q.source ∈ (P.path r).vertexSet) :
    Q.edgeSet ⊆ (P.path r).edgeSet := by
  classical
  have hQvertex :
      Q.vertexSet ⊆ (P.path r).vertexSet :=
    P.path_vertexSet_subset_of_edgeSet_subset_of_source_mem
      Q r hQedge hsource
  intro e heQ
  rcases P.mem_edgeSet.mp (hQedge heQ) with ⟨j, hej⟩
  by_cases hjr : j = r
  · simpa [hjr] using hej
  have heout : s(e.out.1, e.out.2) = e := by
    rw [Sym2.mk, e.out_eq]
  have hxQ : e.out.1 ∈ Q.vertexSet := by
    have heQ' : s(e.out.1, e.out.2) ∈ Q.edgeSet := by
      rw [heout]
      exact heQ
    exact
      (GraphPath.endpoints_mem_vertexSet_of_edgeSet Q
        heQ').1
  have hxr : e.out.1 ∈ (P.path r).vertexSet :=
    hQvertex hxQ
  have hxj : e.out.1 ∈ (P.path j).vertexSet := by
    have hej' : s(e.out.1, e.out.2) ∈ (P.path j).edgeSet := by
      rw [heout]
      exact hej
    exact
      (GraphPath.endpoints_mem_vertexSet_of_edgeSet (P.path j)
        hej').1
  exact False.elim
    (Finset.disjoint_left.mp (P.node_disjoint hjr) hxj hxr)

/-- A path packing can be viewed as a packing in the graph spanned by exactly
its own path edges. -/
noncomputable def inSpanningGraph (P : PathPacking G S T) :
    PathPacking P.spanningGraph S T :=
  P.transfer P.spanningGraph (by
    classical
    intro i e he
    rw [spanningGraph, _root_.SimpleGraph.edgeSet_fromEdgeSet]
    constructor
    · have hei_path : e ∈ (P.path i).edgeSet := by
        simpa [GraphPath.edgeSet] using he
      exact by
        simpa [edgeSet, hei_path] using
          (Finset.mem_biUnion.mpr ⟨i, by simp, hei_path⟩ :
            e ∈ (Finset.univ.biUnion fun i : P.Index => (P.path i).edgeSet))
    · exact G.not_isDiag_of_mem_edgeSet ((P.path i).walk.edges_subset_edgeSet he))

@[simp] theorem inSpanningGraph_card (P : PathPacking G S T) :
    P.inSpanningGraph.card = P.card := rfl

@[simp] theorem inSpanningGraph_path_vertexSet (P : PathPacking G S T)
    (i : P.Index) :
    (P.inSpanningGraph.path i).vertexSet = (P.path i).vertexSet := by
  simp [inSpanningGraph, transfer]

/-- Two path packings are mutually node-disjoint. -/
def MutuallyNodeDisjoint {S' T' : Finset V}
    (P : PathPacking G S T) (Q : PathPacking G S' T') : Prop :=
  ∀ i : P.Index, ∀ j : Q.Index,
    GraphPath.NodeDisjoint (P.path i) (Q.path j)

theorem mutuallyNodeDisjoint_symm {S' T' : Finset V}
    {P : PathPacking G S T} {Q : PathPacking G S' T'}
    (h : P.MutuallyNodeDisjoint Q) :
    Q.MutuallyNodeDisjoint P := by
  intro j i
  exact GraphPath.nodeDisjoint_symm (h i j)

/-- Mutually node-disjoint path packings have disjoint total vertex sets. -/
theorem vertexSet_disjoint_of_mutuallyNodeDisjoint {S' T' : Finset V}
    {P : PathPacking G S T} {Q : PathPacking G S' T'}
    (h : P.MutuallyNodeDisjoint Q) :
    Disjoint P.vertexSet Q.vertexSet := by
  classical
  rw [Finset.disjoint_left]
  intro v hvP hvQ
  rcases (P.mem_vertexSet).1 hvP with ⟨i, hvi⟩
  rcases (Q.mem_vertexSet).1 hvQ with ⟨j, hvj⟩
  exact Finset.disjoint_left.mp (h i j) hvi hvj

/-- Two path packings are mutually edge-disjoint. -/
def MutuallyEdgeDisjoint {S' T' : Finset V}
    (P : PathPacking G S T) (Q : PathPacking G S' T') : Prop :=
  ∀ i : P.Index, ∀ j : Q.Index,
    GraphPath.EdgeDisjoint (P.path i) (Q.path j)

theorem mutuallyEdgeDisjoint_symm {S' T' : Finset V}
    {P : PathPacking G S T} {Q : PathPacking G S' T'}
    (h : P.MutuallyEdgeDisjoint Q) :
    Q.MutuallyEdgeDisjoint P := by
  intro j i
  exact GraphPath.edgeDisjoint_symm (h i j)

/-- Mutually edge-disjoint path packings have disjoint total edge sets. -/
theorem edgeSet_disjoint_of_mutuallyEdgeDisjoint {S' T' : Finset V}
    {P : PathPacking G S T} {Q : PathPacking G S' T'}
    (h : P.MutuallyEdgeDisjoint Q) :
    Disjoint P.edgeSet Q.edgeSet := by
  classical
  rw [Finset.disjoint_left]
  intro e heP heQ
  rcases (P.mem_edgeSet).1 heP with ⟨i, hei⟩
  rcases (Q.mem_edgeSet).1 heQ with ⟨j, hej⟩
  exact Finset.disjoint_left.mp (h i j) hei hej

/-- Orient every path in a packing from the first terminal set to the second
terminal set. -/
def orient (P : PathPacking G S T) : PathPacking G S T where
  Index := P.Index
  path := fun i => (P.path i).orient (P.connects i)
  connects := by
    intro i
    exact Or.inl ⟨GraphPath.orient_source_mem (P.path i) (P.connects i),
      GraphPath.orient_target_mem (P.path i) (P.connects i)⟩
  node_disjoint := by
    intro i j hij
    simpa [GraphPath.NodeDisjoint] using P.node_disjoint hij

@[simp] theorem orient_card (P : PathPacking G S T) :
    P.orient.card = P.card := rfl

@[simp] theorem orient_path_vertexSet (P : PathPacking G S T) (i : P.Index) :
    (P.orient.path i).vertexSet = (P.path i).vertexSet := by
  simp [orient]

@[simp] theorem orient_path_edgeSet (P : PathPacking G S T) (i : P.Index) :
    (P.orient.path i).edgeSet = (P.path i).edgeSet := by
  simp [orient]

@[simp] theorem orient_edgeSet (P : PathPacking G S T) :
    P.orient.edgeSet = P.edgeSet := by
  classical
  ext e
  rw [PathPacking.mem_edgeSet, PathPacking.mem_edgeSet]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, by simpa only [orient, GraphPath.orient_edgeSet] using hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, by simpa using hi⟩

/-- The left terminals actually used by an oriented path packing. -/
noncomputable def sourceSet (P : PathPacking G S T) : Finset V :=
  Finset.univ.image fun i : P.Index => (P.orient.path i).source

/-- The right terminals actually used by an oriented path packing. -/
noncomputable def targetSet (P : PathPacking G S T) : Finset V :=
  Finset.univ.image fun i : P.Index => (P.orient.path i).target

theorem sourceSet_subset_left (P : PathPacking G S T) :
    P.sourceSet ⊆ S := by
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨i, _hi, rfl⟩
  exact GraphPath.orient_source_mem (P.path i) (P.connects i)

theorem targetSet_subset_right (P : PathPacking G S T) :
    P.targetSet ⊆ T := by
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨i, _hi, rfl⟩
  exact GraphPath.orient_target_mem (P.path i) (P.connects i)

/-- Membership in the used source-terminal set is witnessed by an indexed
oriented path with that source. -/
theorem exists_orient_source_eq_of_mem_sourceSet
    (P : PathPacking G S T) {v : V} (hv : v ∈ P.sourceSet) :
    ∃ i : P.Index, (P.orient.path i).source = v := by
  classical
  rcases Finset.mem_image.mp hv with ⟨i, _hi, h⟩
  exact ⟨i, h⟩

/-- Membership in the used target-terminal set is witnessed by an indexed
oriented path with that target. -/
theorem exists_orient_target_eq_of_mem_targetSet
    (P : PathPacking G S T) {v : V} (hv : v ∈ P.targetSet) :
    ∃ i : P.Index, (P.orient.path i).target = v := by
  classical
  rcases Finset.mem_image.mp hv with ⟨i, _hi, h⟩
  exact ⟨i, h⟩

/-- An oriented path in a packing can contain a used source terminal only if
that terminal is its own source. -/
theorem eq_orient_source_of_mem_sourceSet_of_mem_orient_path_vertexSet
    (P : PathPacking G S T) (i : P.Index) {v : V}
    (hvS : v ∈ P.sourceSet)
    (hvpath : v ∈ (P.orient.path i).vertexSet) :
    v = (P.orient.path i).source := by
  classical
  rcases P.exists_orient_source_eq_of_mem_sourceSet hvS with ⟨j, hj⟩
  by_cases hji : j = i
  · simpa [hji] using hj.symm
  · have hvj : v ∈ (P.orient.path j).vertexSet := by
      simpa [hj] using GraphPath.source_mem_vertexSet (P.orient.path j)
    exact False.elim
      (Finset.disjoint_left.mp (P.orient.node_disjoint hji) hvj hvpath)

/-- An oriented path in a packing can contain a used target terminal only if
that terminal is its own target. -/
theorem eq_orient_target_of_mem_targetSet_of_mem_orient_path_vertexSet
    (P : PathPacking G S T) (i : P.Index) {v : V}
    (hvT : v ∈ P.targetSet)
    (hvpath : v ∈ (P.orient.path i).vertexSet) :
    v = (P.orient.path i).target := by
  classical
  rcases P.exists_orient_target_eq_of_mem_targetSet hvT with ⟨j, hj⟩
  by_cases hji : j = i
  · simpa [hji] using hj.symm
  · have hvj : v ∈ (P.orient.path j).vertexSet := by
      simpa [hj] using GraphPath.target_mem_vertexSet (P.orient.path j)
    exact False.elim
      (Finset.disjoint_left.mp (P.orient.node_disjoint hji) hvj hvpath)

@[simp] theorem sourceSet_card (P : PathPacking G S T) :
    P.sourceSet.card = P.card := by
  rw [sourceSet, Finset.card_image_of_injective]
  · simp [card]
  · intro i j hij
    by_contra hne
    have hdisj := P.orient.node_disjoint hne
    have hi :
        (P.orient.path i).source ∈ (P.orient.path i).vertexSet :=
      GraphPath.source_mem_vertexSet (P.orient.path i)
    have hj :
        (P.orient.path i).source ∈ (P.orient.path j).vertexSet := by
      simpa [hij] using GraphPath.source_mem_vertexSet (P.orient.path j)
    exact Finset.disjoint_left.mp hdisj hi hj

@[simp] theorem targetSet_card (P : PathPacking G S T) :
    P.targetSet.card = P.card := by
  rw [targetSet, Finset.card_image_of_injective]
  · simp [card]
  · intro i j hij
    by_contra hne
    have hdisj := P.orient.node_disjoint hne
    have hi :
        (P.orient.path i).target ∈ (P.orient.path i).vertexSet :=
      GraphPath.target_mem_vertexSet (P.orient.path i)
    have hj :
        (P.orient.path i).target ∈ (P.orient.path j).vertexSet := by
      simpa [hij] using GraphPath.target_mem_vertexSet (P.orient.path j)
    exact Finset.disjoint_left.mp hdisj hi hj

/-- If a path packing has as many paths as left terminals, its used source
terminal set is the whole left terminal set. -/
theorem sourceSet_eq_left_of_card_eq (P : PathPacking G S T)
    (hcard : P.card = S.card) :
    P.sourceSet = S := by
  exact Finset.eq_of_subset_of_card_le P.sourceSet_subset_left (by
    rw [sourceSet_card, hcard])

/-- If a path packing has as many paths as right terminals, its used target
terminal set is the whole right terminal set. -/
theorem targetSet_eq_right_of_card_eq (P : PathPacking G S T)
    (hcard : P.card = T.card) :
    P.targetSet = T := by
  exact Finset.eq_of_subset_of_card_le P.targetSet_subset_right (by
    rw [targetSet_card, hcard])

/-- Distinct paths in an oriented packing have distinct right endpoints. -/
theorem orient_target_injective (P : PathPacking G S T) :
    Function.Injective fun i : P.Index => (P.orient.path i).target := by
  intro i j hij
  by_contra hne
  have hdisj := P.orient.node_disjoint hne
  have hi :
      (P.orient.path i).target ∈ (P.orient.path i).vertexSet :=
    GraphPath.target_mem_vertexSet (P.orient.path i)
  have hj :
      (P.orient.path i).target ∈ (P.orient.path j).vertexSet := by
    simpa [hij] using GraphPath.target_mem_vertexSet (P.orient.path j)
  exact Finset.disjoint_left.mp hdisj hi hj

/-- Orienting a packing preserves the property that all paths stay in a finite
vertex set. -/
theorem orient_staysIn {P : PathPacking G S T} {U : Finset V}
    (hP : P.StaysIn U) :
    P.orient.StaysIn U := by
  intro i
  simpa only [orient, GraphPath.orient_vertexSet] using hP i

/-- Orienting a packing preserves internal disjointness from a vertex set. -/
theorem orient_internallyDisjointFromSet
    {P : PathPacking G S T} {U : Finset V}
    (hP : P.InternallyDisjointFromSet U) :
    P.orient.InternallyDisjointFromSet U := by
  intro i v hv hU
  exact (GraphPath.orient_isEndpoint (P.path i) (P.connects i)).2
    (hP i (by simpa only [orient, GraphPath.orient_vertexSet] using hv) hU)

/-- Orienting a packing preserves localized pairwise bridges. -/
theorem orient_hasPairwiseBridgesIn {P : PathPacking G S T} {U : Finset V}
    (h : P.HasPairwiseBridgesIn U) :
    P.orient.HasPairwiseBridgesIn U := by
  intro i j hij
  rcases h hij with ⟨β, hβU⟩
  let β' : P.orient.BridgeBetween i j := {
    path := β.path
    connects := by
      simpa only [orient, GraphPath.orient_vertexSet] using β.connects
    internallyDisjoint := by
      intro v hv hrows
      exact β.internallyDisjoint hv (by
        rcases P.orient.mem_vertexSet.mp hrows with ⟨r, hr⟩
        exact P.mem_vertexSet.mpr ⟨r, by
          simpa only [orient, GraphPath.orient_vertexSet] using hr⟩)
  }
  exact ⟨β', by simpa [β'] using hβU⟩

/-- An oriented path of a packing always meets the right terminal set at its
target endpoint. -/
theorem orient_path_meets_right (P : PathPacking G S T) (i : P.Index) :
    ((P.orient.path i).vertexSet ∩ T).Nonempty := by
  exact ⟨(P.orient.path i).target, Finset.mem_inter.2
    ⟨GraphPath.target_mem_vertexSet (P.orient.path i),
      GraphPath.orient_target_mem (P.path i) (P.connects i)⟩⟩

/-- Clean a packing by replacing every oriented path with the prefix ending at
its first hit of the right terminal set.  The index set and left endpoints are
unchanged, while every resulting path is internally disjoint from the right
terminal set. -/
noncomputable def cleanToRight (P : PathPacking G S T) :
    PathPacking G S T where
  Index := P.Index
  path := fun i =>
    (P.orient.path i).cleanPrefixToSet T (P.orient_path_meets_right i)
  connects := by
    intro i
    exact Or.inl
      ⟨by
        exact GraphPath.orient_source_mem (P.path i) (P.connects i),
       by
        exact (P.orient.path i).cleanPrefixToSet_target_mem T
          (P.orient_path_meets_right i)⟩
  node_disjoint := by
    intro i j hij
    refine (P.orient.node_disjoint hij).mono ?_ ?_
    · exact (P.orient.path i).cleanPrefixToSet_vertexSet_subset T
        (P.orient_path_meets_right i)
    · exact (P.orient.path j).cleanPrefixToSet_vertexSet_subset T
        (P.orient_path_meets_right j)

@[simp] theorem cleanToRight_card (P : PathPacking G S T) :
    P.cleanToRight.card = P.card := rfl

theorem cleanToRight_path_vertexSet_subset
    (P : PathPacking G S T) (i : P.Index) :
    (P.cleanToRight.path i).vertexSet ⊆ (P.path i).vertexSet := by
  intro v hv
  have hv' :
      v ∈ (P.orient.path i).vertexSet :=
    (P.orient.path i).cleanPrefixToSet_vertexSet_subset T
      (P.orient_path_meets_right i) hv
  simpa [PathPacking.orient_path_vertexSet] using hv'

/-- Cleaning a packing makes every path internally disjoint from the right
terminal set. -/
theorem cleanToRight_internallyDisjointFromSet
    (P : PathPacking G S T) :
    P.cleanToRight.InternallyDisjointFromSet T := by
  intro i
  exact (P.orient.path i).cleanPrefixToSet_internallyDisjointFromSet T
    (P.orient_path_meets_right i)

@[simp] theorem cleanToRight_orient_path_source
    (P : PathPacking G S T) (i : P.Index) :
    (P.cleanToRight.orient.path i).source = (P.orient.path i).source := by
  classical
  have hst :
      (P.cleanToRight.path i).source ∈ S ∧
        (P.cleanToRight.path i).target ∈ T := by
    exact ⟨by
      exact GraphPath.orient_source_mem (P.path i) (P.connects i),
      by
        dsimp [cleanToRight]
        exact (P.orient.path i).cleanPrefixToSet_target_mem T
          (P.orient_path_meets_right i)⟩
  change ((P.cleanToRight.path i).orient (P.cleanToRight.connects i)).source =
    (P.orient.path i).source
  rw [GraphPath.orient, if_pos hst]
  rfl

@[simp] theorem cleanToRight_sourceSet
    (P : PathPacking G S T) :
    P.cleanToRight.sourceSet = P.sourceSet := by
  classical
  rw [sourceSet, sourceSet]
  apply Finset.image_congr
  intro i hi
  exact cleanToRight_orient_path_source P i

/-- A packing is terminal-clean when no oriented path has an internal vertex
in either terminal set. -/
def TerminalClean (P : PathPacking G S T) : Prop :=
  P.InternallyDisjointFromSet (S ∪ T)

/-- Clean every path in a packing so that it has no internal vertices in
`S ∪ T`.  This preserves the index set and node-disjointness because each new
path is a subpath of the corresponding old one. -/
noncomputable def cleanToTerminals (P : PathPacking G S T) :
    PathPacking G S T where
  Index := P.Index
  path := fun i => (P.path i).cleanBetweenTerminalSets (P.connects i)
  connects := fun i => (P.path i).cleanBetweenTerminalSets_connects (P.connects i)
  node_disjoint := by
    intro i j hij
    refine (P.node_disjoint hij).mono ?_ ?_
    · exact (P.path i).cleanBetweenTerminalSets_vertexSet_subset (P.connects i)
    · exact (P.path j).cleanBetweenTerminalSets_vertexSet_subset (P.connects j)

@[simp] theorem cleanToTerminals_card (P : PathPacking G S T) :
    P.cleanToTerminals.card = P.card := rfl

theorem cleanToTerminals_path_vertexSet_subset
    (P : PathPacking G S T) (i : P.Index) :
    (P.cleanToTerminals.path i).vertexSet ⊆ (P.path i).vertexSet :=
  (P.path i).cleanBetweenTerminalSets_vertexSet_subset (P.connects i)

/-- Cleaning a packing at both terminal sets makes it terminal-clean. -/
theorem cleanToTerminals_terminalClean (P : PathPacking G S T) :
    P.cleanToTerminals.TerminalClean := by
  intro i
  exact (P.path i).cleanBetweenTerminalSets_internallyDisjointFromSet_union
    (P.connects i)

/-- Map every path in a packing to a supergraph on the same vertex type. -/
def mapLe (P : PathPacking G S T) {H : _root_.SimpleGraph V} (hGH : G ≤ H) :
    PathPacking H S T where
  Index := P.Index
  path := fun i => (P.path i).mapLe hGH
  connects := by
    intro i
    simpa [GraphPath.mapLe, GraphPath.Connects] using P.connects i
  node_disjoint := by
    intro i j hij
    simpa [GraphPath.NodeDisjoint] using P.node_disjoint hij

/-- View a path packing as connecting larger terminal sets.  A path packing
only requires each path to have one endpoint in each terminal set, so enlarging
the allowed terminal sets preserves the same indexed paths and all
node-disjointness information. -/
def widenTerminals {S' T' : Finset V} (P : PathPacking G S T)
    (hS : S ⊆ S') (hT : T ⊆ T') :
    PathPacking G S' T' where
  Index := P.Index
  path := P.path
  connects := by
    intro i
    rcases P.connects i with h | h
    · exact Or.inl ⟨hS h.1, hT h.2⟩
    · exact Or.inr ⟨hT h.1, hS h.2⟩
  node_disjoint := P.node_disjoint

@[simp] theorem widenTerminals_card {S' T' : Finset V}
    (P : PathPacking G S T) (hS : S ⊆ S') (hT : T ⊆ T') :
    (P.widenTerminals hS hT).card = P.card := rfl

@[simp] theorem widenTerminals_path_vertexSet {S' T' : Finset V}
    (P : PathPacking G S T) (hS : S ⊆ S') (hT : T ⊆ T')
    (i : (P.widenTerminals hS hT).Index) :
    ((P.widenTerminals hS hT).path i).vertexSet = (P.path i).vertexSet := rfl

@[simp] theorem widenTerminals_vertexSet {S' T' : Finset V}
    (P : PathPacking G S T) (hS : S ⊆ S') (hT : T ⊆ T') :
    (P.widenTerminals hS hT).vertexSet = P.vertexSet := by
  classical
  ext v
  rw [PathPacking.mem_vertexSet, PathPacking.mem_vertexSet]
  constructor
  · rintro ⟨i, hv⟩
    exact ⟨i, hv⟩
  · rintro ⟨i, hv⟩
    exact ⟨i, hv⟩

/-- Widening terminal sets preserves localized pairwise bridges. -/
theorem widenTerminals_hasPairwiseBridgesIn {S' T' U : Finset V}
    (P : PathPacking G S T) (hS : S ⊆ S') (hT : T ⊆ T')
    (h : P.HasPairwiseBridgesIn U) :
    (P.widenTerminals hS hT).HasPairwiseBridgesIn U := by
  intro i j hij
  rcases h hij with ⟨β, hβU⟩
  let β' : (P.widenTerminals hS hT).BridgeBetween i j := {
    path := β.path
    connects := by
      simpa [PathPacking.widenTerminals] using β.connects
    internallyDisjoint := by
      intro v hv hrows
      exact β.internallyDisjoint hv (by
        simpa [PathPacking.widenTerminals_vertexSet] using hrows)
  }
  exact ⟨β', by simpa [β'] using hβU⟩

@[simp] theorem mapLe_card (P : PathPacking G S T)
    {H : _root_.SimpleGraph V} (hGH : G ≤ H) :
    (P.mapLe hGH).card = P.card := rfl

@[simp] theorem mapLe_vertexSet (P : PathPacking G S T)
    {H : _root_.SimpleGraph V} (hGH : G ≤ H) :
    (P.mapLe hGH).vertexSet = P.vertexSet := by
  classical
  ext v
  rw [mem_vertexSet, mem_vertexSet]
  change (∃ i : P.Index, v ∈ ((P.path i).mapLe hGH).vertexSet) ↔
    ∃ i : P.Index, v ∈ (P.path i).vertexSet
  simp only [GraphPath.mapLe_vertexSet]

@[simp] theorem mapLe_edgeSet (P : PathPacking G S T)
    {H : _root_.SimpleGraph V} (hGH : G ≤ H) :
    (P.mapLe hGH).edgeSet = P.edgeSet := by
  classical
  ext e
  rw [mem_edgeSet, mem_edgeSet]
  change (∃ i : P.Index, e ∈ ((P.path i).mapLe hGH).edgeSet) ↔
    ∃ i : P.Index, e ∈ (P.path i).edgeSet
  simp only [GraphPath.mapLe_edgeSet]

end PathPacking

/-- An oriented perfect path packing from `S` to `T`.

Unlike `PathPacking`, this structure records that each path starts in `S`, ends
in `T`, and that both endpoint maps are bijections.  This is the formal object
needed for the "every vertex of `B_i` to a distinct vertex of `A_{i+1}`"
phrases in the path-of-sets proof.
-/
structure PerfectPathPacking {V : Type*} [DecidableEq V]
    (G : _root_.SimpleGraph V) (S T : Finset V) extends PathPacking G S T where
  /-- Every path starts in the left endpoint set. -/
  source_mem : ∀ i : Index, (path i).source ∈ S
  /-- Every path ends in the right endpoint set. -/
  target_mem : ∀ i : Index, (path i).target ∈ T
  /-- Every left endpoint is used exactly once. -/
  source_bijective :
    Function.Bijective (fun i : Index => (⟨(path i).source, source_mem i⟩ : {v // v ∈ S}))
  /-- Every right endpoint is used exactly once. -/
  target_bijective :
    Function.Bijective (fun i : Index => (⟨(path i).target, target_mem i⟩ : {v // v ∈ T}))

namespace PerfectPathPacking

variable {V : Type*} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {S T : Finset V}

instance (P : PerfectPathPacking G S T) : Fintype P.Index := P.indexFintype
instance (P : PerfectPathPacking G S T) : DecidableEq P.Index := P.indexDecidableEq

/-- The number of paths in a perfect packing. -/
noncomputable def card (P : PerfectPathPacking G S T) : ℕ :=
  Fintype.card P.Index

/-- Reindex a perfect path packing by an equivalent finite index type. -/
noncomputable def reindex {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : PerfectPathPacking G S T) (e : ι ≃ P.Index) :
    PerfectPathPacking G S T where
  toPathPacking := P.toPathPacking.reindex e
  source_mem := fun i => P.source_mem (e i)
  target_mem := fun i => P.target_mem (e i)
  source_bijective := by
    constructor
    · intro i j hij
      apply e.injective
      apply P.source_bijective.1
      exact hij
    · intro v
      rcases P.source_bijective.2 v with ⟨j, hj⟩
      refine ⟨e.symm j, ?_⟩
      change
        (⟨(P.path (e (e.symm j))).source,
          P.source_mem (e (e.symm j))⟩ : {x // x ∈ S}) = v
      simpa using hj
  target_bijective := by
    constructor
    · intro i j hij
      apply e.injective
      apply P.target_bijective.1
      exact hij
    · intro v
      rcases P.target_bijective.2 v with ⟨j, hj⟩
      refine ⟨e.symm j, ?_⟩
      change
        (⟨(P.path (e (e.symm j))).target,
          P.target_mem (e (e.symm j))⟩ : {x // x ∈ T}) = v
      simpa using hj

@[simp] theorem reindex_card {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : PerfectPathPacking G S T) (e : ι ≃ P.Index) :
    (P.reindex e).card = P.card := by
  dsimp [reindex, card, PathPacking.reindex]
  exact Fintype.card_congr e

@[simp] theorem reindex_path_vertexSet
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : PerfectPathPacking G S T) (e : ι ≃ P.Index) (i : ι) :
    ((P.reindex e).path i).vertexSet = (P.path (e i)).vertexSet := rfl

/-- The canonical equivalence from `Fin P.card` to the index type of a
perfect path packing. -/
noncomputable def finIndexEquiv (P : PerfectPathPacking G S T) :
    Fin P.card ≃ P.Index := by
  simpa [card] using (Fintype.equivFin P.Index).symm

/-- Reindex a perfect path packing by `Fin P.card`. -/
noncomputable def finReindex
    (P : PerfectPathPacking G S T) : PerfectPathPacking G S T :=
  P.reindex P.finIndexEquiv

@[simp] theorem finReindex_card (P : PerfectPathPacking G S T) :
    P.finReindex.card = P.card := by
  simp [finReindex]

/-- The identity perfect packing on a finite terminal set, consisting of one
length-zero path at each terminal. -/
noncomputable def refl (G : _root_.SimpleGraph V) (S : Finset V) :
    PerfectPathPacking G S S where
  toPathPacking := {
    Index := Fin S.card
    path := fun i => GraphPath.refl G ((S.equivFin.symm i).1)
    connects := by
      intro i
      exact Or.inl ⟨(S.equivFin.symm i).2, (S.equivFin.symm i).2⟩
    node_disjoint := by
      intro i j hij
      rw [GraphPath.NodeDisjoint, GraphPath.refl_vertexSet,
        GraphPath.refl_vertexSet, Finset.disjoint_singleton_left]
      intro h
      apply hij
      apply S.equivFin.symm.injective
      have hval :
          (S.equivFin.symm i).1 = (S.equivFin.symm j).1 := by
        simpa using h
      exact Subtype.ext hval
  }
  source_mem := fun i => (S.equivFin.symm i).2
  target_mem := fun i => (S.equivFin.symm i).2
  source_bijective := by
    constructor
    · intro i j h
      apply S.equivFin.symm.injective
      exact Subtype.ext (congrArg Subtype.val h)
    · intro v
      refine ⟨S.equivFin v, ?_⟩
      apply Subtype.ext
      simp
  target_bijective := by
    constructor
    · intro i j h
      apply S.equivFin.symm.injective
      exact Subtype.ext (congrArg Subtype.val h)
    · intro v
      refine ⟨S.equivFin v, ?_⟩
      apply Subtype.ext
      simp

@[simp] theorem refl_card (G : _root_.SimpleGraph V) (S : Finset V) :
    (PerfectPathPacking.refl G S).card = S.card := by
  classical
  change Fintype.card (Fin S.card) = S.card
  simp

@[simp] theorem toPathPacking_card (P : PerfectPathPacking G S T) :
    P.toPathPacking.card = P.card := rfl

/-- Transfer every path in a perfect packing to another graph on the same vertex
type, preserving the endpoint bijections. -/
def transfer (P : PerfectPathPacking G S T) (H : _root_.SimpleGraph V)
    (h : ∀ i : P.Index, ∀ e, e ∈ (P.path i).walk.edges → e ∈ H.edgeSet) :
    PerfectPathPacking H S T where
  toPathPacking := P.toPathPacking.transfer H h
  source_mem := P.source_mem
  target_mem := P.target_mem
  source_bijective := by
    simpa [PathPacking.transfer, GraphPath.transfer] using P.source_bijective
  target_bijective := by
    simpa [PathPacking.transfer, GraphPath.transfer] using P.target_bijective

/-- A perfect packing has as many paths as left endpoints. -/
theorem card_eq_left_card (P : PerfectPathPacking G S T) :
    P.card = S.card := by
  classical
  dsimp [card]
  rw [← Fintype.card_coe]
  exact Fintype.card_congr (Equiv.ofBijective _ P.source_bijective)

/-- A perfect packing has as many paths as right endpoints. -/
theorem card_eq_right_card (P : PerfectPathPacking G S T) :
    P.card = T.card := by
  classical
  dsimp [card]
  rw [← Fintype.card_coe]
  exact Fintype.card_congr (Equiv.ofBijective _ P.target_bijective)

/-- The bijection from path indices to left endpoints. -/
noncomputable def sourceEquiv (P : PerfectPathPacking G S T) :
    P.Index ≃ {v // v ∈ S} :=
  Equiv.ofBijective _ P.source_bijective

/-- The bijection from path indices to right endpoints. -/
noncomputable def targetEquiv (P : PerfectPathPacking G S T) :
    P.Index ≃ {v // v ∈ T} :=
  Equiv.ofBijective _ P.target_bijective

/-- The unique path index whose source is a given left endpoint. -/
noncomputable def indexOfSource (P : PerfectPathPacking G S T)
    (v : {x // x ∈ S}) : P.Index :=
  (P.sourceEquiv).symm v

/-- The unique path index whose target is a given right endpoint. -/
noncomputable def indexOfTarget (P : PerfectPathPacking G S T)
    (v : {x // x ∈ T}) : P.Index :=
  (P.targetEquiv).symm v

@[simp] theorem source_indexOfSource (P : PerfectPathPacking G S T)
    (v : {x // x ∈ S}) :
    (⟨(P.path (P.indexOfSource v)).source,
      P.source_mem (P.indexOfSource v)⟩ : {x // x ∈ S}) = v := by
  exact (P.sourceEquiv).apply_symm_apply v

@[simp] theorem target_indexOfTarget (P : PerfectPathPacking G S T)
    (v : {x // x ∈ T}) :
    (⟨(P.path (P.indexOfTarget v)).target,
      P.target_mem (P.indexOfTarget v)⟩ : {x // x ∈ T}) = v := by
  exact (P.targetEquiv).apply_symm_apply v

@[simp] theorem indexOfSource_source (P : PerfectPathPacking G S T)
    (i : P.Index) :
    P.indexOfSource ⟨(P.path i).source, P.source_mem i⟩ = i := by
  exact (P.sourceEquiv).symm_apply_apply i

@[simp] theorem indexOfTarget_target (P : PerfectPathPacking G S T)
    (i : P.Index) :
    P.indexOfTarget ⟨(P.path i).target, P.target_mem i⟩ = i := by
  exact (P.targetEquiv).symm_apply_apply i

/-- Given perfect packings from `S` to `T` and from `T` to `U`, this is the
index of the second packing whose source matches the target of the first path. -/
noncomputable def indexOfSourceTarget {U : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (i : P.Index) : Q.Index :=
  Q.indexOfSource ⟨(P.path i).target, P.target_mem i⟩

@[simp] theorem source_indexOfSourceTarget {U : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (i : P.Index) :
    (Q.path (P.indexOfSourceTarget Q i)).source = (P.path i).target := by
  have h :=
    congrArg Subtype.val
      (source_indexOfSource Q ⟨(P.path i).target, P.target_mem i⟩)
  simpa [indexOfSourceTarget] using h

/-- A path in a perfect packing meets the source terminal set only at its own
source.  If it met another source terminal, it would meet the path whose source
is that terminal, contradicting node-disjointness. -/
theorem eq_source_of_mem_left_of_mem_path_vertexSet
    (P : PerfectPathPacking G S T) (i : P.Index)
    {v : V} (hvS : v ∈ S) (hvpath : v ∈ (P.path i).vertexSet) :
    v = (P.path i).source := by
  classical
  let j := P.indexOfSource ⟨v, hvS⟩
  have hsource_j : (P.path j).source = v := by
    have h :=
      congrArg Subtype.val (P.source_indexOfSource ⟨v, hvS⟩)
    simpa [j] using h
  by_cases hji : j = i
  · simpa [hji] using hsource_j.symm
  · have hvj : v ∈ (P.path j).vertexSet := by
      simpa [hsource_j] using GraphPath.source_mem_vertexSet (P.path j)
    exact False.elim
      (Finset.disjoint_left.mp (P.toPathPacking.node_disjoint hji)
        hvj hvpath)

/-- A path in a perfect packing meets the target terminal set only at its own
target. -/
theorem eq_target_of_mem_right_of_mem_path_vertexSet
    (P : PerfectPathPacking G S T) (i : P.Index)
    {v : V} (hvT : v ∈ T) (hvpath : v ∈ (P.path i).vertexSet) :
    v = (P.path i).target := by
  classical
  let j := P.indexOfTarget ⟨v, hvT⟩
  have htarget_j : (P.path j).target = v := by
    have h :=
      congrArg Subtype.val (P.target_indexOfTarget ⟨v, hvT⟩)
    simpa [j] using h
  by_cases hji : j = i
  · simpa [hji] using htarget_j.symm
  · have hvj : v ∈ (P.path j).vertexSet := by
      simpa [htarget_j] using GraphPath.target_mem_vertexSet (P.path j)
    exact False.elim
      (Finset.disjoint_left.mp (P.toPathPacking.node_disjoint hji)
        hvj hvpath)

/-- Map every path in a perfect packing to a supergraph on the same vertex type. -/
def mapLe (P : PerfectPathPacking G S T) {H : _root_.SimpleGraph V}
    (hGH : G ≤ H) :
    PerfectPathPacking H S T where
  toPathPacking := P.toPathPacking.mapLe hGH
  source_mem := P.source_mem
  target_mem := P.target_mem
  source_bijective := by
    simpa [PathPacking.mapLe, GraphPath.mapLe] using P.source_bijective
  target_bijective := by
    simpa [PathPacking.mapLe, GraphPath.mapLe] using P.target_bijective

@[simp] theorem mapLe_card (P : PerfectPathPacking G S T)
    {H : _root_.SimpleGraph V} (hGH : G ≤ H) :
    (P.mapLe hGH).card = P.card := rfl

@[simp] theorem mapLe_vertexSet (P : PerfectPathPacking G S T)
    {H : _root_.SimpleGraph V} (hGH : G ≤ H) :
    (P.mapLe hGH).toPathPacking.vertexSet = P.toPathPacking.vertexSet := by
  simp [mapLe]

@[simp] theorem mapLe_edgeSet (P : PerfectPathPacking G S T)
    {H : _root_.SimpleGraph V} (hGH : G ≤ H) :
    (P.mapLe hGH).toPathPacking.edgeSet = P.toPathPacking.edgeSet := by
  simp [mapLe]

/-- The disjoint union of two perfect path packings with disjoint terminal
sets and mutually disjoint paths.  The index type is the sum of the two input
index types. -/
noncomputable def disjointUnion
    {S₁ T₁ S₂ T₂ : Finset V}
    (P₁ : PerfectPathPacking G S₁ T₁) (P₂ : PerfectPathPacking G S₂ T₂)
    (hS : Disjoint S₁ S₂) (hT : Disjoint T₁ T₂)
    (hnode : P₁.toPathPacking.MutuallyNodeDisjoint P₂.toPathPacking) :
    PerfectPathPacking G (S₁ ∪ S₂) (T₁ ∪ T₂) where
  toPathPacking := {
    Index := P₁.Index ⊕ P₂.Index
    path := fun i =>
      match i with
      | Sum.inl a => P₁.path a
      | Sum.inr b => P₂.path b
    connects := by
      intro i
      cases i with
      | inl a =>
          exact Or.inl
            ⟨Finset.mem_union_left _ (P₁.source_mem a),
              Finset.mem_union_left _ (P₁.target_mem a)⟩
      | inr b =>
          exact Or.inl
            ⟨Finset.mem_union_right _ (P₂.source_mem b),
              Finset.mem_union_right _ (P₂.target_mem b)⟩
    node_disjoint := by
      intro i j hij
      cases i with
      | inl a =>
          cases j with
          | inl b =>
              exact P₁.toPathPacking.node_disjoint
                (fun h => hij (by simp [h]))
          | inr b =>
              exact hnode a b
      | inr a =>
          cases j with
          | inl b =>
              exact GraphPath.nodeDisjoint_symm (hnode b a)
          | inr b =>
              exact P₂.toPathPacking.node_disjoint
                (fun h => hij (by simp [h]))
  }
  source_mem := by
    intro i
    cases i with
    | inl a => exact Finset.mem_union_left _ (P₁.source_mem a)
    | inr b => exact Finset.mem_union_right _ (P₂.source_mem b)
  target_mem := by
    intro i
    cases i with
    | inl a => exact Finset.mem_union_left _ (P₁.target_mem a)
    | inr b => exact Finset.mem_union_right _ (P₂.target_mem b)
  source_bijective := by
    classical
    constructor
    · intro i j hij
      cases i with
      | inl a =>
          cases j with
          | inl b =>
              apply congrArg Sum.inl
              apply P₁.source_bijective.1
              have hval : (P₁.path a).source = (P₁.path b).source :=
                congrArg (fun x : {v // v ∈ S₁ ∪ S₂} => x.1) hij
              exact Subtype.ext hval
          | inr b =>
              have hval :
                  (P₁.path a).source = (P₂.path b).source :=
                congrArg Subtype.val hij
              exact False.elim
                (Finset.disjoint_left.mp hS (P₁.source_mem a)
                  (by simpa [← hval] using P₂.source_mem b))
      | inr a =>
          cases j with
          | inl b =>
              have hval :
                  (P₂.path a).source = (P₁.path b).source :=
                congrArg Subtype.val hij
              exact False.elim
                (Finset.disjoint_left.mp hS (P₁.source_mem b)
                  (by simpa [hval] using P₂.source_mem a))
          | inr b =>
              apply congrArg Sum.inr
              apply P₂.source_bijective.1
              have hval : (P₂.path a).source = (P₂.path b).source :=
                congrArg (fun x : {v // v ∈ S₁ ∪ S₂} => x.1) hij
              exact Subtype.ext hval
    · rintro ⟨v, hv⟩
      rcases Finset.mem_union.mp hv with hv₁ | hv₂
      · rcases P₁.source_bijective.2 ⟨v, hv₁⟩ with ⟨i, hi⟩
        refine ⟨Sum.inl i, ?_⟩
        have hval : (P₁.path i).source = v :=
          congrArg (fun x : {v // v ∈ S₁} => x.1) hi
        exact Subtype.ext hval
      · rcases P₂.source_bijective.2 ⟨v, hv₂⟩ with ⟨i, hi⟩
        refine ⟨Sum.inr i, ?_⟩
        have hval : (P₂.path i).source = v :=
          congrArg (fun x : {v // v ∈ S₂} => x.1) hi
        exact Subtype.ext hval
  target_bijective := by
    classical
    constructor
    · intro i j hij
      cases i with
      | inl a =>
          cases j with
          | inl b =>
              apply congrArg Sum.inl
              apply P₁.target_bijective.1
              have hval : (P₁.path a).target = (P₁.path b).target :=
                congrArg (fun x : {v // v ∈ T₁ ∪ T₂} => x.1) hij
              exact Subtype.ext hval
          | inr b =>
              have hval :
                  (P₁.path a).target = (P₂.path b).target :=
                congrArg Subtype.val hij
              exact False.elim
                (Finset.disjoint_left.mp hT (P₁.target_mem a)
                  (by simpa [← hval] using P₂.target_mem b))
      | inr a =>
          cases j with
          | inl b =>
              have hval :
                  (P₂.path a).target = (P₁.path b).target :=
                congrArg Subtype.val hij
              exact False.elim
                (Finset.disjoint_left.mp hT (P₁.target_mem b)
                  (by simpa [hval] using P₂.target_mem a))
          | inr b =>
              apply congrArg Sum.inr
              apply P₂.target_bijective.1
              have hval : (P₂.path a).target = (P₂.path b).target :=
                congrArg (fun x : {v // v ∈ T₁ ∪ T₂} => x.1) hij
              exact Subtype.ext hval
    · rintro ⟨v, hv⟩
      rcases Finset.mem_union.mp hv with hv₁ | hv₂
      · rcases P₁.target_bijective.2 ⟨v, hv₁⟩ with ⟨i, hi⟩
        refine ⟨Sum.inl i, ?_⟩
        have hval : (P₁.path i).target = v :=
          congrArg (fun x : {v // v ∈ T₁} => x.1) hi
        exact Subtype.ext hval
      · rcases P₂.target_bijective.2 ⟨v, hv₂⟩ with ⟨i, hi⟩
        refine ⟨Sum.inr i, ?_⟩
        have hval : (P₂.path i).target = v :=
          congrArg (fun x : {v // v ∈ T₂} => x.1) hi
        exact Subtype.ext hval

@[simp] theorem disjointUnion_card
    {S₁ T₁ S₂ T₂ : Finset V}
    (P₁ : PerfectPathPacking G S₁ T₁) (P₂ : PerfectPathPacking G S₂ T₂)
    (hS : Disjoint S₁ S₂) (hT : Disjoint T₁ T₂)
    (hnode : P₁.toPathPacking.MutuallyNodeDisjoint P₂.toPathPacking) :
    (P₁.disjointUnion P₂ hS hT hnode).card = P₁.card + P₂.card := by
  dsimp [disjointUnion, card, PathPacking.card]
  exact Fintype.card_sum

/-- Edges of a disjoint union packing come from one of the two input packings.
-/
theorem disjointUnion_edgeSet_subset_union
    {S₁ T₁ S₂ T₂ : Finset V}
    (P₁ : PerfectPathPacking G S₁ T₁) (P₂ : PerfectPathPacking G S₂ T₂)
    (hS : Disjoint S₁ S₂) (hT : Disjoint T₁ T₂)
    (hnode : P₁.toPathPacking.MutuallyNodeDisjoint P₂.toPathPacking) :
    (P₁.disjointUnion P₂ hS hT hnode).toPathPacking.edgeSet ⊆
      P₁.toPathPacking.edgeSet ∪ P₂.toPathPacking.edgeSet := by
  classical
  intro e he
  rcases ((P₁.disjointUnion P₂ hS hT hnode).toPathPacking.mem_edgeSet).1 he with
    ⟨i, hei⟩
  cases i with
  | inl a =>
      exact Finset.mem_union_left _
        ((P₁.toPathPacking.mem_edgeSet).2
          ⟨a, by simpa [disjointUnion] using hei⟩)
  | inr b =>
      exact Finset.mem_union_right _
        ((P₂.toPathPacking.mem_edgeSet).2
          ⟨b, by simpa [disjointUnion] using hei⟩)

/-- A disjoint union stays in any vertex set containing every path of both
input packings. -/
theorem disjointUnion_staysIn
    {S₁ T₁ S₂ T₂ : Finset V}
    (P₁ : PerfectPathPacking G S₁ T₁) (P₂ : PerfectPathPacking G S₂ T₂)
    (hS : Disjoint S₁ S₂) (hT : Disjoint T₁ T₂)
    (hnode : P₁.toPathPacking.MutuallyNodeDisjoint P₂.toPathPacking)
    {U : Finset V}
    (hP₁ : P₁.toPathPacking.StaysIn U)
    (hP₂ : P₂.toPathPacking.StaysIn U) :
    (P₁.disjointUnion P₂ hS hT hnode).toPathPacking.StaysIn U := by
  intro i
  cases i with
  | inl a =>
      simpa [disjointUnion] using hP₁ a
  | inr b =>
      simpa [disjointUnion] using hP₂ b

/-- A disjoint union is internally disjoint from a vertex set when each input
packing is. -/
theorem disjointUnion_internallyDisjointFromSet
    {S₁ T₁ S₂ T₂ : Finset V}
    (P₁ : PerfectPathPacking G S₁ T₁) (P₂ : PerfectPathPacking G S₂ T₂)
    (hS : Disjoint S₁ S₂) (hT : Disjoint T₁ T₂)
    (hnode : P₁.toPathPacking.MutuallyNodeDisjoint P₂.toPathPacking)
    {U : Finset V}
    (hP₁ : P₁.toPathPacking.InternallyDisjointFromSet U)
    (hP₂ : P₂.toPathPacking.InternallyDisjointFromSet U) :
    (P₁.disjointUnion P₂ hS hT hnode).toPathPacking.InternallyDisjointFromSet U := by
  intro i
  cases i with
  | inl a =>
      simpa [disjointUnion] using hP₁ a
  | inr b =>
      simpa [disjointUnion] using hP₂ b

/-- Lift a perfect path packing that stays inside a finite vertex set to the
induced graph on that set. -/
noncomputable def induce (P : PerfectPathPacking G S T) (U : Finset V)
    (hP : P.toPathPacking.StaysIn U) (hS : S ⊆ U) (hT : T ⊆ U) :
    PerfectPathPacking (G.induce {v : V | v ∈ U})
      (PathPacking.subtypeFinset S U hS)
      (PathPacking.subtypeFinset T U hT) where
  toPathPacking := P.toPathPacking.induce U hP hS hT
  source_mem := by
    intro i
    change ((P.path i).induce U (hP i)).source ∈
      PathPacking.subtypeFinset S U hS
    rw [GraphPath.induce_source]
    exact (PathPacking.mem_subtypeFinset hS _).2 (P.source_mem i)
  target_mem := by
    intro i
    change ((P.path i).induce U (hP i)).target ∈
      PathPacking.subtypeFinset T U hT
    rw [GraphPath.induce_target]
    exact (PathPacking.mem_subtypeFinset hT _).2 (P.target_mem i)
  source_bijective := by
    constructor
    · intro i j hij
      apply P.source_bijective.1
      apply Subtype.ext
      have hval :
          (((⟨((P.path i).induce U (hP i)).source,
              by
                rw [GraphPath.induce_source]
                exact (PathPacking.mem_subtypeFinset hS _).2
                  (P.source_mem i)⟩ :
              {v // v ∈ PathPacking.subtypeFinset S U hS}).1 :
              {v : V // v ∈ U}).1) =
            (((⟨((P.path j).induce U (hP j)).source,
              by
                rw [GraphPath.induce_source]
                exact (PathPacking.mem_subtypeFinset hS _).2
                  (P.source_mem j)⟩ :
              {v // v ∈ PathPacking.subtypeFinset S U hS}).1 :
              {v : V // v ∈ U}).1) :=
        congrArg
          (fun x : {v // v ∈ PathPacking.subtypeFinset S U hS} =>
            ((x.1 : {v : V // v ∈ U}).1)) hij
      simpa using hval
    · intro v
      have hvS : v.1.1 ∈ S :=
        (PathPacking.mem_subtypeFinset hS v.1).1 v.2
      rcases P.source_bijective.2 ⟨v.1.1, hvS⟩ with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      have hval : (P.path i).source = v.1.1 :=
        congrArg Subtype.val hi
      simpa [PathPacking.induce] using hval
  target_bijective := by
    constructor
    · intro i j hij
      apply P.target_bijective.1
      apply Subtype.ext
      have hval :
          (((⟨((P.path i).induce U (hP i)).target,
              by
                rw [GraphPath.induce_target]
                exact (PathPacking.mem_subtypeFinset hT _).2
                  (P.target_mem i)⟩ :
              {v // v ∈ PathPacking.subtypeFinset T U hT}).1 :
              {v : V // v ∈ U}).1) =
            (((⟨((P.path j).induce U (hP j)).target,
              by
                rw [GraphPath.induce_target]
                exact (PathPacking.mem_subtypeFinset hT _).2
                  (P.target_mem j)⟩ :
              {v // v ∈ PathPacking.subtypeFinset T U hT}).1 :
              {v : V // v ∈ U}).1) :=
        congrArg
          (fun x : {v // v ∈ PathPacking.subtypeFinset T U hT} =>
            ((x.1 : {v : V // v ∈ U}).1)) hij
      simpa using hval
    · intro v
      have hvT : v.1.1 ∈ T :=
        (PathPacking.mem_subtypeFinset hT v.1).1 v.2
      rcases P.target_bijective.2 ⟨v.1.1, hvT⟩ with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      have hval : (P.path i).target = v.1.1 :=
        congrArg Subtype.val hi
      simpa [PathPacking.induce] using hval

@[simp] theorem induce_card (P : PerfectPathPacking G S T) (U : Finset V)
    (hP : P.toPathPacking.StaysIn U) (hS : S ⊆ U) (hT : T ⊆ U) :
    (P.induce U hP hS hT).card = P.card := rfl

/-- Reinterpret a perfect path packing after replacing its terminal sets by
definitionally equal finite sets.  The path index type is preserved exactly,
which is useful when later proofs need to refer back to the original indexed
paths. -/
def copyTerminals {S' T' : Finset V} (P : PerfectPathPacking G S T)
    (hS : S = S') (hT : T = T') :
    PerfectPathPacking G S' T' where
  toPathPacking := {
    Index := P.Index
    path := P.path
    connects := by
      intro i
      rcases P.connects i with h | h
      · exact Or.inl ⟨by simpa [← hS] using h.1,
          by simpa [← hT] using h.2⟩
      · exact Or.inr ⟨by simpa [← hT] using h.1,
          by simpa [← hS] using h.2⟩
    node_disjoint := P.node_disjoint
  }
  source_mem := by
    intro i
    simpa [← hS] using P.source_mem i
  target_mem := by
    intro i
    simpa [← hT] using P.target_mem i
  source_bijective := by
    constructor
    · intro i j hij
      apply P.source_bijective.1
      have hsrc : (P.path i).source = (P.path j).source :=
        congrArg (fun x : {v // v ∈ S'} => x.1) hij
      exact Subtype.ext hsrc
    · rintro ⟨v, hv⟩
      have hvS : v ∈ S := by simpa [hS] using hv
      rcases P.source_bijective.2 ⟨v, hvS⟩ with ⟨i, hi⟩
      have hsrc : (P.path i).source = v :=
        congrArg (fun x : {v // v ∈ S} => x.1) hi
      exact ⟨i, Subtype.ext hsrc⟩
  target_bijective := by
    constructor
    · intro i j hij
      apply P.target_bijective.1
      have htgt : (P.path i).target = (P.path j).target :=
        congrArg (fun x : {v // v ∈ T'} => x.1) hij
      exact Subtype.ext htgt
    · rintro ⟨v, hv⟩
      have hvT : v ∈ T := by simpa [hT] using hv
      rcases P.target_bijective.2 ⟨v, hvT⟩ with ⟨i, hi⟩
      have htgt : (P.path i).target = v :=
        congrArg (fun x : {v // v ∈ T} => x.1) hi
      exact ⟨i, Subtype.ext htgt⟩

@[simp] theorem copyTerminals_card {S' T' : Finset V}
    (P : PerfectPathPacking G S T) (hS : S = S') (hT : T = T') :
    (P.copyTerminals hS hT).card = P.card := rfl

@[simp] theorem copyTerminals_path_vertexSet {S' T' : Finset V}
    (P : PerfectPathPacking G S T) (hS : S = S') (hT : T = T')
    (i : (P.copyTerminals hS hT).Index) :
    ((P.copyTerminals hS hT).path i).vertexSet = (P.path i).vertexSet := rfl

@[simp] theorem copyTerminals_vertexSet {S' T' : Finset V}
    (P : PerfectPathPacking G S T) (hS : S = S') (hT : T = T') :
    (P.copyTerminals hS hT).toPathPacking.vertexSet =
      P.toPathPacking.vertexSet := by
  classical
  ext v
  rw [PathPacking.mem_vertexSet, PathPacking.mem_vertexSet]
  constructor
  · rintro ⟨i, hv⟩
    exact ⟨i, hv⟩
  · rintro ⟨i, hv⟩
    exact ⟨i, hv⟩

@[simp] theorem copyTerminals_edgeSet {S' T' : Finset V}
    (P : PerfectPathPacking G S T) (hS : S = S') (hT : T = T') :
    (P.copyTerminals hS hT).toPathPacking.edgeSet =
      P.toPathPacking.edgeSet := by
  classical
  ext e
  rw [PathPacking.mem_edgeSet, PathPacking.mem_edgeSet]
  constructor
  · rintro ⟨i, he⟩
    exact ⟨i, he⟩
  · rintro ⟨i, he⟩
    exact ⟨i, he⟩

/-- Copying terminal-set equalities preserves containment of all path vertices
in a fixed set. -/
theorem copyTerminals_staysIn {S' T' U : Finset V}
    (P : PerfectPathPacking G S T) (hS : S = S') (hT : T = T')
    (hP : P.toPathPacking.StaysIn U) :
    (P.copyTerminals hS hT).toPathPacking.StaysIn U := by
  intro i v hv
  exact hP i (by simpa [copyTerminals] using hv)

/-- The sources of a chosen set of paths in a perfect packing. -/
noncomputable def sourceSet (P : PerfectPathPacking G S T)
    (I : Finset P.Index) : Finset V :=
  I.image fun i => (P.path i).source

/-- The targets of a chosen set of paths in a perfect packing. -/
noncomputable def targetSet (P : PerfectPathPacking G S T)
    (I : Finset P.Index) : Finset V :=
  I.image fun i => (P.path i).target

theorem sourceSet_subset_left (P : PerfectPathPacking G S T)
    (I : Finset P.Index) :
    P.sourceSet I ⊆ S := by
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨i, _hi, rfl⟩
  exact P.source_mem i

theorem targetSet_subset_right (P : PerfectPathPacking G S T)
    (I : Finset P.Index) :
    P.targetSet I ⊆ T := by
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨i, _hi, rfl⟩
  exact P.target_mem i

/-- Source endpoints are monotone with respect to the chosen index set. -/
theorem sourceSet_mono (P : PerfectPathPacking G S T)
    {I J : Finset P.Index} (hIJ : I ⊆ J) :
    P.sourceSet I ⊆ P.sourceSet J := by
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
  exact Finset.mem_image.mpr ⟨i, hIJ hi, rfl⟩

/-- Target endpoints are monotone with respect to the chosen index set. -/
theorem targetSet_mono (P : PerfectPathPacking G S T)
    {I J : Finset P.Index} (hIJ : I ⊆ J) :
    P.targetSet I ⊆ P.targetSet J := by
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
  exact Finset.mem_image.mpr ⟨i, hIJ hi, rfl⟩

/-- Disjoint index sets in a perfect packing have disjoint source endpoint
sets. -/
theorem sourceSet_disjoint (P : PerfectPathPacking G S T)
    {I J : Finset P.Index} (hIJ : Disjoint I J) :
    Disjoint (P.sourceSet I) (P.sourceSet J) := by
  rw [Finset.disjoint_left]
  intro v hvI hvJ
  rcases Finset.mem_image.mp hvI with ⟨i, hi, rfl⟩
  rcases Finset.mem_image.mp hvJ with ⟨j, hj, hsource⟩
  have hij : i = j := by
    apply P.source_bijective.1
    exact Subtype.ext hsource.symm
  exact Finset.disjoint_left.mp hIJ hi (by simpa [hij] using hj)

/-- Disjoint index sets in a perfect packing have disjoint target endpoint
sets. -/
theorem targetSet_disjoint (P : PerfectPathPacking G S T)
    {I J : Finset P.Index} (hIJ : Disjoint I J) :
    Disjoint (P.targetSet I) (P.targetSet J) := by
  rw [Finset.disjoint_left]
  intro v hvI hvJ
  rcases Finset.mem_image.mp hvI with ⟨i, hi, rfl⟩
  rcases Finset.mem_image.mp hvJ with ⟨j, hj, htarget⟩
  have hij : i = j := by
    apply P.target_bijective.1
    exact Subtype.ext htarget.symm
  exact Finset.disjoint_left.mp hIJ hi (by simpa [hij] using hj)

@[simp] theorem sourceSet_card (P : PerfectPathPacking G S T)
    (I : Finset P.Index) :
    (P.sourceSet I).card = I.card := by
  classical
  rw [sourceSet, Finset.card_image_of_injective]
  intro i j hij
  apply P.source_bijective.1
  exact Subtype.ext hij

@[simp] theorem targetSet_card (P : PerfectPathPacking G S T)
    (I : Finset P.Index) :
    (P.targetSet I).card = I.card := by
  classical
  rw [targetSet, Finset.card_image_of_injective]
  intro i j hij
  apply P.target_bijective.1
  exact Subtype.ext hij

/-- Restrict a perfect path packing to a finite set of its path indices.  The
new terminal sets are the corresponding source and target images. -/
noncomputable def restrictIndexSet (P : PerfectPathPacking G S T)
    (I : Finset P.Index) :
    PerfectPathPacking G (P.sourceSet I) (P.targetSet I) where
  toPathPacking := {
    Index := {i : P.Index // i ∈ I}
    path := fun i => P.path i.1
    connects := by
      intro i
      exact Or.inl ⟨Finset.mem_image.mpr ⟨i.1, i.2, rfl⟩,
        Finset.mem_image.mpr ⟨i.1, i.2, rfl⟩⟩
    node_disjoint := by
      intro i j hij
      exact P.node_disjoint (fun h => hij (Subtype.ext h))
  }
  source_mem := by
    intro i
    exact Finset.mem_image.mpr ⟨i.1, i.2, rfl⟩
  target_mem := by
    intro i
    exact Finset.mem_image.mpr ⟨i.1, i.2, rfl⟩
  source_bijective := by
    constructor
    · intro i j hij
      have hsrc : (P.path i.1).source = (P.path j.1).source :=
        congrArg (fun x : {v // v ∈ P.sourceSet I} => x.1) hij
      apply Subtype.ext
      apply P.source_bijective.1
      exact Subtype.ext hsrc
    · rintro ⟨v, hv⟩
      rcases Finset.mem_image.mp hv with ⟨i, hi, hsource⟩
      exact ⟨⟨i, hi⟩, Subtype.ext hsource⟩
  target_bijective := by
    constructor
    · intro i j hij
      have htgt : (P.path i.1).target = (P.path j.1).target :=
        congrArg (fun x : {v // v ∈ P.targetSet I} => x.1) hij
      apply Subtype.ext
      apply P.target_bijective.1
      exact Subtype.ext htgt
    · rintro ⟨v, hv⟩
      rcases Finset.mem_image.mp hv with ⟨i, hi, htarget⟩
      exact ⟨⟨i, hi⟩, Subtype.ext htarget⟩

@[simp] theorem restrictIndexSet_card (P : PerfectPathPacking G S T)
    (I : Finset P.Index) :
    (P.restrictIndexSet I).card = I.card := by
  classical
  exact Fintype.card_coe I

@[simp] theorem restrictIndexSet_path_vertexSet
    (P : PerfectPathPacking G S T) (I : Finset P.Index)
    (i : (P.restrictIndexSet I).Index) :
    ((P.restrictIndexSet I).path i).vertexSet = (P.path i.1).vertexSet := rfl

@[simp] theorem restrictIndexSet_path_edgeSet
    (P : PerfectPathPacking G S T) (I : Finset P.Index)
    (i : (P.restrictIndexSet I).Index) :
    ((P.restrictIndexSet I).path i).edgeSet = (P.path i.1).edgeSet := rfl

theorem restrictIndexSet_vertexSet_subset
    (P : PerfectPathPacking G S T) (I : Finset P.Index) :
    (P.restrictIndexSet I).toPathPacking.vertexSet ⊆
      P.toPathPacking.vertexSet := by
  classical
  intro v hv
  rcases ((P.restrictIndexSet I).toPathPacking.mem_vertexSet).1 hv with
    ⟨i, hvPath⟩
  exact (P.toPathPacking.mem_vertexSet).2 ⟨i.1, hvPath⟩

/-- A packing restricted to selected indices stays inside the vertex trace of
the original perfect packing. -/
theorem restrictIndexSet_staysIn_vertexSet
    (P : PerfectPathPacking G S T) (I : Finset P.Index) :
    (P.restrictIndexSet I).toPathPacking.StaysIn P.toPathPacking.vertexSet := by
  intro i v hv
  exact P.toPathPacking.path_vertexSet_subset_vertexSet i.1 (by simpa using hv)

/-- Restricting a perfect packing to selected indices preserves internal
disjointness from a fixed vertex set. -/
theorem restrictIndexSet_internallyDisjointFromSet
    (P : PerfectPathPacking G S T) (I : Finset P.Index) {U : Finset V}
    (hP : P.toPathPacking.InternallyDisjointFromSet U) :
    (P.restrictIndexSet I).toPathPacking.InternallyDisjointFromSet U := by
  intro i v hv hvU
  exact hP i.1 (by simpa using hv) hvU

theorem restrictIndexSet_edgeSet_subset
    (P : PerfectPathPacking G S T) (I : Finset P.Index) :
    (P.restrictIndexSet I).toPathPacking.edgeSet ⊆
      P.toPathPacking.edgeSet := by
  classical
  intro e he
  rcases ((P.restrictIndexSet I).toPathPacking.mem_edgeSet).1 he with
    ⟨i, hePath⟩
  exact (P.toPathPacking.mem_edgeSet).2 ⟨i.1, by simpa using hePath⟩

/-- The indices of paths whose source lies in a prescribed subset of the left
terminal set. -/
noncomputable def sourceIndexSetOfSubset
    (P : PerfectPathPacking G S T) (S' : Finset V) : Finset P.Index :=
  Finset.univ.filter fun i => (P.path i).source ∈ S'

@[simp] theorem mem_sourceIndexSetOfSubset
    (P : PerfectPathPacking G S T) (S' : Finset V) (i : P.Index) :
    i ∈ P.sourceIndexSetOfSubset S' ↔ (P.path i).source ∈ S' := by
  simp [sourceIndexSetOfSubset]

/-- Restricting by a source subset uses exactly that subset as the new source
terminal set. -/
theorem sourceSet_sourceIndexSetOfSubset
    (P : PerfectPathPacking G S T) {S' : Finset V} (hS : S' ⊆ S) :
    P.sourceSet (P.sourceIndexSetOfSubset S') = S' := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
    exact (P.mem_sourceIndexSetOfSubset S' i).mp hi
  · intro hv
    rcases P.source_bijective.2 ⟨v, hS hv⟩ with ⟨i, hi⟩
    have hsource : (P.path i).source = v :=
      congrArg Subtype.val hi
    rw [sourceSet]
    exact Finset.mem_image.mpr
      ⟨i, by simpa [hsource] using hv, hsource⟩

/-- If a source subset is contained in the sources of `I`, then the indices
recovered from those sources are contained in `I`. -/
theorem sourceIndexSetOfSubset_subset_indexSet
    (P : PerfectPathPacking G S T) {S' : Finset V} {I : Finset P.Index}
    (hS : S' ⊆ P.sourceSet I) :
    P.sourceIndexSetOfSubset S' ⊆ I := by
  intro i hi
  have hsource_mem : (P.path i).source ∈ S' :=
    (P.mem_sourceIndexSetOfSubset S' i).mp hi
  rcases Finset.mem_image.mp (hS hsource_mem) with ⟨j, hj, hsource⟩
  have hij : i = j := by
    apply P.source_bijective.1
    exact Subtype.ext hsource.symm
  simpa [hij] using hj

@[simp] theorem sourceIndexSetOfSubset_card
    (P : PerfectPathPacking G S T) {S' : Finset V} (hS : S' ⊆ S) :
    (P.sourceIndexSetOfSubset S').card = S'.card := by
  have hcard := P.sourceSet_card (P.sourceIndexSetOfSubset S')
  rw [P.sourceSet_sourceIndexSetOfSubset hS] at hcard
  exact hcard.symm

/-- Restrict a perfect packing to the paths whose sources lie in a prescribed
subset of the left terminal set. -/
noncomputable def restrictSourceSet
    (P : PerfectPathPacking G S T) (S' : Finset V) (hS : S' ⊆ S) :
    PerfectPathPacking G S'
      (P.targetSet (P.sourceIndexSetOfSubset S')) :=
  (P.restrictIndexSet (P.sourceIndexSetOfSubset S')).copyTerminals
    (P.sourceSet_sourceIndexSetOfSubset hS) rfl

@[simp] theorem restrictSourceSet_card
    (P : PerfectPathPacking G S T) (S' : Finset V) (hS : S' ⊆ S) :
    (P.restrictSourceSet S' hS).card = S'.card := by
  simp [restrictSourceSet, sourceIndexSetOfSubset_card P hS]

@[simp] theorem restrictSourceSet_path_vertexSet
    (P : PerfectPathPacking G S T) (S' : Finset V) (hS : S' ⊆ S)
    (i : (P.restrictSourceSet S' hS).Index) :
    ((P.restrictSourceSet S' hS).path i).vertexSet = (P.path i.1).vertexSet := rfl

/-- A source-restricted perfect packing stays inside the vertex trace of the
original packing. -/
theorem restrictSourceSet_staysIn_vertexSet
    (P : PerfectPathPacking G S T) (S' : Finset V) (hS : S' ⊆ S) :
    (P.restrictSourceSet S' hS).toPathPacking.StaysIn P.toPathPacking.vertexSet := by
  intro i
  exact P.toPathPacking.path_vertexSet_subset_vertexSet i.1

/-- A source-restricted perfect packing stays in every set in which the
original packing stays. -/
theorem restrictSourceSet_staysIn
    (P : PerfectPathPacking G S T) (S' : Finset V) (hS : S' ⊆ S)
    {U : Finset V} (hP : P.toPathPacking.StaysIn U) :
    (P.restrictSourceSet S' hS).toPathPacking.StaysIn U := by
  intro i v hv
  exact hP i.1 (by simpa [restrictSourceSet, restrictIndexSet, copyTerminals] using hv)

/-- A source-restricted perfect packing preserves internal disjointness from any
finite vertex set. -/
theorem restrictSourceSet_internallyDisjointFromSet
    (P : PerfectPathPacking G S T) (S' : Finset V) (hS : S' ⊆ S)
    {U : Finset V} (hP : P.toPathPacking.InternallyDisjointFromSet U) :
    (P.restrictSourceSet S' hS).toPathPacking.InternallyDisjointFromSet U := by
  intro i v hv hvU
  exact hP i.1
    (by simpa [restrictSourceSet, restrictIndexSet, copyTerminals] using hv)
    hvU

/-- Restricting both sides of mutually node-disjoint perfect packings
preserves mutual node-disjointness. -/
theorem restrictSourceSet_mutuallyNodeDisjoint
    {S₂ T₂ : Finset V}
    (P : PerfectPathPacking G S T)
    (Q : PerfectPathPacking G S₂ T₂)
    (S₁' : Finset V) (hS₁ : S₁' ⊆ S)
    (S₂' : Finset V) (hS₂ : S₂' ⊆ S₂)
    (h : P.toPathPacking.MutuallyNodeDisjoint Q.toPathPacking) :
    (P.restrictSourceSet S₁' hS₁).toPathPacking.MutuallyNodeDisjoint
      (Q.restrictSourceSet S₂' hS₂).toPathPacking := by
  intro i j
  exact h i.1 j.1

/-- The indices of paths whose target lies in a prescribed subset of the right
terminal set. -/
noncomputable def targetIndexSetOfSubset
    (P : PerfectPathPacking G S T) (T' : Finset V) : Finset P.Index :=
  Finset.univ.filter fun i => (P.path i).target ∈ T'

@[simp] theorem mem_targetIndexSetOfSubset
    (P : PerfectPathPacking G S T) (T' : Finset V) (i : P.Index) :
    i ∈ P.targetIndexSetOfSubset T' ↔ (P.path i).target ∈ T' := by
  simp [targetIndexSetOfSubset]

/-- Restricting by a target subset uses exactly that subset as the new target
terminal set. -/
theorem targetSet_targetIndexSetOfSubset
    (P : PerfectPathPacking G S T) {T' : Finset V} (hT : T' ⊆ T) :
    P.targetSet (P.targetIndexSetOfSubset T') = T' := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
    exact (P.mem_targetIndexSetOfSubset T' i).mp hi
  · intro hv
    rcases P.target_bijective.2 ⟨v, hT hv⟩ with ⟨i, hi⟩
    have htarget : (P.path i).target = v :=
      congrArg Subtype.val hi
    rw [targetSet]
    exact Finset.mem_image.mpr
      ⟨i, by simpa [htarget] using hv, htarget⟩

/-- If a target subset is contained in the targets of `I`, then the indices
recovered from those targets are contained in `I`. -/
theorem targetIndexSetOfSubset_subset_indexSet
    (P : PerfectPathPacking G S T) {T' : Finset V} {I : Finset P.Index}
    (hT : T' ⊆ P.targetSet I) :
    P.targetIndexSetOfSubset T' ⊆ I := by
  intro i hi
  have htarget_mem : (P.path i).target ∈ T' :=
    (P.mem_targetIndexSetOfSubset T' i).mp hi
  rcases Finset.mem_image.mp (hT htarget_mem) with ⟨j, hj, htarget⟩
  have hij : i = j := by
    apply P.target_bijective.1
    exact Subtype.ext htarget.symm
  simpa [hij] using hj

@[simp] theorem targetIndexSetOfSubset_card
    (P : PerfectPathPacking G S T) {T' : Finset V} (hT : T' ⊆ T) :
    (P.targetIndexSetOfSubset T').card = T'.card := by
  have hcard := P.targetSet_card (P.targetIndexSetOfSubset T')
  rw [P.targetSet_targetIndexSetOfSubset hT] at hcard
  exact hcard.symm

/-- Restrict a perfect packing to the paths whose targets lie in a prescribed
subset of the right terminal set. -/
noncomputable def restrictTargetSet
    (P : PerfectPathPacking G S T) (T' : Finset V) (hT : T' ⊆ T) :
    PerfectPathPacking G
      (P.sourceSet (P.targetIndexSetOfSubset T')) T' :=
  (P.restrictIndexSet (P.targetIndexSetOfSubset T')).copyTerminals
    rfl (P.targetSet_targetIndexSetOfSubset hT)

@[simp] theorem restrictTargetSet_card
    (P : PerfectPathPacking G S T) (T' : Finset V) (hT : T' ⊆ T) :
    (P.restrictTargetSet T' hT).card = T'.card := by
  simp [restrictTargetSet, targetIndexSetOfSubset_card P hT]

@[simp] theorem restrictTargetSet_path_vertexSet
    (P : PerfectPathPacking G S T) (T' : Finset V) (hT : T' ⊆ T)
    (i : (P.restrictTargetSet T' hT).Index) :
    ((P.restrictTargetSet T' hT).path i).vertexSet = (P.path i.1).vertexSet := rfl

/-- A target-restricted perfect packing stays inside the vertex trace of the
original packing. -/
theorem restrictTargetSet_staysIn_vertexSet
    (P : PerfectPathPacking G S T) (T' : Finset V) (hT : T' ⊆ T) :
    (P.restrictTargetSet T' hT).toPathPacking.StaysIn P.toPathPacking.vertexSet := by
  intro i
  exact P.toPathPacking.path_vertexSet_subset_vertexSet i.1

/-- A target-restricted perfect packing stays in every set in which the
original packing stays. -/
theorem restrictTargetSet_staysIn
    (P : PerfectPathPacking G S T) (T' : Finset V) (hT : T' ⊆ T)
    {U : Finset V} (hP : P.toPathPacking.StaysIn U) :
    (P.restrictTargetSet T' hT).toPathPacking.StaysIn U := by
  intro i v hv
  exact hP i.1 (by simpa [restrictTargetSet, restrictIndexSet, copyTerminals] using hv)

/-- A target-restricted perfect packing preserves internal disjointness from any
finite vertex set. -/
theorem restrictTargetSet_internallyDisjointFromSet
    (P : PerfectPathPacking G S T) (T' : Finset V) (hT : T' ⊆ T)
    {U : Finset V} (hP : P.toPathPacking.InternallyDisjointFromSet U) :
    (P.restrictTargetSet T' hT).toPathPacking.InternallyDisjointFromSet U := by
  intro i v hv hvU
  exact hP i.1
    (by simpa [restrictTargetSet, restrictIndexSet, copyTerminals] using hv)
    hvU

/-- The graph spanned by a restricted perfect packing is a subgraph of the
graph spanned by the original packing. -/
theorem restrictIndexSet_spanningGraph_le
    (P : PerfectPathPacking G S T) (I : Finset P.Index) :
    (P.restrictIndexSet I).toPathPacking.spanningGraph ≤
      P.toPathPacking.spanningGraph := by
  intro u v huv
  rw [PathPacking.spanningGraph_adj_iff_exists_path_edge] at huv ⊢
  rcases huv with ⟨⟨i, hedge⟩, hne⟩
  exact ⟨⟨i.1, by simpa [restrictIndexSet] using hedge⟩, hne⟩

/-- Reverse every path in a perfect packing, swapping its two terminal sets. -/
noncomputable def reverse (P : PerfectPathPacking G S T) :
    PerfectPathPacking G T S where
  toPathPacking := {
    Index := P.Index
    path := fun i => (P.path i).reverse
    connects := by
      intro i
      exact Or.inl ⟨by simpa using P.target_mem i,
        by simpa using P.source_mem i⟩
    node_disjoint := by
      intro i j hij
      simpa [GraphPath.NodeDisjoint] using P.node_disjoint hij
  }
  source_mem := by
    intro i
    simpa using P.target_mem i
  target_mem := by
    intro i
    simpa using P.source_mem i
  source_bijective := by
    simpa using P.target_bijective
  target_bijective := by
    simpa using P.source_bijective

@[simp] theorem reverse_card (P : PerfectPathPacking G S T) :
    P.reverse.card = P.card := rfl

@[simp] theorem reverse_path_vertexSet (P : PerfectPathPacking G S T)
    (i : P.reverse.Index) :
    (P.reverse.path i).vertexSet = (P.path i).vertexSet := by
  simp [reverse]

@[simp] theorem reverse_path_edgeSet (P : PerfectPathPacking G S T)
    (i : P.reverse.Index) :
    (P.reverse.path i).edgeSet = (P.path i).edgeSet := by
  simp [reverse]

/-- Reversing a perfect packing preserves containment of all path vertices in
a fixed finite set. -/
theorem reverse_staysIn {U : Finset V} (P : PerfectPathPacking G S T)
    (hP : P.toPathPacking.StaysIn U) :
    P.reverse.toPathPacking.StaysIn U := by
  intro i
  simpa using hP i

/-- Reversing a perfect packing preserves internal disjointness from a fixed
finite set. -/
theorem reverse_internallyDisjointFromSet {U : Finset V}
    (P : PerfectPathPacking G S T)
    (hP : P.toPathPacking.InternallyDisjointFromSet U) :
    P.reverse.toPathPacking.InternallyDisjointFromSet U := by
  intro i v hv hvU
  have hrev :
      (P.path i).reverse.InternallyDisjointFromSet U :=
    (GraphPath.reverse_internallyDisjointFromSet (P.path i) U).2 (hP i)
  exact hrev (by simpa [reverse] using hv) hvU

/-- Choose exactly `n` paths from a perfect packing when `n` is at most its
cardinality. -/
theorem exists_indexSet_card_eq (P : PerfectPathPacking G S T)
    {n : ℕ} (hn : n ≤ P.card) :
    ∃ I : Finset P.Index, I.card = n ∧
      (P.restrictIndexSet I).card = n := by
  classical
  have hn_univ : n ≤ (Finset.univ : Finset P.Index).card := by
    simpa [card] using hn
  rcases Finset.exists_subset_card_eq hn_univ with ⟨I, _hI, hIcard⟩
  exact ⟨I, hIcard, by simp [hIcard]⟩

/-- A perfect path packing can be viewed inside the graph spanned by exactly
its own path edges. -/
noncomputable def inSpanningGraph (P : PerfectPathPacking G S T) :
    PerfectPathPacking P.toPathPacking.spanningGraph S T where
  toPathPacking := P.toPathPacking.inSpanningGraph
  source_mem := P.source_mem
  target_mem := P.target_mem
  source_bijective := by
    simpa [PathPacking.inSpanningGraph, PathPacking.transfer, GraphPath.transfer]
      using P.source_bijective
  target_bijective := by
    simpa [PathPacking.inSpanningGraph, PathPacking.transfer, GraphPath.transfer]
      using P.target_bijective

@[simp] theorem inSpanningGraph_card (P : PerfectPathPacking G S T) :
    P.inSpanningGraph.card = P.card := rfl

@[simp] theorem inSpanningGraph_path_vertexSet (P : PerfectPathPacking G S T)
    (i : P.Index) :
    (P.inSpanningGraph.path i).vertexSet = (P.path i).vertexSet := by
  simp [inSpanningGraph, PathPacking.inSpanningGraph, PathPacking.transfer]

/-- If the first perfect packing is internally disjoint from a region, the
second stays in that region, and the first source terminals are outside it,
then every matching endpoint concatenation is a simple path. -/
theorem concat_isPath_of_first_internallyDisjointFromSet_second_staysIn
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.InternallyDisjointFromSet A)
    (hQ : Q.toPathPacking.StaysIn A)
    (hSdisj : Disjoint S A) :
    ∀ i : P.Index,
      ((P.path i).walk.append
        ((Q.path (P.indexOfSourceTarget Q i)).walk.copy
          (source_indexOfSourceTarget P Q i) rfl)).IsPath := by
  intro i
  refine GraphPath.appendWithEq_isPath_of_inter_subset_target
    (P.path i) (Q.path (P.indexOfSourceTarget Q i))
    (source_indexOfSourceTarget P Q i).symm ?_
  intro v hvP hvQ
  have hvA : v ∈ A := hQ (P.indexOfSourceTarget Q i) hvQ
  rcases hP i hvP hvA with hsource | htarget
  · exact False.elim
      (Finset.disjoint_left.mp hSdisj (P.source_mem i)
        (by simpa [hsource] using hvA))
  · exact htarget

/-- Under the same separation hypotheses as
`concat_isPath_of_first_internallyDisjointFromSet_second_staysIn`, distinct
matching endpoint concatenations remain node-disjoint. -/
theorem concat_nodeDisjoint_of_first_internallyDisjointFromSet_second_staysIn
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.InternallyDisjointFromSet A)
    (hQ : Q.toPathPacking.StaysIn A)
    (hSdisj : Disjoint S A)
    (hpath :
      ∀ i : P.Index,
        ((P.path i).walk.append
          ((Q.path (P.indexOfSourceTarget Q i)).walk.copy
            (source_indexOfSourceTarget P Q i) rfl)).IsPath) :
    Pairwise fun i j =>
      GraphPath.NodeDisjoint
        ((P.path i).appendWithEq (Q.path (P.indexOfSourceTarget Q i))
          (source_indexOfSourceTarget P Q i).symm (hpath i))
        ((P.path j).appendWithEq (Q.path (P.indexOfSourceTarget Q j))
          (source_indexOfSourceTarget P Q j).symm (hpath j)) := by
  classical
  intro i j hij
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro v hvi hvj
  have hvi_subset :=
    GraphPath.appendWithEq_vertexSet_subset
      (P.path i) (Q.path (P.indexOfSourceTarget Q i))
      (source_indexOfSourceTarget P Q i).symm (hpath i) hvi
  have hvj_subset :=
    GraphPath.appendWithEq_vertexSet_subset
      (P.path j) (Q.path (P.indexOfSourceTarget Q j))
      (source_indexOfSourceTarget P Q j).symm (hpath j) hvj
  rcases Finset.mem_union.mp hvi_subset with hviP | hviQ
  · rcases Finset.mem_union.mp hvj_subset with hvjP | hvjQ
    · exact Finset.disjoint_left.mp (P.toPathPacking.node_disjoint hij) hviP hvjP
    · have hvA : v ∈ A := hQ (P.indexOfSourceTarget Q j) hvjQ
      rcases hP i hviP hvA with hsource | htarget
      · exact Finset.disjoint_left.mp hSdisj (P.source_mem i)
          (by simpa [hsource] using hvA)
      · have hvT : v ∈ T := by
          simpa [htarget] using P.target_mem i
        have hqsource :
            v = (Q.path (P.indexOfSourceTarget Q j)).source :=
          Q.eq_source_of_mem_left_of_mem_path_vertexSet
            (P.indexOfSourceTarget Q j) hvT hvjQ
        have htargets : (P.path i).target = (P.path j).target := by
          calc
            (P.path i).target = v := htarget.symm
            _ = (Q.path (P.indexOfSourceTarget Q j)).source := hqsource
            _ = (P.path j).target := source_indexOfSourceTarget P Q j
        exact hij (P.target_bijective.1 (Subtype.ext htargets))
  · rcases Finset.mem_union.mp hvj_subset with hvjP | hvjQ
    · have hvA : v ∈ A := hQ (P.indexOfSourceTarget Q i) hviQ
      rcases hP j hvjP hvA with hsource | htarget
      · exact Finset.disjoint_left.mp hSdisj (P.source_mem j)
          (by simpa [hsource] using hvA)
      · have hvT : v ∈ T := by
          simpa [htarget] using P.target_mem j
        have hqsource :
            v = (Q.path (P.indexOfSourceTarget Q i)).source :=
          Q.eq_source_of_mem_left_of_mem_path_vertexSet
            (P.indexOfSourceTarget Q i) hvT hviQ
        have htargets : (P.path i).target = (P.path j).target := by
          calc
            (P.path i).target =
                (Q.path (P.indexOfSourceTarget Q i)).source :=
              (source_indexOfSourceTarget P Q i).symm
            _ = v := hqsource.symm
            _ = (P.path j).target := htarget
        exact hij (P.target_bijective.1 (Subtype.ext htargets))
    · have hindex_ne :
          P.indexOfSourceTarget Q i ≠ P.indexOfSourceTarget Q j := by
        intro hindex
        apply hij
        apply P.target_bijective.1
        have htargets : (P.path i).target = (P.path j).target := by
          have hsources :=
            congrArg (fun q => (Q.path q).source) hindex
          exact (source_indexOfSourceTarget P Q i).symm.trans
            (hsources.trans (source_indexOfSourceTarget P Q j))
        exact Subtype.ext htargets
      exact Finset.disjoint_left.mp
        (Q.toPathPacking.node_disjoint hindex_ne) hviQ hvjQ

/-- Variant of
`concat_isPath_of_first_internallyDisjointFromSet_second_staysIn` allowing a
left source terminal to lie in the region only when its path is trivial up to
the glued target. -/
theorem concat_isPath_of_first_internallyDisjointFromSet_second_staysIn_sourceOnlyAtTarget
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.InternallyDisjointFromSet A)
    (hQ : Q.toPathPacking.StaysIn A)
    (hsource_only :
      ∀ i : P.Index, ∀ j : Q.Index,
        (P.path i).source ∈ (Q.path j).vertexSet →
          (P.path i).source = (P.path i).target) :
    ∀ i : P.Index,
      ((P.path i).walk.append
        ((Q.path (P.indexOfSourceTarget Q i)).walk.copy
          (source_indexOfSourceTarget P Q i) rfl)).IsPath := by
  intro i
  refine GraphPath.appendWithEq_isPath_of_inter_subset_target
    (P.path i) (Q.path (P.indexOfSourceTarget Q i))
    (source_indexOfSourceTarget P Q i).symm ?_
  intro v hvP hvQ
  have hvA : v ∈ A := hQ (P.indexOfSourceTarget Q i) hvQ
  rcases hP i hvP hvA with hsource | htarget
  · exact hsource.trans
      (hsource_only i (P.indexOfSourceTarget Q i) (by simpa [hsource] using hvQ))
  · exact htarget

/-- Node-disjointness for the source-exception concatenation variant. -/
theorem concat_nodeDisjoint_of_first_internallyDisjointFromSet_second_staysIn_sourceOnlyAtTarget
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.InternallyDisjointFromSet A)
    (hQ : Q.toPathPacking.StaysIn A)
    (hsource_only :
      ∀ i : P.Index, ∀ j : Q.Index,
        (P.path i).source ∈ (Q.path j).vertexSet →
          (P.path i).source = (P.path i).target)
    (hpath :
      ∀ i : P.Index,
        ((P.path i).walk.append
          ((Q.path (P.indexOfSourceTarget Q i)).walk.copy
            (source_indexOfSourceTarget P Q i) rfl)).IsPath) :
    Pairwise fun i j =>
      GraphPath.NodeDisjoint
        ((P.path i).appendWithEq (Q.path (P.indexOfSourceTarget Q i))
          (source_indexOfSourceTarget P Q i).symm (hpath i))
        ((P.path j).appendWithEq (Q.path (P.indexOfSourceTarget Q j))
          (source_indexOfSourceTarget P Q j).symm (hpath j)) := by
  classical
  intro i j hij
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro v hvi hvj
  have hvi_subset :=
    GraphPath.appendWithEq_vertexSet_subset
      (P.path i) (Q.path (P.indexOfSourceTarget Q i))
      (source_indexOfSourceTarget P Q i).symm (hpath i) hvi
  have hvj_subset :=
    GraphPath.appendWithEq_vertexSet_subset
      (P.path j) (Q.path (P.indexOfSourceTarget Q j))
      (source_indexOfSourceTarget P Q j).symm (hpath j) hvj
  rcases Finset.mem_union.mp hvi_subset with hviP | hviQ
  · rcases Finset.mem_union.mp hvj_subset with hvjP | hvjQ
    · exact Finset.disjoint_left.mp (P.toPathPacking.node_disjoint hij) hviP hvjP
    · have hvA : v ∈ A := hQ (P.indexOfSourceTarget Q j) hvjQ
      rcases hP i hviP hvA with hsource | htarget
      · have hPi_trivial :
            (P.path i).source = (P.path i).target :=
          hsource_only i (P.indexOfSourceTarget Q j) (by simpa [hsource] using hvjQ)
        have hvT : v ∈ T := by
          simpa [hsource, hPi_trivial] using P.target_mem i
        have hqsource :
            v = (Q.path (P.indexOfSourceTarget Q j)).source :=
          Q.eq_source_of_mem_left_of_mem_path_vertexSet
            (P.indexOfSourceTarget Q j) hvT hvjQ
        have htargets : (P.path i).target = (P.path j).target := by
          calc
            (P.path i).target = v := by simp [hsource, hPi_trivial]
            _ = (Q.path (P.indexOfSourceTarget Q j)).source := hqsource
            _ = (P.path j).target := source_indexOfSourceTarget P Q j
        exact hij (P.target_bijective.1 (Subtype.ext htargets))
      · have hvT : v ∈ T := by
          simpa [htarget] using P.target_mem i
        have hqsource :
            v = (Q.path (P.indexOfSourceTarget Q j)).source :=
          Q.eq_source_of_mem_left_of_mem_path_vertexSet
            (P.indexOfSourceTarget Q j) hvT hvjQ
        have htargets : (P.path i).target = (P.path j).target := by
          calc
            (P.path i).target = v := htarget.symm
            _ = (Q.path (P.indexOfSourceTarget Q j)).source := hqsource
            _ = (P.path j).target := source_indexOfSourceTarget P Q j
        exact hij (P.target_bijective.1 (Subtype.ext htargets))
  · rcases Finset.mem_union.mp hvj_subset with hvjP | hvjQ
    · have hvA : v ∈ A := hQ (P.indexOfSourceTarget Q i) hviQ
      rcases hP j hvjP hvA with hsource | htarget
      · have hPj_trivial :
            (P.path j).source = (P.path j).target :=
          hsource_only j (P.indexOfSourceTarget Q i) (by simpa [hsource] using hviQ)
        have hvT : v ∈ T := by
          simpa [hsource, hPj_trivial] using P.target_mem j
        have hqsource :
            v = (Q.path (P.indexOfSourceTarget Q i)).source :=
          Q.eq_source_of_mem_left_of_mem_path_vertexSet
            (P.indexOfSourceTarget Q i) hvT hviQ
        have htargets : (P.path i).target = (P.path j).target := by
          calc
            (P.path i).target =
                (Q.path (P.indexOfSourceTarget Q i)).source :=
              (source_indexOfSourceTarget P Q i).symm
            _ = v := hqsource.symm
            _ = (P.path j).target := by simp [hsource, hPj_trivial]
        exact hij (P.target_bijective.1 (Subtype.ext htargets))
      · have hvT : v ∈ T := by
          simpa [htarget] using P.target_mem j
        have hqsource :
            v = (Q.path (P.indexOfSourceTarget Q i)).source :=
          Q.eq_source_of_mem_left_of_mem_path_vertexSet
            (P.indexOfSourceTarget Q i) hvT hviQ
        have htargets : (P.path i).target = (P.path j).target := by
          calc
            (P.path i).target =
                (Q.path (P.indexOfSourceTarget Q i)).source :=
              (source_indexOfSourceTarget P Q i).symm
            _ = v := hqsource.symm
            _ = (P.path j).target := htarget
        exact hij (P.target_bijective.1 (Subtype.ext htargets))
    · have hindex_ne :
          P.indexOfSourceTarget Q i ≠ P.indexOfSourceTarget Q j := by
        intro hindex
        apply hij
        apply P.target_bijective.1
        have htargets : (P.path i).target = (P.path j).target := by
          have hsources :=
            congrArg (fun q => (Q.path q).source) hindex
          exact (source_indexOfSourceTarget P Q i).symm.trans
            (hsources.trans (source_indexOfSourceTarget P Q j))
        exact Subtype.ext htargets
      exact Finset.disjoint_left.mp
        (Q.toPathPacking.node_disjoint hindex_ne) hviQ hvjQ

/-- If the first perfect packing stays in a region, the second is internally
disjoint from that region, and the second target terminals are outside it, then
every matching endpoint concatenation is a simple path. -/
theorem concat_isPath_of_first_staysIn_second_internallyDisjointFromSet
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.StaysIn A)
    (hQ : Q.toPathPacking.InternallyDisjointFromSet A)
    (hUdisj : Disjoint U A) :
    ∀ i : P.Index,
      ((P.path i).walk.append
        ((Q.path (P.indexOfSourceTarget Q i)).walk.copy
          (source_indexOfSourceTarget P Q i) rfl)).IsPath := by
  intro i
  refine GraphPath.appendWithEq_isPath_of_inter_subset_target
    (P.path i) (Q.path (P.indexOfSourceTarget Q i))
    (source_indexOfSourceTarget P Q i).symm ?_
  intro v hvP hvQ
  have hvA : v ∈ A := hP i hvP
  rcases hQ (P.indexOfSourceTarget Q i) hvQ hvA with hsource | htarget
  · exact hsource.trans (source_indexOfSourceTarget P Q i)
  · exact False.elim
      (Finset.disjoint_left.mp hUdisj
        (Q.target_mem (P.indexOfSourceTarget Q i))
        (by simpa [htarget] using hvA))

/-- Under the same separation hypotheses as
`concat_isPath_of_first_staysIn_second_internallyDisjointFromSet`, distinct
matching endpoint concatenations remain node-disjoint. -/
theorem concat_nodeDisjoint_of_first_staysIn_second_internallyDisjointFromSet
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.StaysIn A)
    (hQ : Q.toPathPacking.InternallyDisjointFromSet A)
    (hUdisj : Disjoint U A)
    (hpath :
      ∀ i : P.Index,
        ((P.path i).walk.append
          ((Q.path (P.indexOfSourceTarget Q i)).walk.copy
            (source_indexOfSourceTarget P Q i) rfl)).IsPath) :
    Pairwise fun i j =>
      GraphPath.NodeDisjoint
        ((P.path i).appendWithEq (Q.path (P.indexOfSourceTarget Q i))
          (source_indexOfSourceTarget P Q i).symm (hpath i))
        ((P.path j).appendWithEq (Q.path (P.indexOfSourceTarget Q j))
          (source_indexOfSourceTarget P Q j).symm (hpath j)) := by
  classical
  intro i j hij
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro v hvi hvj
  have hvi_subset :=
    GraphPath.appendWithEq_vertexSet_subset
      (P.path i) (Q.path (P.indexOfSourceTarget Q i))
      (source_indexOfSourceTarget P Q i).symm (hpath i) hvi
  have hvj_subset :=
    GraphPath.appendWithEq_vertexSet_subset
      (P.path j) (Q.path (P.indexOfSourceTarget Q j))
      (source_indexOfSourceTarget P Q j).symm (hpath j) hvj
  rcases Finset.mem_union.mp hvi_subset with hviP | hviQ
  · rcases Finset.mem_union.mp hvj_subset with hvjP | hvjQ
    · exact Finset.disjoint_left.mp (P.toPathPacking.node_disjoint hij) hviP hvjP
    · have hvA : v ∈ A := hP i hviP
      rcases hQ (P.indexOfSourceTarget Q j) hvjQ hvA with hsource | htarget
      · have hvT : v ∈ T := by
          simpa [hsource, source_indexOfSourceTarget P Q j] using P.target_mem j
        have hPtarget : v = (P.path i).target :=
          P.eq_target_of_mem_right_of_mem_path_vertexSet i hvT hviP
        have htargets : (P.path i).target = (P.path j).target := by
          calc
            (P.path i).target = v := hPtarget.symm
            _ = (Q.path (P.indexOfSourceTarget Q j)).source := hsource
            _ = (P.path j).target := source_indexOfSourceTarget P Q j
        exact hij (P.target_bijective.1 (Subtype.ext htargets))
      · exact Finset.disjoint_left.mp hUdisj
          (Q.target_mem (P.indexOfSourceTarget Q j))
          (by simpa [htarget] using hvA)
  · rcases Finset.mem_union.mp hvj_subset with hvjP | hvjQ
    · have hvA : v ∈ A := hP j hvjP
      rcases hQ (P.indexOfSourceTarget Q i) hviQ hvA with hsource | htarget
      · have hvT : v ∈ T := by
          simpa [hsource, source_indexOfSourceTarget P Q i] using P.target_mem i
        have hPtarget : v = (P.path j).target :=
          P.eq_target_of_mem_right_of_mem_path_vertexSet j hvT hvjP
        have htargets : (P.path i).target = (P.path j).target := by
          calc
            (P.path i).target =
                (Q.path (P.indexOfSourceTarget Q i)).source :=
              (source_indexOfSourceTarget P Q i).symm
            _ = v := hsource.symm
            _ = (P.path j).target := hPtarget
        exact hij (P.target_bijective.1 (Subtype.ext htargets))
      · exact Finset.disjoint_left.mp hUdisj
          (Q.target_mem (P.indexOfSourceTarget Q i))
          (by simpa [htarget] using hvA)
    · have hindex_ne :
          P.indexOfSourceTarget Q i ≠ P.indexOfSourceTarget Q j := by
        intro hindex
        apply hij
        apply P.target_bijective.1
        have htargets : (P.path i).target = (P.path j).target := by
          have hsources :=
            congrArg (fun q => (Q.path q).source) hindex
          exact (source_indexOfSourceTarget P Q i).symm.trans
            (hsources.trans (source_indexOfSourceTarget P Q j))
        exact Subtype.ext htargets
      exact Finset.disjoint_left.mp
        (Q.toPathPacking.node_disjoint hindex_ne) hviQ hvjQ

/-- Variant of
`concat_isPath_of_first_staysIn_second_internallyDisjointFromSet` allowing a
right target terminal to lie in the region only when the second path is
trivial from its source to that target. -/
theorem concat_isPath_of_first_staysIn_second_internallyDisjointFromSet_targetOnlyAtSource
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.StaysIn A)
    (hQ : Q.toPathPacking.InternallyDisjointFromSet A)
    (htarget_only :
      ∀ i : P.Index, ∀ j : Q.Index,
        (Q.path j).target ∈ (P.path i).vertexSet →
          (Q.path j).target = (Q.path j).source) :
    ∀ i : P.Index,
      ((P.path i).walk.append
        ((Q.path (P.indexOfSourceTarget Q i)).walk.copy
          (source_indexOfSourceTarget P Q i) rfl)).IsPath := by
  intro i
  refine GraphPath.appendWithEq_isPath_of_inter_subset_target
    (P.path i) (Q.path (P.indexOfSourceTarget Q i))
    (source_indexOfSourceTarget P Q i).symm ?_
  intro v hvP hvQ
  have hvA : v ∈ A := hP i hvP
  rcases hQ (P.indexOfSourceTarget Q i) hvQ hvA with hsource | htarget
  · exact hsource.trans (source_indexOfSourceTarget P Q i)
  · exact htarget.trans
      ((htarget_only i (P.indexOfSourceTarget Q i) (by simpa [htarget] using hvP)).trans
        (source_indexOfSourceTarget P Q i))

/-- Node-disjointness for the target-exception symmetric concatenation
variant. -/
theorem concat_nodeDisjoint_of_first_staysIn_second_internallyDisjointFromSet_targetOnlyAtSource
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.StaysIn A)
    (hQ : Q.toPathPacking.InternallyDisjointFromSet A)
    (htarget_only :
      ∀ i : P.Index, ∀ j : Q.Index,
        (Q.path j).target ∈ (P.path i).vertexSet →
          (Q.path j).target = (Q.path j).source)
    (hpath :
      ∀ i : P.Index,
        ((P.path i).walk.append
          ((Q.path (P.indexOfSourceTarget Q i)).walk.copy
            (source_indexOfSourceTarget P Q i) rfl)).IsPath) :
    Pairwise fun i j =>
      GraphPath.NodeDisjoint
        ((P.path i).appendWithEq (Q.path (P.indexOfSourceTarget Q i))
          (source_indexOfSourceTarget P Q i).symm (hpath i))
        ((P.path j).appendWithEq (Q.path (P.indexOfSourceTarget Q j))
          (source_indexOfSourceTarget P Q j).symm (hpath j)) := by
  classical
  intro i j hij
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro v hvi hvj
  have hvi_subset :=
    GraphPath.appendWithEq_vertexSet_subset
      (P.path i) (Q.path (P.indexOfSourceTarget Q i))
      (source_indexOfSourceTarget P Q i).symm (hpath i) hvi
  have hvj_subset :=
    GraphPath.appendWithEq_vertexSet_subset
      (P.path j) (Q.path (P.indexOfSourceTarget Q j))
      (source_indexOfSourceTarget P Q j).symm (hpath j) hvj
  rcases Finset.mem_union.mp hvi_subset with hviP | hviQ
  · rcases Finset.mem_union.mp hvj_subset with hvjP | hvjQ
    · exact Finset.disjoint_left.mp (P.toPathPacking.node_disjoint hij) hviP hvjP
    · have hvA : v ∈ A := hP i hviP
      rcases hQ (P.indexOfSourceTarget Q j) hvjQ hvA with hsource | htarget
      · have hvT : v ∈ T := by
          simpa [hsource, source_indexOfSourceTarget P Q j] using P.target_mem j
        have hPtarget : v = (P.path i).target :=
          P.eq_target_of_mem_right_of_mem_path_vertexSet i hvT hviP
        have htargets : (P.path i).target = (P.path j).target := by
          calc
            (P.path i).target = v := hPtarget.symm
            _ = (Q.path (P.indexOfSourceTarget Q j)).source := hsource
            _ = (P.path j).target := source_indexOfSourceTarget P Q j
        exact hij (P.target_bijective.1 (Subtype.ext htargets))
      · have hQj_trivial :
            (Q.path (P.indexOfSourceTarget Q j)).target =
              (Q.path (P.indexOfSourceTarget Q j)).source :=
          htarget_only i (P.indexOfSourceTarget Q j) (by simpa [htarget] using hviP)
        have hvT : v ∈ T := by
          simpa [htarget, hQj_trivial, source_indexOfSourceTarget P Q j]
            using P.target_mem j
        have hPtarget : v = (P.path i).target :=
          P.eq_target_of_mem_right_of_mem_path_vertexSet i hvT hviP
        have htargets : (P.path i).target = (P.path j).target := by
          calc
            (P.path i).target = v := hPtarget.symm
            _ = (Q.path (P.indexOfSourceTarget Q j)).target := htarget
            _ = (Q.path (P.indexOfSourceTarget Q j)).source := hQj_trivial
            _ = (P.path j).target := source_indexOfSourceTarget P Q j
        exact hij (P.target_bijective.1 (Subtype.ext htargets))
  · rcases Finset.mem_union.mp hvj_subset with hvjP | hvjQ
    · have hvA : v ∈ A := hP j hvjP
      rcases hQ (P.indexOfSourceTarget Q i) hviQ hvA with hsource | htarget
      · have hvT : v ∈ T := by
          simpa [hsource, source_indexOfSourceTarget P Q i] using P.target_mem i
        have hPtarget : v = (P.path j).target :=
          P.eq_target_of_mem_right_of_mem_path_vertexSet j hvT hvjP
        have htargets : (P.path i).target = (P.path j).target := by
          calc
            (P.path i).target =
                (Q.path (P.indexOfSourceTarget Q i)).source :=
              (source_indexOfSourceTarget P Q i).symm
            _ = v := hsource.symm
            _ = (P.path j).target := hPtarget
        exact hij (P.target_bijective.1 (Subtype.ext htargets))
      · have hQi_trivial :
            (Q.path (P.indexOfSourceTarget Q i)).target =
              (Q.path (P.indexOfSourceTarget Q i)).source :=
          htarget_only j (P.indexOfSourceTarget Q i) (by simpa [htarget] using hvjP)
        have hvT : v ∈ T := by
          simpa [htarget, hQi_trivial, source_indexOfSourceTarget P Q i]
            using P.target_mem i
        have hPtarget : v = (P.path j).target :=
          P.eq_target_of_mem_right_of_mem_path_vertexSet j hvT hvjP
        have htargets : (P.path i).target = (P.path j).target := by
          calc
            (P.path i).target =
                (Q.path (P.indexOfSourceTarget Q i)).source :=
              (source_indexOfSourceTarget P Q i).symm
            _ = (Q.path (P.indexOfSourceTarget Q i)).target := hQi_trivial.symm
            _ = v := htarget.symm
            _ = (P.path j).target := hPtarget
        exact hij (P.target_bijective.1 (Subtype.ext htargets))
    · have hindex_ne :
          P.indexOfSourceTarget Q i ≠ P.indexOfSourceTarget Q j := by
        intro hindex
        apply hij
        apply P.target_bijective.1
        have htargets : (P.path i).target = (P.path j).target := by
          have hsources :=
            congrArg (fun q => (Q.path q).source) hindex
          exact (source_indexOfSourceTarget P Q i).symm.trans
            (hsources.trans (source_indexOfSourceTarget P Q j))
        exact Subtype.ext htargets
      exact Finset.disjoint_left.mp
        (Q.toPathPacking.node_disjoint hindex_ne) hviQ hvjQ

/-- Concatenate two perfect path packings with matching middle terminal set.

The two proof arguments record the genuinely graph-theoretic obligations:
each concatenated walk is still a simple path, and different concatenated
paths remain node-disjoint. -/
noncomputable def concat {U : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hpath :
      ∀ i : P.Index,
        ((P.path i).walk.append
          ((Q.path (P.indexOfSourceTarget Q i)).walk.copy
            (source_indexOfSourceTarget P Q i) rfl)).IsPath)
    (hnode :
      Pairwise fun i j =>
        GraphPath.NodeDisjoint
          ((P.path i).appendWithEq (Q.path (P.indexOfSourceTarget Q i))
            (source_indexOfSourceTarget P Q i).symm (hpath i))
          ((P.path j).appendWithEq (Q.path (P.indexOfSourceTarget Q j))
            (source_indexOfSourceTarget P Q j).symm (hpath j))) :
    PerfectPathPacking G S U where
  toPathPacking := {
    Index := P.Index
    path := fun i =>
      (P.path i).appendWithEq (Q.path (P.indexOfSourceTarget Q i))
        (source_indexOfSourceTarget P Q i).symm (hpath i)
    connects := by
      intro i
      exact Or.inl ⟨P.source_mem i, Q.target_mem (P.indexOfSourceTarget Q i)⟩
    node_disjoint := hnode
  }
  source_mem := P.source_mem
  target_mem := fun i => Q.target_mem (P.indexOfSourceTarget Q i)
  source_bijective := by
    simpa [GraphPath.appendWithEq] using P.source_bijective
  target_bijective := by
    classical
    apply (Fintype.bijective_iff_injective_and_card _).2
    constructor
    · intro i j hij
      have hq :
          P.indexOfSourceTarget Q i = P.indexOfSourceTarget Q j := by
        apply Q.target_bijective.1
        simpa [GraphPath.appendWithEq] using hij
      have htargets :
          (P.path i).target = (P.path j).target := by
        have hs :=
          congrArg (fun q => (Q.path q).source) hq
        exact (source_indexOfSourceTarget P Q i).symm.trans
          (hs.trans (source_indexOfSourceTarget P Q j))
      apply P.target_bijective.1
      exact Subtype.ext htargets
    · have hPU : P.card = U.card :=
        (P.card_eq_right_card.trans (Q.card_eq_left_card).symm).trans
          Q.card_eq_right_card
      rw [Fintype.card_coe]
      simpa [card] using hPU

/-- Concatenate two perfect packings using a region-separation certificate
instead of separately supplying path-simplicity and node-disjointness proofs. -/
noncomputable def concatOfFirstInternallyDisjointSecondStaysIn
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.InternallyDisjointFromSet A)
    (hQ : Q.toPathPacking.StaysIn A)
    (hSdisj : Disjoint S A) :
    PerfectPathPacking G S U :=
  let hpath :=
    concat_isPath_of_first_internallyDisjointFromSet_second_staysIn
      P Q hP hQ hSdisj
  P.concat Q hpath
    (concat_nodeDisjoint_of_first_internallyDisjointFromSet_second_staysIn
      P Q hP hQ hSdisj hpath)

/-- Concatenate two perfect packings when the first is internally disjoint from
the region containing the second, allowing a first source to lie in that region
only when the corresponding first path is trivial up to its target. -/
noncomputable def concatOfFirstInternallyDisjointSecondStaysInSourceOnlyAtTarget
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.InternallyDisjointFromSet A)
    (hQ : Q.toPathPacking.StaysIn A)
    (hsource_only :
      ∀ i : P.Index, ∀ j : Q.Index,
        (P.path i).source ∈ (Q.path j).vertexSet →
          (P.path i).source = (P.path i).target) :
    PerfectPathPacking G S U :=
  let hpath :=
    concat_isPath_of_first_internallyDisjointFromSet_second_staysIn_sourceOnlyAtTarget
      P Q hP hQ hsource_only
  P.concat Q hpath
    (concat_nodeDisjoint_of_first_internallyDisjointFromSet_second_staysIn_sourceOnlyAtTarget
      P Q hP hQ hsource_only hpath)

/-- Concatenate two perfect packings using the symmetric region-separation
certificate: the first packing stays in the region, the second is internally
disjoint from it, and the second target terminals are outside it. -/
noncomputable def concatOfFirstStaysInSecondInternallyDisjoint
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.StaysIn A)
    (hQ : Q.toPathPacking.InternallyDisjointFromSet A)
    (hUdisj : Disjoint U A) :
    PerfectPathPacking G S U :=
  let hpath :=
    concat_isPath_of_first_staysIn_second_internallyDisjointFromSet
      P Q hP hQ hUdisj
  P.concat Q hpath
    (concat_nodeDisjoint_of_first_staysIn_second_internallyDisjointFromSet
      P Q hP hQ hUdisj hpath)

/-- Concatenate two perfect packings when the second is internally disjoint
from the region containing the first, allowing a second target to lie in that
region only when that second path is trivial from source to target. -/
noncomputable def concatOfFirstStaysInSecondInternallyDisjointTargetOnlyAtSource
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.StaysIn A)
    (hQ : Q.toPathPacking.InternallyDisjointFromSet A)
    (htarget_only :
      ∀ i : P.Index, ∀ j : Q.Index,
        (Q.path j).target ∈ (P.path i).vertexSet →
          (Q.path j).target = (Q.path j).source) :
    PerfectPathPacking G S U :=
  let hpath :=
    concat_isPath_of_first_staysIn_second_internallyDisjointFromSet_targetOnlyAtSource
      P Q hP hQ htarget_only
  P.concat Q hpath
    (concat_nodeDisjoint_of_first_staysIn_second_internallyDisjointFromSet_targetOnlyAtSource
      P Q hP hQ htarget_only hpath)

@[simp] theorem concatOfFirstInternallyDisjointSecondStaysIn_card
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.InternallyDisjointFromSet A)
    (hQ : Q.toPathPacking.StaysIn A)
    (hSdisj : Disjoint S A) :
    (P.concatOfFirstInternallyDisjointSecondStaysIn Q hP hQ hSdisj).card =
      P.card := by
  rfl

@[simp] theorem concatOfFirstInternallyDisjointSecondStaysInSourceOnlyAtTarget_card
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.InternallyDisjointFromSet A)
    (hQ : Q.toPathPacking.StaysIn A)
    (hsource_only :
      ∀ i : P.Index, ∀ j : Q.Index,
        (P.path i).source ∈ (Q.path j).vertexSet →
          (P.path i).source = (P.path i).target) :
    (P.concatOfFirstInternallyDisjointSecondStaysInSourceOnlyAtTarget
      Q hP hQ hsource_only).card = P.card := by
  rfl

@[simp] theorem concatOfFirstStaysInSecondInternallyDisjoint_card
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.StaysIn A)
    (hQ : Q.toPathPacking.InternallyDisjointFromSet A)
    (hUdisj : Disjoint U A) :
    (P.concatOfFirstStaysInSecondInternallyDisjoint Q hP hQ hUdisj).card =
      P.card := by
  rfl

@[simp] theorem concatOfFirstStaysInSecondInternallyDisjointTargetOnlyAtSource_card
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.StaysIn A)
    (hQ : Q.toPathPacking.InternallyDisjointFromSet A)
    (htarget_only :
      ∀ i : P.Index, ∀ j : Q.Index,
        (Q.path j).target ∈ (P.path i).vertexSet →
          (Q.path j).target = (Q.path j).source) :
    (P.concatOfFirstStaysInSecondInternallyDisjointTargetOnlyAtSource
      Q hP hQ htarget_only).card = P.card := by
  rfl

@[simp] theorem concat_card {U : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hpath :
      ∀ i : P.Index,
        ((P.path i).walk.append
          ((Q.path (P.indexOfSourceTarget Q i)).walk.copy
            (source_indexOfSourceTarget P Q i) rfl)).IsPath)
    (hnode :
      Pairwise fun i j =>
        GraphPath.NodeDisjoint
          ((P.path i).appendWithEq (Q.path (P.indexOfSourceTarget Q i))
            (source_indexOfSourceTarget P Q i).symm (hpath i))
          ((P.path j).appendWithEq (Q.path (P.indexOfSourceTarget Q j))
            (source_indexOfSourceTarget P Q j).symm (hpath j))) :
    (P.concat Q hpath hnode).card = P.card := rfl

/-- A concatenated path uses only vertices from the two paths that were glued. -/
theorem concat_path_vertexSet_subset {U : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hpath :
      ∀ i : P.Index,
        ((P.path i).walk.append
          ((Q.path (P.indexOfSourceTarget Q i)).walk.copy
            (source_indexOfSourceTarget P Q i) rfl)).IsPath)
    (hnode :
      Pairwise fun i j =>
        GraphPath.NodeDisjoint
          ((P.path i).appendWithEq (Q.path (P.indexOfSourceTarget Q i))
            (source_indexOfSourceTarget P Q i).symm (hpath i))
          ((P.path j).appendWithEq (Q.path (P.indexOfSourceTarget Q j))
            (source_indexOfSourceTarget P Q j).symm (hpath j)))
    (i : (P.concat Q hpath hnode).Index) :
    ((P.concat Q hpath hnode).path i).vertexSet ⊆
      (P.path i).vertexSet ∪ (Q.path (P.indexOfSourceTarget Q i)).vertexSet :=
  GraphPath.appendWithEq_vertexSet_subset
    (P.path i) (Q.path (P.indexOfSourceTarget Q i))
    (source_indexOfSourceTarget P Q i).symm (hpath i)

/-- A concatenated path uses only edges from the two paths that were glued. -/
theorem concat_path_edgeSet_subset {U : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hpath :
      ∀ i : P.Index,
        ((P.path i).walk.append
          ((Q.path (P.indexOfSourceTarget Q i)).walk.copy
            (source_indexOfSourceTarget P Q i) rfl)).IsPath)
    (hnode :
      Pairwise fun i j =>
        GraphPath.NodeDisjoint
          ((P.path i).appendWithEq (Q.path (P.indexOfSourceTarget Q i))
            (source_indexOfSourceTarget P Q i).symm (hpath i))
          ((P.path j).appendWithEq (Q.path (P.indexOfSourceTarget Q j))
            (source_indexOfSourceTarget P Q j).symm (hpath j)))
    (i : (P.concat Q hpath hnode).Index) :
    ((P.concat Q hpath hnode).path i).edgeSet ⊆
      (P.path i).edgeSet ∪
        (Q.path (P.indexOfSourceTarget Q i)).edgeSet :=
  GraphPath.appendWithEq_edgeSet_subset
    (P.path i) (Q.path (P.indexOfSourceTarget Q i))
    (source_indexOfSourceTarget P Q i).symm (hpath i)

/-- A path in the region-separated concatenation uses only vertices from its
two input paths. -/
theorem concatOfFirstInternallyDisjointSecondStaysIn_path_vertexSet_subset
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.InternallyDisjointFromSet A)
    (hQ : Q.toPathPacking.StaysIn A)
    (hSdisj : Disjoint S A)
    (i : (P.concatOfFirstInternallyDisjointSecondStaysIn Q hP hQ hSdisj).Index) :
    ((P.concatOfFirstInternallyDisjointSecondStaysIn Q hP hQ hSdisj).path i).vertexSet ⊆
      (P.path i).vertexSet ∪ (Q.path (P.indexOfSourceTarget Q i)).vertexSet := by
  dsimp [concatOfFirstInternallyDisjointSecondStaysIn]
  exact P.concat_path_vertexSet_subset Q _ _ i

theorem concatOfFirstInternallyDisjointSecondStaysIn_path_edgeSet_subset
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.InternallyDisjointFromSet A)
    (hQ : Q.toPathPacking.StaysIn A)
    (hSdisj : Disjoint S A)
    (i : (P.concatOfFirstInternallyDisjointSecondStaysIn Q hP hQ hSdisj).Index) :
    ((P.concatOfFirstInternallyDisjointSecondStaysIn Q hP hQ hSdisj).path i).edgeSet ⊆
      (P.path i).edgeSet ∪
        (Q.path (P.indexOfSourceTarget Q i)).edgeSet := by
  dsimp [concatOfFirstInternallyDisjointSecondStaysIn]
  exact P.concat_path_edgeSet_subset Q _ _ i

/-- A path in the source-exception region-separated concatenation uses only
vertices from its two input paths. -/
theorem concatOfFirstInternallyDisjointSecondStaysInSourceOnlyAtTarget_path_vertexSet_subset
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.InternallyDisjointFromSet A)
    (hQ : Q.toPathPacking.StaysIn A)
    (hsource_only :
      ∀ i : P.Index, ∀ j : Q.Index,
        (P.path i).source ∈ (Q.path j).vertexSet →
          (P.path i).source = (P.path i).target)
    (i : (P.concatOfFirstInternallyDisjointSecondStaysInSourceOnlyAtTarget
      Q hP hQ hsource_only).Index) :
    ((P.concatOfFirstInternallyDisjointSecondStaysInSourceOnlyAtTarget
      Q hP hQ hsource_only).path i).vertexSet ⊆
      (P.path i).vertexSet ∪ (Q.path (P.indexOfSourceTarget Q i)).vertexSet := by
  dsimp [concatOfFirstInternallyDisjointSecondStaysInSourceOnlyAtTarget]
  exact P.concat_path_vertexSet_subset Q _ _ i

/-- A path in the symmetric region-separated concatenation uses only vertices
from its two input paths. -/
theorem concatOfFirstStaysInSecondInternallyDisjoint_path_vertexSet_subset
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.StaysIn A)
    (hQ : Q.toPathPacking.InternallyDisjointFromSet A)
    (hUdisj : Disjoint U A)
    (i : (P.concatOfFirstStaysInSecondInternallyDisjoint Q hP hQ hUdisj).Index) :
    ((P.concatOfFirstStaysInSecondInternallyDisjoint Q hP hQ hUdisj).path i).vertexSet ⊆
      (P.path i).vertexSet ∪ (Q.path (P.indexOfSourceTarget Q i)).vertexSet := by
  dsimp [concatOfFirstStaysInSecondInternallyDisjoint]
  exact P.concat_path_vertexSet_subset Q _ _ i

theorem concatOfFirstStaysInSecondInternallyDisjoint_path_edgeSet_subset
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.StaysIn A)
    (hQ : Q.toPathPacking.InternallyDisjointFromSet A)
    (hUdisj : Disjoint U A)
    (i : (P.concatOfFirstStaysInSecondInternallyDisjoint Q hP hQ hUdisj).Index) :
    ((P.concatOfFirstStaysInSecondInternallyDisjoint Q hP hQ hUdisj).path i).edgeSet ⊆
      (P.path i).edgeSet ∪
        (Q.path (P.indexOfSourceTarget Q i)).edgeSet := by
  dsimp [concatOfFirstStaysInSecondInternallyDisjoint]
  exact P.concat_path_edgeSet_subset Q _ _ i

/-- A path in the target-exception symmetric concatenation uses only vertices
from its two input paths. -/
theorem concatOfFirstStaysInSecondInternallyDisjointTargetOnlyAtSource_path_vertexSet_subset
    {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.StaysIn A)
    (hQ : Q.toPathPacking.InternallyDisjointFromSet A)
    (htarget_only :
      ∀ i : P.Index, ∀ j : Q.Index,
        (Q.path j).target ∈ (P.path i).vertexSet →
          (Q.path j).target = (Q.path j).source)
    (i : (P.concatOfFirstStaysInSecondInternallyDisjointTargetOnlyAtSource
      Q hP hQ htarget_only).Index) :
    ((P.concatOfFirstStaysInSecondInternallyDisjointTargetOnlyAtSource
      Q hP hQ htarget_only).path i).vertexSet ⊆
      (P.path i).vertexSet ∪ (Q.path (P.indexOfSourceTarget Q i)).vertexSet := by
  dsimp [concatOfFirstStaysInSecondInternallyDisjointTargetOnlyAtSource]
  exact P.concat_path_vertexSet_subset Q _ _ i

/-- If the two input perfect packings stay in prescribed vertex sets, then the
concatenated packing stays in their union. -/
theorem concat_staysIn_union {U : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hpath :
      ∀ i : P.Index,
        ((P.path i).walk.append
          ((Q.path (P.indexOfSourceTarget Q i)).walk.copy
            (source_indexOfSourceTarget P Q i) rfl)).IsPath)
    (hnode :
      Pairwise fun i j =>
        GraphPath.NodeDisjoint
          ((P.path i).appendWithEq (Q.path (P.indexOfSourceTarget Q i))
            (source_indexOfSourceTarget P Q i).symm (hpath i))
          ((P.path j).appendWithEq (Q.path (P.indexOfSourceTarget Q j))
            (source_indexOfSourceTarget P Q j).symm (hpath j)))
    {A B : Finset V}
    (hP : P.toPathPacking.StaysIn A)
    (hQ : Q.toPathPacking.StaysIn B) :
    (P.concat Q hpath hnode).toPathPacking.StaysIn (A ∪ B) := by
  intro i v hv
  have hsubset := P.concat_path_vertexSet_subset Q hpath hnode i hv
  rcases Finset.mem_union.mp hsubset with hvP | hvQ
  · exact Finset.mem_union_left _ (hP i hvP)
  · exact Finset.mem_union_right _ (hQ (P.indexOfSourceTarget Q i) hvQ)

/-- If the left input packing is internally disjoint from a set, the right input
packing is disjoint from that set, and the glued terminal set avoids it, then
the concatenated packing is internally disjoint from that set. -/
theorem concat_internallyDisjointFromSet_left {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hpath :
      ∀ i : P.Index,
        ((P.path i).walk.append
          ((Q.path (P.indexOfSourceTarget Q i)).walk.copy
            (source_indexOfSourceTarget P Q i) rfl)).IsPath)
    (hnode :
      Pairwise fun i j =>
        GraphPath.NodeDisjoint
          ((P.path i).appendWithEq (Q.path (P.indexOfSourceTarget Q i))
            (source_indexOfSourceTarget P Q i).symm (hpath i))
          ((P.path j).appendWithEq (Q.path (P.indexOfSourceTarget Q j))
            (source_indexOfSourceTarget P Q j).symm (hpath j)))
    (hP : P.toPathPacking.InternallyDisjointFromSet A)
    (hTdisj : Disjoint T A)
    (hQdisj : Disjoint Q.toPathPacking.vertexSet A) :
    (P.concat Q hpath hnode).toPathPacking.InternallyDisjointFromSet A := by
  intro i v hv hA
  have hsplit := P.concat_path_vertexSet_subset Q hpath hnode i hv
  rcases Finset.mem_union.mp hsplit with hvP | hvQ
  · rcases hP i hvP hA with hsource | htarget
    · exact Or.inl (by simpa [concat, GraphPath.IsEndpoint] using hsource)
    · exact False.elim
        (Finset.disjoint_left.mp hTdisj (P.target_mem i)
          (by simpa [htarget] using hA))
  · have hvQtotal :
        v ∈ Q.toPathPacking.vertexSet :=
      Q.toPathPacking.path_vertexSet_subset_vertexSet
        (P.indexOfSourceTarget Q i) hvQ
    exact False.elim
      (Finset.disjoint_left.mp hQdisj hvQtotal hA)

/-- If the right input packing is internally disjoint from a set, the left input
packing is disjoint from that set, and the glued terminal set avoids it, then
the concatenated packing is internally disjoint from that set. -/
theorem concat_internallyDisjointFromSet_right {U A : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hpath :
      ∀ i : P.Index,
        ((P.path i).walk.append
          ((Q.path (P.indexOfSourceTarget Q i)).walk.copy
            (source_indexOfSourceTarget P Q i) rfl)).IsPath)
    (hnode :
      Pairwise fun i j =>
        GraphPath.NodeDisjoint
          ((P.path i).appendWithEq (Q.path (P.indexOfSourceTarget Q i))
            (source_indexOfSourceTarget P Q i).symm (hpath i))
          ((P.path j).appendWithEq (Q.path (P.indexOfSourceTarget Q j))
            (source_indexOfSourceTarget P Q j).symm (hpath j)))
    (hPdisj : Disjoint P.toPathPacking.vertexSet A)
    (hTdisj : Disjoint T A)
    (hQ : Q.toPathPacking.InternallyDisjointFromSet A) :
    (P.concat Q hpath hnode).toPathPacking.InternallyDisjointFromSet A := by
  intro i v hv hA
  have hsplit := P.concat_path_vertexSet_subset Q hpath hnode i hv
  rcases Finset.mem_union.mp hsplit with hvP | hvQ
  · have hvPtotal :
        v ∈ P.toPathPacking.vertexSet :=
      P.toPathPacking.path_vertexSet_subset_vertexSet i hvP
    exact False.elim
      (Finset.disjoint_left.mp hPdisj hvPtotal hA)
  · rcases hQ (P.indexOfSourceTarget Q i) hvQ hA with hsource | htarget
    · exact False.elim
        (Finset.disjoint_left.mp hTdisj
          (Q.source_mem (P.indexOfSourceTarget Q i))
          (by simpa [hsource] using hA))
    · exact Or.inr (by simpa [concat, GraphPath.IsEndpoint] using htarget)

/-- The region-separated concatenation stays in the union of the region used
by the first packing and the region used by the second packing. -/
theorem concatOfFirstInternallyDisjointSecondStaysIn_staysIn_union
    {U A B : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.InternallyDisjointFromSet A)
    (hQ : Q.toPathPacking.StaysIn A)
    (hSdisj : Disjoint S A)
    (hPstay : P.toPathPacking.StaysIn B) :
    (P.concatOfFirstInternallyDisjointSecondStaysIn Q hP hQ hSdisj).toPathPacking.StaysIn
      (B ∪ A) := by
  dsimp [concatOfFirstInternallyDisjointSecondStaysIn]
  exact P.concat_staysIn_union Q _ _ hPstay hQ

/-- The source-exception region-separated concatenation stays in the union of
the region used by the first packing and the region used by the second
packing. -/
theorem concatOfFirstInternallyDisjointSecondStaysInSourceOnlyAtTarget_staysIn_union
    {U A B : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.InternallyDisjointFromSet A)
    (hQ : Q.toPathPacking.StaysIn A)
    (hsource_only :
      ∀ i : P.Index, ∀ j : Q.Index,
        (P.path i).source ∈ (Q.path j).vertexSet →
          (P.path i).source = (P.path i).target)
    (hPstay : P.toPathPacking.StaysIn B) :
    (P.concatOfFirstInternallyDisjointSecondStaysInSourceOnlyAtTarget
      Q hP hQ hsource_only).toPathPacking.StaysIn (B ∪ A) := by
  dsimp [concatOfFirstInternallyDisjointSecondStaysInSourceOnlyAtTarget]
  exact P.concat_staysIn_union Q _ _ hPstay hQ

/-- The symmetric region-separated concatenation stays in the union of the
region used by the first packing and the region used by the second packing. -/
theorem concatOfFirstStaysInSecondInternallyDisjoint_staysIn_union
    {U A B : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.StaysIn A)
    (hQ : Q.toPathPacking.InternallyDisjointFromSet A)
    (hUdisj : Disjoint U A)
    (hQstay : Q.toPathPacking.StaysIn B) :
    (P.concatOfFirstStaysInSecondInternallyDisjoint Q hP hQ hUdisj).toPathPacking.StaysIn
      (A ∪ B) := by
  dsimp [concatOfFirstStaysInSecondInternallyDisjoint]
  exact P.concat_staysIn_union Q _ _ hP hQstay

/-- The target-exception symmetric concatenation stays in the union of the
region used by the first packing and the region used by the second packing. -/
theorem concatOfFirstStaysInSecondInternallyDisjointTargetOnlyAtSource_staysIn_union
    {U A B : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.StaysIn A)
    (hQ : Q.toPathPacking.InternallyDisjointFromSet A)
    (htarget_only :
      ∀ i : P.Index, ∀ j : Q.Index,
        (Q.path j).target ∈ (P.path i).vertexSet →
          (Q.path j).target = (Q.path j).source)
    (hQstay : Q.toPathPacking.StaysIn B) :
    (P.concatOfFirstStaysInSecondInternallyDisjointTargetOnlyAtSource
      Q hP hQ htarget_only).toPathPacking.StaysIn (A ∪ B) := by
  dsimp [concatOfFirstStaysInSecondInternallyDisjointTargetOnlyAtSource]
  exact P.concat_staysIn_union Q _ _ hP hQstay

/-- A region-separated concatenation is internally disjoint from a third set
when both input packings are internally disjoint from that set and the glued
terminal set avoids it. -/
theorem concatOfFirstInternallyDisjointSecondStaysIn_internallyDisjointFromSet
    {U A C : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.InternallyDisjointFromSet A)
    (hQ : Q.toPathPacking.StaysIn A)
    (hSdisj : Disjoint S A)
    (hPC : P.toPathPacking.InternallyDisjointFromSet C)
    (hQC : Q.toPathPacking.InternallyDisjointFromSet C)
    (hTdisj : Disjoint T C) :
    ((P.concatOfFirstInternallyDisjointSecondStaysIn Q hP hQ hSdisj).toPathPacking).InternallyDisjointFromSet C := by
  intro i v hv hvC
  have hsplit :=
    P.concatOfFirstInternallyDisjointSecondStaysIn_path_vertexSet_subset
      Q hP hQ hSdisj i hv
  rcases Finset.mem_union.mp hsplit with hvP | hvQ
  · rcases hPC i hvP hvC with hsource | htarget
    · exact Or.inl (by
        exact hsource)
    · exact False.elim
        (Finset.disjoint_left.mp hTdisj (P.target_mem i)
          (by simpa [htarget] using hvC))
  · rcases hQC (P.indexOfSourceTarget Q i) hvQ hvC with hsource | htarget
    · exact False.elim
        (Finset.disjoint_left.mp hTdisj
          (Q.source_mem (P.indexOfSourceTarget Q i))
          (by simpa [hsource] using hvC))
    · exact Or.inr (by
        exact htarget)

/-- The symmetric region-separated concatenation is internally disjoint from a
third set when both input packings are internally disjoint from that set and the
glued terminal set avoids it. -/
theorem concatOfFirstStaysInSecondInternallyDisjoint_internallyDisjointFromSet
    {U A C : Finset V}
    (P : PerfectPathPacking G S T) (Q : PerfectPathPacking G T U)
    (hP : P.toPathPacking.StaysIn A)
    (hQ : Q.toPathPacking.InternallyDisjointFromSet A)
    (hUdisj : Disjoint U A)
    (hPC : P.toPathPacking.InternallyDisjointFromSet C)
    (hQC : Q.toPathPacking.InternallyDisjointFromSet C)
    (hTdisj : Disjoint T C) :
    ((P.concatOfFirstStaysInSecondInternallyDisjoint Q hP hQ hUdisj).toPathPacking).InternallyDisjointFromSet C := by
  intro i v hv hvC
  have hsplit :=
    P.concatOfFirstStaysInSecondInternallyDisjoint_path_vertexSet_subset
      Q hP hQ hUdisj i hv
  rcases Finset.mem_union.mp hsplit with hvP | hvQ
  · rcases hPC i hvP hvC with hsource | htarget
    · exact Or.inl (by
        exact hsource)
    · exact False.elim
        (Finset.disjoint_left.mp hTdisj (P.target_mem i)
          (by simpa [htarget] using hvC))
  · rcases hQC (P.indexOfSourceTarget Q i) hvQ hvC with hsource | htarget
    · exact False.elim
        (Finset.disjoint_left.mp hTdisj
          (Q.source_mem (P.indexOfSourceTarget Q i))
          (by simpa [hsource] using hvC))
    · exact Or.inr (by
        exact htarget)

end PerfectPathPacking

namespace PathPacking

variable {V : Type*} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {S T : Finset V}

/-- An equal-size node-disjoint packing can be promoted to an oriented perfect
packing.  The node-disjointness and cardinality hypotheses imply that every
terminal on both sides is used exactly once. -/
noncomputable def toPerfectOfCardEq (P : PathPacking G S T)
    (hcardS : P.card = S.card) (hcardT : P.card = T.card) :
    PerfectPathPacking G S T where
  toPathPacking := P.orient
  source_mem := by
    intro i
    exact GraphPath.orient_source_mem (P.path i) (P.connects i)
  target_mem := by
    intro i
    exact GraphPath.orient_target_mem (P.path i) (P.connects i)
  source_bijective := by
    classical
    apply (Fintype.bijective_iff_injective_and_card _).2
    constructor
    · intro i j hij
      by_contra hne
      have hdisj := (P.orient).node_disjoint hne
      have hsrc :
          ((P.orient).path i).source = ((P.orient).path j).source :=
        congrArg Subtype.val hij
      have hi : ((P.orient).path i).source ∈ ((P.orient).path i).vertexSet :=
        GraphPath.source_mem_vertexSet ((P.orient).path i)
      have hj : ((P.orient).path i).source ∈ ((P.orient).path j).vertexSet := by
        simpa [hsrc] using GraphPath.source_mem_vertexSet ((P.orient).path j)
      exact Finset.disjoint_left.mp hdisj hi hj
    · rw [Fintype.card_coe]
      exact hcardS
  target_bijective := by
    classical
    apply (Fintype.bijective_iff_injective_and_card _).2
    constructor
    · intro i j hij
      by_contra hne
      have hdisj := (P.orient).node_disjoint hne
      have htgt :
          ((P.orient).path i).target = ((P.orient).path j).target :=
        congrArg Subtype.val hij
      have hi : ((P.orient).path i).target ∈ ((P.orient).path i).vertexSet :=
        GraphPath.target_mem_vertexSet ((P.orient).path i)
      have hj : ((P.orient).path i).target ∈ ((P.orient).path j).vertexSet := by
        simpa [htgt] using GraphPath.target_mem_vertexSet ((P.orient).path j)
      exact Finset.disjoint_left.mp hdisj hi hj
    · rw [Fintype.card_coe]
      exact hcardT

/-- Promote a path packing to a perfect packing on the terminal sets actually
used by its oriented paths. -/
noncomputable def toPerfectUsedTerminals (P : PathPacking G S T) :
    PerfectPathPacking G P.sourceSet P.targetSet where
  toPathPacking := {
    Index := P.Index
    path := fun i => P.orient.path i
    connects := by
      intro i
      exact Or.inl
        ⟨Finset.mem_image.mpr ⟨i, by simp, rfl⟩,
          Finset.mem_image.mpr ⟨i, by simp, rfl⟩⟩
    node_disjoint := P.orient.node_disjoint
  }
  source_mem := by
    intro i
    exact Finset.mem_image.mpr ⟨i, by simp, rfl⟩
  target_mem := by
    intro i
    exact Finset.mem_image.mpr ⟨i, by simp, rfl⟩
  source_bijective := by
    classical
    constructor
    · intro i j hij
      by_contra hne
      have hdisj := (P.orient).node_disjoint hne
      have hsrc :
          (P.orient.path i).source = (P.orient.path j).source :=
        congrArg Subtype.val hij
      have hi : (P.orient.path i).source ∈ (P.orient.path i).vertexSet :=
        GraphPath.source_mem_vertexSet (P.orient.path i)
      have hj : (P.orient.path i).source ∈ (P.orient.path j).vertexSet := by
        simpa [hsrc] using GraphPath.source_mem_vertexSet (P.orient.path j)
      exact Finset.disjoint_left.mp hdisj hi hj
    · intro v
      rcases Finset.mem_image.mp v.2 with ⟨i, _hi, hv⟩
      refine ⟨i, Subtype.ext ?_⟩
      exact hv
  target_bijective := by
    classical
    constructor
    · intro i j hij
      by_contra hne
      have hdisj := (P.orient).node_disjoint hne
      have htgt :
          (P.orient.path i).target = (P.orient.path j).target :=
        congrArg Subtype.val hij
      have hi : (P.orient.path i).target ∈ (P.orient.path i).vertexSet :=
        GraphPath.target_mem_vertexSet (P.orient.path i)
      have hj : (P.orient.path i).target ∈ (P.orient.path j).vertexSet := by
        simpa [htgt] using GraphPath.target_mem_vertexSet (P.orient.path j)
      exact Finset.disjoint_left.mp hdisj hi hj
    · intro v
      rcases Finset.mem_image.mp v.2 with ⟨i, _hi, hv⟩
      refine ⟨i, Subtype.ext ?_⟩
      exact hv

@[simp] theorem toPerfectUsedTerminals_card (P : PathPacking G S T) :
    P.toPerfectUsedTerminals.card = P.card := rfl

/-- Promoting a packing to a perfect packing on its used terminal sets
preserves vertex containment. -/
theorem toPerfectUsedTerminals_staysIn
    (P : PathPacking G S T) {U : Finset V} (hP : P.StaysIn U) :
    P.toPerfectUsedTerminals.toPathPacking.StaysIn U := by
  exact PathPacking.orient_staysIn hP

/-- Promoting a packing to a perfect packing on its used terminal sets
preserves internal disjointness from a vertex set. -/
theorem toPerfectUsedTerminals_internallyDisjointFromSet
    (P : PathPacking G S T) {U : Finset V}
    (hP : P.InternallyDisjointFromSet U) :
    P.toPerfectUsedTerminals.toPathPacking.InternallyDisjointFromSet U := by
  exact PathPacking.orient_internallyDisjointFromSet hP

/-- Promoting a packing to a perfect packing on its used terminal sets
preserves localized pairwise bridges. -/
theorem toPerfectUsedTerminals_hasPairwiseBridgesIn
    (P : PathPacking G S T) {U : Finset V}
    (hP : P.HasPairwiseBridgesIn U) :
    P.toPerfectUsedTerminals.toPathPacking.HasPairwiseBridgesIn U := by
  intro i j hij
  rcases (PathPacking.orient_hasPairwiseBridgesIn hP) hij with ⟨β, hβU⟩
  let β' : P.toPerfectUsedTerminals.toPathPacking.BridgeBetween i j := {
    path := β.path
    connects := by
      simpa [toPerfectUsedTerminals] using β.connects
    internallyDisjoint := by
      intro v hv hrows
      exact β.internallyDisjoint hv (by
        exact hrows)
  }
  exact ⟨β', by simpa [β'] using hβU⟩

end PathPacking

/-- A finite indexed family of edge-disjoint paths connecting two vertex sets.

Unlike `PathPacking`, this structure does not require the paths to be
vertex-disjoint.  This matches the paper's edge-well-linkedness convention,
where paths may share endpoints and internal vertices but not edges. -/
structure EdgePathPacking {V : Type*} [DecidableEq V]
    (G : _root_.SimpleGraph V) (S T : Finset V) where
  /-- The finite index type for the paths in the packing. -/
  Index : Type
  /-- The index type is finite. -/
  [indexFintype : Fintype Index]
  /-- The index type has decidable equality. -/
  [indexDecidableEq : DecidableEq Index]
  /-- The path assigned to each index. -/
  path : Index → GraphPath G
  /-- Every path connects the two specified vertex sets. -/
  connects : ∀ i : Index, (path i).Connects S T
  /-- Distinct indexed paths are edge-disjoint. -/
  edge_disjoint : Pairwise fun i j => GraphPath.EdgeDisjoint (path i) (path j)

namespace EdgePathPacking

variable {V : Type*} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {S T : Finset V}

instance (P : EdgePathPacking G S T) : Fintype P.Index := P.indexFintype
instance (P : EdgePathPacking G S T) : DecidableEq P.Index := P.indexDecidableEq

/-- The number of paths in an edge-disjoint packing. -/
noncomputable def card (P : EdgePathPacking G S T) : ℕ :=
  Fintype.card P.Index

/-- Every path in the edge-disjoint packing has all vertices contained in
`U`. -/
def StaysIn (P : EdgePathPacking G S T) (U : Finset V) : Prop :=
  ∀ i : P.Index, (P.path i).vertexSet ⊆ U

/-- Map every path in an edge-disjoint packing to a supergraph on the same
vertex type. -/
def mapLe (P : EdgePathPacking G S T) {H : _root_.SimpleGraph V} (hGH : G ≤ H) :
    EdgePathPacking H S T where
  Index := P.Index
  path := fun i => (P.path i).mapLe hGH
  connects := by
    intro i
    simpa [GraphPath.mapLe, GraphPath.Connects] using P.connects i
  edge_disjoint := by
    intro i j hij
    simpa [GraphPath.EdgeDisjoint] using P.edge_disjoint hij

end EdgePathPacking

/-- A finite vertex set is node-well-linked inside a finite region `C` of `G`
when every pair of disjoint subfamilies can be linked by the maximum possible
number of node-disjoint paths contained in `C`.

This is the paper's node-well-linkedness specialized to finite sets and with
the ambient cluster `C` made explicit. -/
def NodeWellLinkedIn {V : Type*} [DecidableEq V]
    (G : _root_.SimpleGraph V) (C T : Finset V) : Prop :=
  T ⊆ C ∧
    ∀ ⦃A B : Finset V⦄, A ⊆ T → B ⊆ T → Disjoint A B →
      ∃ P : PathPacking G A B,
        P.card = min A.card B.card ∧ P.StaysIn C

namespace NodeWellLinkedIn

variable {V : Type*} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {C T U : Finset V}

/-- Node-well-linkedness is inherited by smaller terminal sets. -/
theorem mono_terminals (h : NodeWellLinkedIn G C T) (hU : U ⊆ T) :
    NodeWellLinkedIn G C U := by
  constructor
  · exact subset_trans hU h.1
  · intro A B hA hB hdisj
    exact h.2 (subset_trans hA hU) (subset_trans hB hU) hdisj

/-- Node-well-linkedness is preserved when edges are added to the ambient
graph. -/
theorem mono_graph {G' : _root_.SimpleGraph V}
    (h : NodeWellLinkedIn G C T) (hGG' : G ≤ G') :
    NodeWellLinkedIn G' C T := by
  constructor
  · exact h.1
  · intro A B hA hB hdisj
    rcases h.2 hA hB hdisj with ⟨P, hcard, hstay⟩
    refine ⟨P.mapLe hGG', ?_, ?_⟩
    · exact hcard
    · intro i
      change ((P.path i).mapLe hGG').vertexSet ⊆ C
      simpa using hstay i

end NodeWellLinkedIn

/-- Edge-well-linkedness inside a finite region `C`.  Paths may share vertices
but must be pairwise edge-disjoint. -/
def EdgeWellLinkedIn {V : Type*} [DecidableEq V]
    (G : _root_.SimpleGraph V) (C T : Finset V) : Prop :=
  T ⊆ C ∧
    ∀ ⦃A B : Finset V⦄, A ⊆ T → B ⊆ T → Disjoint A B →
      ∃ P : EdgePathPacking G A B,
        P.card = min A.card B.card ∧ P.StaysIn C

namespace EdgeWellLinkedIn

variable {V : Type*} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {C T U : Finset V}

/-- Edge-well-linkedness is inherited by smaller terminal sets. -/
theorem mono_terminals (h : EdgeWellLinkedIn G C T) (hU : U ⊆ T) :
    EdgeWellLinkedIn G C U := by
  constructor
  · exact subset_trans hU h.1
  · intro A B hA hB hdisj
    exact h.2 (subset_trans hA hU) (subset_trans hB hU) hdisj

/-- Edge-well-linkedness is preserved when edges are added to the ambient
graph. -/
theorem mono_graph {G' : _root_.SimpleGraph V}
    (h : EdgeWellLinkedIn G C T) (hGG' : G ≤ G') :
    EdgeWellLinkedIn G' C T := by
  constructor
  · exact h.1
  · intro A B hA hB hdisj
    rcases h.2 hA hB hdisj with ⟨P, hcard, hstay⟩
    refine ⟨P.mapLe hGG', ?_, ?_⟩
    · exact hcard
    · intro i
      change ((P.path i).mapLe hGG').vertexSet ⊆ C
      simpa using hstay i

end EdgeWellLinkedIn

/-- Two finite vertex sets are linked inside `C` if all subfamilies can be
joined by the maximum possible number of node-disjoint paths contained in `C`. -/
def NodeLinkedIn {V : Type*} [DecidableEq V]
    (G : _root_.SimpleGraph V) (C A B : Finset V) : Prop :=
  A ⊆ C ∧ B ⊆ C ∧ Disjoint A B ∧
    ∀ ⦃A' B' : Finset V⦄, A' ⊆ A → B' ⊆ B →
      ∃ P : PathPacking G A' B',
        P.card = min A'.card B'.card ∧ P.StaysIn C

namespace NodeLinkedIn

variable {V : Type*} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {C A B : Finset V}

/-- Node-linkedness is inherited by smaller terminal sets on both sides. -/
theorem mono_terminals {A₀ B₀ : Finset V} (h : NodeLinkedIn G C A B)
    (hA₀ : A₀ ⊆ A) (hB₀ : B₀ ⊆ B) :
    NodeLinkedIn G C A₀ B₀ := by
  refine ⟨subset_trans hA₀ h.1, subset_trans hB₀ h.2.1, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro v hvA hvB
    exact Finset.disjoint_left.mp h.2.2.1 (hA₀ hvA) (hB₀ hvB)
  · intro A' B' hA' hB'
    exact h.2.2.2 (subset_trans hA' hA₀) (subset_trans hB' hB₀)

/-- Node-linkedness is preserved when edges are added to the ambient graph. -/
theorem mono_graph {G' : _root_.SimpleGraph V}
    (h : NodeLinkedIn G C A B) (hGG' : G ≤ G') :
    NodeLinkedIn G' C A B := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  intro A' B' hA' hB'
  rcases h.2.2.2 hA' hB' with ⟨P, hcard, hstay⟩
  refine ⟨P.mapLe hGG', ?_, ?_⟩
  · simpa using hcard
  · intro i
    change ((P.path i).mapLe hGG').vertexSet ⊆ C
    simpa using hstay i

/-- A linked pair supplies a full-size path packing between the two full sets. -/
theorem exists_pathPacking (h : NodeLinkedIn G C A B) :
    ∃ P : PathPacking G A B,
      P.card = min A.card B.card ∧ P.StaysIn C :=
  h.2.2.2 subset_rfl subset_rfl

/-- If linked terminal sets have the same size, the full linkage can be
oriented and promoted to a perfect path packing. -/
theorem exists_perfectPathPacking_of_card_eq (h : NodeLinkedIn G C A B)
    (hcard : A.card = B.card) :
    ∃ P : PerfectPathPacking G A B,
      P.card = A.card ∧ P.toPathPacking.StaysIn C := by
  rcases h.exists_pathPacking with ⟨P, hPcard, hstay⟩
  have hPcardA : P.card = A.card := by
    simpa [hcard] using hPcard
  have hPcardB : P.card = B.card := hPcardA.trans hcard
  refine ⟨P.toPerfectOfCardEq hPcardA hPcardB, ?_, ?_⟩
  · exact hPcardA
  · exact PathPacking.orient_staysIn hstay

end NodeLinkedIn

namespace NodeWellLinkedIn

variable {V : Type*} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {C T : Finset V}

/-- Disjoint subfamilies of one node-well-linked terminal set are node-linked
inside the same region. -/
theorem nodeLinkedIn_between_disjoint_subsets
    (h : NodeWellLinkedIn G C T) {A B : Finset V}
    (hA : A ⊆ T) (hB : B ⊆ T) (hdisj : Disjoint A B) :
    NodeLinkedIn G C A B := by
  refine ⟨subset_trans hA h.1, subset_trans hB h.1, hdisj, ?_⟩
  intro A' B' hA' hB'
  have hA'T : A' ⊆ T := subset_trans hA' hA
  have hB'T : B' ⊆ T := subset_trans hB' hB
  have hA'B' : Disjoint A' B' := by
    rw [Finset.disjoint_left]
    intro v hvA hvB
    exact Finset.disjoint_left.mp hdisj (hA' hvA) (hB' hvB)
  exact h.2 hA'T hB'T hA'B'

end NodeWellLinkedIn

end SimpleGraph

end Erdos73Infrastructure
