/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PreliminaryInternalSafeCandidates
import ErdosProblems.Erdos207.ReserveWedgeSampling

/-!
# Geometry of a reserve-protected preliminary family

In the KSSS master step the preliminary process runs in
`G \ (R ∪ G[U])`.  Thus it uses neither an edge wholly inside the next
vortex set nor an edge of the sampled crossing reserve.  This file records
the part of that restriction needed by the internal cover: a residual
outside edge together with two reserve spokes still forms a triangle whose
three pairs avoid the old and preliminary packing.
-/

namespace Erdos207

open Finset

noncomputable section

/-- Available triangles none of whose three pairs belongs to `reserve`. -/
def reserveProtectedAvailable
    {V : Type*} [DecidableEq V]
    (reserve : Finset (Sym2 V)) (A : TripleSystemOn V) : TripleSystemOn V :=
  A.filter fun T ↦ Disjoint (tripleEdgeFinset T) reserve

@[simp]
lemma mem_reserveProtectedAvailable_iff
    {V : Type*} [DecidableEq V]
    {reserve : Finset (Sym2 V)} {A : TripleSystemOn V} {T : TripleOn V} :
    T ∈ reserveProtectedAvailable reserve A ↔
      T ∈ A ∧ Disjoint (tripleEdgeFinset T) reserve := by
  simp [reserveProtectedAvailable]

lemma reserveProtectedAvailable_subset
    {V : Type*} [DecidableEq V]
    (reserve : Finset (Sym2 V)) (A : TripleSystemOn V) :
    reserveProtectedAvailable reserve A ⊆ A :=
  filter_subset _ _

lemma ConsistsOfTriangles.reserveProtectedAvailable
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {reserve : Finset (Sym2 V)}
    {A : TripleSystemOn V} (hA : ConsistsOfTriangles G A) :
    ConsistsOfTriangles G (reserveProtectedAvailable reserve A) := by
  intro T hT
  exact hA T (reserveProtectedAvailable_subset reserve A hT)

/-- The edge set of the KSSS preliminary graph
`G \ (R ∪ G[U])`: retain precisely the outer edges not placed in the
sampled reserve. -/
def reserveProtectedOuterEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (reserve : Finset (Sym2 V)) :
    Finset (Sym2 V) :=
  outerGraphEdges G U \ reserve

lemma reserveProtectedOuterEdges_subset_graphEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (reserve : Finset (Sym2 V)) :
    reserveProtectedOuterEdges G U reserve ⊆ graphEdges G := by
  intro e he
  exact (mem_outerGraphEdges_iff.mp (mem_sdiff.mp he).1).1

lemma crossingEdges_subset_outerGraphEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) :
    crossingEdges G U ⊆ outerGraphEdges G U := by
  intro e he
  have hc := mem_crossingEdges_iff.mp he
  rw [mem_outerGraphEdges_iff]
  refine ⟨mem_graphEdges_iff.mpr hc.1, ?_⟩
  intro hsub
  obtain ⟨x, hx⟩ := hc.2.2
  have hxdata := mem_sdiff.mp hx
  exact hxdata.2 (hsub hxdata.1)

lemma reserveEdges_subset_outerGraphEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (ω : Sym2 V → Bool) :
    reserveEdges G U ω ⊆ outerGraphEdges G U :=
  (reserveEdges_subset_crossingEdges G U ω).trans
    (crossingEdges_subset_outerGraphEdges G U)

/-- The spanning simple graph whose edges are the protected preliminary
edges. -/
def reserveProtectedOuterGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (reserve : Finset (Sym2 V)) :
    SimpleGraph V :=
  SimpleGraph.fromEdgeSet
    (reserveProtectedOuterEdges G U reserve : Set (Sym2 V))

lemma edgeSet_reserveProtectedOuterGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (reserve : Finset (Sym2 V)) :
    (reserveProtectedOuterGraph G U reserve).edgeSet =
      (reserveProtectedOuterEdges G U reserve : Set (Sym2 V)) := by
  ext e
  simp only [reserveProtectedOuterGraph, SimpleGraph.edgeSet_fromEdgeSet,
    Set.mem_sdiff, Finset.mem_coe, Sym2.mem_diagSet]
  constructor
  · exact fun h ↦ h.1
  · intro he
    refine ⟨he, ?_⟩
    exact G.not_isDiag_of_mem_edgeSet
      (mem_graphEdges_iff.mp
        (reserveProtectedOuterEdges_subset_graphEdges G U reserve he))

lemma graphEdges_reserveProtectedOuterGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (reserve : Finset (Sym2 V)) :
    graphEdges (reserveProtectedOuterGraph G U reserve) =
      reserveProtectedOuterEdges G U reserve := by
  ext e
  rw [mem_graphEdges_iff, edgeSet_reserveProtectedOuterGraph]
  rfl

lemma reserveProtectedOuterGraph_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (reserve : Finset (Sym2 V)) :
    reserveProtectedOuterGraph G U reserve ≤ G := by
  rw [← SimpleGraph.edgeSet_subset_edgeSet,
    edgeSet_reserveProtectedOuterGraph]
  intro e he
  exact mem_graphEdges_iff.mp
    (reserveProtectedOuterEdges_subset_graphEdges G U reserve he)

/-- Every edge of the protected preliminary graph is outer, so applying the
generic outer-edge operator does not change it. -/
lemma outerGraphEdges_reserveProtectedOuterGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (reserve : Finset (Sym2 V)) :
    outerGraphEdges (reserveProtectedOuterGraph G U reserve) U =
      reserveProtectedOuterEdges G U reserve := by
  ext e
  rw [mem_outerGraphEdges_iff, graphEdges_reserveProtectedOuterGraph]
  constructor
  · exact fun h ↦ h.1
  · intro he
    exact ⟨he, (mem_outerGraphEdges_iff.mp (mem_sdiff.mp he).1).2⟩

/-- Pair-stars for every protected edge are exactly the auxiliary
outside-pair survival condition for the complement of the protected graph. -/
lemma outsideLeavePairsAlive_compl_reserveProtectedOuterGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V}
    {reserve : Finset (Sym2 V)} {S : GreedyStateOn V}
    (halive : ∀ e ∈ reserveProtectedOuterEdges G U reserve,
      PairAlive e.toFinset S) :
    OutsideLeavePairsAlive (reserveProtectedOuterGraph G U reserve)ᶜ U S := by
  intro u v hnotCompl _hnotBoth hleave
  have hprotected : (reserveProtectedOuterGraph G U reserve).Adj u v := by
    by_contra hnotProtected
    apply hnotCompl
    simp only [SimpleGraph.compl_adj]
    exact ⟨hleave.ne, hnotProtected⟩
  have he : s(u, v) ∈ reserveProtectedOuterEdges G U reserve := by
    rw [← graphEdges_reserveProtectedOuterGraph G U reserve,
      mem_graphEdges_iff]
    exact hprotected
  simpa [Sym2.toFinset_mk_eq] using halive s(u, v) he

/-- The actual preliminary family: triangles of the master availability all
of whose pairs lie in `G \ (R ∪ G[U])`. -/
def reserveProtectedOuterAvailable
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (reserve : Finset (Sym2 V))
    (A : TripleSystemOn V) : TripleSystemOn V :=
  A.filter fun T ↦
    tripleEdgeFinset T ⊆ reserveProtectedOuterEdges G U reserve

/-- Every member of a triangle family meets `U` in at most one vertex.  This
is the exact geometric property needed for localized preliminary-star loss;
unlike disjointness from `U`, it remains true at an arbitrary reserve
density. -/
def TrianglesMeetAtMostOne
    {V : Type*} [DecidableEq V]
    (U : Finset V) (P : TripleSystemOn V) : Prop :=
  ∀ T ∈ P, ∀ {x y : V}, x ∈ T.1 → x ∈ U → y ∈ T.1 → y ∈ U → x = y

@[simp]
lemma mem_reserveProtectedOuterAvailable_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} {reserve : Finset (Sym2 V)}
    {A : TripleSystemOn V} {T : TripleOn V} :
    T ∈ reserveProtectedOuterAvailable G U reserve A ↔
      T ∈ A ∧
        tripleEdgeFinset T ⊆ reserveProtectedOuterEdges G U reserve := by
  simp [reserveProtectedOuterAvailable]

lemma reserveProtectedOuterAvailable_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (reserve : Finset (Sym2 V))
    (A : TripleSystemOn V) :
    reserveProtectedOuterAvailable G U reserve A ⊆ A :=
  filter_subset _ _

/-- Protected preliminary triangles cannot contain two distinct vertices of
`U`, since their connecting pair would not be an outer edge. -/
lemma trianglesMeetAtMostOne_reserveProtectedOuterAvailable
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (reserve : Finset (Sym2 V))
    (A : TripleSystemOn V) :
    TrianglesMeetAtMostOne U
      (reserveProtectedOuterAvailable G U reserve A) := by
  intro T hT x y hxT hxU hyT hyU
  by_contra hxy
  have heT : s(x, y) ∈ tripleEdgeFinset T :=
    mk_mem_tripleEdgeFinset_iff.mpr ⟨hxT, hyT, hxy⟩
  have heOuter := (mem_reserveProtectedOuterAvailable_iff.mp hT).2 heT
  exact (mem_outerGraphEdges_iff.mp (mem_sdiff.mp heOuter).1).2 (by
    intro z hz
    simp only [Sym2.toFinset_mk_eq, mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hxU
    · exact hyU)

lemma reserveProtectedOuterAvailable_subset_reserveProtectedAvailable
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (reserve : Finset (Sym2 V))
    (A : TripleSystemOn V) :
    reserveProtectedOuterAvailable G U reserve A ⊆
      reserveProtectedAvailable reserve A := by
  intro T hT
  rw [mem_reserveProtectedAvailable_iff]
  refine ⟨(mem_reserveProtectedOuterAvailable_iff.mp hT).1, ?_⟩
  rw [Finset.disjoint_left]
  intro e heT heReserve
  exact (mem_sdiff.mp
    ((mem_reserveProtectedOuterAvailable_iff.mp hT).2 heT)).2 heReserve

lemma ConsistsOfTriangles.reserveProtectedOuterAvailable
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} {reserve : Finset (Sym2 V)}
    {A : TripleSystemOn V} (hA : ConsistsOfTriangles G A) :
    ConsistsOfTriangles G
      (reserveProtectedOuterAvailable G U reserve A) := by
  intro T hT
  exact hA T (reserveProtectedOuterAvailable_subset G U reserve A hT)

/-- If every crossing edge is reserved, every protected preliminary triangle
is wholly outside `U`.  Indeed a triangle meeting `U` has a second vertex;
its connecting edge is either internal to `U` (hence not outer) or crossing
(hence reserved), contradicting protected availability in either case. -/
lemma trianglesDisjointFrom_reserveProtectedOuterAvailable_full
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (A : TripleSystemOn V) :
    TrianglesDisjointFrom U
      (reserveProtectedOuterAvailable G U (crossingEdges G U) A) := by
  intro T hT
  rw [Finset.disjoint_left]
  intro u huT huU
  have hcard : 1 < T.1.card := by simpa [T.2]
  obtain ⟨v, hvT, hvu⟩ := T.1.exists_mem_ne hcard u
  have heT : s(u, v) ∈ tripleEdgeFinset T :=
    mk_mem_tripleEdgeFinset_iff.mpr ⟨huT, hvT, Ne.symm hvu⟩
  have heProtected :=
    (mem_reserveProtectedOuterAvailable_iff.mp hT).2 heT
  have heOuter := (mem_sdiff.mp heProtected).1
  have hvU : v ∉ U := by
    intro hvU
    exact (mem_outerGraphEdges_iff.mp heOuter).2 (by
      intro x hx
      simp only [Sym2.toFinset_mk_eq, mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact huU
      · exact hvU)
  have heCrossing : s(u, v) ∈ crossingEdges G U := by
    rw [mem_crossingEdges_iff]
    refine ⟨(mem_outerGraphEdges_iff.mp heOuter).1 |> mem_graphEdges_iff.mp,
      ?_⟩
    exact isCrossingEdge_mk_iff.mpr (Or.inl ⟨huU, hvU⟩)
  exact (mem_sdiff.mp heProtected).2 heCrossing

/-- The protected availability consists of triangles of the protected
preliminary graph itself, not merely of the original graph. -/
lemma consistsOfTriangles_reserveProtectedOuterGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (reserve : Finset (Sym2 V))
    (A : TripleSystemOn V) :
    ConsistsOfTriangles (reserveProtectedOuterGraph G U reserve)
      (reserveProtectedOuterAvailable G U reserve A) := by
  intro T hT u hu v hv huv
  have heT : s(u, v) ∈ tripleEdgeFinset T :=
    mk_mem_tripleEdgeFinset_iff.mpr ⟨hu, hv, huv⟩
  have heProtected :=
    (mem_reserveProtectedOuterAvailable_iff.mp hT).2 heT
  have heGraph : s(u, v) ∈ graphEdges
      (reserveProtectedOuterGraph G U reserve) := by
    rw [graphEdges_reserveProtectedOuterGraph]
    exact heProtected
  have heSet := mem_graphEdges_iff.mp heGraph
  change (reserveProtectedOuterGraph G U reserve).Adj u v at heSet
  exact heSet

/-- Residual protected outer edges are exactly the original residual outer
edges with the sampled reserve removed. -/
lemma preliminaryResidualOuterEdges_reserveProtectedOuterGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (reserve : Finset (Sym2 V))
    (P : TripleSystemOn V) :
    preliminaryResidualOuterEdges
        (reserveProtectedOuterGraph G U reserve) U P =
      preliminaryResidualOuterEdges G U P \ reserve := by
  ext e
  simp only [preliminaryResidualOuterEdges,
    outerGraphEdges_reserveProtectedOuterGraph,
    reserveProtectedOuterEdges, mem_sdiff]
  tauto

/-- An edge with both endpoints outside `U` cannot be a crossing edge. -/
lemma internalOuterEdges_disjoint_crossingEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) :
    Disjoint (internalOuterEdges G U) (crossingEdges G U) := by
  rw [Finset.disjoint_left]
  intro e heInternal heCrossing
  have hout := (mem_internalOuterEdges_iff.mp heInternal).2
  obtain ⟨x, hx⟩ := (mem_crossingEdges_iff.mp heCrossing).2.1
  have hxdata := mem_inter.mp hx
  have hx' := Sym2.mem_toFinset.mp hxdata.1
  have hxpair : x ∈ s(e.out.1, e.out.2) := by
    simpa only [e.out_eq] using hx'
  rcases Sym2.mem_iff.mp hxpair with rfl | rfl
  · exact hout.1 hxdata.2
  · exact hout.2 hxdata.2

/-- Every residual internal edge is tracked by the protected preliminary
graph when the protected set consists only of crossing edges. -/
lemma preliminaryResidualInternalEdges_subset_protectedResidualOuter
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (reserve : Finset (Sym2 V))
    (P : TripleSystemOn V) (hreserve : reserve ⊆ crossingEdges G U) :
    preliminaryResidualInternalEdges G U P ⊆
      preliminaryResidualOuterEdges
        (reserveProtectedOuterGraph G U reserve) U P := by
  rw [preliminaryResidualOuterEdges_reserveProtectedOuterGraph]
  intro e he
  have hedata := mem_inter.mp he
  apply mem_sdiff.mpr
  refine ⟨hedata.2, ?_⟩
  intro heReserve
  exact Finset.disjoint_left.mp
    (internalOuterEdges_disjoint_crossingEdges G U)
      hedata.1 (hreserve heReserve)

/-- Crossing residual edges not already sampled are contained in the
residual edge family tracked by the protected preliminary graph. -/
lemma residualCrossing_sdiff_reserve_subset_protectedResidualOuter
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (reserve : Finset (Sym2 V))
    (P : TripleSystemOn V) :
    preliminaryResidualCrossingEdges G U P \ reserve ⊆
      preliminaryResidualOuterEdges
        (reserveProtectedOuterGraph G U reserve) U P := by
  rw [preliminaryResidualOuterEdges_reserveProtectedOuterGraph]
  intro e he
  have hdata := mem_sdiff.mp he
  exact mem_sdiff.mpr
    ⟨mem_sdiff.mpr
      ⟨crossingEdges_subset_outerGraphEdges G U
        (mem_sdiff.mp hdata.1).1, (mem_sdiff.mp hdata.1).2⟩,
      hdata.2⟩

/-- Adding the sampled part after removing it from the new residual part
recovers the usual augmented reserve. -/
lemma union_residualCrossing_sdiff_reserve
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (reserve : Finset (Sym2 V))
    (P : TripleSystemOn V) :
    reserve ∪ (preliminaryResidualCrossingEdges G U P \ reserve) =
      preliminaryAugmentedReserve G U reserve P := by
  unfold preliminaryAugmentedReserve
  ext e
  simp only [mem_union, mem_sdiff]
  tauto

/-- A family selected from reserve-protected availability covers no reserve
edge. -/
lemma reserve_not_covered_of_subset_reserveProtected
    {V : Type*} [Fintype V] [DecidableEq V]
    {reserve : Finset (Sym2 V)} {A M : TripleSystemOn V}
    (hM : M ⊆ reserveProtectedAvailable reserve A) :
    ∀ e ∈ reserve, e ∉ graphEdges (coveredGraph M) := by
  intro e heR heCovered
  have hadj : (coveredGraph M).Adj e.out.1 e.out.2 :=
    graph_adj_out_of_mem_graphEdges heCovered
  obtain ⟨T, hTM, huT, hvT, hne⟩ := coveredGraph_adj.mp hadj
  have heT : e ∈ tripleEdgeFinset T := by
    rw [← e.out_eq]
    exact mk_mem_tripleEdgeFinset_iff.mpr ⟨huT, hvT, hne⟩
  have hprotected := (mem_reserveProtectedAvailable_iff.mp (hM hTM)).2
  exact Finset.disjoint_left.mp hprotected heT heR

/-- The old packing covers no edge of a graph contained in its leave. -/
lemma not_covered_of_graph_le_leave
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {P : TripleSystemOn V}
    (hold : G ≤ leaveGraph P) {e : Sym2 V} (heG : e ∈ graphEdges G) :
    e ∉ graphEdges (coveredGraph P) := by
  intro heCovered
  have hG : G.Adj e.out.1 e.out.2 :=
    graph_adj_out_of_mem_graphEdges heG
  have hleave := leaveGraph_adj.mp (hold hG)
  exact hleave.2 (graph_adj_out_of_mem_graphEdges heCovered)

/-- A residual outside edge and two protected reserve spokes form a triangle
whose pairs all avoid the union of the old and preliminary families. -/
lemma thirdVertexTriple_avoids_old_union_reserveProtected
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V}
    {reserve : Finset (Sym2 V)} {A P M : TripleSystemOn V}
    {e : Sym2 V}
    (he : e ∈ preliminaryResidualInternalEdges G U (P ∪ M))
    (hreserve : reserve ⊆ graphEdges G)
    (hold : G ≤ leaveGraph P)
    (hM : M ⊆ reserveProtectedAvailable reserve A)
    (w : ThirdVertex e.out.1 e.out.2)
    (hspokes : reserveWedgeBlock e.out.1 e.out.2 w.1 ⊆ reserve) :
    TriangleAvoidsGraph (coveredGraph (P ∪ M))
      (thirdVertexTriple
        (out_fst_ne_snd_of_mem_graphEdges
          (internalOuterEdges_subset_graphEdges G U
            (preliminaryResidualInternalEdges_subset_internalOuterEdges
              G U (P ∪ M) he))) w) := by
  let hne : e.out.1 ≠ e.out.2 :=
    out_fst_ne_snd_of_mem_graphEdges
      (internalOuterEdges_subset_graphEdges G U
        (preliminaryResidualInternalEdges_subset_internalOuterEdges
          G U (P ∪ M) he))
  rw [triangleAvoidsGraph_thirdVertexTriple_iff]
  have hnotUV : ¬ (coveredGraph (P ∪ M)).Adj e.out.1 e.out.2 := by
    intro hcovered
    have hres := preliminaryResidualInternalEdges_subset_residualOuterEdges
      G U (P ∪ M) he
    exact (mem_sdiff.mp hres).2 (by
      rw [← e.out_eq]
      exact mem_graphEdges_iff.mpr hcovered)
  have spoke_not_covered : ∀ f ∈ reserveWedgeBlock e.out.1 e.out.2 w.1,
      ¬ (coveredGraph (P ∪ M)).Adj f.out.1 f.out.2 := by
    intro f hfW hcovered
    have hfR : f ∈ reserve := hspokes hfW
    obtain ⟨T, hT, huT, hvT, hneT⟩ := coveredGraph_adj.mp hcovered
    rcases mem_union.mp hT with hTP | hTM
    · have hfG : f ∈ graphEdges G := hreserve hfR
      have hnotP := not_covered_of_graph_le_leave hold hfG
      apply hnotP
      apply mem_graphEdges_iff.mpr
      rw [← f.out_eq]
      exact coveredGraph_adj.mpr ⟨T, hTP, huT, hvT, hneT⟩
    · have hprotected :=
        (mem_reserveProtectedAvailable_iff.mp (hM hTM)).2
      apply Finset.disjoint_left.mp hprotected _ hfR
      rw [← f.out_eq]
      exact mk_mem_tripleEdgeFinset_iff.mpr ⟨huT, hvT, hneT⟩
  have huwW : s(e.out.1, w.1) ∈
      reserveWedgeBlock e.out.1 e.out.2 w.1 := by
    simp [reserveWedgeBlock]
  have hvwW : s(e.out.2, w.1) ∈
      reserveWedgeBlock e.out.1 e.out.2 w.1 := by
    simp [reserveWedgeBlock]
  refine ⟨hnotUV, ?_, ?_⟩
  · have h := spoke_not_covered s(e.out.1, w.1) huwW
    intro hadj
    apply h
    exact graph_adj_out_of_mem_graphEdges (mem_graphEdges_iff.mpr hadj)
  · have h := spoke_not_covered s(e.out.2, w.1) hvwW
    intro hadj
    apply h
    exact graph_adj_out_of_mem_graphEdges (mem_graphEdges_iff.mpr hadj)

/-- Every reserve-active third vertex for a residual outside edge remains
available after imposing pair-safety against the old and preliminary
packings, provided the preliminary packing used no sampled reserve edge. -/
lemma activeReserveWedgeVertices_subset_pairSafe_of_reserveProtected
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V}
    {A P M : TripleSystemOn V} {e : Sym2 V}
    {ω : Sym2 V → Bool}
    (he : e ∈ preliminaryResidualInternalEdges G U (P ∪ M))
    (hold : G ≤ leaveGraph P)
    (hM : M ⊆ reserveProtectedAvailable (reserveEdges G U ω) A) :
    activeReserveWedgeVertices G U
        (iterationExtensionVertices A
          (SimpleGraph.edge e.out.1 e.out.2) U)
        e.out.1 e.out.2 ω ⊆
      iterationExtensionVertices (pairSafeAvailable A (P ∪ M))
        (SimpleGraph.edge e.out.1 e.out.2) U := by
  intro w hw
  have hwdata := mem_activeReserveWedgeVertices_iff.mp hw
  have hwS := hwdata.1
  have hspokes := hwdata.2
  have heInternal :=
    preliminaryResidualInternalEdges_subset_internalOuterEdges G U (P ∪ M) he
  have heGraph := internalOuterEdges_subset_graphEdges G U heInternal
  have hne := out_fst_ne_snd_of_mem_graphEdges heGraph
  have houter := (mem_internalOuterEdges_iff.mp heInternal).2
  have hwU := iterationExtensionVertices_subset A
    (SimpleGraph.edge e.out.1 e.out.2) U hwS
  let w' : ThirdVertex e.out.1 e.out.2 :=
    ⟨w, fun h ↦ houter.1 (h ▸ hwU), fun h ↦ houter.2 (h ▸ hwU)⟩
  have hTA : thirdVertexTriple hne w' ∈ A :=
    iterationExtensionVertices_edge_thirdVertexTriple_mem
      hne houter.1 houter.2 hwS
  have hsafe : thirdVertexTriple hne w' ∈
      pairSafeAvailable A (P ∪ M) := by
    apply mem_pairSafeAvailable_iff.mpr
    refine ⟨hTA, ?_⟩
    exact thirdVertexTriple_avoids_old_union_reserveProtected he
      (reserveEdges_subset_graphEdges G U ω) hold hM w' hspokes
  apply mem_iterationExtensionVertices_iff.mpr
  refine ⟨hwU, ?_⟩
  intro f hf
  rw [graphEdges_edge hne] at hf
  have hfe : f = s(e.out.1, e.out.2) := by simpa using hf
  subst f
  refine ⟨thirdVertexTriple hne w', hsafe,
    third_mem_thirdVertexTriple hne w', ?_⟩
  exact mk_mem_tripleEdgeFinset_iff.mpr
    ⟨left_mem_thirdVertexTriple hne w',
      right_mem_thirdVertexTriple hne w', hne⟩

/-- Filtering a larger third-vertex set by the same sampled reserve wedges
preserves every active candidate. -/
lemma activeReserveWedgeVertices_mono_candidates
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U S S' : Finset V} {u v : V}
    {bits : Sym2 V → Bool}
    (hSS' : S ⊆ S') :
    activeReserveWedgeVertices G U S u v bits ⊆
      activeReserveWedgeVertices G U S' u v bits := by
  intro w hw
  have hw' := mem_activeReserveWedgeVertices_iff.mp hw
  exact mem_activeReserveWedgeVertices_iff.mpr ⟨hSS' hw'.1, hw'.2⟩

/-- The sampled reserve-wedge supply surviving at the start of the internal
phase is at least its supply before a reserve-protected preliminary phase. -/
lemma card_activeReserveWedgeVertices_pairSafe_ge
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V}
    {A P M : TripleSystemOn V} {e : Sym2 V}
    {bits : Sym2 V → Bool}
    (he : e ∈ preliminaryResidualInternalEdges G U (P ∪ M))
    (hold : G ≤ leaveGraph P)
    (hM : M ⊆ reserveProtectedAvailable (reserveEdges G U bits) A) :
    (activeReserveWedgeVertices G U
        (iterationExtensionVertices A
          (SimpleGraph.edge e.out.1 e.out.2) U)
        e.out.1 e.out.2 bits).card ≤
      (activeReserveWedgeVertices G U
        (iterationExtensionVertices (pairSafeAvailable A (P ∪ M))
          (SimpleGraph.edge e.out.1 e.out.2) U)
        e.out.1 e.out.2 bits).card := by
  apply card_le_card
  intro w hw
  apply mem_activeReserveWedgeVertices_iff.mpr
  refine ⟨?_, (mem_activeReserveWedgeVertices_iff.mp hw).2⟩
  exact activeReserveWedgeVertices_subset_pairSafe_of_reserveProtected
    he hold hM hw

end

end Erdos207
