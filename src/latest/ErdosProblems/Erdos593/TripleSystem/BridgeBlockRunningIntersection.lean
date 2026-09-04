import ErdosProblems.Erdos593.Graph.RootedTree
import ErdosProblems.Erdos593.TripleSystem.BridgeBlockRestriction
import ErdosProblems.Erdos593.TripleSystem.ConstructiveForward
import ErdosProblems.Erdos593.TripleSystem.DegenerateBridgeBlock
import ErdosProblems.Erdos593.TripleSystem.EdgeRestrictionFull
import ErdosProblems.Erdos593.TripleSystem.EdgeRestrictionReconstruction
import ErdosProblems.Erdos593.TripleSystem.Isolated
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Running intersection for bridge-free Levi blocks

Every hyperedge belongs to the unique bridge-free Levi component containing
its Levi hyperedge-node.  This file packages those components, including the
degree-zero hyperedge components, and proves the exact edge partition and
non-isolated-point coverage used in the reverse reconstruction.

The quotient forest is rooted independently in each connected component.
Hyperedge-containing blocks are then listed component-by-component and in
nonincreasing depth order.  Since `RunningEdgeAssembly` stores the newest
piece first, its recursive assembly order is the reverse order: roots first,
with nondecreasing depth.
-/

namespace Erdos593

universe u v w

namespace TripleSystem
namespace BridgeBlock

noncomputable section

variable {V : Type u} {E : Type v} (F : TripleSystem V E)
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [DecidableRel F.levi.Adj]

private noncomputable abbrev core :=
  Erdos593.SimpleGraph.bridgeFree F.levi

private noncomputable abbrev quotientForest :=
  Erdos593.SimpleGraph.bridgeQuotient F.levi

/-- A bridge-free Levi component containing at least one hyperedge-node.
This includes singleton components coming from degree-zero hyperedge-nodes. -/
abbrev HyperedgeComponent :=
  {C : Component F // (componentHyperedgeSet F C).Nonempty}

/-- The unique hyperedge-containing bridge-free component assigned to an
original hyperedge. -/
noncomputable def hyperedgeComponentOf (e : E) : HyperedgeComponent F :=
  ⟨(core F).connectedComponentMk (Sum.inr e),
    e, _root_.SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩

@[simp]
theorem hyperedgeComponentOf_val (e : E) :
    (hyperedgeComponentOf F e : Component F) =
      (core F).connectedComponentMk (Sum.inr e) :=
  rfl

@[simp]
theorem mem_hyperedgeComponentOf_set (e : E) :
    e ∈ componentHyperedgeSet F (hyperedgeComponentOf F e) :=
  _root_.SimpleGraph.ConnectedComponent.connectedComponentMk_mem

/-- Distinct hyperedge-containing bridge-free components carry disjoint
original edge sets. -/
theorem componentHyperedgeSet_disjoint
    {C D : HyperedgeComponent F} (hCD : C ≠ D) :
    Disjoint (componentHyperedgeSet F C) (componentHyperedgeSet F D) := by
  rw [Set.disjoint_left]
  intro e heC heD
  apply hCD
  apply Subtype.ext
  change Sum.inr e ∈ (C : Component F).supp at heC
  change Sum.inr e ∈ (D : Component F).supp at heD
  change (core F).connectedComponentMk (Sum.inr e) = (C : Component F) at heC
  change (core F).connectedComponentMk (Sum.inr e) = (D : Component F) at heD
  have hC := heC
  have hD := heD
  exact hC.symm.trans hD

/-- The component edge sets are an exact partition of all original edges. -/
theorem iUnion_componentHyperedgeSet :
    (⋃ C : HyperedgeComponent F, componentHyperedgeSet F C) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro e
  rw [Set.mem_iUnion]
  exact ⟨hyperedgeComponentOf F e, mem_hyperedgeComponentOf_set F e⟩

/-- The supports of all component pieces cover exactly the non-isolated
vertices of the original triple system. -/
theorem iUnion_componentHyperedgeSupport :
    (⋃ C : HyperedgeComponent F,
        F.edgeSupportSet (componentHyperedgeSet F C)) =
      {x : V | ¬ F.IsIsolated x} := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_iUnion] at hx
    rcases hx with ⟨C, e, heC, hxe⟩
    exact F.not_isolated_of_inc hxe
  · intro hx
    rcases F.not_isolated_iff_exists_inc.mp hx with ⟨e, hxe⟩
    rw [Set.mem_iUnion]
    exact ⟨hyperedgeComponentOf F e, e,
      mem_hyperedgeComponentOf_set F e, hxe⟩

/-- Hypergraph-facing closed-star statement for the exact component pieces:
if the piece of `C` contains `x`, then `C` is either the bridge-free component
of the point-node `x`, or is adjacent to that component in the quotient
forest. -/
theorem hyperedgeComponent_mem_closedStar
    (C : HyperedgeComponent F) {x : V}
    (hx : x ∈ F.edgeSupportSet (componentHyperedgeSet F C)) :
    (C : Component F) = (core F).connectedComponentMk (Sum.inl x) ∨
      (quotientForest F).Adj C
        ((core F).connectedComponentMk (Sum.inl x)) := by
  rcases hx with ⟨e, heC, hxe⟩
  exact component_eq_or_leviBridgeQuotient_adj_of_inc F heC hxe

/-- A connected component of the quotient forest.  Each such component will
be rooted independently. -/
abbrev QuotientTreeComponent :=
  (quotientForest F).ConnectedComponent

/-- The quotient-tree component containing a bridge-free Levi component. -/
def quotientTreeComponent (C : Component F) : QuotientTreeComponent F :=
  (quotientForest F).connectedComponentMk C

/-- A fixed root in each connected component of the quotient forest. -/
noncomputable def quotientTreeRoot (T : QuotientTreeComponent F) : Component F :=
  Classical.choose T.nonempty_supp

theorem quotientTreeRoot_mem (T : QuotientTreeComponent F) :
    quotientTreeRoot F T ∈ T.supp :=
  Classical.choose_spec T.nonempty_supp

/-- The root as a vertex of its connected-component graph. -/
noncomputable def quotientTreeRootVertex (T : QuotientTreeComponent F) : T.supp :=
  ⟨quotientTreeRoot F T, quotientTreeRoot_mem F T⟩

/-- A quotient vertex as a vertex of its own connected-component graph. -/
def quotientTreeVertex (C : Component F) : (quotientTreeComponent F C).supp :=
  ⟨C, _root_.SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩

/-- Rooted depth of a bridge-free block inside its quotient-tree component. -/
noncomputable def componentDepth (C : Component F) : ℕ :=
  (quotientForest F).dist
    (quotientTreeRoot F (quotientTreeComponent F C)) C

noncomputable local instance componentFintype : Fintype (Component F) :=
  Fintype.ofFinite _

noncomputable local instance quotientTreeComponentFintype :
    Fintype (QuotientTreeComponent F) :=
  Fintype.ofFinite _

noncomputable local instance hyperedgeComponentFintype :
    Fintype (HyperedgeComponent F) :=
  Fintype.ofFinite _

/-- A lexicographic key: quotient-tree component first, rooted depth second,
and a finite tie-breaker last.  The last coordinate makes the key injective. -/
noncomputable def componentOrderKey (C : HyperedgeComponent F) :
    Fin (Fintype.card (QuotientTreeComponent F)) ×ₗ
      (ℕ ×ₗ Fin (Fintype.card (HyperedgeComponent F))) :=
  toLex
    ((Fintype.equivFin (QuotientTreeComponent F))
        (quotientTreeComponent F C),
      toLex (componentDepth F C,
        (Fintype.equivFin (HyperedgeComponent F)) C))

theorem componentOrderKey_injective :
    Function.Injective (componentOrderKey F) := by
  intro C D hCD
  have hlast := congrArg
    (fun z : Fin (Fintype.card (QuotientTreeComponent F)) ×ₗ
        (ℕ ×ₗ Fin (Fintype.card (HyperedgeComponent F))) =>
      (ofLex (ofLex z).2).2) hCD
  exact (Fintype.equivFin (HyperedgeComponent F)).injective hlast

/-- The linear order used only to enumerate the finite component family. -/
@[reducible] noncomputable def hyperedgeComponentLinearOrder :
    LinearOrder (HyperedgeComponent F) :=
  LinearOrder.lift' (componentOrderKey F) (componentOrderKey_injective F)

/-- All hyperedge-containing components, with deeper components placed first.
Consequently the recursive assembly order (tail before head) is rooted and
nondecreasing in depth inside each quotient-tree component. -/
noncomputable def rootedHyperedgeComponentList : List (HyperedgeComponent F) := by
  letI := hyperedgeComponentLinearOrder F
  exact Finset.univ.sort (fun C D => D ≤ C)

@[simp]
theorem mem_rootedHyperedgeComponentList (C : HyperedgeComponent F) :
    C ∈ rootedHyperedgeComponentList F := by
  classical
  let := hyperedgeComponentLinearOrder F
  simp [rootedHyperedgeComponentList]

theorem rootedHyperedgeComponentList_nodup :
    (rootedHyperedgeComponentList F).Nodup := by
  classical
  let := hyperedgeComponentLinearOrder F
  simp [rootedHyperedgeComponentList]

/-- Earlier recursive pieces have no greater rooted depth than the new head
whenever both blocks belong to the same quotient tree. -/
theorem rootedHyperedgeComponentList_pairwise_depth :
    (rootedHyperedgeComponentList F).Pairwise
      (fun C D : HyperedgeComponent F =>
        quotientTreeComponent F D = quotientTreeComponent F C →
          componentDepth F D ≤ componentDepth F C) := by
  classical
  let := hyperedgeComponentLinearOrder F
  have hsorted :
      (Finset.univ.sort (fun C D : HyperedgeComponent F => D ≤ C)).Pairwise
        (fun C D => D ≤ C) :=
    Finset.pairwise_sort _ _
  rw [rootedHyperedgeComponentList]
  refine hsorted.imp ?_
  intro C D hDC htree
  change componentOrderKey F D ≤ componentOrderKey F C at hDC
  unfold componentOrderKey at hDC
  rw [Prod.Lex.toLex_le_toLex] at hDC
  have hq :
      (Fintype.equivFin (QuotientTreeComponent F))
          (quotientTreeComponent F D) =
        (Fintype.equivFin (QuotientTreeComponent F))
          (quotientTreeComponent F C) :=
    congrArg (Fintype.equivFin (QuotientTreeComponent F)) htree
  rcases hDC with hless | ⟨heq, hrest⟩
  · exact (lt_irrefl _ (hq ▸ hless)).elim
  · rw [Prod.Lex.toLex_le_toLex] at hrest
    rcases hrest with hdepth | ⟨hdepth, _⟩
    · exact hdepth.le
    · exact hdepth.le

/-- Pieces sharing an ambient point lie in the same connected component of
the quotient forest. -/
theorem quotientTreeComponent_eq_of_common_support
    {C D : HyperedgeComponent F} {x : V}
    (hxC : x ∈ F.edgeSupportSet (componentHyperedgeSet F C))
    (hxD : x ∈ F.edgeSupportSet (componentHyperedgeSet F D)) :
    quotientTreeComponent F C = quotientTreeComponent F D := by
  let X : Component F := (core F).connectedComponentMk (Sum.inl x)
  have hC := hyperedgeComponent_mem_closedStar F C hxC
  have hD := hyperedgeComponent_mem_closedStar F D hxD
  have hCX :
      (quotientForest F).connectedComponentMk (C : Component F) =
        (quotientForest F).connectedComponentMk X := by
    rcases hC with hCX | hCX
    · exact congrArg (quotientForest F).connectedComponentMk hCX
    · exact
        _root_.SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hCX
  have hDX :
      (quotientForest F).connectedComponentMk (D : Component F) =
        (quotientForest F).connectedComponentMk X := by
    rcases hD with hDX | hDX
    · exact congrArg (quotientForest F).connectedComponentMk hDX
    · exact
        _root_.SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hDX
  exact hCX.trans hDX.symm

private theorem eq_of_adj_of_dist_add_one_in_forest
    {W : Type*} {G : _root_.SimpleGraph W} (hG : G.IsAcyclic)
    (root : W) {C D X : W}
    (hCX : G.Adj C X) (hDX : G.Adj D X)
    (hrootC : G.Reachable root C) (hrootD : G.Reachable root D)
    (hCdepth : G.dist root C + 1 = G.dist root X)
    (hDdepth : G.dist root D + 1 = G.dist root X) :
    C = D := by
  classical
  obtain ⟨pC, hpC, hpCdist⟩ := hrootC.exists_path_of_dist
  obtain ⟨pD, hpD, hpDdist⟩ := hrootD.exists_path_of_dist
  have hXnotC : X ∉ pC.support := by
    intro hX
    have hdist := G.dist_le (pC.takeUntil X hX)
    have htake := pC.length_takeUntil_le_length hX
    omega
  have hXnotD : X ∉ pD.support := by
    intro hX
    have hdist := G.dist_le (pD.takeUntil X hX)
    have htake := pD.length_takeUntil_le_length hX
    omega
  have hpCX : (pC.concat hCX).IsPath := hpC.concat hXnotC hCX
  have hpDX : (pD.concat hDX).IsPath := hpD.concat hXnotD hDX
  have hpaths : pC.concat hCX = pD.concat hDX := by
    exact Subtype.mk.inj (hG.path_unique ⟨_, hpCX⟩ ⟨_, hpDX⟩)
  have hpenultimate := congrArg (fun p => p.penultimate) hpaths
  simpa using! hpenultimate

/-- Forest version of the rooted closed-star direction lemma.  Connectivity
is required only from the chosen root to the two compared vertices. -/
private theorem closedStar_earlier_direction_in_forest
    {W : Type*} {G : _root_.SimpleGraph W} (hG : G.IsAcyclic)
    (root C D X : W)
    (hCD : C ≠ D)
    (hC : C = X ∨ G.Adj C X)
    (hD : D = X ∨ G.Adj D X)
    (hdepth : G.dist root D ≤ G.dist root C)
    (hrootC : G.Reachable root C) (hrootD : G.Reachable root D) :
    (X = C ∧ G.Adj D C ∧ G.dist root D + 1 = G.dist root C) ∨
      (X ≠ C ∧ G.Adj C X ∧ G.dist root X + 1 = G.dist root C) := by
  rcases hC with (rfl | hCX)
  · left
    have hDC : G.Adj D C := by
      rcases hD with (rfl | hDC)
      · exact (hCD rfl).elim
      · exact hDC
    refine ⟨rfl, hDC, ?_⟩
    rcases hG.dist_eq_dist_add_one_of_adj_of_reachable root hDC hrootD with h | h
    · omega
    · exact h.symm
  · right
    refine ⟨hCX.ne', hCX, ?_⟩
    rcases hG.dist_eq_dist_add_one_of_adj_of_reachable root hCX hrootC with
      hCXup | hXup
    · exact hCXup.symm
    · exfalso
      have hDX : G.Adj D X := by
        rcases hD with (rfl | hDX)
        · omega
        · exact hDX
      rcases hG.dist_eq_dist_add_one_of_adj_of_reachable root hDX hrootD with
        hDup | hXupD
      · omega
      · have hDC : D = C :=
          eq_of_adj_of_dist_add_one_in_forest hG root hDX hCX
            hrootD hrootC hXupD.symm hXup.symm
        exact hCD hDC.symm

/-- The unique parent bridge through which an already assembled, no-deeper
piece can meet a new piece.  `inside` and `outside` orient the original Levi
edge from the new component to its parent, while `edge_eq_incidence` records
the underlying point--hyperedge incidence without orientation. -/
structure ParentBridgeWitness (C : HyperedgeComponent F) (x : V) where
  parent : Component F
  edge : E
  inside : V ⊕ E
  outside : V ⊕ E
  quotientAdj :
    (quotientForest F).Adj parent (C : Component F)
  parentDepth :
    (quotientForest F).dist
        (quotientTreeRoot F (quotientTreeComponent F C)) parent + 1 =
      componentDepth F C
  leviAdj : F.levi.Adj inside outside
  inside_mem : inside ∈ (C : Component F).supp
  outside_mem : outside ∈ parent.supp
  incidence : F.Inc x edge
  edge_eq_incidence : s(inside, outside) = s(Sum.inl x, Sum.inr edge)

/-- A common point between a new block and a distinct no-deeper block
determines an oriented Levi bridge over the parent edge of the new block. -/
theorem parentBridgeWitnessOfCommonPoint_nonempty
    {C D : HyperedgeComponent F} (hCD : C ≠ D) {x : V}
    (hxC : x ∈ F.edgeSupportSet (componentHyperedgeSet F C))
    (hxD : x ∈ F.edgeSupportSet (componentHyperedgeSet F D))
    (hdepth : componentDepth F D ≤ componentDepth F C) :
    Nonempty (ParentBridgeWitness F C x) := by
  let T : QuotientTreeComponent F := quotientTreeComponent F C
  let X : Component F := (core F).connectedComponentMk (Sum.inl x)
  have htreeDC : quotientTreeComponent F D = T :=
    quotientTreeComponent_eq_of_common_support F hxD hxC
  have hCstar := hyperedgeComponent_mem_closedStar F C hxC
  have hDstar := hyperedgeComponent_mem_closedStar F D hxD
  have hCDval : (C : Component F) ≠ (D : Component F) := by
    intro h
    exact hCD (Subtype.ext h)
  have hrootC : (quotientForest F).Reachable
      (quotientTreeRoot F T) (C : Component F) :=
    T.reachable_of_mem_supp (quotientTreeRoot_mem F T)
      _root_.SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hrootD : (quotientForest F).Reachable
      (quotientTreeRoot F T) (D : Component F) :=
    T.reachable_of_mem_supp (quotientTreeRoot_mem F T)
      ((_root_.SimpleGraph.ConnectedComponent.mem_supp_iff T D).mpr htreeDC)
  have hdepth' :
      (quotientForest F).dist (quotientTreeRoot F T) (D : Component F) ≤
        (quotientForest F).dist (quotientTreeRoot F T) (C : Component F) := by
    simpa [componentDepth, T, htreeDC] using! hdepth
  have hAcyclic := Erdos593.SimpleGraph.bridgeQuotient_isAcyclic F.levi
  rcases closedStar_earlier_direction_in_forest hAcyclic
      (quotientTreeRoot F T) (C : Component F) (D : Component F) X
      hCDval hCstar hDstar hdepth' hrootC hrootD with hparent | hparent
  · rcases hparent with ⟨hXC, hDCadj, hDdepth⟩
    rcases hxD with ⟨e, heD, hxe⟩
    refine ⟨
      { parent := D
        edge := e
        inside := Sum.inl x
        outside := Sum.inr e
        quotientAdj := hDCadj
        parentDepth := hDdepth
        leviAdj := F.levi_adj_point_edge.mpr hxe
        inside_mem := ?_
        outside_mem := heD
        incidence := hxe
        edge_eq_incidence := rfl }⟩
    simp [X, hXC]
  · rcases hparent with ⟨_, hCXadj, hXdepth⟩
    rcases hxC with ⟨e, heC, hxe⟩
    refine ⟨
      { parent := X
        edge := e
        inside := Sum.inr e
        outside := Sum.inl x
        quotientAdj := hCXadj.symm
        parentDepth := hXdepth
        leviAdj := (F.levi_adj_point_edge.mpr hxe).symm
        inside_mem := heC
        outside_mem := by
          simp [X]
        incidence := hxe
        edge_eq_incidence := Sym2.eq_swap }⟩

/-- A chosen parent-bridge witness supplied by
`parentBridgeWitnessOfCommonPoint_nonempty`. -/
noncomputable def parentBridgeWitnessOfCommonPoint
    {C D : HyperedgeComponent F} (hCD : C ≠ D) {x : V}
    (hxC : x ∈ F.edgeSupportSet (componentHyperedgeSet F C))
    (hxD : x ∈ F.edgeSupportSet (componentHyperedgeSet F D))
    (hdepth : componentDepth F D ≤ componentDepth F C) :
    ParentBridgeWitness F C x :=
  Classical.choice
    (parentBridgeWitnessOfCommonPoint_nonempty F hCD hxC hxD hdepth)

/-- Two parent-bridge witnesses for the same new component have the same
parent quotient vertex. -/
theorem ParentBridgeWitness.parent_unique
    {C : HyperedgeComponent F} {x y : V}
    (hx : ParentBridgeWitness F C x)
    (hy : ParentBridgeWitness F C y) :
    hx.parent = hy.parent := by
  let T := quotientTreeComponent F C
  have hrootC : (quotientForest F).Reachable
      (quotientTreeRoot F T) (C : Component F) :=
    T.reachable_of_mem_supp (quotientTreeRoot_mem F T)
      _root_.SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hrootX : (quotientForest F).Reachable
      (quotientTreeRoot F T) hx.parent :=
    hrootC.trans hx.quotientAdj.symm.reachable
  have hrootY : (quotientForest F).Reachable
      (quotientTreeRoot F T) hy.parent :=
    hrootC.trans hy.quotientAdj.symm.reachable
  apply eq_of_adj_of_dist_add_one_in_forest
    (Erdos593.SimpleGraph.bridgeQuotient_isAcyclic F.levi)
    (quotientTreeRoot F T) hx.quotientAdj hy.quotientAdj hrootX hrootY
  · simpa [componentDepth, T] using! hx.parentDepth
  · simpa [componentDepth, T] using! hy.parentDepth

/-- The parent bridge has only one point endpoint, so two earlier pieces can
meet a new block only at the same ambient point. -/
theorem eq_of_common_support_of_depth_le
    {C D A : HyperedgeComponent F}
    (hCD : C ≠ D) (hCA : C ≠ A) {x y : V}
    (hxC : x ∈ F.edgeSupportSet (componentHyperedgeSet F C))
    (hxD : x ∈ F.edgeSupportSet (componentHyperedgeSet F D))
    (hyC : y ∈ F.edgeSupportSet (componentHyperedgeSet F C))
    (hyA : y ∈ F.edgeSupportSet (componentHyperedgeSet F A))
    (hdepthD : componentDepth F D ≤ componentDepth F C)
    (hdepthA : componentDepth F A ≤ componentDepth F C) :
    x = y := by
  let wx := parentBridgeWitnessOfCommonPoint F hCD hxC hxD hdepthD
  let wy := parentBridgeWitnessOfCommonPoint F hCA hyC hyA hdepthA
  have hparent : wx.parent = wy.parent :=
    ParentBridgeWitness.parent_unique F wx wy
  have hCparent : (C : Component F) ≠ wx.parent := by
    intro h
    apply wx.quotientAdj.ne
    exact h.symm
  have hedge : s(wy.inside, wy.outside) = s(wx.inside, wx.outside) := by
    apply Erdos593.SimpleGraph.bridgeQuotient_originalEdge_unique F.levi hCparent
      wx.leviAdj wx.inside_mem wx.outside_mem wy.leviAdj wy.inside_mem
    simpa [hparent] using! wy.outside_mem
  have hincidence :
      s(Sum.inl y, Sum.inr wy.edge) = s(Sum.inl x, Sum.inr wx.edge) :=
    wy.edge_eq_incidence.symm.trans (hedge.trans wx.edge_eq_incidence)
  rcases Sym2.eq_iff.mp hincidence with h | h
  · exact Sum.inl.inj h.1 |>.symm
  · exact (Sum.inl_ne_inr h.1).elim

/-- The exact edge set attached to a hyperedge-containing component, with a
domain-specific wrapper that prevents accidental coercion of component lists
to lists of their underlying bridge-free components. -/
def componentPieceEdgeSet (C : HyperedgeComponent F) : Set E :=
  componentHyperedgeSet F (C : Component F)

/-- The edge sets of the rooted hyperedge-component list. -/
noncomputable def rootedComponentPieceList : List (Set E) :=
  (rootedHyperedgeComponentList F).map (componentPieceEdgeSet F)

/-- Membership in the exact union of the edge sets attached to a component
list. -/
theorem mem_edgePieceUnion_componentList
    (components : List (HyperedgeComponent F)) {e : E} :
    e ∈ edgePieceUnion
        (components.map (componentPieceEdgeSet F)) ↔
      ∃ C : HyperedgeComponent F,
        C ∈ components ∧ e ∈ componentPieceEdgeSet F C := by
  induction components with
  | nil => simp [edgePieceUnion]
  | cons C components ih =>
      change
        (e ∈ edgePieceUnion
            (components.map (componentPieceEdgeSet F)) ∨
          e ∈ componentPieceEdgeSet F C) ↔ _
      rw [ih]
      constructor
      · rintro (⟨D, hD, heD⟩ | heC)
        · exact ⟨D, List.mem_cons.mpr (Or.inr hD), heD⟩
        · exact ⟨C, List.mem_cons.mpr (Or.inl rfl), heC⟩
      · rintro ⟨D, hD, heD⟩
        rcases List.mem_cons.mp hD with rfl | hD
        · exact Or.inr heD
        · exact Or.inl ⟨D, hD, heD⟩

/-- The total exact edge union of the rooted component pieces is all `E`. -/
theorem edgePieceUnion_rootedComponentPieceList :
    edgePieceUnion (rootedComponentPieceList F) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro e
  rw [rootedComponentPieceList,
    mem_edgePieceUnion_componentList]
  exact ⟨hyperedgeComponentOf F e,
    mem_rootedHyperedgeComponentList F _,
    mem_hyperedgeComponentOf_set F e⟩

/-- The geometric portion of `RunningEdgeAssembly`: exact recursive
edge-disjointness and empty-or-singleton support overlap, without yet asking
that the individual restrictions be constructible. -/
def RunningEdgeAssemblyGeometry (pieces : List (Set E)) : Prop :=
  match pieces with
  | [] => True
  | S :: pieces =>
      RunningEdgeAssemblyGeometry pieces ∧
      Disjoint (edgePieceUnion pieces) S ∧
      (Disjoint
          (F.edgeSupportSet (edgePieceUnion pieces))
          (F.edgeSupportSet S) ∨
        ∃ r : V,
          F.edgeSupportSet (edgePieceUnion pieces) ∩
            F.edgeSupportSet S = {r})

/-- Any noduplicated component list in parent-after-child order has the exact
edge-disjointness and running-intersection geometry. -/
theorem componentList_runningEdgeAssemblyGeometry
    (components : List (HyperedgeComponent F))
    (hnodup : components.Nodup)
    (hdepth : components.Pairwise
      (fun C D : HyperedgeComponent F =>
        quotientTreeComponent F D = quotientTreeComponent F C →
          componentDepth F D ≤ componentDepth F C)) :
    RunningEdgeAssemblyGeometry F
      (components.map (componentPieceEdgeSet F)) := by
  induction components with
  | nil => trivial
  | cons C components ih =>
      rw [List.nodup_cons] at hnodup
      rw [List.pairwise_cons] at hdepth
      refine ⟨ih hnodup.2 hdepth.2, ?_, ?_⟩
      · rw [Set.disjoint_left]
        intro e hePrevious heC
        rcases (mem_edgePieceUnion_componentList F components).mp hePrevious with
          ⟨D, hD, heD⟩
        have hDC : D ≠ C := by
          intro h
          apply hnodup.1
          exact h ▸ hD
        exact (Set.disjoint_left.mp
          (componentHyperedgeSet_disjoint F hDC)) heD heC
      · by_cases hdisjoint : Disjoint
            (F.edgeSupportSet
              (edgePieceUnion (components.map (componentPieceEdgeSet F))))
            (F.edgeSupportSet (componentPieceEdgeSet F C))
        · exact Or.inl hdisjoint
        · right
          rcases Set.not_disjoint_iff.mp hdisjoint with
            ⟨r, hrPrevious, hrC⟩
          refine ⟨r, Set.Subset.antisymm ?_ ?_⟩
          · intro x hx
            rcases hx.1 with ⟨e, hePrevious, hxe⟩
            rcases (mem_edgePieceUnion_componentList F components).mp
                hePrevious with ⟨D, hD, heD⟩
            have hxD :
                x ∈ F.edgeSupportSet (componentPieceEdgeSet F D) :=
              ⟨e, heD, hxe⟩
            rcases hrPrevious with ⟨f, hfPrevious, hrf⟩
            rcases (mem_edgePieceUnion_componentList F components).mp
                hfPrevious with ⟨A, hA, hfA⟩
            have hrA :
                r ∈ F.edgeSupportSet (componentPieceEdgeSet F A) :=
              ⟨f, hfA, hrf⟩
            have hCD : C ≠ D := by
              intro h
              apply hnodup.1
              exact h.symm ▸ hD
            have hCA : C ≠ A := by
              intro h
              apply hnodup.1
              exact h.symm ▸ hA
            have hdepthD : componentDepth F D ≤ componentDepth F C :=
              hdepth.1 D hD
                (quotientTreeComponent_eq_of_common_support F hxD hx.2)
            have hdepthA : componentDepth F A ≤ componentDepth F C :=
              hdepth.1 A hA
                (quotientTreeComponent_eq_of_common_support F hrA hrC)
            have hxr : x = r :=
              eq_of_common_support_of_depth_le F hCD hCA
                hx.2 hxD hrC hrA hdepthD hdepthA
            simp [hxr]
          · intro x hx
            have hxr : x = r := Set.mem_singleton_iff.mp hx
            simpa [hxr] using! And.intro hrPrevious hrC

/-- The canonical rooted piece list has the exact geometric hypotheses of a
running edge assembly. -/
theorem rootedComponentPieceList_runningEdgeAssemblyGeometry :
    RunningEdgeAssemblyGeometry F (rootedComponentPieceList F) := by
  apply componentList_runningEdgeAssemblyGeometry F
  · exact rootedHyperedgeComponentList_nodup F
  · exact rootedHyperedgeComponentList_pairwise_depth F

/-- Geometry plus constructibility of every listed exact restriction gives
the literal `RunningEdgeAssembly` predicate used by reconstruction.  The
current reconstruction API places vertices and edges in one universe, so this
interface follows that convention. -/
theorem RunningEdgeAssemblyGeometry.toRunningEdgeAssembly
    {X I : Type w} (K : TripleSystem X I)
    (pieces : List (Set I))
    (hgeometry : RunningEdgeAssemblyGeometry K pieces)
    (hconstructible : ∀ S ∈ pieces,
      Constructible (K.edgeRestriction S)) :
    K.RunningEdgeAssembly pieces := by
  induction pieces with
  | nil => trivial
  | cons S pieces ih =>
      rcases hgeometry with ⟨hprevious, hEdges, hSupports⟩
      refine ⟨ih hprevious ?_, hconstructible S (by simp), hEdges, hSupports⟩
      intro T hT
      exact hconstructible T (by simp [hT])

/-- Once every exact component restriction is supplied as constructible, the
canonical rooted list is a full `RunningEdgeAssembly`.  This is the interface
used to combine the active-block and degree-zero-block packaging theorems. -/
theorem rootedComponentPieceList_runningEdgeAssembly
    {X I : Type w} (K : TripleSystem X I)
    [Fintype X] [Fintype I] [DecidableEq X] [DecidableEq I]
    [DecidableRel K.levi.Adj]
    (hconstructible : ∀ C : HyperedgeComponent K,
      Constructible
        (K.edgeRestriction (componentPieceEdgeSet K C))) :
    K.RunningEdgeAssembly (rootedComponentPieceList K) := by
  apply (rootedComponentPieceList_runningEdgeAssemblyGeometry K).toRunningEdgeAssembly K
  intro S hS
  rw [rootedComponentPieceList, List.mem_map] at hS
  rcases hS with ⟨C, _, rfl⟩
  exact hconstructible C

/-- Every hyperedge-containing bridge-free component gives a constructible
exact restriction: degree zero is the singleton-edge case, while degree two
supplies a genuine active component. -/
theorem hyperedgeComponentRestriction_constructible
    {X I : Type w} (K : TripleSystem X I)
    [Fintype X] [Fintype I] [DecidableEq X] [DecidableEq I]
    [DecidableRel K.levi.Adj]
    (hlinear : K.Linear) (hbridge : K.BridgeAtEveryEdge)
    (hberge : K.EvenBergeCycles) (C : HyperedgeComponent K) :
    Constructible (K.edgeRestriction (componentPieceEdgeSet K C)) := by
  rcases C.2 with ⟨e, heC⟩
  change Sum.inr e ∈ (C : Component K).supp at heC
  rcases K.levi_bridgeFree_edge_degree_eq_zero_or_two hbridge e with
    hzero | htwo
  · change Constructible
      (K.edgeRestriction (componentHyperedgeSet K (C : Component K)))
    exact degreeZeroComponentRestriction_constructible K heC hzero
  · have hpositive : 0 <
        (Erdos593.SimpleGraph.bridgeFree K.levi).degree (Sum.inr e) := by
      omega
    rcases ((Erdos593.SimpleGraph.bridgeFree K.levi).degree_pos_iff_exists_adj
        (Sum.inr e)).mp hpositive with ⟨z, hez⟩
    have hC : HasIncidence K C := by
      rcases z with x | f
      · refine ⟨x, e, ?_, heC, hez.symm⟩
        exact (C : Component K).mem_supp_of_adj_mem_supp heC hez
      · have hle : Erdos593.SimpleGraph.bridgeFree K.levi ≤ K.levi := by
          dsimp only [Erdos593.SimpleGraph.bridgeFree]
          exact K.levi.deleteEdges_le _
        exact (K.not_levi_adj_edge_edge (hle hez)).elim
    change Constructible
      (K.edgeRestriction (componentHyperedgeSet K (C : Component K)))
    exact activeComponentRestriction_constructible K
      hlinear hbridge hberge hC

/-- The intrinsic finite hypotheses make the canonical component ordering a
full running edge assembly. -/
theorem intrinsic_rootedComponentPieceList_runningEdgeAssembly
    {X I : Type w} (K : TripleSystem X I)
    [Fintype X] [Fintype I] [DecidableEq X] [DecidableEq I]
    [DecidableRel K.levi.Adj]
    (hlinear : K.Linear) (hbridge : K.BridgeAtEveryEdge)
    (hberge : K.EvenBergeCycles) :
    K.RunningEdgeAssembly (rootedComponentPieceList K) := by
  exact rootedComponentPieceList_runningEdgeAssembly K
    (hyperedgeComponentRestriction_constructible K hlinear hbridge hberge)

/-- Exact finite reverse structural theorem after isolated vertices are
removed: the intrinsic Levi conditions reconstruct the original system from
the rooted bridge-block running assembly. -/
theorem constructible_of_intrinsic_of_hasNoIsolatedPoints
    {X I : Type w} (K : TripleSystem X I)
    [Fintype X] [Fintype I] [DecidableEq X] [DecidableEq I]
    [DecidableRel K.levi.Adj]
    (hintrinsic : K.Intrinsic) (hnoisolated : K.HasNoIsolatedPoints) :
    Constructible K := by
  rcases hintrinsic with ⟨hlinear, hbridge, hberge⟩
  have hrunning : K.RunningEdgeAssembly (rootedComponentPieceList K) :=
    intrinsic_rootedComponentPieceList_runningEdgeAssembly K
      hlinear hbridge hberge
  have hrestriction : Constructible
      (K.edgeRestriction (edgePieceUnion (rootedComponentPieceList K))) :=
    K.runningEdgeAssembly_constructible (rootedComponentPieceList K) hrunning
  rw [edgePieceUnion_rootedComponentPieceList K] at hrestriction
  exact Constructible.ofIso hrestriction
    (K.edgeRestrictionUnivIso hnoisolated)

/-- Finite structural classification on systems with no isolated points. -/
theorem constructible_iff_intrinsic_of_hasNoIsolatedPoints
    {X I : Type w} (K : TripleSystem X I)
    [Fintype X] [Fintype I] [DecidableEq X] [DecidableEq I]
    [DecidableRel K.levi.Adj]
    (hnoisolated : K.HasNoIsolatedPoints) :
    Constructible K ↔ K.Intrinsic := by
  constructor
  · exact Constructible.intrinsic
  · intro hintrinsic
    exact constructible_of_intrinsic_of_hasNoIsolatedPoints K
      hintrinsic hnoisolated

/-- Clean isolated-reduction form of the finite structural classification. -/
theorem isolatedReduction_constructible_iff_intrinsic
    {X I : Type w} (K : TripleSystem X I)
    [Fintype X] [Fintype I] [DecidableEq X] [DecidableEq I] :
    Constructible K.isolatedReduction ↔ K.isolatedReduction.Intrinsic := by
  classical
  let : Fintype K.NonIsolatedPoint := Fintype.ofFinite _
  let : DecidableRel K.isolatedReduction.levi.Adj := Classical.decRel _
  exact constructible_iff_intrinsic_of_hasNoIsolatedPoints
    K.isolatedReduction K.isolatedReduction_hasNoIsolatedPoints

end
end BridgeBlock
end TripleSystem
end Erdos593
