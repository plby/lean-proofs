/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCutConstruction
import ErdosProblems.Erdos599.HalfwayInsideFragmentUnion

/-!
# The canonical inside family of a selected Section 9 cut

The literal outside fragments retain the edges of a row which do not have
both endpoints in the closing set `X`.  This file constructs the complementary
inside family from the edges with both endpoints in `X`.

The carrier also retains every root and sink of the outside cut.  These
vertices are important even when they are isolated in the inside relation:
they are precisely the endpoints to which the projected simultaneous
assignment is attached.  The resulting incidence statements are the local
part of Assertion 9.31 and require no separately assumed splice geometry.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating
open Alternating.RelationDecomposition

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa theta : Cardinal.{u}}

/-- Edges of the provisional row which remain wholly inside the selected
closing set. -/
def insideFamilyEdges (W : Set Gamma.DPath) (X : Set V) : Set (V × V) :=
  familyEdges W ∩ (X ×ˢ X)

/-- The carrier of the inside family.  In addition to vertices incident with
inside edges, it retains every outside-cut root and sink.  The latter become
the attachment points of the simultaneous assignment. -/
def insideCutCarrier (Y W : Set Gamma.DPath) (X : Set V) : Set V :=
  (Gamma.vertexSet W ∩ X) ∪
    (CutSplit.initialVertices (outsideCarrier W X)
      (outsideFamilyEdges W X) X \ Gamma.initialSet Y) ∪
    (CutSplit.terminalVertices (outsideCarrier W X)
      (outsideFamilyEdges W X) X \ Gamma.vertexSet Y)

theorem outsideCarrier_subset_vertexSet (W : Set Gamma.DPath) (X : Set V) :
    outsideCarrier W X ⊆ Gamma.vertexSet W := by
  intro x hx
  rcases hx with hx | hx
  · exact hx.1
  · obtain ⟨y, hxy | hyx⟩ := hx
    · exact (familyEdges_subset_vertexSet_prod W
        (outsideFamilyEdges_subset W X hxy)).1
    · exact (familyEdges_subset_vertexSet_prod W
        (outsideFamilyEdges_subset W X hyx)).2

theorem cutInitial_subset_vertexSet (W : Set Gamma.DPath) (X : Set V) :
    CutSplit.initialVertices (outsideCarrier W X)
      (outsideFamilyEdges W X) X ⊆ Gamma.vertexSet W := by
  intro x hx
  rcases hx with hx | hx
  · obtain ⟨_hxX, y, hxy⟩ := hx
    exact (familyEdges_subset_vertexSet_prod W
      (outsideFamilyEdges_subset W X hxy)).1
  · exact outsideCarrier_subset_vertexSet W X hx.1

theorem cutTerminal_subset_vertexSet (W : Set Gamma.DPath) (X : Set V) :
    CutSplit.terminalVertices (outsideCarrier W X)
      (outsideFamilyEdges W X) X ⊆ Gamma.vertexSet W := by
  intro x hx
  rcases hx with hx | hx
  · obtain ⟨_hxX, y, hyx⟩ := hx
    exact (familyEdges_subset_vertexSet_prod W
      (outsideFamilyEdges_subset W X hyx)).2
  · exact outsideCarrier_subset_vertexSet W X hx.1

theorem insideCutCarrier_subset_vertexSet (Y W : Set Gamma.DPath) (X : Set V) :
    insideCutCarrier Y W X ⊆ Gamma.vertexSet W := by
  intro x hx
  rcases hx with (hx | hx) | hx
  · exact hx.1
  · exact cutInitial_subset_vertexSet W X hx.1
  · exact cutTerminal_subset_vertexSet W X hx.1

theorem insideFamilyEdges_endpoints (W : Set Gamma.DPath) (X : Set V)
    {e : V × V} (he : e ∈ insideFamilyEdges W X) :
    e.1 ∈ insideCutCarrier Y W X ∧ e.2 ∈ insideCutCarrier Y W X := by
  exact ⟨Or.inl (Or.inl
      ⟨(familyEdges_subset_vertexSet_prod W he.1).1, he.2.1⟩),
    Or.inl (Or.inl
      ⟨(familyEdges_subset_vertexSet_prod W he.1).2, he.2.2⟩)⟩

theorem insideFamilyEdges_in_graph (W : Set Gamma.DPath) (X : Set V) :
    insideFamilyEdges W X ⊆ {e | Gamma.graph.Adj e.1 e.2} := by
  intro e he
  exact familyEdges_subset_adj W he.1

/-- The internal-edge relation, with all cut attachment vertices retained,
has an exact blueprint realization. -/
structure CanonicalInsideCut
    (W : Set Gamma.DPath) (X : Set V) where
  insideFamily : LinkageBlueprint Gamma Y kappa
  edgeSet_eq : insideFamily.edgeSet = insideFamilyEdges W X
  vertexSet_eq : insideFamily.vertexSet = insideCutCarrier Y W X

theorem exists_canonicalInsideCut (W : Set Gamma.DPath) (X : Set V)
    (hW : Gamma.IsWarp W) : Nonempty (CanonicalInsideCut (Y := Y)
      (kappa := kappa) W X) := by
  let E : Set (V × V) := insideFamilyEdges W X
  let C : Set V := insideCutCarrier Y W X
  have hgraph : E ⊆
      {e | (imaginaryGraph Gamma Y kappa).Adj e.1 e.2} := by
    intro e he
    exact original_adj_imaginaryGraph
      (insideFamilyEdges_in_graph W X he)
  have hendpoints : ∀ e ∈ E, e.1 ∈ C ∧ e.2 ∈ C := by
    intro e he
    exact insideFamilyEdges_endpoints W X he
  have hunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ E) := by
    constructor
    · intro x y z hxz hyz
      exact (Alternating.IsWarp.familyEdges_leftUnique hW) hxz.1 hyz.1
    · intro x y z hxy hxz
      exact (Alternating.IsWarp.familyEdges_rightUnique hW) hxy.1 hxz.1
  have hcycle : ¬ ContainsDirectedCycle E := by
    rintro ⟨K, hK⟩
    exact PathFilterComponents.DWeb.IsWarp.familyEdges_not_containsDirectedCycle
      hW ⟨K, hK.trans (fun _ he ↦ he.1)⟩
  have hreverse : ¬ ContainsReverseDirectedRay E := by
    rintro ⟨R, hR⟩
    exact PathFilterComponents.DWeb.IsWarp.familyEdges_not_containsReverseDirectedRay
      hW ⟨R, fun n ↦ (hR n).1⟩
  obtain ⟨F, hFE, hFC⟩ := exists_blueprint_realizing_relation_exact
    (Γ := Gamma) (Y := Y) (κ := kappa) E C hgraph hendpoints hunique
      hcycle hreverse
  exact ⟨⟨F, hFE, hFC⟩⟩

/-- A fixed canonical realization of the inside relation.  This is only a
choice of the path decomposition whose existence was proved above; its edge
relation and carrier are still definitionally certified by the two fields of
`CanonicalInsideCut`. -/
noncomputable def canonicalInsideCutOfWarp (W : Set Gamma.DPath) (X : Set V)
    (hW : Gamma.IsWarp W) :
    CanonicalInsideCut (Y := Y) (kappa := kappa) W X :=
  Classical.choice (exists_canonicalInsideCut (Y := Y) (kappa := kappa)
    W X hW)

/-- The blueprint selected by `canonicalInsideCutOfWarp`. -/
noncomputable abbrev insideCutFamilyOfWarp (W : Set Gamma.DPath) (X : Set V)
    (hW : Gamma.IsWarp W) : LinkageBlueprint Gamma Y kappa :=
  (canonicalInsideCutOfWarp (Y := Y) (kappa := kappa) W X hW).insideFamily

/-- The inside carrier is contained in the closing set together with the
earlier-stage set.  This is the cardinality bridge used at a club stage: the
only carrier vertices outside `X` are uncovered cut endpoints, and the cut
boundary places all of those endpoints in `before`. -/
theorem insideCutCarrier_subset_closure_union_before
    {before innerRoof outerRoof : Set V}
    (D : OutsideCutConstruction (Y := Y) W X before innerRoof outerRoof) :
    insideCutCarrier Y W X ⊆ X ∪ before := by
  intro x hx
  rcases hx with (hx | hx) | hx
  · exact Or.inl hx.2
  · exact Or.inr (D.boundary.source_location hx).1
  · exact Or.inr (D.boundary.terminal_location hx).1

/-- The paths of any blueprint inject into its carrier by their initial
vertices.  Warp disjointness is the only input: two members with the same
initial vertex have intersecting supports and hence are equal. -/
theorem mk_paths_le_mk_vertexSet_by_initial
    (U : LinkageBlueprint Gamma Y kappa) :
    #U.paths ≤ #U.vertexSet := by
  let f : U.paths → U.vertexSet := fun p ↦
    ⟨p.1.initial, ⟨p.1, p.2, p.1.initial_mem_support⟩⟩
  apply Cardinal.mk_le_of_injective (f := f)
  intro p q hpq
  apply Subtype.ext
  apply Alternating.DWeb.IsWarp.eq_of_mem_support U.isWarp
    p.2 q.2 p.1.initial_mem_support
  have hinitial : p.1.initial = q.1.initial :=
    congrArg Subtype.val hpq
  exact hinitial.symm ▸ q.1.initial_mem_support

/-- Every blueprint edge has both endpoints in its vertex set. -/
theorem edgeSet_endpoints_mem_vertexSet
    (U : LinkageBlueprint Gamma Y kappa) {e : V × V}
    (he : e ∈ U.edgeSet) :
    e.1 ∈ U.vertexSet ∧ e.2 ∈ U.vertexSet := by
  simp only [edgeSet, Set.mem_iUnion] at he
  obtain ⟨p, hp, he⟩ := he
  have hend := p.edgeSet_subset_support_prod he
  exact ⟨⟨p, hp, hend.1⟩, ⟨p, hp, hend.2⟩⟩

/-- A vertex of a path family with no outgoing family edge is a finite
terminal of that family. -/
theorem mem_terminalFrontier_of_no_outgoing_familyEdges
    (W : Set Gamma.DPath) {x : V} (hx : x ∈ Gamma.vertexSet W)
    (hno : ¬ ∃ y, (x, y) ∈ familyEdges W) :
    x ∈ Gamma.terminalFrontier W := by
  obtain ⟨p, hpW, hxp⟩ := hx
  rcases p with p | r
  · have hfinish : x = p.finish := by
      by_contra hne
      obtain ⟨y, hxy⟩ :=
        Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
          p hxp hne
      exact hno ⟨y, Set.mem_iUnion.2 ⟨Sum.inl p,
        Set.mem_iUnion.2 ⟨hpW, hxy⟩⟩⟩
    refine ⟨Sum.inl p, hpW, ?_⟩
    simp [DWeb.terminal?, DirectedPath.Path.terminal?, hfinish]
  · obtain ⟨n, hn⟩ := hxp
    apply False.elim
    apply hno
    refine ⟨r (n + 1), Set.mem_iUnion.2 ⟨Sum.inr r,
      Set.mem_iUnion.2 ⟨hpW, ?_⟩⟩⟩
    exact ⟨n, congrArg (fun z ↦ (z, r (n + 1))) hn.symm⟩

/-- The canonical inside path family has size at most `kappa` whenever the
closing set and the earlier-stage set do. -/
theorem CanonicalInsideCut.card_paths_of_cut
    {before innerRoof outerRoof : Set V}
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (D : OutsideCutConstruction (Y := Y) W X before innerRoof outerRoof)
    (hkappa : aleph0 ≤ kappa) (hX : #X ≤ kappa)
    (hbefore : #before ≤ kappa) :
    #I.insideFamily.paths ≤ kappa := by
  refine (mk_paths_le_mk_vertexSet_by_initial I.insideFamily).trans ?_
  rw [I.vertexSet_eq]
  refine (Cardinal.mk_subtype_mono
    (insideCutCarrier_subset_closure_union_before D)).trans ?_
  exact (Cardinal.mk_union_le X before).trans
    (Cardinal.add_le_of_le hkappa hX hbefore)

namespace CanonicalInsideCut

variable {W : Set Gamma.DPath} {X : Set V}

theorem uncoveredCutInitial_subset_terminalSet
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (hW : Gamma.IsWarp W) :
    CutSplit.initialVertices (outsideCarrier W X)
        (outsideFamilyEdges W X) X \ Gamma.initialSet Y ⊆
      I.insideFamily.terminalSet := by
  intro x hx
  rw [I.insideFamily.terminalSet_eq_no_outgoing, I.vertexSet_eq]
  refine ⟨Or.inl (Or.inr hx), ?_⟩
  rintro ⟨y, hxy⟩
  rw [I.edgeSet_eq] at hxy
  rcases hx.1 with hxCut | hxOutside
  · obtain ⟨_hxX, z, hxz⟩ := hxCut
    have hyz : y = z :=
      (Alternating.IsWarp.familyEdges_rightUnique hW) hxy.1 hxz.1
    subst z
    exact hxz.2 ⟨_hxX, hxy.2.2⟩
  · exact hxOutside.2.1 hxy.2.1

theorem uncoveredCutTerminal_subset_initialSet
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (hW : Gamma.IsWarp W) :
    CutSplit.terminalVertices (outsideCarrier W X)
        (outsideFamilyEdges W X) X \ Gamma.vertexSet Y ⊆
      I.insideFamily.initialSet := by
  intro x hx
  rw [I.insideFamily.initialSet_eq_no_incoming, I.vertexSet_eq]
  refine ⟨Or.inr hx, ?_⟩
  rintro ⟨y, hyx⟩
  rw [I.edgeSet_eq] at hyx
  rcases hx.1 with hxCut | hxOutside
  · obtain ⟨_hxX, z, hzx⟩ := hxCut
    have hyz : y = z :=
      (Alternating.IsWarp.familyEdges_leftUnique hW) hyx.1 hzx.1
    subst z
    exact hzx.2 ⟨hyx.2.1, _hxX⟩
  · exact hxOutside.2.1 hyx.2.2

variable {F : OutsideFracturedWarp W X}
variable {A : SimultaneousAssignment F.holes.paths Y}

/-- Every source of the projected cut assignment is an actual terminal of
the complementary inside family. -/
theorem assignmentSource_mem_terminalSet
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (hW : Gamma.IsWarp W)
    (s : {z // z ∈ Gamma.initialSet F.holes.paths \ Gamma.initialSet Y}) :
    s.1 ∈ I.insideFamily.terminalSet := by
  apply I.uncoveredCutInitial_subset_terminalSet hW
  rw [← F.initialSet_eq]
  exact s.property

/-- Every finite target of the projected cut assignment is an actual initial
of the complementary inside family. -/
theorem finiteAssignmentTarget_mem_initialSet
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (hW : Gamma.IsWarp W)
    (s : {z // z ∈ Gamma.initialSet F.holes.paths \ Gamma.initialSet Y})
    {v : V} (hv : (A.assigned s).terminal? = some v) :
    v ∈ I.insideFamily.initialSet := by
  apply I.uncoveredCutTerminal_subset_initialSet hW
  rw [← F.terminalFrontier_eq]
  exact A.finite_terminal_mem s hv

/-- Sources assigned to infinity are terminals of the inside family. -/
theorem assignedInfiniteSources_subset_terminalSet
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (hW : Gamma.IsWarp W) :
    assignedInfiniteSources A ⊆ I.insideFamily.terminalSet := by
  rintro x ⟨s, rfl, _hinfinite⟩
  exact I.assignmentSource_mem_terminalSet hW s

theorem assignedEndpoints_mem_vertexSet
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (hW : Gamma.IsWarp W) {e : V × V}
    (he : e ∈ assignedFiniteEdges A) :
    e.1 ∈ I.insideFamily.vertexSet ∧
      e.2 ∈ I.insideFamily.vertexSet := by
  obtain ⟨s, hterm, hs⟩ := he
  have hsource := I.assignmentSource_mem_terminalSet hW s
  have htarget := I.finiteAssignmentTarget_mem_initialSet hW s hterm
  rw [I.insideFamily.terminalSet_eq_no_outgoing] at hsource
  rw [I.insideFamily.initialSet_eq_no_incoming] at htarget
  exact ⟨hs ▸ hsource.1, htarget.1⟩

theorem insideAssigned_cross_in
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (hW : Gamma.IsWarp W) {x y z : V}
    (hxz : (x, z) ∈ I.insideFamily.edgeSet)
    (hyz : (y, z) ∈ assignedFiniteEdges A) : x = y := by
  obtain ⟨s, hterm, _hsy⟩ := hyz
  exact False.elim <| I.insideFamily.no_incoming_of_mem_initialSet
    (I.finiteAssignmentTarget_mem_initialSet hW s hterm) ⟨x, hxz⟩

theorem insideAssigned_cross_out
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (hW : Gamma.IsWarp W) {x y z : V}
    (hxy : (x, y) ∈ I.insideFamily.edgeSet)
    (hxz : (x, z) ∈ assignedFiniteEdges A) : y = z := by
  obtain ⟨s, _hterm, hsx⟩ := hxz
  exact False.elim <| I.insideFamily.no_outgoing_of_mem_terminalSet
    (by simpa [hsx] using I.assignmentSource_mem_terminalSet hW s) ⟨y, hxy⟩

theorem fullRelation_biUnique
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (hW : Gamma.IsWarp W) :
    Relator.BiUnique (fun x y ↦
      (x, y) ∈ I.insideFamily.edgeSet ∪ assignedFiniteEdges A) := by
  exact biUnique_union_of_cross
    (by
      change Relator.BiUnique (fun x y ↦
        (x, y) ∈ familyEdges (Γ := imaginaryWeb Gamma Y kappa)
          I.insideFamily.paths)
      exact Alternating.IsWarp.familyEdges_biUnique
        (Γ := imaginaryWeb Gamma Y kappa) I.insideFamily.isWarp)
    (assignedFiniteEdges_biUnique A)
    (I.insideAssigned_cross_in hW)
    (I.insideAssigned_cross_out hW)

/-- Every terminal of the complementary inside family has one of the two
expected origins: it is a root of a literal outside fragment, or it was
already a finite terminal of the provisional row. -/
theorem terminalSet_subset_cutInitial_union_terminalFrontier
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X) :
    I.insideFamily.terminalSet ⊆
      CutSplit.initialVertices (outsideCarrier W X)
          (outsideFamilyEdges W X) X ∪
        Gamma.terminalFrontier W := by
  intro x hx
  have hx' := hx
  rw [I.insideFamily.terminalSet_eq_no_outgoing, I.vertexSet_eq] at hx'
  obtain ⟨hxcarrier, hnoInside⟩ := hx'
  by_cases hout : ∃ y, (x, y) ∈ familyEdges W
  · obtain ⟨y, hxy⟩ := hout
    apply Or.inl
    rcases hxcarrier with (hxbase | hxinitial) | hxterminal
    · by_cases hyX : y ∈ X
      · exact False.elim <| hnoInside ⟨y, by
          rw [I.edgeSet_eq]
          exact ⟨hxy, ⟨hxbase.2, hyX⟩⟩⟩
      · exact Or.inl ⟨hxbase.2, y, hxy, by
          rintro ⟨_hxX, hyX'⟩
          exact hyX hyX'⟩
    · exact hxinitial.1
    · rcases hxterminal.1 with hxcut | hxoutside
      · by_cases hyX : y ∈ X
        · exact False.elim <| hnoInside ⟨y, by
            rw [I.edgeSet_eq]
            exact ⟨hxy, ⟨hxcut.1, hyX⟩⟩⟩
        · exact Or.inl ⟨hxcut.1, y, hxy, by
            rintro ⟨_hxX, hyX'⟩
            exact hyX hyX'⟩
      · apply False.elim
        apply hxoutside.2.2
        refine ⟨y, hxy, ?_⟩
        rintro ⟨hxX, _hyX⟩
        exact hxoutside.2.1 hxX
  · apply Or.inr
    apply mem_terminalFrontier_of_no_outgoing_familyEdges W
    · exact insideCutCarrier_subset_vertexSet Y W X hxcarrier
    · exact hout

/-- Concrete terminal boundary obtained from the two row/cut boundary
inclusions.  In particular the assignment domain is not postulated: it is
identified with the uncovered literal cut initials by `initialSet_eq`. -/
theorem terminalBoundary_of_cut
    {C : ClubStageGeometry Gamma Y kappa theta}
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (D : OutsideCutConstruction (Y := Y) W X
      C.before C.innerRoof C.outerRoof)
    (reference_cut_initials :
      CutSplit.initialVertices (outsideCarrier W X)
          (outsideFamilyEdges W X) X ∩ Gamma.initialSet Y ⊆ C.newSlice)
    (row_terminals : Gamma.terminalFrontier W ⊆ C.newSlice) :
    I.insideFamily.terminalSet ⊆
      {x | ∃ s : {z // z ∈
        Gamma.initialSet D.fractured.paths \ Gamma.initialSet Y}, s.1 = x} ∪
        C.newSlice := by
  intro x hx
  rcases I.terminalSet_subset_cutInitial_union_terminalFrontier hx with
    hxcut | hxterminal
  · by_cases hxY : x ∈ Gamma.initialSet Y
    · exact Or.inr (reference_cut_initials ⟨hxcut, hxY⟩)
    · apply Or.inl
      refine ⟨⟨x, ?_, hxY⟩, rfl⟩
      change x ∈ Gamma.initialSet D.outside.holes.paths
      rw [D.outside.initialSet_eq]
      exact hxcut
  · exact Or.inr (row_terminals hxterminal)

/-- A set containing both the closing set and the earlier-stage set contains
the complete canonical inside carrier. -/
theorem vertexSet_subset_of_cut
    {before innerRoof outerRoof Z : Set V}
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (D : OutsideCutConstruction (Y := Y) W X before innerRoof outerRoof)
    (hX : X ⊆ Z) (hbefore : before ⊆ Z) :
    I.insideFamily.vertexSet ⊆ Z := by
  rw [I.vertexSet_eq]
  intro x hx
  rcases insideCutCarrier_subset_closure_union_before D hx with hx | hx
  · exact hX hx
  · exact hbefore hx

/-- Old vertices already present in the provisional row and in the closing
set are vertices of the inside family. -/
theorem oldRealVertices_subset
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (old : LinkageBlueprint Gamma Y kappa)
    (hrow : old.vertexSet ⊆ Gamma.vertexSet W)
    (hX : old.vertexSet ⊆ X) :
    old.realPart.vertices ⊆ I.insideFamily.vertexSet := by
  rw [I.vertexSet_eq]
  intro x hx
  exact Or.inl (Or.inl ⟨hrow hx, hX hx⟩)

/-- Old real edges which occur in the provisional row remain literal inside
edges once all old vertices lie in the closing set. -/
theorem oldRealEdges_subset
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (old : LinkageBlueprint Gamma Y kappa)
    (hrow : old.realPart.edges ⊆ familyEdges W)
    (hX : old.vertexSet ⊆ X) :
    old.realPart.edges ⊆ relationRealEdges (Gamma := Gamma)
      (I.insideFamily.edgeSet ∪ assignedFiniteEdges A) := by
  intro e he
  have hend := edgeSet_endpoints_mem_vertexSet old
    (old.realPart_edges_subset he)
  refine ⟨Or.inl ?_, old.realPart_edges_are_original he⟩
  rw [I.edgeSet_eq]
  exact ⟨hrow he, ⟨hX hend.1, hX hend.2⟩⟩

/-- A target route retained in the provisional row and wholly contained in
the closing set is carried by the canonical inside family. -/
theorem targetPath_support_subset
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (p : FinitePath Gamma.graph)
    (hrow : p.support ⊆ Gamma.vertexSet W)
    (hX : p.support ⊆ X) :
    p.support ⊆ I.insideFamily.vertexSet := by
  rw [I.vertexSet_eq]
  intro x hx
  exact Or.inl (Or.inl ⟨hrow hx, hX hx⟩)

/-- The edges of such a target route are real edges of the full splice. -/
theorem targetPath_edges_subset
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (p : FinitePath Gamma.graph)
    (hrow : p.edgeSet ⊆ familyEdges W)
    (hX : p.support ⊆ X) :
    p.edgeSet ⊆ relationRealEdges (Gamma := Gamma)
      (I.insideFamily.edgeSet ∪ assignedFiniteEdges A) := by
  intro e he
  have hend := p.edgeSet_subset_support_prod he
  refine ⟨Or.inl ?_, p.edgeSet_subset_adj he⟩
  rw [I.edgeSet_eq]
  exact ⟨hrow he, ⟨hX hend.1, hX hend.2⟩⟩

end CanonicalInsideCut

/-! ## Rank-free compilation to the checked stage datum -/

variable {C : ClubStageGeometry Gamma Y kappa theta}
variable {old : LinkageBlueprint Gamma Y kappa}
variable {W : Set Gamma.DPath} {X : Set V}
variable {F : OutsideFracturedWarp W X}
variable {A : SimultaneousAssignment F.holes.paths Y}
variable {u : V}

/-- Compile the actual cut and its projected assignment to the concrete
inside-fragment splice.  The caller supplies the global Section 9 boundary
facts, but supplies no rank: the natural-number construction rank is derived
from acyclicity and absence of a reverse ray in the complete splice relation.

The three endpoint-attachment fields, both cross-incidence fields, all
assigned endpoint containment, and the inside family itself are theorems of
the literal cut construction above. -/
noncomputable def concreteInsideFragmentSpliceOfCut
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (hW : Gamma.IsWarp W)
    (hcycle : ¬ ContainsDirectedCycle
      (I.insideFamily.edgeSet ∪ assignedFiniteEdges A))
    (hreverse : ¬ ContainsReverseDirectedRay
      (I.insideFamily.edgeSet ∪ assignedFiniteEdges A))
    (terminal_boundary : I.insideFamily.terminalSet ⊆
      {x | ∃ s : {z // z ∈
        Gamma.initialSet F.holes.paths \ Gamma.initialSet Y}, s.1 = x} ∪
        C.newSlice)
    (carrier_roofed : I.insideFamily.vertexSet ⊆ C.outerRoof)
    (covers_source : Gamma.source ⊆
      I.insideFamily.initialSet ∪
        Gamma.initialSet
          (referencePathsMeeting Y C.newSlice \
            referencePathsMeeting Y I.insideFamily.vertexSet))
    (covered_initial_not_assigned_target :
      Gamma.source ∩ I.insideFamily.initialSet ⊆
        {x | ¬ ∃ y, (y, x) ∈ assignedFiniteEdges A})
    (carrier_closed : I.insideFamily.vertexSet ⊆ C.closedSet)
    (card_paths : #I.insideFamily.paths ≤ kappa)
    (every_relation_ray_strong :
      ∀ r : Ray (imaginaryGraph Gamma Y kappa),
        r.edgeSet ⊆ I.insideFamily.edgeSet ∪ assignedFiniteEdges A →
          (strongEdgeIndices r).Infinite)
    (inside_stable : I.insideFamily.Stable C.newSlice C.persistent)
    (old_real_vertices : old.realPart.vertices ⊆
      I.insideFamily.vertexSet)
    (old_real_edges : old.realPart.edges ⊆
      relationRealEdges (Gamma := Gamma)
        (I.insideFamily.edgeSet ∪ assignedFiniteEdges A))
    (old_vertices_accounted : old.vertexSet ⊆
      (I.insideFamily.terminalSet ∩ old.terminalSet) ∪
        {x | ∃ y,
          (x, y) ∈ old.familyGraph.edges ∩
            (I.insideFamily.edgeSet ∪ assignedFiniteEdges A)} ∪
          relationCompletedRealVertices (Gamma := Gamma)
            (I.insideFamily.edgeSet ∪ assignedFiniteEdges A)
            I.insideFamily.vertexSet Gamma.target)
    (preserved_old_terminal_not_assigned_source :
      I.insideFamily.terminalSet ∩ old.terminalSet ⊆
        {x | ¬ ∃ y, (x, y) ∈ assignedFiniteEdges A})
    (target_path : FinitePath Gamma.graph)
    (target_path_start : target_path.start = u)
    (target_path_finish : target_path.finish ∈ Gamma.target)
    (target_path_vertices : target_path.support ⊆
      I.insideFamily.vertexSet)
    (target_path_edges : target_path.edgeSet ⊆
      relationRealEdges (Gamma := Gamma)
        (I.insideFamily.edgeSet ∪ assignedFiniteEdges A))
    (preserves_other_real_terminals :
      old.realPart.terminals \ {u} ⊆
        relationRealTerminals (Gamma := Gamma)
          (I.insideFamily.edgeSet ∪ assignedFiniteEdges A)
          I.insideFamily.vertexSet) :
    ConcreteInsideFragmentSplice C old A u := by
  let E : Set (V × V) :=
    I.insideFamily.edgeSet ∪ assignedFiniteEdges A
  have hunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ E) := by
    exact I.fullRelation_biUnique hW
  let hwf : WellFounded (fun x y ↦ (x, y) ∈ E) :=
    ForwardOrientation.predecessor_wellFounded E hcycle hreverse
  let rank : V → Nat := ForwardOrientation.wellFoundedDepth E hwf
  have hrank {x y : V} (hxy : (x, y) ∈ E) : rank x < rank y := by
    have hstep := ForwardOrientation.wellFoundedDepth_step E hunique hwf hxy
    change ForwardOrientation.wellFoundedDepth E hwf x <
      ForwardOrientation.wellFoundedDepth E hwf y
    omega
  exact {
    insideFamily := I.insideFamily
    finite_sources_terminal := fun s _v _hterm ↦
      I.assignmentSource_mem_terminalSet hW s
    finite_targets_initial := fun s _v hterm ↦
      I.finiteAssignmentTarget_mem_initialSet hW s hterm
    infinite_sources_terminal :=
      I.assignedInfiniteSources_subset_terminalSet hW
    terminal_boundary := terminal_boundary
    carrier_roofed := carrier_roofed
    covers_source := covers_source
    covered_initial_not_assigned_target :=
      covered_initial_not_assigned_target
    carrier_closed := carrier_closed
    card_paths := card_paths
    rank := rank
    inside_rank := fun hxy ↦ hrank (Or.inl hxy)
    assigned_rank := fun hxy ↦ hrank (Or.inr hxy)
    every_relation_ray_strong := every_relation_ray_strong
    inside_stable := inside_stable
    old_real_vertices := old_real_vertices
    old_real_edges := old_real_edges
    old_vertices_accounted := old_vertices_accounted
    preserved_old_terminal_not_assigned_source :=
      preserved_old_terminal_not_assigned_source
    target_path := target_path
    target_path_start := target_path_start
    target_path_finish := target_path_finish
    target_path_vertices := target_path_vertices
    target_path_edges := target_path_edges
    preserves_other_real_terminals := preserves_other_real_terminals }

/-- Scheduler-facing form of `concreteInsideFragmentSpliceOfCut`.

This constructor consumes the actual cut package, including its
closure-selected outside assignment.  It chooses the canonical inside
decomposition itself and discharges the carrier, cardinality, old-real-part,
and embedded-target-route containment fields from literal row/cut
containment.  The remaining arguments are exactly the nonlocal Section 9
facts: global orientation, source/sink boundary, strong-ray/stability, the
9.32 accounting alternative, and terminal persistence. -/
noncomputable def concreteInsideFragmentSpliceOfOutsideCut
    (D : OutsideCutConstruction (Y := Y) W X
      C.before C.innerRoof C.outerRoof)
    (hW : Gamma.IsWarp W)
    (hXcard : #X ≤ kappa)
    (hXclosed : X ⊆ C.closedSet)
    (hXroof : X ⊆ C.outerRoof)
    (hclosed_roof : C.closedSet ⊆ C.outerRoof)
    (old_vertices_row : old.vertexSet ⊆ Gamma.vertexSet W)
    (old_vertices_closure : old.vertexSet ⊆ X)
    (old_edges_row : old.realPart.edges ⊆ familyEdges W)
    (hcycle : ¬ ContainsDirectedCycle
      ((insideCutFamilyOfWarp (Y := Y) (kappa := kappa) W X hW).edgeSet ∪
        assignedFiniteEdges D.assignment))
    (hreverse : ¬ ContainsReverseDirectedRay
      ((insideCutFamilyOfWarp (Y := Y) (kappa := kappa) W X hW).edgeSet ∪
        assignedFiniteEdges D.assignment))
    (reference_cut_initials :
      CutSplit.initialVertices (outsideCarrier W X)
          (outsideFamilyEdges W X) X ∩ Gamma.initialSet Y ⊆ C.newSlice)
    (row_terminals : Gamma.terminalFrontier W ⊆ C.newSlice)
    (covers_source : Gamma.source ⊆
      (insideCutFamilyOfWarp (Y := Y) (kappa := kappa) W X hW).initialSet ∪
        Gamma.initialSet
          (referencePathsMeeting Y C.newSlice \
            referencePathsMeeting Y
              (insideCutFamilyOfWarp (Y := Y) (kappa := kappa)
                W X hW).vertexSet))
    (covered_initial_not_assigned_target :
      Gamma.source ∩
          (insideCutFamilyOfWarp (Y := Y) (kappa := kappa) W X hW).initialSet ⊆
        {x | ¬ ∃ y, (y, x) ∈ assignedFiniteEdges D.assignment})
    (every_relation_ray_strong :
      ∀ r : Ray (imaginaryGraph Gamma Y kappa),
        r.edgeSet ⊆
            (insideCutFamilyOfWarp (Y := Y) (kappa := kappa) W X hW).edgeSet ∪
              assignedFiniteEdges D.assignment →
          (strongEdgeIndices r).Infinite)
    (inside_stable :
      (insideCutFamilyOfWarp (Y := Y) (kappa := kappa) W X hW).Stable
        C.newSlice C.persistent)
    (old_vertices_accounted : old.vertexSet ⊆
      ((insideCutFamilyOfWarp (Y := Y) (kappa := kappa) W X hW).terminalSet ∩
          old.terminalSet) ∪
        {x | ∃ y,
          (x, y) ∈ old.familyGraph.edges ∩
            ((insideCutFamilyOfWarp (Y := Y) (kappa := kappa)
              W X hW).edgeSet ∪ assignedFiniteEdges D.assignment)} ∪
          relationCompletedRealVertices (Gamma := Gamma)
            ((insideCutFamilyOfWarp (Y := Y) (kappa := kappa)
              W X hW).edgeSet ∪ assignedFiniteEdges D.assignment)
            (insideCutFamilyOfWarp (Y := Y) (kappa := kappa)
              W X hW).vertexSet Gamma.target)
    (preserved_old_terminal_not_assigned_source :
      (insideCutFamilyOfWarp (Y := Y) (kappa := kappa) W X hW).terminalSet ∩
          old.terminalSet ⊆
        {x | ¬ ∃ y, (x, y) ∈ assignedFiniteEdges D.assignment})
    (target_path : FinitePath Gamma.graph)
    (target_path_start : target_path.start = u)
    (target_path_finish : target_path.finish ∈ Gamma.target)
    (target_path_vertices_row : target_path.support ⊆ Gamma.vertexSet W)
    (target_path_vertices_closure : target_path.support ⊆ X)
    (target_path_edges_row : target_path.edgeSet ⊆ familyEdges W)
    (preserves_other_real_terminals :
      old.realPart.terminals \ {u} ⊆
        relationRealTerminals (Gamma := Gamma)
          ((insideCutFamilyOfWarp (Y := Y) (kappa := kappa)
            W X hW).edgeSet ∪ assignedFiniteEdges D.assignment)
          (insideCutFamilyOfWarp (Y := Y) (kappa := kappa)
            W X hW).vertexSet) :
    ConcreteInsideFragmentSplice C old D.assignment u := by
  let I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X :=
    canonicalInsideCutOfWarp (Y := Y) (kappa := kappa) W X hW
  apply concreteInsideFragmentSpliceOfCut
    (C := C) (old := old) (F := D.outside) (A := D.assignment)
    (u := u) (target_path := target_path)
    I hW hcycle hreverse
      (I.terminalBoundary_of_cut D reference_cut_initials row_terminals)
  · exact I.vertexSet_subset_of_cut D hXroof
      (C.before_subset_closedSet.trans hclosed_roof)
  · exact covers_source
  · exact covered_initial_not_assigned_target
  · exact I.vertexSet_subset_of_cut D hXclosed C.before_subset_closedSet
  · exact I.card_paths_of_cut D C.capacity_infinite hXcard C.before_card
  · exact every_relation_ray_strong
  · exact inside_stable
  · exact I.oldRealVertices_subset old old_vertices_row old_vertices_closure
  · exact I.oldRealEdges_subset old old_edges_row old_vertices_closure
  · exact old_vertices_accounted
  · exact preserved_old_terminal_not_assigned_source
  · exact target_path_start
  · exact target_path_finish
  · exact I.targetPath_support_subset target_path target_path_vertices_row
      target_path_vertices_closure
  · exact I.targetPath_edges_subset target_path target_path_edges_row
      target_path_vertices_closure
  · exact preserves_other_real_terminals

end LinkageBlueprint
end Blueprint
end Erdos599
