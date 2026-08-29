/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingSelectedSourceFirstTerminalOwner
import ErdosProblems.Erdos599.DeferredGroundingSelectedSourceFirstFork
import ErdosProblems.Erdos599.BlueprintSplice

/-!
# The virtual-escape branch after source-owner saturation

A virtual escape at the last required source-first point is an actual
ambient forward edge out of that point.  It therefore has only two honest
interactions with the maximal restoring prefix of the sacrificed owner.

* its head already lies on the prefix, and the edge is a literal return to
  an earlier rooted point; or
* its head is new, and adjoining this single edge gives a simple ambient
  path whose whole restoring prefix is unchanged.

The second alternative simultaneously keeps every required source-first
point of the owner.  This is the positive finite operation needed by the
moving transaction; no global matching or separator preservation is
assumed here.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

open _root_.Erdos599.DirectedPath
open Alternating PopularAuxiliary.Input
open PopularGroundingBridge GroundingSimultaneousDecode GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
variable {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}

local notation "J" => popularAuxiliaryInput L hL.legal

namespace ReservedStrongSelectedStartingLastContact.SourceSaturation

/-- The original endpoint represented by the first auxiliary occurrence of
a virtual escape.  The two alternatives retain the precise old/edge-gadget
provenance used by the decoder. -/
theorem relevantVirtualEscape_exists_forwardVertex
    {b : V}
    (E : GroundingInputRelevantDecoder.RelevantVirtualEscape J S.cut b) :
    ∃ y : V, Gamma.graph.Adj b y ∧
      ((E.escape.route.start = .old y ∧
          y ∈ PopularAuxiliary.Input.offLadder J ∪
            PopularAuxiliary.Input.targetMarkers J) ∨
        (∃ u : V, E.escape.route.start = .edge u y ∧
          (u, y) ∈ PopularAuxiliary.Input.familyEdges J)) := by
  cases hstart : E.escape.route.start with
  | old y =>
      have hvirtual := E.virtual
      rw [hstart] at hvirtual
      exact ⟨y, hvirtual.2, Or.inl ⟨rfl, hvirtual.1⟩⟩
  | edge u y =>
      have hvirtual := E.virtual
      rw [hstart] at hvirtual
      exact ⟨y, hvirtual.2, Or.inr ⟨u, rfl, hvirtual.1⟩⟩
  | proxy i =>
      have hvirtual := E.virtual
      rw [hstart] at hvirtual
      exact False.elim hvirtual

/-- A directed nonloop edge as a one-edge finite path. -/
private def virtualEdgePath {x y : V}
    (hxy : Gamma.graph.Adj x y) (hne : x ≠ y) : FinitePath Gamma.graph where
  start := x
  finish := y
  walk := .cons hxy .nil
  isPath := by
    simp only [Walk.IsPath, Walk.support_cons, Walk.support_nil]
    simp [hne]

@[simp] private theorem virtualEdgePath_start {x y : V}
    (hxy : Gamma.graph.Adj x y) (hne : x ≠ y) :
    (virtualEdgePath hxy hne).start = x := rfl

@[simp] private theorem virtualEdgePath_finish {x y : V}
    (hxy : Gamma.graph.Adj x y) (hne : x ≠ y) :
    (virtualEdgePath hxy hne).finish = y := rfl

@[simp] private theorem virtualEdgePath_support {x y : V}
    (hxy : Gamma.graph.Adj x y) (hne : x ≠ y) :
    (virtualEdgePath hxy hne).support = {x, y} := by
  ext z
  simp [virtualEdgePath, FinitePath.support]

@[simp] private theorem virtualEdgePath_edgeSet {x y : V}
    (hxy : Gamma.graph.Adj x y) (hne : x ≠ y) :
    (virtualEdgePath hxy hne).edgeSet = {(x, y)} := by
  ext e
  simp [virtualEdgePath, FinitePath.edgeSet, Walk.edgeSet]

/-- If the virtual connector does not return to the maximal restoring
prefix, appending it produces a literal simple source path.  Its support and
edge set are exact, and the old prefix is preserved as an actual prefix. -/
theorem LastSourceFirstPrefix.exists_virtualExtension_of_not_mem
    {r : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X} (F : LastSourceFirstPrefix D)
    {y : V} (hforward : Gamma.graph.Adj F.boundary y)
    (hy : y ∉ F.sourcePrefix.support) :
    ∃ q : FinitePath Gamma.graph,
      q.start = F.sourcePrefix.start ∧
      q.start ∈ Gamma.source ∧
      q.finish = y ∧
      F.sourcePrefix.IsPrefixOf q ∧
      q.support = F.sourcePrefix.support ∪ {y} ∧
      q.edgeSet = F.sourcePrefix.edgeSet ∪ {(F.boundary, y)} := by
  have hne : F.boundary ≠ y := by
    intro heq
    subst y
    apply hy
    rw [← F.sourcePrefix_finish]
    exact F.sourcePrefix.finish_mem_support
  let e : FinitePath Gamma.graph := virtualEdgePath hforward hne
  have hjoin : e.start = F.sourcePrefix.finish := by
    simpa only [e, virtualEdgePath_start, F.sourcePrefix_finish]
  have hinter : F.sourcePrefix.support ∩ e.support ⊆
      {F.sourcePrefix.finish} := by
    intro z hz
    have hzEdge : z = F.boundary ∨ z = y := by
      have := hz.2
      change z ∈ (virtualEdgePath hforward hne).support at this
      rw [virtualEdgePath_support] at this
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
    rcases hzEdge with rfl | rfl
    · simpa only [F.sourcePrefix_finish, Set.mem_singleton_iff]
    · exact False.elim (hy hz.1)
  let q := F.sourcePrefix.appendFinite e hjoin hinter
  refine ⟨q, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact F.sourcePrefix.appendFinite_start e hjoin hinter
  · change
      (F.sourcePrefix.appendFinite e hjoin hinter).start ∈ Gamma.source
    rw [F.sourcePrefix.appendFinite_start]
    exact F.sourcePrefix_source
  · simpa only [q, e, virtualEdgePath_finish] using
      F.sourcePrefix.appendFinite_finish e hjoin hinter
  · exact F.sourcePrefix.isPrefixOf_appendFinite e hjoin hinter
  · change
      (F.sourcePrefix.appendFinite e hjoin hinter).support = _
    rw [F.sourcePrefix.support_appendFinite_eq_union]
    change F.sourcePrefix.support ∪
      (virtualEdgePath hforward hne).support = _
    rw [virtualEdgePath_support]
    have hb : F.boundary ∈ F.sourcePrefix.support := by
      rw [← F.sourcePrefix_finish]
      exact F.sourcePrefix.finish_mem_support
    ext z
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (hz | hz | hz)
      · exact Or.inl hz
      · exact Or.inl (hz ▸ hb)
      · exact Or.inr hz
    · rintro (hz | hz)
      · exact Or.inl hz
      · exact Or.inr (Or.inr hz)
  · change
      (F.sourcePrefix.appendFinite e hjoin hinter).edgeSet = _
    rw [Blueprint.LinkageBlueprint.FinitePath.edgeSet_appendFinite]
    change F.sourcePrefix.edgeSet ∪
      (virtualEdgePath hforward hne).edgeSet = _
    rw [virtualEdgePath_edgeSet]

/-- Every required source-first point on the sacrificed owner remains
source-rooted inside the extended path.  Thus virtual forward progress is
made only after all same-owner obligations have been covered. -/
theorem LastSourceFirstPrefix.virtualExtension_roots_owner_boundaries
    {r : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X} (F : LastSourceFirstPrefix D)
    {y : V} (hforward : Gamma.graph.Adj F.boundary y)
    (hy : y ∉ F.sourcePrefix.support) :
    ∃ q : FinitePath Gamma.graph,
      q.start ∈ Gamma.source ∧ q.finish = y ∧
      q.edgeSet = F.sourcePrefix.edgeSet ∪ {(F.boundary, y)} ∧
      ∀ {z : V},
        z ∈ reservedStrongSelectedSourceFirstBB
          (L := L) (hL := hL) (S := S) →
        z ∈ D.owner.support →
        ∃ a ∈ Gamma.source,
          Relation.ReflTransGen
            (fun x w ↦ (x, w) ∈ q.edgeSet) a z := by
  obtain ⟨q, hqStart, hqSource, hqFinish, _hprefix,
      _hqSupport, hqEdges⟩ := F.exists_virtualExtension_of_not_mem
        hforward hy
  refine ⟨q, hqSource, hqFinish, hqEdges, ?_⟩
  intro z hz hzOwner
  obtain ⟨a, haSource, hreach⟩ := F.reaches_every_owner_boundary hz hzOwner
  refine ⟨a, haSource, ?_⟩
  apply Relation.ReflTransGen.mono
      (r := fun x w ↦ (x, w) ∈ F.sourcePrefix.edgeSet)
      (p := fun x w ↦ (x, w) ∈ q.edgeSet)
      ?_ a z hreach
  intro x w hxw
  rw [hqEdges]
  exact Set.mem_union_left _ hxw

/-- The exact virtual branch.  Either the connector returns to a vertex
already rooted by the restoring prefix, or it produces the concrete
one-edge extension above.  The represented first auxiliary occurrence is
retained in both alternatives. -/
theorem LastSourceFirstPrefix.virtualEscape_return_or_extension
    {r : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X} (F : LastSourceFirstPrefix D)
    (E : GroundingInputRelevantDecoder.RelevantVirtualEscape
      J S.cut F.boundary) :
    (∃ y : V, Gamma.graph.Adj F.boundary y ∧
      ((E.escape.route.start = .old y ∧
          y ∈ PopularAuxiliary.Input.offLadder J ∪
            PopularAuxiliary.Input.targetMarkers J) ∨
        (∃ u : V, E.escape.route.start = .edge u y ∧
          (u, y) ∈ PopularAuxiliary.Input.familyEdges J)) ∧
      y ∈ F.sourcePrefix.support) ∨
    (∃ y : V, Gamma.graph.Adj F.boundary y ∧
      ((E.escape.route.start = .old y ∧
          y ∈ PopularAuxiliary.Input.offLadder J ∪
            PopularAuxiliary.Input.targetMarkers J) ∨
        (∃ u : V, E.escape.route.start = .edge u y ∧
          (u, y) ∈ PopularAuxiliary.Input.familyEdges J)) ∧
      ∃ q : FinitePath Gamma.graph,
        q.start = F.sourcePrefix.start ∧
        q.start ∈ Gamma.source ∧
        q.finish = y ∧
        F.sourcePrefix.IsPrefixOf q ∧
        q.support = F.sourcePrefix.support ∪ {y} ∧
        q.edgeSet = F.sourcePrefix.edgeSet ∪ {(F.boundary, y)}) := by
  obtain ⟨y, hforward, hkind⟩ :=
    relevantVirtualEscape_exists_forwardVertex E
  by_cases hy : y ∈ F.sourcePrefix.support
  · exact Or.inl ⟨y, hforward, hkind, hy⟩
  · exact Or.inr ⟨y, hforward, hkind,
      F.exists_virtualExtension_of_not_mem hforward hy⟩

/-- A virtual extension either performs a literal clean warp augmentation,
or its new head lies on a distinct current component.  In the clean case
the sacrificed owner prefix is replaced by its one-edge extension: initials
are unchanged, the old prefix terminal is replaced by the new head, every
same-owner source-first obligation remains rooted, and the globally reserved
record remains a whole member.  The second alternative is the exact
cross-owner matching obligation, rather than an assumed compatibility
condition. -/
theorem LastSourceFirstPrefix.exists_cleanVirtualExtensionWarp_or_otherOwner
    {r : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X} (F : LastSourceFirstPrefix D)
    {y : V} (hforward : Gamma.graph.Adj F.boundary y)
    (hy : y ∉ F.sourcePrefix.support) :
    (∃ (q : FinitePath Gamma.graph) (W' : Set Gamma.DPath),
      q.start ∈ Gamma.source ∧ q.finish = y ∧
        (Sum.inl q : Gamma.DPath) ∈ W' ∧
        Gamma.IsWarp W' ∧
        Gamma.initialSet W' = Gamma.initialSet F.restoredWarp ∧
        Gamma.terminalFrontier W' = insert y
          (Gamma.terminalFrontier F.restoredWarp \ {F.boundary}) ∧
        (canonicalReservedRecord L hL S).record ∈ W' ∧
        ∀ {z : V},
          z ∈ reservedStrongSelectedSourceFirstBB
              (L := L) (hL := hL) (S := S) →
          z ∈ D.owner.support →
          ∃ a ∈ Gamma.source,
            Relation.ReflTransGen
              (fun x w ↦ (x, w) ∈ Alternating.familyEdges W') a z) ∨
      (∃ Y ∈ X.truncatedWarp \ {D.owner}, y ∈ Y.support) := by
  obtain ⟨q, hqStart, hqSource, hqFinish, _hqPrefix,
      hqSupport, hqEdges⟩ := F.exists_virtualExtension_of_not_mem
        hforward hy
  by_cases hyWarp : y ∈ Gamma.vertexSet F.restoredWarp
  · right
    obtain ⟨Y, hYW, hyY⟩ := hyWarp
    have hYne : Y ≠ (Sum.inl F.sourcePrefix : Gamma.DPath) := by
      intro hY
      subst Y
      exact hy hyY
    have hYRest : Y ∈ X.truncatedWarp \ {D.owner} := by
      simpa only [LastSourceFirstPrefix.restoredWarp,
        Set.mem_insert_iff, hYne, false_or] using hYW
    exact ⟨Y, hYRest, hyY⟩
  · left
    let p : Gamma.DPath := .inl F.sourcePrefix
    let W' : Set Gamma.DPath := insert (.inl q : Gamma.DPath)
      (F.restoredWarp \ {p})
    have hpW : p ∈ F.restoredWarp := by
      exact Set.mem_insert _ _
    have hdisjoint : Disjoint q.support
        (Gamma.vertexSet (F.restoredWarp \ {p})) := by
      rw [Set.disjoint_left]
      intro z hzq hzRest
      obtain ⟨Z, hZRest, hzZ⟩ := hzRest
      rw [hqSupport] at hzq
      rcases hzq with hzPrefix | hzY
      · have hpZ : p ≠ Z := by
          intro hpZ
          subst Z
          exact hZRest.2 (Set.mem_singleton p)
        exact Set.disjoint_left.mp
          (F.restoredWarp_isWarp hpW hZRest.1 hpZ)
            hzPrefix hzZ
      · have hzy : z = y := Set.mem_singleton_iff.mp hzY
        exact hyWarp (hzy ▸ ⟨Z, hZRest.1, hzZ⟩)
    have hW' : Gamma.IsWarp W' := by
      exact DWeb.IsWarp.insert_finite_of_disjoint Gamma
        (DWeb.IsWarp.sdiff_singleton Gamma F.restoredWarp_isWarp p) q
          hdisjoint
    have hW'Initial : Gamma.initialSet W' =
        Gamma.initialSet F.restoredWarp := by
      change Gamma.initialSet
        (insert (.inl q : Gamma.DPath) (F.restoredWarp \ {p})) = _
      rw [Gamma.initialSet_insert_finite,
        DWeb.IsWarp.initialSet_sdiff_singleton Gamma
          F.restoredWarp_isWarp hpW, hqStart]
      change insert F.sourcePrefix.start
        (Gamma.initialSet F.restoredWarp \ {F.sourcePrefix.start}) = _
      ext x
      simp only [Set.mem_insert_iff, Set.mem_diff,
        Set.mem_singleton_iff]
      constructor
      · rintro (rfl | hx)
        · exact ⟨p, hpW, rfl⟩
        · exact hx.1
      · intro hx
        by_cases hxeq : x = F.sourcePrefix.start
        · exact Or.inl hxeq
        · exact Or.inr ⟨hx, hxeq⟩
    have hW'Terminal : Gamma.terminalFrontier W' = insert y
        (Gamma.terminalFrontier F.restoredWarp \ {F.boundary}) := by
      change Gamma.terminalFrontier
        (insert (.inl q : Gamma.DPath) (F.restoredWarp \ {p})) = _
      rw [Gamma.terminalFrontier_insert_finite,
        DWeb.IsWarp.terminalFrontier_sdiff_singleton Gamma
          F.restoredWarp_isWarp hpW rfl, hqFinish,
        F.sourcePrefix_finish]
    have hreservedNe :
        (canonicalReservedRecord L hL S).record ≠ p := by
      intro hEq
      have hbRelevant : F.boundary ∈
          reservedStrongSelectedRelevantBB
            (L := L) (hL := hL) (S := S) :=
        reservedStrongSelectedSourceFirstBB_subset_relevantBB F.boundary_mem
      have hbReserved : F.boundary ∈
          (canonicalReservedRecord L hL S).record.support := by
        rw [hEq]
        change F.boundary ∈ F.sourcePrefix.support
        rw [← F.sourcePrefix_finish]
        exact F.sourcePrefix.finish_mem_support
      exact Set.disjoint_left.mp
        canonicalReservedRecord_disjoint_reservedStrongSelectedRelevantBB
          hbRelevant hbReserved
    have hreserved : (canonicalReservedRecord L hL S).record ∈ W' := by
      exact Set.mem_insert_of_mem _
        ⟨F.canonicalReservedRecord_mem_restoredWarp,
          by simpa only [Set.mem_singleton_iff] using hreservedNe⟩
    refine ⟨q, W', hqSource, hqFinish, Set.mem_insert _ _, hW',
      hW'Initial, hW'Terminal, hreserved, ?_⟩
    intro z hz hzOwner
    obtain ⟨a, haSource, hreach⟩ :=
      F.reaches_every_owner_boundary hz hzOwner
    refine ⟨a, haSource, ?_⟩
    have hprefixEdges : F.sourcePrefix.edgeSet ⊆ q.edgeSet := by
      intro e he
      rw [hqEdges]
      exact Set.mem_union_left _ he
    have hqFamily : q.edgeSet ⊆ Alternating.familyEdges W' := by
      intro e he
      simp only [Alternating.familyEdges, Set.mem_iUnion]
      exact ⟨(.inl q : Gamma.DPath), Set.mem_insert _ _, he⟩
    exact Relation.ReflTransGen.mono
      (r := fun x w ↦ (x, w) ∈ F.sourcePrefix.edgeSet)
      (p := fun x w ↦ (x, w) ∈ Alternating.familyEdges W')
      (fun _ _ he ↦ hqFamily (hprefixEdges he)) a z hreach

/-- If the component hit by a virtual extension is itself source-grounded,
no exchange is needed.  The restored warp already roots every required
point on both involved owners and retains the globally reserved record.
Thus the only genuine cross-owner virtual obligation is a hit on a
nongrounded (hanging) component. -/
theorem LastSourceFirstPrefix.restoredWarp_roots_owner_and_sourceGroundedHit
    {r : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X} (F : LastSourceFirstPrefix D)
    {Y : Gamma.DPath}
    (hY : Y ∈ X.truncatedWarp \ {D.owner})
    (hYSource : Y.initial ∈ Gamma.source) :
    (canonicalReservedRecord L hL S).record ∈ F.restoredWarp ∧
      ∀ {z : V},
        z ∈ reservedStrongSelectedSourceFirstBB
            (L := L) (hL := hL) (S := S) →
        z ∈ D.owner.support ∪ Y.support →
        ∃ a ∈ Gamma.source,
          Relation.ReflTransGen
            (fun x w ↦ (x, w) ∈
              Alternating.familyEdges F.restoredWarp) a z := by
  refine ⟨F.canonicalReservedRecord_mem_restoredWarp, ?_⟩
  intro z hz hzOwner
  rcases hzOwner with hzD | hzY
  · exact F.restoredWarp_roots_owner_boundaries hz hzD
  · obtain ⟨q, hqStart, hqFinish, _hqSupport, hqEdges⟩ :=
      GroundingPathPrefix.exists_initialFinitePrefix Y hzY
    have hYW : Y ∈ F.restoredWarp :=
      Set.mem_insert_of_mem _ hY
    refine ⟨q.start, hqStart ▸ hYSource, ?_⟩
    have hwalk := Alternating.Walk.reflTransGen_edgeSet q.walk
    have hedge : q.edgeSet ⊆ Alternating.familyEdges F.restoredWarp := by
      intro e he
      simp only [Alternating.familyEdges, Set.mem_iUnion]
      exact ⟨Y, hYW, hqEdges he⟩
    simpa only [hqFinish] using
      Relation.ReflTransGen.mono
        (r := fun x w ↦ (x, w) ∈ q.edgeSet)
        (p := fun x w ↦ (x, w) ∈
          Alternating.familyEdges F.restoredWarp)
        (fun _ _ he ↦ hedge he) q.start q.finish hwalk

/-- A distinct restored-warp component which is not source-grounded is a
genuine hanging member of the original limiting warp.  The temporary
own-start prefix is excluded because its start is grounded. -/
theorem otherVirtualOwner_mem_hangingPaths
    {r : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X}
    {Y : Gamma.DPath}
    (hY : Y ∈ X.truncatedWarp \ {D.owner})
    (hnotSource : Y.initial ∉ Gamma.source) :
    Y ∈ PopularAuxiliary.hangingPaths Gamma L.limitWarp := by
  have hYW := hY.1
  rw [ReservedStrongSelectedStartingLastContact.truncatedWarp] at hYW
  rcases hYW with hprefix | hlimit
  · have hsource : Y.initial ∈ Gamma.source := by
      rw [hprefix]
      exact X.oldPrefix_source
    exact False.elim (hnotSource hsource)
  · exact ⟨hlimit.1, hnotSource⟩

/-- A finite path whose start and every edge lie on one reference path has
its whole support on that reference path. -/
private theorem finitePath_support_subset_of_start_and_edges
    (q : FinitePath Gamma.graph) (Y : Gamma.DPath)
    (hstart : q.start ∈ Y.support)
    (hedges : q.edgeSet ⊆ Y.edgeSet) :
    q.support ⊆ Y.support := by
  intro z hz
  by_cases hzs : z = q.start
  · exact hzs ▸ hstart
  · obtain ⟨x, hxz⟩ :=
      FinitePath.exists_incoming_edge_of_mem_support_of_ne_start q hz hzs
    exact (Y.edgeSet_subset_support_prod (hedges hxz)).2

/-- The concrete suffix selected from a finite path or ray begins at the
chosen vertex. -/
private theorem path_suffixFrom_initial
    (P : Gamma.DPath) {x : V} (hx : x ∈ P.support) :
    (P.suffixFrom x hx).initial = x := by
  rcases P with p | ray
  · exact p.suffixFromAux_start x hx
  · exact ray.initial_suffixFrom x hx

/-- Selecting a suffix introduces no new directed edge. -/
private theorem path_suffixFrom_edgeSet_subset
    (P : Gamma.DPath) {x : V} (hx : x ∈ P.support) :
    (P.suffixFrom x hx).edgeSet ⊆ P.edgeSet := by
  rcases P with p | ray
  · change (p.suffixFromAux x hx).walk.edgeSet ⊆ p.walk.edgeSet
    exact (p.suffixData x hx).walk.edgeSet_subset_of_support_suffix
      p.walk (p.suffixData_support_suffix x hx)
  · change (ray.tail (Classical.choose hx)).edgeSet ⊆ ray.edgeSet
    exact GroundingRayFragment.rayTail_edgeSet_subset
      ray (Classical.choose hx)

/-- A directed finite walk using only edges of one reference path moves
forward in that path's intrinsic order. -/
private theorem walk_beforeEq_of_edgeSet_subset
    (P : Gamma.DPath) {a b : V} (q : Walk Gamma.graph a b)
    (ha : a ∈ P.support) (hq : q.edgeSet ⊆ P.edgeSet) :
    GroundingCut.BeforeEq P a b := by
  induction q with
  | nil => exact GroundingCut.beforeEq_refl ha
  | @cons a c b hac q ih =>
      have hacP : (a, c) ∈ P.edgeSet := by
        apply hq
        simp
      have hcP : c ∈ P.support :=
        (P.edgeSet_subset_support_prod hacP).2
      have hqP : q.edgeSet ⊆ P.edgeSet := by
        intro e he
        apply hq
        simp only [Walk.edgeSet_cons, Set.mem_union,
          Set.mem_singleton_iff]
        exact Or.inr he
      exact GroundingFragmentResidualOrder.beforeEq_trans
        (GroundingCut.beforeEq_of_mem_edgeSet hacP) (ih hcP hqP)

/-- Intrinsic order has the expected suffix semantics for both finite paths
and rays.  This small bridge lets the cross-owner transaction use the
uniform `Path.appendAt` operation without splitting on finiteness. -/
private theorem mem_path_suffixFrom_of_beforeEq
    (P : Gamma.DPath) {x z : V}
    (hx : x ∈ P.support) (hz : z ∈ P.support)
    (hxz : GroundingCut.BeforeEq P x z) :
    z ∈ (P.suffixFrom x hx).support := by
  rcases Path.start_mem_suffixFrom_or_start_mem_suffixFrom P hx hz with
      hwrong | hright
  · obtain ⟨q, hqStart, hqFinish, _hqSupport, hqEdges⟩ :=
      GroundingPathPrefix.exists_initialFinitePrefix
        (P.suffixFrom z hz) hwrong
    have hstart : q.start = z :=
      hqStart.trans (path_suffixFrom_initial P hz)
    have hzx : GroundingCut.BeforeEq P z x := by
      have hmono : q.edgeSet ⊆ P.edgeSet :=
        hqEdges.trans (path_suffixFrom_edgeSet_subset P hz)
      have hqStartP : q.start ∈ P.support := hstart.symm ▸ hz
      simpa only [hstart, hqFinish] using
        walk_beforeEq_of_edgeSet_subset P q.walk hqStartP hmono
    have hxEq : x = z :=
      GroundingCutDecoder.beforeEq_antisymm hxz hzx
    rw [← hxEq]
    have hinitial := Path.initial_mem_support (P.suffixFrom x hx)
    simpa only [path_suffixFrom_initial P hx] using hinitial
  · exact hright

/-- Insert an arbitrary finite-or-ray path into a warp when its support is
disjoint from the old vertex union. -/
private theorem isWarp_insert_path_of_disjoint
    {W : Set Gamma.DPath} (hW : Gamma.IsWarp W) (P : Gamma.DPath)
    (hdis : Disjoint P.support (Gamma.vertexSet W)) :
    Gamma.IsWarp (insert P W) := by
  intro A hA B hB hne
  rcases Set.mem_insert_iff.mp hA with hAP | hAW
  · subst A
    rcases Set.mem_insert_iff.mp hB with hBP | hBW
    · exact False.elim (hne hBP.symm)
    · apply hdis.mono_right
      intro x hx
      exact ⟨B, hBW, hx⟩
  · rcases Set.mem_insert_iff.mp hB with hBP | hBW
    · apply Disjoint.symm
      subst B
      apply hdis.mono_right
      intro x hx
      exact ⟨A, hAW, hx⟩
    · exact hW hAW hBW hne

/-- When the virtual head lies on another current component, the extension
continues along that component to every point at or after the hit.  The
result is a literal ambient source path; its support stays inside the two
owners and the single connector endpoint. -/
theorem LastSourceFirstPrefix.exists_virtualTransferPath_to_laterOwnerVertex
    {r : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X} (F : LastSourceFirstPrefix D)
    {y : V} (hforward : Gamma.graph.Adj F.boundary y)
    (hyPrefix : y ∉ F.sourcePrefix.support)
    {Y : Gamma.DPath}
    (hY : Y ∈ X.truncatedWarp \ {D.owner})
    (hyY : y ∈ Y.support)
    {z : V} (hzY : z ∈ Y.support)
    (hyz : GroundingCut.BeforeEq Y y z) :
    ∃ q : FinitePath Gamma.graph,
      q.start ∈ Gamma.source ∧ q.finish = z ∧
        q.support ⊆ F.sourcePrefix.support ∪ Y.support := by
  obtain ⟨front, _hfrontStart, hfrontSource, hfrontFinish,
      _hfrontPrefix, hfrontSupport, _hfrontEdges⟩ :=
    F.exists_virtualExtension_of_not_mem hforward hyPrefix
  by_cases hyzEq : y = z
  · subst z
    refine ⟨front, hfrontSource, hfrontFinish, ?_⟩
    intro x hx
    rw [hfrontSupport] at hx
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (Set.mem_singleton_iff.mp hx ▸ hyY)
  · have hyzStrict : GroundingCut.Before Y y z := ⟨hyz, hyzEq⟩
    obtain ⟨tail, htailStart, htailFinish, htailEdges⟩ :=
      GroundingCutDecoder.exists_forward_segment_of_before hyzStrict
    have htailSupport : tail.support ⊆ Y.support :=
      finitePath_support_subset_of_start_and_edges tail Y
        (htailStart.symm ▸ hyY) htailEdges
    have hjoin : tail.start = front.finish := by
      exact htailStart.trans hfrontFinish.symm
    have hinter : front.support ∩ tail.support ⊆ {front.finish} := by
      intro x hx
      have hxFront := hx.1
      rw [hfrontSupport] at hxFront
      rcases hxFront with hxPrefix | hxy
      · have hxD : x ∈ D.owner.support :=
          F.sourcePrefix_support hxPrefix
        have hxY : x ∈ Y.support := htailSupport hx.2
        have hne : D.owner ≠ Y := by
          intro hEq
          subst Y
          exact hY.2 (Set.mem_singleton D.owner)
        exact False.elim <| Set.disjoint_left.mp
          (X.truncatedWarp_isWarp D.owner_mem hY.1 hne) hxD hxY
      · have hxyEq : x = y := Set.mem_singleton_iff.mp hxy
        exact Set.mem_singleton_iff.mpr
          (hxyEq.trans hfrontFinish.symm)
    let q := front.appendFinite tail hjoin hinter
    refine ⟨q, ?_, ?_, ?_⟩
    · change (front.appendFinite tail hjoin hinter).start ∈ Gamma.source
      rw [FinitePath.appendFinite_start]
      exact hfrontSource
    · change (front.appendFinite tail hjoin hinter).finish = z
      rw [FinitePath.appendFinite_finish]
      exact htailFinish
    · intro x hx
      change x ∈ (front.appendFinite tail hjoin hinter).support at hx
      rw [front.support_appendFinite_eq_union] at hx
      rcases hx with hxFront | hxTail
      · rw [hfrontSupport] at hxFront
        rcases hxFront with hxPrefix | hxy
        · exact Or.inl hxPrefix
        · exact Or.inr (Set.mem_singleton_iff.mp hxy ▸ hyY)
      · exact Or.inr (htailSupport hxTail)

/-- Pointwise cross-owner progress.  Every required point on the hit owner
is either reached by the literal transfer path, or lies strictly before the
hit.  No incomparable residual is possible because each owner is a path. -/
theorem LastSourceFirstPrefix.virtualTransfer_roots_or_strictlyEarlier
    {r : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X} (F : LastSourceFirstPrefix D)
    {y : V} (hforward : Gamma.graph.Adj F.boundary y)
    (hyPrefix : y ∉ F.sourcePrefix.support)
    {Y : Gamma.DPath}
    (hY : Y ∈ X.truncatedWarp \ {D.owner})
    (hyY : y ∈ Y.support)
    {z : V} (hzY : z ∈ Y.support) :
    (∃ q : FinitePath Gamma.graph,
      q.start ∈ Gamma.source ∧ q.finish = z ∧
        q.support ⊆ F.sourcePrefix.support ∪ Y.support) ∨
      GroundingCut.Before Y z y := by
  rcases GroundingCut.beforeEq_total hyY hzY with hyz | hzy
  · exact Or.inl
      (F.exists_virtualTransferPath_to_laterOwnerVertex hforward hyPrefix
        hY hyY hzY hyz)
  · by_cases hEq : z = y
    · subst z
      exact Or.inl
        (F.exists_virtualTransferPath_to_laterOwnerVertex hforward hyPrefix
          hY hyY hyY (GroundingCut.beforeEq_refl hyY))
    · exact Or.inr ⟨hzy, hEq⟩

/-- The unresolved strict-prefix obligations on a virtual-hit owner form a
finite set, even when the owner is a ray: they all lie on the finite initial
prefix ending at the hit vertex. -/
theorem virtualOwner_strictPrefixObligations_finite
    (Y : Gamma.DPath) {y : V} (hyY : y ∈ Y.support) :
    ({z | z ∈ reservedStrongSelectedSourceFirstBB
            (L := L) (hL := hL) (S := S) ∧
          GroundingCut.Before Y z y} : Set V).Finite := by
  obtain ⟨q, hqStart, hqFinish, _hqSupport, hqEdges⟩ :=
    GroundingPathPrefix.exists_initialFinitePrefix Y hyY
  apply q.support_finite.subset
  intro z hz
  apply initialSubpath_mem_of_beforeEq_finish Y q hqStart hqEdges
  simpa only [hqFinish] using hz.2.1

/-- The genuine cross-owner virtual transaction.  A connector which hits a
nongrounded current owner is spliced to that owner's forward suffix, while
the sacrificed source-grounded owner is replaced by its maximal restoring
prefix.  The resulting finite-or-ray path is inserted after deleting the
two old owners.

The transaction is an actual warp, retains the canonical reserved record,
roots every required point of the sacrificed owner, and roots every required
point of the hit owner at or after the collision.  Its only unresolved
obligations are the explicitly displayed finite strict prefix of the hit
owner.  In particular this theorem performs the two-owner coexistence
operation without assuming a global matching or coverage certificate. -/
theorem LastSourceFirstPrefix.exists_virtualHangingOwnerSpliceWarp
    {r : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X} (F : LastSourceFirstPrefix D)
    {y : V} (hforward : Gamma.graph.Adj F.boundary y)
    (hyPrefix : y ∉ F.sourcePrefix.support)
    {Y : Gamma.DPath}
    (hY : Y ∈ X.truncatedWarp \ {D.owner})
    (hyY : y ∈ Y.support)
    (hnotSource : Y.initial ∉ Gamma.source) :
    ∃ (P : Gamma.DPath) (W' : Set Gamma.DPath),
      P ∈ W' ∧ Gamma.IsWarp W' ∧
      P.initial ∈ Gamma.source ∧ P.terminal? = Y.terminal? ∧
      P.support ⊆ D.owner.support ∪ Y.support ∧
      Gamma.initialSet W' =
        Gamma.initialSet X.truncatedWarp \ {Y.initial} ∧
      Gamma.terminalFrontier W' =
        Gamma.terminalFrontier (X.truncatedWarp \ {D.owner}) ∧
      (canonicalReservedRecord L hL S).record ∈ W' ∧
      (∀ {z : V},
        z ∈ reservedStrongSelectedSourceFirstBB
            (L := L) (hL := hL) (S := S) →
        z ∈ D.owner.support →
        ∃ a ∈ Gamma.source,
          Relation.ReflTransGen
            (fun x w ↦ (x, w) ∈ Alternating.familyEdges W') a z) ∧
      (∀ {z : V},
        z ∈ reservedStrongSelectedSourceFirstBB
            (L := L) (hL := hL) (S := S) →
        z ∈ Y.support →
        (∃ a ∈ Gamma.source,
          Relation.ReflTransGen
            (fun x w ↦ (x, w) ∈ Alternating.familyEdges W') a z) ∨
          GroundingCut.Before Y z y) ∧
      ({z | z ∈ reservedStrongSelectedSourceFirstBB
              (L := L) (hL := hL) (S := S) ∧
            GroundingCut.Before Y z y} : Set V).Finite := by
  obtain ⟨front, hfrontStart, hfrontSource, hfrontFinish,
      hprefix, hfrontSupport, _hfrontEdges⟩ :=
    F.exists_virtualExtension_of_not_mem hforward hyPrefix
  have hyFront : front.finish ∈ Y.support := hfrontFinish.symm ▸ hyY
  have happend : Path.Appendable front Y hyFront := by
    rw [Path.Appendable, Set.disjoint_left]
    intro x hxFront hxTail
    have hxY : x ∈ Y.support :=
      Y.support_suffixFrom_subset front.finish hyFront hxTail.1
    rw [hfrontSupport] at hxFront
    rcases hxFront with hxPrefix | hxy
    · have hxOwner : x ∈ D.owner.support :=
        F.sourcePrefix_support hxPrefix
      have hownerNe : D.owner ≠ Y := by
        intro hEq
        subst Y
        exact hY.2 (Set.mem_singleton D.owner)
      exact Set.disjoint_left.mp
        (X.truncatedWarp_isWarp D.owner_mem hY.1 hownerNe)
          hxOwner hxY
    · have hxyEq : x = y := Set.mem_singleton_iff.mp hxy
      exact hxTail.2 (hxyEq.trans hfrontFinish.symm)
  let P : Gamma.DPath := Path.appendAt front Y hyFront happend
  let W0 : Set Gamma.DPath :=
    X.truncatedWarp \ {D.owner, Y}
  let W' : Set Gamma.DPath := insert P W0
  have hPInitial : P.initial = front.start := by
    exact (Path.extends_initial
      (Path.extends_appendAt front Y hyFront happend)).symm
  have hPSource : P.initial ∈ Gamma.source := by
    rw [hPInitial]
    exact hfrontSource
  have hPInitialOwner : P.initial = D.owner.initial :=
    hPInitial.trans (hfrontStart.trans F.sourcePrefix_start)
  have hPTerminal : P.terminal? = Y.terminal? := by
    exact Path.terminal?_appendAt front Y hyFront happend
  have hPSupport : P.support ⊆ D.owner.support ∪ Y.support := by
    intro x hxP
    change x ∈ (Path.appendAt front Y hyFront happend).support at hxP
    rw [Path.support_appendAt] at hxP
    rcases hxP with hxFront | hxSuffix
    · rw [hfrontSupport] at hxFront
      rcases hxFront with hxPrefix | hxy
      · exact Or.inl (F.sourcePrefix_support hxPrefix)
      · exact Or.inr (Set.mem_singleton_iff.mp hxy ▸ hyY)
    · exact Or.inr
        (Y.support_suffixFrom_subset front.finish hyFront hxSuffix)
  have hownerNeY : D.owner ≠ Y := by
    intro hEq
    subst Y
    exact hY.2 (Set.mem_singleton D.owner)
  have hW0 : Gamma.IsWarp W0 := by
    intro A hA B hB hne
    exact X.truncatedWarp_isWarp hA.1 hB.1 hne
  have hPDisjoint : Disjoint P.support (Gamma.vertexSet W0) := by
    rw [Set.disjoint_left]
    intro x hxP hxW0
    obtain ⟨Z, hZW0, hxZ⟩ := hxW0
    have hZneOwner : D.owner ≠ Z := by
      intro hEq
      subst Z
      exact hZW0.2 (by simp)
    have hZneY : Y ≠ Z := by
      intro hEq
      subst Z
      exact hZW0.2 (by simp)
    have hOwnerDisjoint : Disjoint D.owner.support Z.support :=
      X.truncatedWarp_isWarp D.owner_mem hZW0.1 hZneOwner
    have hYDisjoint : Disjoint Y.support Z.support :=
      X.truncatedWarp_isWarp hY.1 hZW0.1 hZneY
    have hxAppend := hxP
    change x ∈ (Path.appendAt front Y hyFront happend).support at hxAppend
    rw [Path.support_appendAt] at hxAppend
    rcases hxAppend with hxFront | hxSuffix
    · rw [hfrontSupport] at hxFront
      rcases hxFront with hxPrefix | hxy
      · exact Set.disjoint_left.mp hOwnerDisjoint
          (F.sourcePrefix_support hxPrefix) hxZ
      · exact Set.disjoint_left.mp hYDisjoint
          (Set.mem_singleton_iff.mp hxy ▸ hyY) hxZ
    · exact Set.disjoint_left.mp hYDisjoint
        (Y.support_suffixFrom_subset front.finish hyFront hxSuffix) hxZ
  have hW' : Gamma.IsWarp W' :=
    isWarp_insert_path_of_disjoint hW0 P hPDisjoint
  have hPmem : P ∈ W' := Set.mem_insert P W0
  have hW'Initial : Gamma.initialSet W' =
      Gamma.initialSet X.truncatedWarp \ {Y.initial} := by
    ext x
    constructor
    · rintro ⟨Q, hQW, hQInitial⟩
      rcases Set.mem_insert_iff.mp hQW with hQP | hQRest
      · subst Q
        refine ⟨⟨D.owner, D.owner_mem,
          hPInitialOwner.symm.trans hQInitial⟩,
          ?_⟩
        intro hEq
        have hInitEq : D.owner.initial = Y.initial := by
          exact hPInitialOwner.symm.trans (hQInitial.trans hEq)
        exact hownerNeY
          (DWeb.IsWarp.eq_of_initial_eq Gamma X.truncatedWarp_isWarp
            D.owner_mem hY.1 hInitEq)
      · refine ⟨⟨Q, hQRest.1, hQInitial⟩, ?_⟩
        intro hEq
        have hQY : Q = Y :=
          DWeb.IsWarp.eq_of_initial_eq Gamma X.truncatedWarp_isWarp
            hQRest.1 hY.1 (hQInitial.trans hEq)
        subst Q
        exact hQRest.2 (by simp)
    · rintro ⟨⟨Q, hQX, hQInitial⟩, hxNeY⟩
      by_cases hQD : Q = D.owner
      · subst Q
        refine ⟨P, hPmem, ?_⟩
        exact hPInitialOwner.trans hQInitial
      · have hQY : Q ≠ Y := by
          intro hEq
          subst Q
          exact hxNeY hQInitial.symm
        refine ⟨Q, ?_, hQInitial⟩
        exact Set.mem_insert_of_mem P
          ⟨hQX, by simp [hQD, hQY]⟩
  have hW'Terminal : Gamma.terminalFrontier W' =
      Gamma.terminalFrontier (X.truncatedWarp \ {D.owner}) := by
    ext t
    constructor
    · rintro ⟨Q, hQW, hQTerminal⟩
      rcases Set.mem_insert_iff.mp hQW with hQP | hQRest
      · subst Q
        exact ⟨Y, ⟨hY.1, by
          simpa only [Set.mem_singleton_iff] using hownerNeY.symm⟩,
          hPTerminal.symm.trans hQTerminal⟩
      · exact ⟨Q, ⟨hQRest.1, by
          intro hQD
          exact hQRest.2 (by simp [Set.mem_singleton_iff.mp hQD])⟩,
          hQTerminal⟩
    · rintro ⟨Q, hQRest, hQTerminal⟩
      by_cases hQY : Q = Y
      · subst Q
        exact ⟨P, hPmem, hPTerminal.trans hQTerminal⟩
      · refine ⟨Q, ?_, hQTerminal⟩
        exact Set.mem_insert_of_mem P ⟨hQRest.1, by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
            not_or]
          exact ⟨hQRest.2, hQY⟩⟩
  have hPEdges : P.edgeSet ⊆ Alternating.familyEdges W' := by
    intro e he
    simp only [Alternating.familyEdges, Set.mem_iUnion]
    exact ⟨P, hPmem, he⟩
  have hfrontEdges : front.edgeSet ⊆ P.edgeSet :=
    Path.edgeSet_mono_of_extends
      (Path.extends_appendAt front Y hyFront happend)
  have hprefixEdges : F.sourcePrefix.edgeSet ⊆ P.edgeSet := by
    apply Set.Subset.trans _ hfrontEdges
    exact F.sourcePrefix.walk.edgeSet_subset_of_support_prefix
      front.walk hprefix
  have hrootOfMem {z : V} (hzP : z ∈ P.support) :
      ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x w ↦ (x, w) ∈ Alternating.familyEdges W') a z := by
    obtain ⟨q, hqStart, hqFinish, _hqSupport, hqEdges⟩ :=
      GroundingPathPrefix.exists_initialFinitePrefix P hzP
    refine ⟨q.start, ?_, ?_⟩
    · rw [hqStart]
      exact hPSource
    · have hwalk := Alternating.Walk.reflTransGen_edgeSet q.walk
      simpa only [hqFinish] using
        Relation.ReflTransGen.mono
          (r := fun x w ↦ (x, w) ∈ q.edgeSet)
          (p := fun x w ↦ (x, w) ∈ Alternating.familyEdges W')
          (fun _ _ he ↦ hPEdges (hqEdges he)) q.start q.finish hwalk
  have hreservedNeOwner :
      (canonicalReservedRecord L hL S).record ≠ D.owner := by
    intro hEq
    have hbRelevant : F.boundary ∈
        reservedStrongSelectedRelevantBB
          (L := L) (hL := hL) (S := S) :=
      reservedStrongSelectedSourceFirstBB_subset_relevantBB F.boundary_mem
    have hbReserved : F.boundary ∈
        (canonicalReservedRecord L hL S).record.support := by
      rw [hEq]
      exact F.boundary_mem_owner
    exact Set.disjoint_left.mp
      canonicalReservedRecord_disjoint_reservedStrongSelectedRelevantBB
        hbRelevant hbReserved
  have hreservedNeY :
      (canonicalReservedRecord L hL S).record ≠ Y := by
    intro hEq
    apply hnotSource
    rw [← hEq]
    exact (canonicalReservedRecord L hL S).grounded
  have hreservedNePrefix :
      (canonicalReservedRecord L hL S).record ≠
        (Sum.inl F.sourcePrefix : Gamma.DPath) := by
    intro hEq
    have hbRelevant : F.boundary ∈
        reservedStrongSelectedRelevantBB
          (L := L) (hL := hL) (S := S) :=
      reservedStrongSelectedSourceFirstBB_subset_relevantBB F.boundary_mem
    have hbReserved : F.boundary ∈
        (canonicalReservedRecord L hL S).record.support := by
      rw [hEq]
      change F.boundary ∈ F.sourcePrefix.support
      rw [← F.sourcePrefix_finish]
      exact F.sourcePrefix.finish_mem_support
    exact Set.disjoint_left.mp
      canonicalReservedRecord_disjoint_reservedStrongSelectedRelevantBB
        hbRelevant hbReserved
  have hreserved : (canonicalReservedRecord L hL S).record ∈ W' := by
    apply Set.mem_insert_of_mem
    have hmem := F.canonicalReservedRecord_mem_restoredWarp
    rw [LastSourceFirstPrefix.restoredWarp,
      Set.mem_insert_iff] at hmem
    have hrest : (canonicalReservedRecord L hL S).record ∈
        X.truncatedWarp \ {D.owner} :=
      hmem.resolve_left hreservedNePrefix
    exact ⟨hrest.1, by simp [hreservedNeOwner, hreservedNeY]⟩
  refine ⟨P, W', hPmem, hW', hPSource, hPTerminal, hPSupport,
    hW'Initial, hW'Terminal, hreserved,
    ?_, ?_, virtualOwner_strictPrefixObligations_finite Y hyY⟩
  · intro z hzT hzOwner
    obtain ⟨a, haSource, hreach⟩ :=
      F.reaches_every_owner_boundary hzT hzOwner
    refine ⟨a, haSource, ?_⟩
    exact Relation.ReflTransGen.mono
      (r := fun x w ↦ (x, w) ∈ F.sourcePrefix.edgeSet)
      (p := fun x w ↦ (x, w) ∈ Alternating.familyEdges W')
      (fun _ _ he ↦ hPEdges (hprefixEdges he)) a z hreach
  · intro z _hzT hzY
    rcases GroundingCut.beforeEq_total hyY hzY with hyz | hzy
    · left
      apply hrootOfMem
      change z ∈ (Path.appendAt front Y hyFront happend).support
      rw [Path.support_appendAt]
      have hzSuffix := mem_path_suffixFrom_of_beforeEq Y hyY hzY hyz
      apply Set.mem_union_right
      simpa only [hfrontFinish] using hzSuffix
    · by_cases hEq : z = y
      · left
        subst z
        apply hrootOfMem
        change y ∈ (Path.appendAt front Y hyFront happend).support
        rw [Path.support_appendAt]
        exact Or.inl (hfrontSupport.symm ▸ Or.inr (Set.mem_singleton y))
      · exact Or.inr ⟨hzy, hEq⟩

end ReservedStrongSelectedStartingLastContact.SourceSaturation

end Deferred
end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.relevantVirtualEscape_exists_forwardVertex
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.LastSourceFirstPrefix.exists_virtualExtension_of_not_mem
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.LastSourceFirstPrefix.virtualExtension_roots_owner_boundaries
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.LastSourceFirstPrefix.virtualEscape_return_or_extension
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.LastSourceFirstPrefix.exists_cleanVirtualExtensionWarp_or_otherOwner
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.LastSourceFirstPrefix.restoredWarp_roots_owner_and_sourceGroundedHit
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.otherVirtualOwner_mem_hangingPaths
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.LastSourceFirstPrefix.exists_virtualTransferPath_to_laterOwnerVertex
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.LastSourceFirstPrefix.virtualTransfer_roots_or_strictlyEarlier
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.virtualOwner_strictPrefixObligations_finite
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.LastSourceFirstPrefix.exists_virtualHangingOwnerSpliceWarp
