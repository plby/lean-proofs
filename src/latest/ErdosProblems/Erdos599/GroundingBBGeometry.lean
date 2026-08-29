/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingErasedDecode
import ErdosProblems.Erdos599.WaveLimits

/-!
# Component geometry at the grounding cut

This file isolates two elementary, but useful, parts of the geometry at the
end of Assertion 8.22.

First, every point of `BB` is either an old cut point which was already an
auxiliary source, the exit of an actual old-vertex switching request, or the
blocking point of a retained deleted fragment.  This is the exact case split
needed by the switched-relation argument; in particular it does not pretend
that old auxiliary sources give rise to requests.

Second, once the literal switched relation has shown that `BB` lies in the
terminal frontier of its realizing warp, all componentwise uniqueness is
formal.  A member of a warp which contains a frontier point has that point as
its own terminal, and hence cannot contain two such points.  The same
observation turns the pathwise source-rootedness statement into the precise
coverage statement used by the pruning construction.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingBBGeometry

open DirectedPath PopularGroundingBridge GroundingErasedDecode

universe u

variable {V I : Type u} {Gamma : DWeb V}

/-- Every point of the old-vertex part of the auxiliary cut is either an
old auxiliary source or the exit of the corresponding old request. -/
theorem mem_CV_finiteSource_or_oldRequestExit
    {L : PopularAuxiliary.Input Gamma I} {C : Set L.LV} {x : V}
    (hx : x ∈ GroundingCut.CV L C) :
    x ∈ L.finiteSource ∨
      ∃ r : Request L C, requestAuxVertex r = .old x ∧ requestExit r = x := by
  by_cases hxSource : x ∈ L.finiteSource
  · exact Or.inl hxSource
  · let r : Request L C := Sum.inl ⟨x, hx, hxSource⟩
    exact Or.inr ⟨r, rfl, rfl⟩

/-- Concrete trichotomy for the points of `BB`.  The final case retains the
fragment itself, its membership in `G0`, and the literal blocking-point
equality, so downstream relation proofs do not need to reopen an image-set
membership proof. -/
theorem mem_BB_finiteSource_or_oldRequestExit_or_blockingPoint
    {L : PopularAuxiliary.Input Gamma I} {C : Set L.LV} {x : V}
    (hx : x ∈ GroundingCut.BB L C) :
    x ∈ L.finiteSource ∨
      (∃ r : Request L C,
        requestAuxVertex r = .old x ∧ requestExit r = x) ∨
      ∃ P : L.Fragment, P ∈ GroundingCut.G0 L C ∧
        GroundingCut.IsBlockable L C P ∧
        GroundingCut.blockingPoint L C P = x ∧ x ∈ P.path.support := by
  rcases hx with hxCV | hxBL
  · rcases mem_CV_finiteSource_or_oldRequestExit hxCV with hxSource | hxRequest
    · exact Or.inl hxSource
    · exact Or.inr (Or.inl hxRequest)
  · obtain ⟨P, hP, hxEq, hxSupport⟩ :=
      GroundingCut.BL_covered_by_G0 hxBL
    exact Or.inr (Or.inr ⟨P, hP, hP.2, hxEq.symm, hxSupport⟩)

/-- Strengthened form of
`mem_BB_finiteSource_or_oldRequestExit_or_blockingPoint` which remembers that
a finite-source point arising from the `CV` half of `BB` is still an old
vertex of the auxiliary cut.  This is the form needed to recover its
canonical cut-source parent. -/
theorem mem_BB_finiteSourceWithCut_or_oldRequestExit_or_blockingPoint
    {L : PopularAuxiliary.Input Gamma I} {C : Set L.LV} {x : V}
    (hx : x ∈ GroundingCut.BB L C) :
    (x ∈ L.finiteSource ∧
        (PopularAuxiliary.Input.LambdaVertex.old x : L.LV) ∈ C) ∨
      (∃ r : Request L C,
        requestAuxVertex r = .old x ∧ requestExit r = x) ∨
      ∃ P : L.Fragment, P ∈ GroundingCut.G0 L C ∧
        GroundingCut.IsBlockable L C P ∧
        GroundingCut.blockingPoint L C P = x ∧ x ∈ P.path.support := by
  rcases hx with hxCV | hxBL
  · have hxCut :
        (PopularAuxiliary.Input.LambdaVertex.old x : L.LV) ∈ C :=
      GroundingCut.mem_CV.mp hxCV
    rcases mem_CV_finiteSource_or_oldRequestExit hxCV with hxSource | hxRequest
    · exact Or.inl ⟨hxSource, hxCut⟩
    · exact Or.inr (Or.inl hxRequest)
  · obtain ⟨P, hP, hxEq, hxSupport⟩ :=
      GroundingCut.BL_covered_by_G0 hxBL
    exact Or.inr (Or.inr ⟨P, hP, hP.2, hxEq.symm, hxSupport⟩)

/-- A vertex which is either an explicitly retained singleton or is incident
with an edge of exact switch data belongs to every realizing warp.  This is
the coverage bridge appropriate for `BB`: unlike the terminal-frontier
bridge below, it makes no false sink assertion. -/
theorem mem_vertexSet_of_realized_isolated_or_incident
    {S : Alternating.SwitchData Gamma} {W : Set Gamma.DPath}
    (hR : S.RealizedBy W) {x : V}
    (hx : x ∈ S.isolated ∨
      x ∈ Alternating.RelationDecomposition.IncidentVertices S.edges) :
    x ∈ Gamma.vertexSet W := by
  rcases hx with hxIso | hxIncident
  · have hxIsoW : x ∈ Alternating.isolatedVertices W := by
      rw [hR.2.2]
      exact hxIso
    exact ⟨Gamma.trivialPath x, hxIsoW, by simp⟩
  · obtain ⟨y, hxy | hyx⟩ := hxIncident
    · have hxyW : (x, y) ∈ Alternating.familyEdges W := by
        rw [hR.2.1]
        exact hxy
      simp only [Alternating.familyEdges, Set.mem_iUnion] at hxyW
      obtain ⟨p, hpW, hxyP⟩ := hxyW
      exact ⟨p, hpW, (p.edgeSet_subset_support_prod hxyP).1⟩
    · have hyxW : (y, x) ∈ Alternating.familyEdges W := by
        rw [hR.2.1]
        exact hyx
      simp only [Alternating.familyEdges, Set.mem_iUnion] at hyxW
      obtain ⟨p, hpW, hyxP⟩ := hyxW
      exact ⟨p, hpW, (p.edgeSet_subset_support_prod hyxP).2⟩

/-- Set-valued form of the exact isolated-or-incident coverage bridge. -/
theorem subset_vertexSet_of_realized_isolated_or_incident
    {S : Alternating.SwitchData Gamma} {W : Set Gamma.DPath}
    (hR : S.RealizedBy W) {B : Set V}
    (hB : B ⊆ S.isolated ∪
      Alternating.RelationDecomposition.IncidentVertices S.edges) :
    B ⊆ Gamma.vertexSet W := by
  intro x hx
  exact mem_vertexSet_of_realized_isolated_or_incident hR (hB hx)

/-- A component of a warp meets its terminal frontier in at most one point.
This holds equally for finite components and rays; a ray cannot contain a
terminal-frontier point at all. -/
theorem component_inter_terminalFrontier_subsingleton
    {W : Set Gamma.DPath} (hW : Gamma.IsWarp W)
    {p : Gamma.DPath} (hp : p ∈ W) :
    (p.support ∩ Gamma.terminalFrontier W).Subsingleton := by
  intro x hx y hy
  have htx : Gamma.terminal? p = some x :=
    DWeb.IsWarp.terminal_eq_of_mem_support_mem_terminalFrontier
      Gamma hW hp hx.1 hx.2
  have hty : Gamma.terminal? p = some y :=
    DWeb.IsWarp.terminal_eq_of_mem_support_mem_terminalFrontier
      Gamma hW hp hy.1 hy.2
  exact Option.some.inj (htx.symm.trans hty)

/-- Any subset of a realizing warp's terminal frontier is met at most once
by every component. -/
theorem component_inter_subsingleton_of_subset_terminalFrontier
    {W : Set Gamma.DPath} (hW : Gamma.IsWarp W) {B : Set V}
    (hB : B ⊆ Gamma.terminalFrontier W)
    {p : Gamma.DPath} (hp : p ∈ W) :
    (p.support ∩ B).Subsingleton := by
  intro x hx y hy
  exact component_inter_terminalFrontier_subsingleton hW hp
    ⟨hx.1, hB hx.2⟩ ⟨hy.1, hB hy.2⟩

/-- A relation-level sink (or an explicitly retained isolated vertex) is a
terminal-frontier point of every warp realizing the switch data.  This is
the small boundary bridge used to turn concrete incidence calculations for
the erased switched relation into component geometry. -/
theorem subset_terminalFrontier_of_realized_sinks
    {S : Alternating.SwitchData Gamma} {W : Set Gamma.DPath}
    (hR : S.RealizedBy W) {B : Set V}
    (hsink : ∀ x ∈ B,
      x ∈ S.isolated ∨
        (Alternating.HasIncoming S.edges x ∧
          ¬ Alternating.HasOutgoing S.edges x)) :
    B ⊆ Gamma.terminalFrontier W := by
  intro x hx
  rw [Alternating.mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one_anyWarp
    hR.1, hR.2.1, hR.2.2]
  rcases hsink x hx with hxIso | hxSink
  · exact Or.inl hxIso
  · exact Or.inr <| Alternating.edgeBalance_eq_neg_one_iff.2 hxSink

/-- If all components meeting `B` start in the original source, then
terminal-frontier containment gives exactly the source-starting coverage
used by the Assertion 8.22 pruning step. -/
theorem subset_vertexSet_sourceComponents_of_subset_terminalFrontier
    {W : Set Gamma.DPath} {B : Set V}
    (hB : B ⊆ Gamma.terminalFrontier W)
    (hsource : ∀ p : Gamma.DPath, p ∈ W →
      (∃ x ∈ p.support, x ∈ B) → p.initial ∈ Gamma.source) :
    B ⊆ Gamma.vertexSet {p | p ∈ W ∧ p.initial ∈ Gamma.source} := by
  intro b hb
  obtain ⟨p, hpW, hpTerminal⟩ := hB hb
  have hbp : b ∈ p.support := Gamma.terminal_mem_support hpTerminal
  exact ⟨p, ⟨hpW, hsource p hpW ⟨b, hbp, hb⟩⟩, hbp⟩

/-- Specialized reduction for the grounding set `BB`: the two relation-level
facts needed from the literal switch imply both geometric inputs consumed by
the generic pruning construction. -/
theorem bb_coverage_and_component_uniqueness
    {L : PopularAuxiliary.Input Gamma I} {C : Set L.LV}
    {W : Set Gamma.DPath} (hW : Gamma.IsWarp W)
    (hterminal : GroundingCut.BB L C ⊆ Gamma.terminalFrontier W)
    (hsource : ∀ p : Gamma.DPath, p ∈ W →
      (∃ x ∈ p.support, x ∈ GroundingCut.BB L C) →
        p.initial ∈ Gamma.source) :
    GroundingCut.BB L C ⊆
        Gamma.vertexSet {p | p ∈ W ∧ p.initial ∈ Gamma.source} ∧
      ∀ p : Gamma.DPath, p ∈ W →
        (p.support ∩ GroundingCut.BB L C).Subsingleton := by
  exact ⟨subset_vertexSet_sourceComponents_of_subset_terminalFrontier
      hterminal hsource,
    fun p hp ↦ component_inter_subsingleton_of_subset_terminalFrontier
      hW hterminal hp⟩

end GroundingBBGeometry
end Erdos599
