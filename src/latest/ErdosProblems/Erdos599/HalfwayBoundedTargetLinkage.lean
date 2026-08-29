/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCurrentTargetRow
import ErdosProblems.Erdos599.HalfwayStageGeometry
import ErdosProblems.Erdos599.SliceDeltaLift
import ErdosProblems.Erdos599.RegularCandidateProvider
import ErdosProblems.Erdos599.GroundingSuccessorRoofTransport

/-!
# Simultaneous target linkages for a bounded set of requests

The half-way construction eventually has at most `kappa` pending terminals,
not necessarily exactly `kappa` of them.  Restricting the ambient source to
that request set preserves unhinderedness.  The lower induction hypothesis
handles the strict-cardinality case and the current extension clause handles
the equality case.  This produces one genuine linkage, so the selected target
tails are pairwise disjoint; choosing the tails independently would not give
the relation geometry required by the global scheduler.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace CardinalInduction

open DirectedPath

universe u

variable {V : Type u}

/-- Every `kappa`-bounded subset of the source of a normalized unhindered web
has a simultaneous linkage to the ambient target. -/
theorem exists_designatedSourceLinkage_of_mk_le
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hext : UniversalExtensionClauseAt V kappa)
    (G : DWeb V) (hG : G.IsUnhindered) (hNorm : G.IsNormalized)
    {A : Set V} (hA : A ⊆ G.source) (hcard : #A ≤ kappa) :
    ∃ P : Set G.DPath, IsLinkageBetween G A G.target P := by
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro u v huv hv
    exact (hNorm huv).1 hv
  have hsubUnhindered : (G.sourceSubweb A).IsUnhindered :=
    hG.sourceSubweb G hNoEnter hA
  have hlinkable : IsLinkable (G.sourceSubweb A) := by
    apply isLinkable_of_source_mk_le_current hlower hext
      (G.sourceSubweb A) hsubUnhindered
    simpa only [DWeb.sourceSubweb_source] using hcard
  obtain ⟨P, hP⟩ := hlinkable
  change IsLinkageBetween G A G.target P at hP
  exact ⟨P, hP⟩

#print axioms exists_designatedSourceLinkage_of_mk_le

end CardinalInduction

namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Ladder

variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- The stage-web form of the bounded target linkage.  Keeping the paths in
the stage web retains the one-point roof-incidence information used when all
target tails are attached simultaneously. -/
theorem ClubStageGeometry.exists_newStageTargetLinkage_of_mk_le
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hlower : CardinalInduction.UniversalCardinalInductionBelow V kappa)
    (hext : CardinalInduction.UniversalExtensionClauseAt V kappa)
    {A : Set V} (hA : A ⊆ C.newSlice) (hcard : #A ≤ kappa) :
    ∃ P : Set (C.ladder.stageWeb C.newStage).DPath,
      CardinalInduction.IsLinkageBetween
        (C.ladder.stageWeb C.newStage) A
          (C.ladder.stageWeb C.newStage).target P := by
  let H := C.ladder.stageWeb C.newStage
  have hNorm : H.IsNormalized :=
    CardinalInduction.RegularCandidateProvider.stageWeb_isNormalized
      C.normalized C.ladder C.newStage
  exact CardinalInduction.exists_designatedSourceLinkage_of_mk_le
    hlower hext H C.newStage_isUnhindered hNorm hA hcard

/-- A bounded set on the later club frontier has one simultaneous ambient
target linkage.  The construction is performed in the genuine later stage
web, whose source is definitionally that frontier, and then lifted back to
the ambient web. -/
theorem ClubStageGeometry.exists_newSliceTargetLinkage_of_mk_le
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hlower : CardinalInduction.UniversalCardinalInductionBelow V kappa)
    (hext : CardinalInduction.UniversalExtensionClauseAt V kappa)
    {A : Set V} (hA : A ⊆ C.newSlice) (hcard : #A ≤ kappa) :
    ∃ P : Set Gamma.DPath,
      CardinalInduction.IsLinkageBetween Gamma A Gamma.target P := by
  obtain ⟨P, hP⟩ := C.exists_newStageTargetLinkage_of_mk_le
    hlower hext hA hcard
  exact ⟨CardinalInduction.SliceSegmentCore.liftStageFamily
      C.ladder C.newStage P,
    CardinalInduction.SliceDeltaLift.IsLinkageBetween.liftStageFamily hP⟩

/-- A target linkage lifted out of the later stage meets the complete old
side of the frontier exactly in its prescribed initial set.  This is the
cross-incidence fact needed to adjoin all selected target tails to a roofed
macro relation without creating a second incoming or outgoing edge. -/
theorem ClubStageGeometry.vertexSet_liftNewStageFamily_inter_outerRoof
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {A : Set V} {P : Set (C.ladder.stageWeb C.newStage).DPath}
    (hA : A ⊆ C.newSlice)
    (hP : CardinalInduction.IsLinkageBetween
      (C.ladder.stageWeb C.newStage) A
        (C.ladder.stageWeb C.newStage).target P) :
    Gamma.vertexSet
        (CardinalInduction.SliceSegmentCore.liftStageFamily
          C.ladder C.newStage P) ∩ C.outerRoof = A := by
  apply Set.Subset.antisymm
  · rintro x ⟨⟨q, hq, hxq⟩, hxRoof⟩
    rw [CardinalInduction.SliceSegmentCore.mem_liftStageFamily] at hq
    obtain ⟨r, hrP, rfl⟩ := hq
    have hxeq : x = r.initial := by
      by_contra hxne
      have hxRawRoof : x ∈ Gamma.roof
          (Gamma.terminalFrontier (C.ladder.warpAt C.newStage)) := by
        rw [← Gamma.roof_essential,
          ← C.ladder.frontier_eq_essential_terminalFrontier
            C.legal.roofsSourceAtStages C.newStage]
        exact hxRoof
      exact (C.ladder.liftStagePath_not_mem_roof_of_ne_initial
        C.newStage r hxq hxne) hxRawRoof
    rw [hxeq, ← hP.initialSet_eq]
    exact ⟨r, hrP, rfl⟩
  · intro x hxA
    have hxInitial : x ∈
        (C.ladder.stageWeb C.newStage).initialSet P :=
      hP.initialSet_eq.symm ▸ hxA
    obtain ⟨p, hpP, hpInitial⟩ := hxInitial
    refine ⟨?_, Gamma.subset_roof C.newSlice ?_⟩
    · refine ⟨C.ladder.liftStagePath C.newStage p, ?_, ?_⟩
      · rw [CardinalInduction.SliceSegmentCore.mem_liftStageFamily]
        exact ⟨p, hpP, rfl⟩
      · change x ∈ (C.ladder.liftStagePath C.newStage p).support
        rw [C.ladder.support_liftStagePath, ← hpInitial]
        exact p.initial_mem_support
    · exact hA hxA

#print axioms ClubStageGeometry.exists_newSliceTargetLinkage_of_mk_le
#print axioms ClubStageGeometry.exists_newStageTargetLinkage_of_mk_le
#print axioms ClubStageGeometry.vertexSet_liftNewStageFamily_inter_outerRoof

end LinkageBlueprint
end Blueprint
end Erdos599
