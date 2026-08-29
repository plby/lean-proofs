/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredStageReferenceEmbedding
import ErdosProblems.Erdos599.UncountableWarpLimitAttainment
import ErdosProblems.Erdos599.SingularCardinal
import ErdosProblems.Erdos599.SeededHammock

/-!
# Eventual stage safeness of one globally safe alternating path

For one fixed alternating path `Q`, only countably many members of a warp can
meet `Q.vertexSet`.  At an uncountable regular direct limit those particular
limiting members occur literally together at one stage, and persist at every
later stage.  Once they are present, safeness for the limiting reference
reflects to the stage reference.

This is deliberately a pathwise statement.  It neither selects one stage
for an entire hammock nor claims that stage-local maximality automatically
transfers to the limiting reference.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

open DirectedPath Alternating Ladder

universe u

variable {V : Type u} {Gamma : DWeb V}
variable {kappa : Cardinal.{u}}

namespace Blueprint.ReferenceSubpathEmbedding

variable {Local Global : Set Gamma.DPath}

/-- The global reference members whose carriers meet one fixed alternating
path.  These, and only these, must be attained literally before reflecting
global safeness to a local subpath reference. -/
def pathsMeetingAltPath (Gamma : DWeb V) (Global : Set Gamma.DPath)
    (Q : AltPath Gamma.graph) : Set Gamma.DPath :=
  {p | p ∈ Global ∧ ¬ Disjoint p.support Q.vertexSet}

@[simp] theorem mem_pathsMeetingAltPath {Q : AltPath Gamma.graph}
    {p : Gamma.DPath} :
    p ∈ pathsMeetingAltPath Gamma Global Q ↔
      p ∈ Global ∧ ¬ Disjoint p.support Q.vertexSet :=
  Iff.rfl

private theorem vertexSet_subset
    (E : ReferenceSubpathEmbedding Gamma Local Global) :
    Gamma.vertexSet Local ⊆ Gamma.vertexSet Global := by
  rintro x ⟨p, hp, hxp⟩
  let ps : Local := ⟨p, hp⟩
  exact ⟨(E.owner ps).1, (E.owner ps).2, E.support_subset ps hxp⟩

private theorem directionEdge_endpoints_mem_vertexSet
    (Q : AltPath Gamma.graph) {d : Direction} {e : V × V}
    (he : e ∈ Q.directionEdges d) :
    e.1 ∈ Q.vertexSet ∧ e.2 ∈ Q.vertexSet := by
  simp only [AltPath.directionEdges, Set.mem_iUnion] at he
  obtain ⟨l, hl, _hd, hel⟩ := he
  have hend := l.path.edgeSet_subset_support_prod hel
  exact ⟨Q.link_support_subset_vertexSet hl hend.1,
    Q.link_support_subset_vertexSet hl hend.2⟩

/-- On edges of `Q`, a local reference containing every global member which
meets `Q` has exactly the same reference-edge incidence as the global one. -/
theorem edgeSet_sdiff_familyEdges_eq_of_pathsMeeting_subset
    (E : ReferenceSubpathEmbedding Gamma Local Global)
    {Q : AltPath Gamma.graph}
    (hcapture : pathsMeetingAltPath Gamma Global Q ⊆ Local) :
    Q.edgeSet \ familyEdges Local = Q.edgeSet \ familyEdges Global := by
  ext e
  simp only [Set.mem_sdiff]
  constructor
  · rintro ⟨heQ, heLocal⟩
    refine ⟨heQ, ?_⟩
    intro heGlobal
    simp only [familyEdges, Set.mem_iUnion] at heGlobal
    obtain ⟨p, hp, hep⟩ := heGlobal
    have heEnds := Q.edgeSet_subset_vertexSet_prod heQ
    have hpMeet : p ∈ pathsMeetingAltPath Gamma Global Q := by
      refine ⟨hp, Set.not_disjoint_iff.mpr ?_⟩
      exact ⟨e.1, (p.edgeSet_subset_support_prod hep).1, heEnds.1⟩
    apply heLocal
    simp only [familyEdges, Set.mem_iUnion]
    exact ⟨p, hcapture hpMeet, hep⟩
  · rintro ⟨heQ, heGlobal⟩
    refine ⟨heQ, ?_⟩
    intro heLocal
    exact heGlobal (E.familyEdges_subset heLocal)

/-- If every global reference member meeting `Q` is literally in the local
reference, global safeness reflects to the local reference.  Members of the
local family which do not meet `Q` may still be proper subpaths of their
global owners. -/
theorem isSafe_local_of_global_of_pathsMeeting_subset
    (E : ReferenceSubpathEmbedding Gamma Local Global)
    (hLocal : Gamma.IsWarp Local)
    {Q : AltPath Gamma.graph} (hQ : IsSafe Global Q)
    (hcapture : pathsMeetingAltPath Gamma Global Q ⊆ Local) :
    IsSafe Local Q := by
  have hbackward : BackwardLinksOn Local Q := by
    intro l hl hdir
    obtain ⟨p, hp, hlp⟩ := hQ.1.2.1 l hl hdir
    have hpMeet : p ∈ pathsMeetingAltPath Gamma Global Q := by
      refine ⟨hp, Set.not_disjoint_iff.mpr ?_⟩
      exact ⟨l.path.start, hlp.1 l.path.start_mem_support,
        Q.link_support_subset_vertexSet hl l.path.start_mem_support⟩
    exact ⟨p, hcapture hpMeet, hlp⟩
  refine ⟨⟨hLocal, hbackward, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro hfirst hinitialLocal
    exact hQ.1.2.2.1 hfirst (E.vertexSet_subset hinitialLocal)
  · intro t hterminal hlast hterminalLocal
    exact hQ.1.2.2.2 t hterminal hlast
      (E.vertexSet_subset hterminalLocal)
  · intro q hq
    by_cases hempty :
        Q.directionEdges .backward ∩ q.edgeSet = ∅
    · exact Or.inl hempty
    · obtain ⟨e, heBack, heq⟩ := Set.nonempty_iff_ne_empty.mpr hempty
      let qs : Local := ⟨q, hq⟩
      have heEnds := directionEdge_endpoints_mem_vertexSet Q heBack
      have hownerMeet : (E.owner qs).1 ∈
          pathsMeetingAltPath Gamma Global Q := by
        refine ⟨(E.owner qs).2, Set.not_disjoint_iff.mpr ?_⟩
        exact ⟨e.1, E.edgeSet_subset qs heq
          |> (E.owner qs).1.edgeSet_subset_support_prod |>.1, heEnds.1⟩
      have hownerLocal : (E.owner qs).1 ∈ Local :=
        hcapture hownerMeet
      have hqowner : q = (E.owner qs).1 := by
        apply DWeb.IsWarp.eq_of_mem_support hLocal hq hownerLocal
        · exact (q.edgeSet_subset_support_prod heq).1
        · exact ((E.owner qs).1.edgeSet_subset_support_prod
            (E.edgeSet_subset qs heq)).1
      simpa only [hqowner] using hQ.2.1 (E.owner qs).1 (E.owner qs).2
  · rw [E.edgeSet_sdiff_familyEdges_eq_of_pathsMeeting_subset hcapture]
    exact hQ.2.2.1
  · rw [E.edgeSet_sdiff_familyEdges_eq_of_pathsMeeting_subset hcapture]
    exact hQ.2.2.2

#print axioms edgeSet_sdiff_familyEdges_eq_of_pathsMeeting_subset
#print axioms isSafe_local_of_global_of_pathsMeeting_subset

end Blueprint.ReferenceSubpathEmbedding

namespace DWeb.KappaLadder.Deferred

variable {L : Gamma.KappaLadder kappa}

/-- The limiting reference members meeting one fixed alternating path form
a countable family. -/
theorem HalfwayGeometry.pathsMeetingAltPath_countable
    (hL : HalfwayGeometry L) (Q : AltPath Gamma.graph) :
    (Blueprint.ReferenceSubpathEmbedding.pathsMeetingAltPath
      Gamma L.limitWarp Q).Countable := by
  rw [← Cardinal.le_aleph0_iff_set_countable]
  exact (Gamma.mk_pathsMeeting_le L.limitWarp Q.vertexSet
    (hL.warpStages (Ladder.finalStage kappa))).trans
      (Blueprint.altPath_vertexSet_countable Q).le_aleph0

/-- Every fixed path safe for the limiting reference is safe for the full
stage warp at all sufficiently late ordinary stages. -/
theorem HalfwayGeometry.exists_eventually_isSafe_warpAt
    (hL : HalfwayGeometry L) (Q : AltPath Gamma.graph)
    (hQ : IsSafe L.limitWarp Q) :
    ∃ a : Ladder.Stage kappa, ∀ b, a ≤ b → IsSafe (L.warpAt b) Q := by
  let P := Blueprint.ReferenceSubpathEmbedding.pathsMeetingAltPath
    Gamma L.limitWarp Q
  have hPsmall : #P < kappa :=
    (hL.pathsMeetingAltPath_countable Q).le_aleph0.trans_lt hL.uncountable
  have hlimit : Order.IsSuccLimit kappa.ord :=
    Cardinal.isSuccLimit_ord hL.regular.aleph0_le
  obtain ⟨C, hstage, hfinal⟩ :=
    hL.limitStages (Ladder.finalStage kappa) hlimit
  have hP_limit : P ⊆ C.limitPaths Gamma := by
    intro p hp
    rw [← hfinal]
    exact hp.1
  obtain ⟨a, ha⟩ := C.exists_stage_subset_of_small_limitFamily
    hL.regular hL.uncountable hP_limit hPsmall
  refine ⟨a, ?_⟩
  intro b hab
  apply (hL.stageReferenceEmbedding b).isSafe_local_of_global_of_pathsMeeting_subset
    (hL.warpStages (Ladder.Stage.toExtended b)) hQ
  intro p hp
  have hpStage := ha b hab hp
  rw [hstage b] at hpStage
  exact hpStage

#print axioms HalfwayGeometry.pathsMeetingAltPath_countable
#print axioms HalfwayGeometry.exists_eventually_isSafe_warpAt

end DWeb.KappaLadder.Deferred
end Erdos599
