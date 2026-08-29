/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LadderMarkerDisjoint
import ErdosProblems.Erdos599.LadderSuccessorSelfRoof

/-!
# Looseness after exhaustion of the ladder markers

At an active canonical state with no marker candidate, the successor is just
the canonical arrow.  Every vertex which can occur in the essential quotient
after that arrow is already either an old stage source or a vertex of the
chosen rung.  Both kinds of vertices are roofed by the new arrow frontier.
The quotient definition therefore forbids an edge entering any
target-reachable vertex.  Thus the next essential stage has no edges and is
loose.
-/

noncomputable section

namespace Erdos599

open Set DirectedPath

universe u

namespace DWeb

variable {V : Type u} (G : DWeb V)

/-- A path in a digraph without edges is the trivial path at its initial
vertex.  The ray case is impossible already at its first edge. -/
theorem path_eq_trivialPath_of_not_adj
    (Q : DWeb V) (hno : ∀ {x y : V}, Q.graph.Adj x y → False)
    (p : Q.DPath) : p = Q.trivialPath p.initial := by
  rcases p with p | r
  · rcases p with ⟨a, b, w, hw⟩
    cases w with
    | nil => rfl
    | @cons _ c _ h q => exact False.elim (hno h)
  · exact False.elim (hno (r.adj_succ 0))

/-- If a web has no edges and all its sources can reach the target, then its
only wave is the trivial wave. -/
theorem isLoose_of_not_adj_of_source_subset_reachableToTarget
    (Q : DWeb V) (hno : ∀ {x y : V}, Q.graph.Adj x y → False)
    (hreach : Q.source ⊆ Q.reachableToTarget) : Q.IsLoose := by
  intro W hW
  apply Set.Subset.antisymm
  · intro p hp
    have hpEq := Q.path_eq_trivialPath_of_not_adj hno p
    refine ⟨p.initial, hW.2.1 ⟨p, hp, rfl⟩, ?_⟩
    exact hpEq.symm
  · rintro _ ⟨x, hxSource, rfl⟩
    obtain ⟨p, hpStart, hpTarget⟩ := hreach hxSource
    have hpEq : (Sum.inl p : Q.DPath) = Q.trivialPath x := by
      have h := Q.path_eq_trivialPath_of_not_adj hno (Sum.inl p : Q.DPath)
      calc
        (Sum.inl p : Q.DPath) = Q.trivialPath p.start := h
        _ = Q.trivialPath x := congrArg Q.trivialPath hpStart
    obtain ⟨y, hyp, hyW⟩ := hW.2.2 hxSource p ⟨hpStart, hpTarget⟩
    have hyx : y = x := by
      have : y ∈ (Q.trivialPath x).support := by
        rw [← hpEq]
        exact hyp
      simpa using this
    subst y
    obtain ⟨q, hqW, hqTerminal⟩ := hyW
    have hqEq := Q.path_eq_trivialPath_of_not_adj hno q
    have hInitial : q.initial = x := by
      rw [hqEq, Q.terminal?_trivialPath] at hqTerminal
      exact Option.some.inj hqTerminal
    have : q = Q.trivialPath x := by simpa [hInitial] using hqEq
    rwa [← this]

/-- Reachability is unchanged by passage to the essential induced subweb in
the direction needed here. -/
theorem mem_essentialPart_reachableToTarget_of_mem'
    (Q : DWeb V) {x : V} (hx : x ∈ Q.reachableToTarget) :
    x ∈ Q.essentialPart.reachableToTarget := by
  obtain ⟨p, hpStart, hpFinish⟩ := hx
  have hsupport : p.support ⊆ Q.reachableToTarget :=
    Q.finitePath_support_subset_reachableToTarget p hpFinish
  let q : FinitePath Q.essentialPart.graph :=
    p.restrictGraphOnSupport fun e hu hv ↦ ⟨e, hsupport hu, hsupport hv⟩
  exact ⟨q,
    by simpa only [q, FinitePath.restrictGraphOnSupport] using hpStart,
    by
      change q.finish ∈ Q.target
      simpa only [q, FinitePath.restrictGraphOnSupport] using hpFinish⟩

/-- The two cross-roof hypotheses for the canonical arrow, exposed together
for the exhaustion calculation. -/
theorem canonicalArrow_crossRoof
    (hNoEnter : G.NoEdgeEnters G.source)
    (s : G.LadderAccumulationState)
    (hwarp : G.IsWarp s.1)
    (hself : G.vertexSet s.1 ⊆ G.roof (G.terminalFrontier s.1))
    (hsource : G.source ⊆ G.roof (G.terminalFrontier s.1)) :
    G.initialSet (s.1 ∪ G.liftedLadderRungOfState s) ⊆
        G.roof (G.terminalFrontier s.1) ∧
      G.initialSet (s.1 ∪ G.liftedLadderRungOfState s) ⊆
        G.roof (G.terminalFrontier (G.liftedLadderRungOfState s)) := by
  let R := G.liftedLadderRungOfState s
  have hRinitial : G.initialSet R ⊆
      G.essential (G.terminalFrontier s.1) :=
    G.initialSet_liftedLadderRungOfState_subset_essential s hsource
  have hEssR : G.essential (G.terminalFrontier s.1) ⊆
      G.roof (G.terminalFrontier R) :=
    G.essential_subset_roof_terminalFrontier_liftedLadderRungOfState
      hNoEnter s
  have hOldRoofR : G.roof (G.terminalFrontier s.1) ⊆
      G.roof (G.terminalFrontier R) := by
    rw [← G.roof_essential (G.terminalFrontier s.1)]
    exact G.roof_cut hEssR
  constructor
  · rw [G.initialSet_union]
    intro x hx
    rcases hx with hxOld | hxR
    · exact hself (G.initialSet_subset_vertexSet' s.1 hxOld)
    · exact G.essential_subset_roof _ (hRinitial hxR)
  · rw [G.initialSet_union]
    intro x hx
    rcases hx with hxOld | hxR
    · exact hOldRoofR
        (hself (G.initialSet_subset_vertexSet' s.1 hxOld))
    · exact hEssR (hRinitial hxR)

/-- With no candidates, the optional marker family is empty and the active
successor is literally the canonical arrow. -/
theorem activeLadderSuccessor_eq_arrow_of_candidates_empty
    (preferred : Option V) (s : G.LadderAccumulationState)
    (hactive : s.2 = true)
    (hempty : G.ladderMarkerCandidatesOfState s = ∅) :
    G.activeLadderSuccessor preferred s =
      G.arrow s.1 (G.liftedLadderRungOfState s) := by
  have hm : G.ladderMarkerOfState preferred s = none :=
    (G.ladderMarkerOfState_eq_none_iff preferred s hactive).2 hempty
  simp [activeLadderSuccessor, ladderMarkerPathSetOfState, hm]

/-- The recursive successor flag switches permanently to `false` at the
first exhausted active state. -/
theorem ladderSuccessorState_eq_exhausted
    (preferred : Ordinal.{u} → Option V) (o : Ordinal.{u})
    (s : G.LadderAccumulationState)
    (hactive : s.2 = true)
    (hempty : G.ladderMarkerCandidatesOfState s = ∅) :
    G.ladderSuccessorState preferred o s =
      (G.activeLadderSuccessor (preferred o) s, false) := by
  rw [ladderSuccessorState, dif_pos hactive]
  simp [hempty]

/-- If the active state has exhausted its marker candidates, the essential
quotient stage after the canonical successor has no directed edge. -/
theorem not_adj_stageWebOf_activeLadderSuccessor_of_candidates_empty
    (hNoEnter : G.NoEdgeEnters G.source)
    (preferred : Option V) (s : G.LadderAccumulationState)
    (hactive : s.2 = true)
    (hwarp : G.IsWarp s.1)
    (hself : G.vertexSet s.1 ⊆ G.roof (G.terminalFrontier s.1))
    (hsource : G.source ⊆ G.roof (G.terminalFrontier s.1))
    (hempty : G.ladderMarkerCandidatesOfState s = ∅) :
    ∀ {x y : V},
      (G.stageWebOf (G.activeLadderSuccessor preferred s)).graph.Adj x y →
        False := by
  classical
  have hm : G.ladderMarkerOfState preferred s = none :=
    (G.ladderMarkerOfState_eq_none_iff preferred s hactive).2 hempty
  have hsucc : G.activeLadderSuccessor preferred s =
      G.arrow s.1 (G.liftedLadderRungOfState s) := by
    simp [activeLadderSuccessor, ladderMarkerPathSetOfState, hm]
  let A := G.terminalFrontier s.1
  let R := G.liftedLadderRungOfState s
  let S := G.arrow s.1 R
  let B := G.terminalFrontier R
  let T := G.terminalFrontier S
  let Q := G.quotient A
  let K := G.quotient T
  have hRwarp : G.IsWarp R := G.isWarp_liftedLadderRungOfState' s
  have hRself : G.vertexSet R ⊆ G.roof B := by
    simpa only [R, B] using
      G.liftedLadderRungOfState_self_roofing hNoEnter s
  have hcross := G.canonicalArrow_crossRoof hNoEnter s hwarp hself hsource
  have hroofA : G.roof A ⊆ G.roof T := by
    have h := G.roof_terminalFrontier_arrow_eq_union_of_crossRoof'
      hwarp hRwarp hself hRself hcross.1 hcross.2
    rw [show G.terminalFrontier S = T by rfl,
      show G.terminalFrontier s.1 = A by rfl,
      show G.terminalFrontier R = B by rfl] at h
    rw [h]
    exact G.roof_mono Set.subset_union_left
  have hroofB : G.roof B ⊆ G.roof T := by
    have h := G.roof_terminalFrontier_arrow_eq_union_of_crossRoof'
      hwarp hRwarp hself hRself hcross.1 hcross.2
    rw [show G.terminalFrontier S = T by rfl,
      show G.terminalFrontier s.1 = A by rfl,
      show G.terminalFrontier R = B by rfl] at h
    rw [h]
    exact G.roof_mono Set.subset_union_right
  have hessential : G.essential T = G.essential (A ∪ B) := by
    apply RelationalRoof.essential_sandwich G.graph.Adj G.target
    · change G.essential (A ∪ B) ⊆ T
      simpa only [A, R, S, B, T] using
        G.essential_union_subset_terminalFrontier_arrow_of_crossRoof
          hwarp hRwarp hself hRself hcross.1
    · simpa only [A, R, S, B, T] using
        G.terminalFrontier_arrow_subset_union s.1 R
  have hstrict : G.strictRoof A ⊆ G.strictRoof T := by
    intro z hz
    refine ⟨hroofA hz.1, ?_⟩
    intro hzEssential
    have hzUnion : z ∈ G.essential (A ∪ B) := hessential ▸ hzEssential
    have hzSmall : z ∈ G.roof (A \ {z}) := by
      rwa [← G.mem_strictRoof_iff_mem_roof_sdiff_singleton]
    exact hzUnion.2 (G.roof_mono (by
      intro w hw
      exact ⟨Or.inl hw.1, hw.2⟩) hzSmall)
  intro x y hxy
  rw [hsucc] at hxy
  change K.essentialPart.graph.Adj x y at hxy
  have hKy : K.graph.Adj x y := hxy.1
  have hyReachK : y ∈ K.reachableToTarget := hxy.2.2
  have hyReachQ : y ∈ Q.reachableToTarget := by
    obtain ⟨p, hpStart, hpTarget⟩ := hyReachK
    let q : FinitePath Q.graph := p.lift fun {u v} e ↦ by
      have eK : K.graph.Adj u v := e
      have huOld : u ∉ G.strictRoof A := fun hu ↦
        eK.2.1 (hstrict hu)
      have hvOld : v ∉ G.strictRoof A := fun hv ↦
        eK.2.2.1 (hstrict hv)
      have hvNotA : v ∉ A := by
        intro hvA
        have hvRoofT : v ∈ G.roof T := hroofA (G.subset_roof A hvA)
        have hvEssT : v ∈ G.essential T := by
          by_contra hvNotEss
          exact eK.2.2.1 ⟨hvRoofT, hvNotEss⟩
        exact eK.2.2.2 (G.essential_subset T hvEssT)
      exact ⟨eK.1, huOld, hvOld, hvNotA⟩
    exact ⟨q,
      by simpa only [q, FinitePath.lift] using hpStart,
      by
        change p.finish ∈ G.target at hpTarget
        change q.finish ∈ G.target
        simpa only [q, FinitePath.lift] using hpTarget⟩
  have hyStageReach : y ∈ (G.stageWebOf s.1).reachableToTarget := by
    change y ∈ Q.essentialPart.reachableToTarget
    exact Q.mem_essentialPart_reachableToTarget_of_mem' hyReachQ
  have hyOldQuotient : y ∈ G.quotientVertexSet A := by
    change y ∉ G.strictRoof A
    exact fun hyOld ↦ hKy.2.2.1 (hstrict hyOld)
  have hyCovered : y ∈ (G.stageWebOf s.1).source ∪
      (G.stageWebOf s.1).vertexSet (G.ladderRungOfState s) := by
    by_contra hyNot
    have hyCandidate : y ∈ G.ladderMarkerCandidatesOfState s :=
      ⟨⟨hyStageReach, hyOldQuotient⟩, hyNot⟩
    simpa [hempty] using hyCandidate
  have hyRoofT : y ∈ G.roof T := by
    rcases hyCovered with hySource | hyRung
    · have hyQSource : y ∈ Q.source := hySource.1
      have hyA : y ∈ G.essential A := by
        rw [← G.quotient_source_eq_essential_terminalFrontier_of_roofsSource
          hsource]
        exact hyQSource
      exact hroofA (G.subset_roof A (G.essential_subset A hyA))
    · have hyR : y ∈ G.vertexSet R := by
        simpa only [R, G.vertexSet_liftedLadderRungOfState s] using hyRung
      exact hroofB (hRself hyR)
  have hyEssT : y ∈ G.essential T := by
    by_contra hyNotEss
    exact hKy.2.2.1 ⟨hyRoofT, hyNotEss⟩
  exact hKy.2.2.2 (G.essential_subset T hyEssT)

/-- At the exhausted successor, every target-reachable vertex which survives
the new ambient quotient is already a source of the new essential stage.
This is the form which directly implies that the next marker-candidate set
is empty. -/
theorem stageWebOf_activeLadderSuccessor_surviving_reachable_subset_source
    (hNoEnter : G.NoEdgeEnters G.source)
    (preferred : Option V) (s : G.LadderAccumulationState)
    (hactive : s.2 = true)
    (hwarp : G.IsWarp s.1)
    (hself : G.vertexSet s.1 ⊆ G.roof (G.terminalFrontier s.1))
    (hsource : G.source ⊆ G.roof (G.terminalFrontier s.1))
    (hempty : G.ladderMarkerCandidatesOfState s = ∅) :
    (G.stageWebOf (G.activeLadderSuccessor preferred s)).reachableToTarget ∩
        G.quotientVertexSet
          (G.terminalFrontier (G.activeLadderSuccessor preferred s)) ⊆
      (G.stageWebOf (G.activeLadderSuccessor preferred s)).source := by
  classical
  have hm : G.ladderMarkerOfState preferred s = none :=
    (G.ladderMarkerOfState_eq_none_iff preferred s hactive).2 hempty
  have hsucc : G.activeLadderSuccessor preferred s =
      G.arrow s.1 (G.liftedLadderRungOfState s) := by
    simp [activeLadderSuccessor, ladderMarkerPathSetOfState, hm]
  let A := G.terminalFrontier s.1
  let R := G.liftedLadderRungOfState s
  let S := G.arrow s.1 R
  let B := G.terminalFrontier R
  let T := G.terminalFrontier S
  let Q := G.quotient A
  let K := G.quotient T
  have hRwarp : G.IsWarp R := G.isWarp_liftedLadderRungOfState' s
  have hRself : G.vertexSet R ⊆ G.roof B := by
    simpa only [R, B] using
      G.liftedLadderRungOfState_self_roofing hNoEnter s
  have hcross := G.canonicalArrow_crossRoof hNoEnter s hwarp hself hsource
  have hroofA : G.roof A ⊆ G.roof T := by
    have h := G.roof_terminalFrontier_arrow_eq_union_of_crossRoof'
      hwarp hRwarp hself hRself hcross.1 hcross.2
    rw [show G.terminalFrontier S = T by rfl,
      show G.terminalFrontier s.1 = A by rfl,
      show G.terminalFrontier R = B by rfl] at h
    rw [h]
    exact G.roof_mono Set.subset_union_left
  have hroofB : G.roof B ⊆ G.roof T := by
    have h := G.roof_terminalFrontier_arrow_eq_union_of_crossRoof'
      hwarp hRwarp hself hRself hcross.1 hcross.2
    rw [show G.terminalFrontier S = T by rfl,
      show G.terminalFrontier s.1 = A by rfl,
      show G.terminalFrontier R = B by rfl] at h
    rw [h]
    exact G.roof_mono Set.subset_union_right
  have hessential : G.essential T = G.essential (A ∪ B) := by
    apply RelationalRoof.essential_sandwich G.graph.Adj G.target
    · change G.essential (A ∪ B) ⊆ T
      simpa only [A, R, S, B, T] using
        G.essential_union_subset_terminalFrontier_arrow_of_crossRoof
          hwarp hRwarp hself hRself hcross.1
    · simpa only [A, R, S, B, T] using
        G.terminalFrontier_arrow_subset_union s.1 R
  have hstrict : G.strictRoof A ⊆ G.strictRoof T := by
    intro z hz
    refine ⟨hroofA hz.1, ?_⟩
    intro hzEssential
    have hzUnion : z ∈ G.essential (A ∪ B) := hessential ▸ hzEssential
    have hzSmall : z ∈ G.roof (A \ {z}) := by
      rwa [← G.mem_strictRoof_iff_mem_roof_sdiff_singleton]
    exact hzUnion.2 (G.roof_mono (by
      intro w hw
      exact ⟨Or.inl hw.1, hw.2⟩) hzSmall)
  intro y hy
  rw [hsucc] at hy ⊢
  change y ∈ K.essentialPart.reachableToTarget ∩
      G.quotientVertexSet T at hy
  change y ∈ K.essentialPart.source
  obtain ⟨p, hpStart, hpTarget⟩ := hy.1
  let pK : FinitePath K.graph :=
    p.lift (fun {_ _} e ↦ K.essentialPart_adj_imp e)
  have hyReachK : y ∈ K.reachableToTarget := by
    refine ⟨pK, ?_, ?_⟩
    · simpa only [pK, FinitePath.lift] using hpStart
    · change pK.finish ∈ G.target
      change p.finish ∈ G.target at hpTarget
      simpa only [pK, FinitePath.lift] using hpTarget
  have hyReachQ : y ∈ Q.reachableToTarget := by
    let q : FinitePath Q.graph := pK.lift fun {u v} e ↦ by
      have eK : K.graph.Adj u v := e
      have huOld : u ∉ G.strictRoof A := fun hu ↦
        eK.2.1 (hstrict hu)
      have hvOld : v ∉ G.strictRoof A := fun hv ↦
        eK.2.2.1 (hstrict hv)
      have hvNotA : v ∉ A := by
        intro hvA
        have hvRoofT : v ∈ G.roof T := hroofA (G.subset_roof A hvA)
        have hvEssT : v ∈ G.essential T := by
          by_contra hvNotEss
          exact eK.2.2.1 ⟨hvRoofT, hvNotEss⟩
        exact eK.2.2.2 (G.essential_subset T hvEssT)
      exact ⟨eK.1, huOld, hvOld, hvNotA⟩
    exact ⟨q,
      by simpa only [q, pK, FinitePath.lift] using hpStart,
      by
        change p.finish ∈ G.target at hpTarget
        change q.finish ∈ G.target
        simpa only [q, pK, FinitePath.lift] using hpTarget⟩
  have hyStageReach : y ∈ (G.stageWebOf s.1).reachableToTarget := by
    change y ∈ Q.essentialPart.reachableToTarget
    exact Q.mem_essentialPart_reachableToTarget_of_mem' hyReachQ
  have hyOldQuotient : y ∈ G.quotientVertexSet A := by
    change y ∉ G.strictRoof A
    exact fun hyOld ↦ hy.2 (hstrict hyOld)
  have hyCovered : y ∈ (G.stageWebOf s.1).source ∪
      (G.stageWebOf s.1).vertexSet (G.ladderRungOfState s) := by
    by_contra hyNot
    have hyCandidate : y ∈ G.ladderMarkerCandidatesOfState s :=
      ⟨⟨hyStageReach, hyOldQuotient⟩, hyNot⟩
    simpa [hempty] using hyCandidate
  have hyRoofT : y ∈ G.roof T := by
    rcases hyCovered with hySource | hyRung
    · have hyQSource : y ∈ Q.source := hySource.1
      have hyA : y ∈ G.essential A := by
        rw [← G.quotient_source_eq_essential_terminalFrontier_of_roofsSource
          hsource]
        exact hyQSource
      exact hroofA (G.subset_roof A (G.essential_subset A hyA))
    · have hyR : y ∈ G.vertexSet R := by
        simpa only [R, G.vertexSet_liftedLadderRungOfState s] using hyRung
      exact hroofB (hRself hyR)
  have hyEssT : y ∈ G.essential T := by
    by_contra hyNotEss
    exact hy.2 ⟨hyRoofT, hyNotEss⟩
  have hyKSource : y ∈ K.source := by
    have hnewSource : G.source ⊆ G.roof T := hsource.trans hroofA
    rw [show K.source = G.essential T by
      exact G.quotient_source_eq_essential_terminalFrontier_of_roofsSource
        hnewSource]
    exact hyEssT
  exact ⟨hyKSource, hyReachK⟩

/-- Exhaustion persists for the concrete successor family.  The Boolean
component is irrelevant to candidate formation, so this is stated for an
arbitrary next flag. -/
theorem ladderMarkerCandidatesOfState_activeLadderSuccessor_eq_empty
    (hNoEnter : G.NoEdgeEnters G.source)
    (preferred : Option V) (s : G.LadderAccumulationState) (nextFlag : Bool)
    (hactive : s.2 = true)
    (hwarp : G.IsWarp s.1)
    (hself : G.vertexSet s.1 ⊆ G.roof (G.terminalFrontier s.1))
    (hsource : G.source ⊆ G.roof (G.terminalFrontier s.1))
    (hempty : G.ladderMarkerCandidatesOfState s = ∅) :
    G.ladderMarkerCandidatesOfState
      (G.activeLadderSuccessor preferred s, nextFlag) = ∅ := by
  ext y
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hy
  have hySource :=
    G.stageWebOf_activeLadderSuccessor_surviving_reachable_subset_source
      hNoEnter preferred s hactive hwarp hself hsource hempty ⟨hy.1.1, hy.1.2⟩
  exact hy.2 (Or.inl hySource)

/-- The canonical rung at the exhausted successor is the trivial wave. -/
theorem ladderRungOfState_activeLadderSuccessor_eq_trivialWave
    (hNoEnter : G.NoEdgeEnters G.source)
    (preferred : Option V) (s : G.LadderAccumulationState) (nextFlag : Bool)
    (hactive : s.2 = true)
    (hwarp : G.IsWarp s.1)
    (hself : G.vertexSet s.1 ⊆ G.roof (G.terminalFrontier s.1))
    (hsource : G.source ⊆ G.roof (G.terminalFrontier s.1))
    (hempty : G.ladderMarkerCandidatesOfState s = ∅) :
    G.ladderRungOfState (G.activeLadderSuccessor preferred s, nextFlag) =
      (G.stageWebOf (G.activeLadderSuccessor preferred s)).trivialWave := by
  have hloose :
      (G.stageWebOf (G.activeLadderSuccessor preferred s)).IsLoose := by
    let H := G.stageWebOf (G.activeLadderSuccessor preferred s)
    apply H.isLoose_of_not_adj_of_source_subset_reachableToTarget
    · exact G.not_adj_stageWebOf_activeLadderSuccessor_of_candidates_empty
        hNoEnter preferred s hactive hwarp hself hsource hempty
    · intro x hx
      let K := G.quotient
        (G.terminalFrontier (G.activeLadderSuccessor preferred s))
      change x ∈ K.essentialPart.reachableToTarget
      exact K.mem_essentialPart_reachableToTarget_of_mem' hx.2
  exact (G.stageWebOf (G.activeLadderSuccessor preferred s))
    |>.chosenMaximalWave_eq_trivialWave hloose

/-- Source-faithful exhaustion lemma: the next stage web after an active
state with no marker candidates is loose. -/
theorem stageWebOf_activeLadderSuccessor_isLoose_of_candidates_empty
    (hNoEnter : G.NoEdgeEnters G.source)
    (preferred : Option V) (s : G.LadderAccumulationState)
    (hactive : s.2 = true)
    (hwarp : G.IsWarp s.1)
    (hself : G.vertexSet s.1 ⊆ G.roof (G.terminalFrontier s.1))
    (hsource : G.source ⊆ G.roof (G.terminalFrontier s.1))
    (hempty : G.ladderMarkerCandidatesOfState s = ∅) :
    (G.stageWebOf (G.activeLadderSuccessor preferred s)).IsLoose := by
  let H := G.stageWebOf (G.activeLadderSuccessor preferred s)
  apply H.isLoose_of_not_adj_of_source_subset_reachableToTarget
  · exact G.not_adj_stageWebOf_activeLadderSuccessor_of_candidates_empty
      hNoEnter preferred s hactive hwarp hself hsource hempty
  · intro x hx
    let K := G.quotient
      (G.terminalFrontier (G.activeLadderSuccessor preferred s))
    change x ∈ K.essentialPart.reachableToTarget
    exact K.mem_essentialPart_reachableToTarget_of_mem' hx.2

end DWeb
end Erdos599
