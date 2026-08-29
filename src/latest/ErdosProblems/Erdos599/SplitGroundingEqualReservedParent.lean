/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingSimultaneous
import ErdosProblems.Erdos599.GroundingPathPrefix
import ErdosProblems.Erdos599.GroundingRootedReachabilityWarp

/-!
# A grounded reserved parent for the split equal branch

The split auxiliary represents every obstruction record, including records
which are not grounded.  In the stationary equal branch, however, the
selector in `SplitGroundingSimultaneous` first reserves a route whose source
index lies in `phiGround`.  This file converts exactly that additional fact
into an original source-rooted inessential parent and proves that the
collision-avoiding selected relation cannot leave the parent.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open GroundingEqualActiveSelection
open GroundingRootedReachabilityWarp
open _root_.Erdos599.DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

private abbrev SplitEqualInput
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance) :=
  L.splitPopularAuxiliaryInput hL.legal

/-- The original grounded limiting-ladder parent represented by a reserved
split-auxiliary source route. -/
structure SplitReservedGroundedParent
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (q : FinitePath (SplitEqualInput L hL).lambda.graph)
    (hqsource : q.start ∈ (SplitEqualInput L hL).lambda.source) where
  parent : Gamma.DPath
  parent_inessential : parent ∈ Gamma.inessentialPaths L.limitWarp
  parent_initial_source : parent.initial ∈ Gamma.source
  source_represents :
    (∃ p : FinitePath Gamma.graph,
      parent = .inl p ∧ q.start = .old p.finish) ∨
    (∃ i : L.splitInfiniteRecords,
      parent = (SplitEqualInput L hL).proxyPath i ∧
        q.start = .proxy i)
  parent_exposed : parent ∈
    GroundingSimultaneousDecode.exposedLadderPaths
      (SplitEqualInput L hL) q

/-- A reserved split route whose source index is genuinely grounded has a
canonical original source-rooted inessential parent. -/
theorem splitReservedGroundedParent_nonempty
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (q : FinitePath (SplitEqualInput L hL).lambda.graph)
    (hqsource : q.start ∈ (SplitEqualInput L hL).lambda.source)
    (hqground : (L.splitPopularAuxiliaryIndexed hL).f
      ⟨q.start, hqsource⟩ ∈ L.phiGround) :
    Nonempty (L.SplitReservedGroundedParent hL q hqsource) := by
  let I := SplitEqualInput L hL
  rcases I.start_of_mem_lambda_source q hqsource with
      ⟨b, hbFinite, hstart⟩ | ⟨i, hstart⟩
  · let x : L.finiteTerminalSet := ⟨b, hbFinite⟩
    obtain ⟨_haFinite, parent, hchosen, hterminal⟩ :=
      L.finiteTerminalStage_spec x
    have hground : L.finiteTerminalStage x ∈ L.phiGround := by
      have hsourceEq :
          (⟨q.start, hqsource⟩ : I.lambda.source) =
            ⟨.old b, (I.mem_lambda_source_old b).2 hbFinite⟩ :=
        Subtype.ext hstart
      rw [hsourceEq] at hqground
      change L.finiteTerminalStage x ∈ L.phiGround at hqground
      exact hqground
    obtain ⟨groundedParent, hparentChosen, hparentSource⟩ := hground
    have hparent : groundedParent = parent :=
      Option.some.inj (hparentChosen.symm.trans hchosen)
    subst groundedParent
    rcases parent with p | r
    · have hfinish : p.finish = b := Option.some.inj hterminal
      have hinessential : (.inl p : Gamma.DPath) ∈
          Gamma.inessentialPaths L.limitWarp := by
        apply L.recorded_mem_inessential hL.legal.recordedPathsPersist hchosen
        change (L.finiteTerminalStage x).1 + 1 ≤ kappa.ord
        exact (Order.add_one_le_iff).2 (L.finiteTerminalStage x).2
      refine ⟨{
        parent := .inl p
        parent_inessential := hinessential
        parent_initial_source := hparentSource
        source_represents := Or.inl ⟨p, rfl, by
          simpa only [hfinish] using hstart⟩
        parent_exposed := Or.inl ⟨hinessential.1, ?_⟩ }⟩
      refine ⟨.old b, ?_, Or.inl ⟨b, ?_, rfl⟩⟩
      · simpa only [hstart] using q.start_mem_support
      · change b ∈ p.support
        simpa only [hfinish] using p.finish_mem_support
    · change (none : Option V) = some b at hterminal
      cases hterminal
  · have hispec := L.splitInfiniteStage_spec i
    have hground : L.splitInfiniteStage i ∈ L.phiGround := by
      have hsourceEq :
          (⟨q.start, hqsource⟩ : I.lambda.source) =
            ⟨.proxy i, I.mem_lambda_source_proxy i⟩ :=
        Subtype.ext hstart
      rw [hsourceEq] at hqground
      change L.splitInfiniteStage i ∈ L.phiGround at hqground
      exact hqground
    obtain ⟨parent, hparentChosen, hparentSource⟩ := hground
    have hchosen : L.chosen (L.splitInfiniteStage i) = some i.1 :=
      hispec.2
    have hiparent : i.1 = parent :=
      Option.some.inj (hchosen.symm.trans hparentChosen)
    have hiSource : i.1.initial ∈ Gamma.source := hiparent ▸ hparentSource
    have hiInessential : i.1 ∈ Gamma.inessentialPaths L.limitWarp := by
      apply L.recorded_mem_inessential hL.legal.recordedPathsPersist hchosen
      change (L.splitInfiniteStage i).1 + 1 ≤ kappa.ord
      exact (Order.add_one_le_iff).2 (L.splitInfiniteStage i).2
    refine ⟨{
      parent := i.1
      parent_inessential := hiInessential
      parent_initial_source := hiSource
      source_represents := Or.inr ⟨i, by
        simp only [SplitEqualInput, splitPopularAuxiliaryInput,
          splitInfinitePath], hstart⟩
      parent_exposed := ?_ }⟩
    right
    simpa [GroundingSimultaneousDecode.exposedLadderPaths, hstart,
      SplitEqualInput, splitPopularAuxiliaryInput, splitInfinitePath]

/-- The essential terminal cut is disjoint from every inessential component
of the limiting split ladder. -/
theorem splitTerminalCut_not_mem_support_of_inessential
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    {b : V} (hb : b ∈ (SplitEqualInput L hL).terminalCut)
    {p : Gamma.DPath} (hp : p ∈ Gamma.inessentialPaths L.limitWarp) :
    b ∉ p.support := by
  intro hbp
  change b ∈ Gamma.terminalFrontier
    (Gamma.essentialWarpPart L.limitWarp) at hb
  obtain ⟨q, hqEssential, hqb⟩ := hb
  have hqbSupport : b ∈ q.support := Gamma.terminal_mem_support hqb
  by_cases hpq : p = q
  · subst q
    exact hp.2 hqEssential
  · exact Set.disjoint_left.1
      (hL.legal.warpStages (Ladder.finalStage kappa)
        hp.1 hqEssential.1 hpq) hbp hqbSupport

namespace SplitReservedGroundedParent

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {q : FinitePath (SplitEqualInput L hL).lambda.graph}
  {hqsource : q.start ∈ (SplitEqualInput L hL).lambda.source}

/-- Avoidance of the reserved route's collision carrier makes every retained
decoded carrier disjoint from its grounded parent. -/
theorem decodedCarriers_disjoint
    (R : L.SplitReservedGroundedParent hL q hqsource)
    (Q : Popular.XSWarp
      (SplitEqualInput L hL).lambda (SplitEqualInput L hL).lambda.target)
    (havoid : ∀ p ∈ Q.paths,
      Disjoint p.support (collisionCarrier (SplitEqualInput L hL) q)) :
    ∀ p ∈ Q.paths,
      Disjoint ((SplitEqualInput L hL).decodedVertexCarrier p)
        R.parent.support := by
  intro p hp
  exact decodedVertexCarrier_disjoint_exposedLadderPath_of_support_disjoint
    (SplitEqualInput L hL) (L.splitPopularAuxiliary_proxyPathsFaithful hL)
    p q (Q.starts_in_source hp) R.parent_exposed (havoid p hp)

/-- Inserted forward edges cannot touch the reserved grounded parent. -/
theorem forwardEdges_endpoints_not_mem
    (R : L.SplitReservedGroundedParent hL q hqsource)
    (Q : Popular.XSWarp
      (SplitEqualInput L hL).lambda (SplitEqualInput L hL).lambda.target)
    (havoid : ∀ p ∈ Q.paths,
      Disjoint p.support (collisionCarrier (SplitEqualInput L hL) q))
    {e : V × V} (he : e ∈
      canonicalErasedForwardEdges (SplitEqualInput L hL) Q) :
    e.1 ∉ R.parent.support ∧ e.2 ∉ R.parent.support := by
  apply canonicalErasedForwardEdges_endpoints_not_mem
    (SplitEqualInput L hL) Q (R.decodedCarriers_disjoint Q havoid) he

/-- Every limiting-ladder edge beginning on the reserved parent remains on
that same limiting-warp component. -/
theorem familyEdge_head_mem
    (R : L.SplitReservedGroundedParent hL q hqsource)
    {x y : V} (hx : x ∈ R.parent.support)
    (hxy : (x, y) ∈ (SplitEqualInput L hL).familyEdges) :
    y ∈ R.parent.support := by
  obtain ⟨p, hpLimit, hxyP⟩ := hxy
  have hxP : x ∈ p.support := (p.edgeSet_subset_support_prod hxyP).1
  have hparentP : R.parent = p :=
    Alternating.DWeb.IsWarp.eq_of_mem_support
      (hL.legal.warpStages (Ladder.finalStage kappa))
      R.parent_inessential.1 hpLimit hx hxP
  rw [hparentP]
  exact (p.edgeSet_subset_support_prod hxyP).2

/-- The reserved parent is forward-closed under the complete canonical
collision-repaired equal-family relation. -/
theorem repairedEdge_head_mem
    (R : L.SplitReservedGroundedParent hL q hqsource)
    (Q : Popular.XSWarp
      (SplitEqualInput L hL).lambda (SplitEqualInput L hL).lambda.target)
    (havoid : ∀ p ∈ Q.paths,
      Disjoint p.support (collisionCarrier (SplitEqualInput L hL) q))
    {x y : V} (hx : x ∈ R.parent.support)
    (hxy : (x, y) ∈
      canonicalErasedRepairedEdges (SplitEqualInput L hL) Q) :
    y ∈ R.parent.support := by
  rcases hxy with hbase | hforward
  · exact R.familyEdge_head_mem hx hbase.1.1
  · exact False.elim
      ((R.forwardEdges_endpoints_not_mem Q havoid hforward).1 hx)

/-- Every vertex reachable from the reserved original source remains on its
grounded inessential parent. -/
theorem reachable_mem_support
    (R : L.SplitReservedGroundedParent hL q hqsource)
    (Q : Popular.XSWarp
      (SplitEqualInput L hL).lambda (SplitEqualInput L hL).lambda.target)
    (havoid : ∀ p ∈ Q.paths,
      Disjoint p.support (collisionCarrier (SplitEqualInput L hL) q))
    {x : V}
    (hx : Relation.ReflTransGen
      (fun u v ↦ (u, v) ∈
        canonicalErasedRepairedEdges (SplitEqualInput L hL) Q)
      R.parent.initial x) :
    x ∈ R.parent.support := by
  induction hx with
  | refl => exact R.parent.initial_mem_support
  | tail hxy hyz ih => exact R.repairedEdge_head_mem Q havoid ih hyz

/-- Hence the reserved original source cannot reach the essential terminal
cut in the collision-repaired relation. -/
theorem not_reaches_terminalCut
    (R : L.SplitReservedGroundedParent hL q hqsource)
    (Q : Popular.XSWarp
      (SplitEqualInput L hL).lambda (SplitEqualInput L hL).lambda.target)
    (havoid : ∀ p ∈ Q.paths,
      Disjoint p.support (collisionCarrier (SplitEqualInput L hL) q))
    {b : V} (hb : b ∈ (SplitEqualInput L hL).terminalCut) :
    ¬ Relation.ReflTransGen
      (fun u v ↦ (u, v) ∈
        canonicalErasedRepairedEdges (SplitEqualInput L hL) Q)
      R.parent.initial b := by
  intro hreach
  exact splitTerminalCut_not_mem_support_of_inessential L hL hb
    R.parent_inessential (R.reachable_mem_support Q havoid hreach)

end SplitReservedGroundedParent

/-- Vertices admitting an ambient finite directed path from an original
source. -/
def splitAmbientSourceReachable (Gamma : DWeb V) : Set V :=
  {x | ∃ p : FinitePath Gamma.graph,
    p.start ∈ Gamma.source ∧ p.finish = x}

/-- The essential terminal boundary after discarding points irrelevant to
all original source--target paths. -/
def splitReachableTerminalCut
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance) : Set V :=
  (SplitEqualInput L hL).terminalCut ∩ splitAmbientSourceReachable Gamma

/-- Every original source--target path meets a terminal-cut point reached by
its own initial segment. -/
theorem splitReachableTerminalCut_isSeparator
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance) :
    Popular.IsSeparator Gamma (splitReachableTerminalCut L hL) := by
  have hroof : Gamma.source ⊆ Gamma.roof
      (Gamma.terminalFrontier (SplitEqualInput L hL).ladder.paths) := by
    simpa only [SplitEqualInput, splitPopularAuxiliaryInput,
      KappaLadder.limitWarp] using
        hL.legal.roofsSourceAtStages (Ladder.finalStage kappa)
  have hroofEssential :
      Gamma.source ⊆ Gamma.roof (SplitEqualInput L hL).terminalCut := by
    intro x hx
    rw [PopularAuxiliary.Input.terminalCut,
      PopularAuxiliary.Input.essentialLadder,
      Gamma.terminalFrontier_essentialWarpPart, Gamma.roof_essential]
    exact hroof hx
  intro p hpSource hpTarget
  obtain ⟨x, hxp, hxCut⟩ := hroofEssential hpSource p ⟨rfl, hpTarget⟩
  obtain ⟨r, hrStart, hrFinish, _hrSupport, _hrEdges⟩ :=
    GroundingPathPrefix.exists_initialFinitePrefix
      (Sum.inl p : Gamma.DPath) (by
        change x ∈ p.support
        exact hxp)
  refine ⟨x, hxp, hxCut, r, ?_, hrFinish⟩
  simpa only [hrStart, DirectedPath.Path.initial] using hpSource

namespace SplitReservedGroundedParent

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {q : FinitePath (SplitEqualInput L hL).lambda.graph}
  {hqsource : q.start ∈ (SplitEqualInput L hL).lambda.source}

/-- Rooting the source-reachable terminal boundary in the concrete repaired
relation produces an ordinary hindrance.  The reserved parent's source is
removed internally: its forward closure prevents it from reaching any point
of the terminal cut. -/
theorem exists_hindrance_of_splitReachableTerminalCut_sourceRooted
    (R : L.SplitReservedGroundedParent hL q hqsource)
    (Q : Popular.XSWarp
      (SplitEqualInput L hL).lambda (SplitEqualInput L hL).lambda.target)
    (hQdisjoint : Q.paths.PairwiseDisjoint
      (SplitEqualInput L hL).decodedVertexCarrier)
    (havoid : ∀ p ∈ Q.paths,
      Disjoint p.support (collisionCarrier (SplitEqualInput L hL) q))
    (hanti : IsReachabilityAntichain
      (canonicalErasedRepairedEdges (SplitEqualInput L hL) Q)
      (splitReachableTerminalCut L hL))
    (hroot : ∀ b ∈ splitReachableTerminalCut L hL,
      ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈
            canonicalErasedRepairedEdges (SplitEqualInput L hL) Q) a b) :
    ∃ H : Set Gamma.DPath, Gamma.IsHindrance H := by
  classical
  let E := canonicalErasedRepairedEdges (SplitEqualInput L hL) Q
  let A : Set V := Gamma.source \ {R.parent.initial}
  have hrootA : ∀ b ∈ splitReachableTerminalCut L hL,
      ∃ a ∈ A, Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a b := by
    intro b hb
    obtain ⟨a, haSource, hab⟩ := hroot b hb
    have hane : a ≠ R.parent.initial := by
      intro hae
      subst a
      exact R.not_reaches_terminalCut Q havoid hb.1 hab
    exact ⟨a, ⟨haSource, by simpa using hane⟩, hab⟩
  obtain ⟨P, hcover, hpaths⟩ :=
    GroundingRootedReachabilityWarp.exists_rootedReachabilityWarp
      (canonicalErasedRepairedEdges_subset_adj (SplitEqualInput L hL) Q)
      (canonicalErasedRepairedEdges_biUnique
        (SplitEqualInput L hL) Q hQdisjoint)
      Set.sdiff_subset hanti hrootA
  let W : Set Gamma.DPath := PopularSwitching.pathFamily P
  have hWwarp : Gamma.IsWarp W :=
    PopularSwitching.pathFamily_isWarp P
  have hWinitial : Gamma.initialSet W ⊆ Gamma.source :=
    PopularSwitching.pathFamily_initialSet_subset P
  have hWterminal : Gamma.terminalFrontier W =
      splitReachableTerminalCut L hL :=
    PopularSwitching.pathFamily_terminalFrontier_eq P hcover
  have hWwave : Gamma.IsWave W :=
    ⟨hWwarp, hWinitial, by
      intro x hx p hp
      rw [hWterminal]
      exact splitReachableTerminalCut_isSeparator L hL p
        (hp.1 ▸ hx) hp.2⟩
  refine ⟨Gamma.essentialWarpPart W, hWwave.essentialWarpPart, ?_⟩
  intro heq
  have huInitial : R.parent.initial ∈
      Gamma.initialSet (Gamma.essentialWarpPart W) :=
    heq.symm ▸ R.parent_initial_source
  obtain ⟨p, hpEssential, hpInitial⟩ := huInitial
  obtain ⟨r, hrP, hpr⟩ := hpEssential.1
  cases hpr
  have hnotA : R.parent.initial ∉ A := by simp [A]
  apply hnotA
  exact hpInitial ▸ (hpaths r hrP).2.1

end SplitReservedGroundedParent
end KappaLadder
end DWeb
end Erdos599
