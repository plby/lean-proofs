/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularSplitCanonicalHistoryBase
import ErdosProblems.Erdos599.RegularWeakSplitCandidate
import ErdosProblems.Erdos599.RegularGlobalAdmissibleProvider
import ErdosProblems.Erdos599.RegularWeakSource915Rows
import ErdosProblems.Erdos599.RegularWeakHalfwayCoordinatePreparation
import ErdosProblems.Erdos599.RegularEnrichedExactFullRow
import ErdosProblems.Erdos599.RegularWeakFullRowSplit
import ErdosProblems.Erdos599.RegularWeakSplitRowClosure
import ErdosProblems.Erdos599.RegularWeakSelectedCoordinateProvider
import ErdosProblems.Erdos599.SingularQuotientReentry
import ErdosProblems.Erdos599.SplitHindranceGrounding

/-!
# The weak regular annular-candidate constructor

The regular recursion has two installed tracks.  Requested components which
have already reached the later frontier are retained on the small target
track; only the complementary clean track is required to meet that frontier
at its terminal.  This is the source-faithful persistent/completed split and
avoids the false all-request right-tight candidate interface.

This module first records why every history coordinate used by the regular
extension has an infinite frontier.  It then composes the causally registered
half-way payload, club roof capture, first-hit whole-component exchange and
normalized continuation into the weak selected-coordinate provider consumed
by the final recursion.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularSliceCandidateConstructor

open SingularExtension SliceSpliceSource

universe u

variable {V : Type u}

private theorem mk_initialSet_le_family
    (G : DWeb V) (W : Set G.DPath) :
    #(G.initialSet W) ≤ #W := by
  let f : G.initialSet W → W := fun x ↦
    ⟨Classical.choose x.2, (Classical.choose_spec x.2).1⟩
  apply Cardinal.mk_le_of_injective (f := f)
  intro x y hxy
  apply Subtype.ext
  have hx := (Classical.choose_spec x.2).2
  have hy := (Classical.choose_spec y.2).2
  exact calc
    x.1 = (f x).1.initial := hx.symm
    _ = (f y).1.initial := congrArg (fun p : W ↦ p.1.initial) hxy
    _ = y.1 := hy

private theorem mk_family_le_terminalFrontier
    (G : DWeb V) {W : Set G.DPath} (hW : G.IsWarp W)
    (hterminal : ∀ p ∈ W, ∃ t, G.terminal? p = some t) :
    #W ≤ #(G.terminalFrontier W) := by
  let f : W → G.terminalFrontier W := fun p ↦
    ⟨Classical.choose (hterminal p.1 p.2), p.1, p.2,
      Classical.choose_spec (hterminal p.1 p.2)⟩
  apply Cardinal.mk_le_of_injective (f := f)
  intro p q hpq
  apply Subtype.ext
  by_contra hpne
  have htermEq : (f p).1 = (f q).1 := congrArg Subtype.val hpq
  have hpterm := Classical.choose_spec (hterminal p.1 p.2)
  have hqterm := Classical.choose_spec (hterminal q.1 q.2)
  have hpSupport : (f p).1 ∈ p.1.support :=
    G.terminal_mem_support hpterm
  have hqSupport : (f p).1 ∈ q.1.support := by
    rw [htermEq]
    exact G.terminal_mem_support hqterm
  exact Set.disjoint_left.1 (hW p.2 q.2 hpne) hpSupport hqSupport

/-- Every terminal of a certified history base lies on its recorded ladder
frontier.  Pending terminals lie there by tightness.  A completed terminal is
an ambient target vertex; the base-roof invariant and the target length-zero
path then put it literally on the frontier. -/
theorem historyBase_terminalFrontier_subset_frontier
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (B : RegularSplitCanonicalHistoryBase.HistoryBase
      G L Sigma Z A request i previous) :
    G.terminalFrontier B.base ⊆ L.frontier B.baseStage := by
  rintro x ⟨p, hp, hpx⟩
  rw [← completedPart_union_pendingPart G B.base] at hp
  rcases hp with hpCompleted | hpPending
  · obtain ⟨b, hbTarget, hpb⟩ := hpCompleted.2
    have hxb : x = b := Option.some.inj (hpx.symm.trans hpb)
    subst x
    apply SliceSpliceConstructor.target_mem_of_mem_roof hbTarget
    exact B.base_below_roof
      ⟨p, hpCompleted.1, G.terminal_mem_support hpb⟩
  · exact B.pending_tight.1.terminalFrontier_subset
      ⟨p, hpPending, hpx⟩

/-- If the initial set of a certified history has cardinal at least `kappa`,
then its recorded frontier is infinite.  Finite character gives every member
a terminal, while warp disjointness makes the terminal map injective. -/
theorem historyBase_frontier_infinite
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (huncountable : aleph0 < kappa) (hA : kappa ≤ #A)
    (B : RegularSplitCanonicalHistoryBase.HistoryBase
      G L Sigma Z A request i previous) :
    aleph0 ≤ #(L.frontier B.baseStage) := by
  have hterminal : ∀ p ∈ B.base, ∃ x, G.terminal? p = some x := by
    intro p hp
    obtain ⟨f, rfl⟩ := B.base_finite hp
    exact ⟨f.finish, rfl⟩
  calc
    aleph0 ≤ kappa := huncountable.le
    _ ≤ #A := hA
    _ = #(G.initialSet B.base) :=
      Cardinal.mk_congr (Equiv.setCongr B.base_initial.symm)
    _ ≤ #B.base := mk_initialSet_le_family G B.base
    _ ≤ #(G.terminalFrontier B.base) :=
      mk_family_le_terminalFrontier G B.base_warp hterminal
    _ ≤ #(L.frontier B.baseStage) := Cardinal.mk_subtype_mono
      (historyBase_terminalFrontier_subset_frontier B)

/-- The target-reachable induced part of an unhindered web is unhindered.
Lifting a wave to the ambient web and using fullness gives the result. -/
theorem essentialPart_isUnhindered_of_isUnhindered
    (Q : DWeb V) (hQ : Q.IsUnhindered) :
    Q.essentialPart.IsUnhindered := by
  rw [Q.essentialPart.isUnhindered_iff]
  intro W hW
  let U : Set Q.DPath := Q.liftEssentialPartFamily W
  have hU : Q.IsWave U := Q.isWave_liftEssentialPartFamily hW
  have hfull : Q.initialSet U = Q.source :=
    Q.isUnhindered_iff.mp hQ U hU
  have hinitial : Q.essentialPart.initialSet W = Q.source := by
    simpa only [U, Q.initialSet_liftEssentialPartFamily] using hfull
  apply Set.Subset.antisymm hW.2.1
  intro x hx
  rw [hinitial]
  rw [DWeb.essentialPart_source] at hx
  exact hx.1

/-- The initial stage web of a legal canonical ladder is unhindered whenever
the ambient web is. -/
theorem zeroStageWeb_isUnhindered
    {kappa : Cardinal.{u}} (G : DWeb V)
    (hNorm : G.IsNormalized) (hUnhindered : G.IsUnhindered)
    {L : G.KappaLadder kappa} (hL : L.IsSplitLegal) :
    (L.stageWeb ⟨0, hL.regular.ord_pos⟩).IsUnhindered := by
  let zero : Ladder.Stage kappa := ⟨0, hL.regular.ord_pos⟩
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  have hquotient : (G.quotient G.source).IsUnhindered :=
    SingularQuotientReentry.quotient_source_isUnhindered
      G hNoEnter hUnhindered
  have hzeroWarp : L.warpAt zero = G.trivialWave := hL.initialStage
  have hstage : L.stageWeb zero = (G.quotient G.source).essentialPart := by
    simp only [DWeb.KappaLadder.stageWeb, DWeb.stageWebOf, hzeroWarp,
      G.terminalFrontier_trivialWave]
  rw [hstage]
  exact essentialPart_isUnhindered_of_isUnhindered _ hquotient

/-- The genuine weak selected-coordinate provider for the enhanced causal
row.  The fixed seed has cardinal `kappa`; hence every certified history base
has an infinite frontier and is eligible for the half-way construction.

The resulting full stage row is built by first-hit whole-component exchange
and normalized quotient continuation.  Its requested persistent components
are then separated onto the small completed track, leaving a terminal-clean
complementary track for the recursion. -/
theorem hasWeakSelectedCoordinateProvider
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNorm : G.IsNormalized) (hUnhindered : G.IsUnhindered)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (seed : Set V) (hseedSource : seed ⊆ G.source)
    (hseedCard : #seed = kappa) :
    RegularExtension.HasWeakSelectedCoordinateProvider G hregular
      huncountable hNorm hlower F hF seed hseedCard.le := by
  let Q := RegularRows.CausalRegular.weakSplitRowRule G hregular
    huncountable hNorm hlower F hF seed hseedCard.le
  let R := Q.rowSystem hregular.aleph0_le
  let L := DWeb.KappaLadder.canonicalLadder G kappa
    (Q.preferred hregular.aleph0_le)
  let tableRequest := RegularRows.CausalRegular.finalRequest G Q
    hregular.aleph0_le
  intro Sigma hSigma havoid schedule i previous hprevious B gamma
    _hrequired
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  have hL : L.IsSplitLegal :=
    DWeb.KappaLadder.canonicalLadder_isSplitLegal
      (Q.preferred hregular.aleph0_le) hregular huncountable hNoEnter
  have hmax : RegularExtension.HasMaximalRungs G L := by
    simpa only [L, DWeb.KappaLadder.canonicalLadder] using
      (RegularExtension.canonicalLadderWithBookkeeping_hasMaximalRungs
        (G := G) kappa (Q.preferred hregular.aleph0_le))
  have hstage : (L.stageWeb B.baseStage).IsUnhindered := by
    rcases B.baseStage_admissible with hzero | hclub
    · have hbaseZero : B.baseStage = ⟨0, hregular.ord_pos⟩ := by
        apply Subtype.ext
        exact hzero
      rw [hbaseZero]
      exact zeroStageWeb_isUnhindered G hNorm hUnhindered hL
    · exact RegularExtension.stageWeb_isUnhindered_of_mem_avoiding
        G hmax
        (hL.phiHindrance_subset_phi hNorm) havoid hclub
  have hrequest : tableRequest B.baseStage gamma ⊆
      L.frontier B.baseStage := by
    exact Set.inter_subset_left
  have hrequestSmall : #(tableRequest B.baseStage gamma) < kappa := by
    exact ControlledSlices.mk_diagonalRequest_lt hregular _ _ _ _
  have hseedCarrier : seed ⊆ R.carrier := by
    exact RegularRows.CausalRegular.base_subset_weakSplitRowRule_carrier
      G hregular huncountable hNorm hlower F hF seed hseedCard.le
  have hseedA : seed ⊆ G.source ∩ R.carrier :=
    fun x hx ↦ ⟨hseedSource hx, hseedCarrier hx⟩
  have hAcard : kappa ≤ #(G.source ∩ R.carrier : Set V) := by
    exact hseedCard.symm.le.trans (Cardinal.mk_subtype_mono hseedA)
  have hfrontierInfinite : aleph0 ≤ #(L.frontier B.baseStage) :=
    historyBase_frontier_infinite huncountable hAcard B
  have heligible : SliceCandidate.HalfwayChoiceEligible L B.baseStage
      (tableRequest B.baseStage gamma) :=
    ⟨hstage, hrequest, hrequestSmall, hfrontierInfinite⟩
  have hZroof : R.carrier ⊆ L.limitRoof :=
    RegularWeakSplitRowClosure.carrier_subset_limitRoof G hregular
      huncountable hNorm hlower F hF seed hseedCard.le
  let Lcore := G.canonicalLadderCore kappa
    (Q.preferred hregular.aleph0_le)
  have hregisteredCore :
      RegularWeakHalfwayRegistration.registrationAt hlower huncountable
          Lcore tableRequest B.baseStage gamma ⊆ R.carrier := by
    simpa only [Lcore, tableRequest, Q] using
      (RegularRows.CausalRegular.halfwayRegistrationAt_subset_weakSplitRowRule_carrier
        G hregular huncountable hNorm hlower F hF seed hseedCard.le
          B.baseStage gamma)
  have hwarp : Lcore.warpAt B.baseStage = L.warpAt B.baseStage := by
    simp only [L, Lcore, DWeb.KappaLadder.canonicalLadder,
      DWeb.KappaLadder.withValidBookkeeping_warpAt]
  have hregistered :
      RegularWeakHalfwayRegistration.registrationAt hlower huncountable
          L tableRequest B.baseStage gamma ⊆ R.carrier := by
    rw [← RegularWeakHalfwayRegistration.registrationAt_congr_stageData
      hlower huncountable hwarp rfl]
    exact hregisteredCore
  obtain ⟨D, zeta, _hzeta, beta, hbeta, hdeltaZeta, hzetaBeta,
      hbetaNotPhi, _hregisteredD, hCroof, _hselectedRoof⟩ :=
    RegularWeakHalfwayCoordinatePreparation.exists_halfwayPayload_later_roofed_coordinate
      hregular hNorm hlower hL hSigma havoid tableRequest hZroof
        B.baseStage gamma heligible hregistered
  have hdeltaBeta : B.baseStage < beta := hdeltaZeta.trans hzetaBeta
  obtain ⟨W, hW, hlinks, hregion, hmavericks⟩ :=
    RegularEnrichedExactFullRow.HalfwayPayload.exists_enrichedTargetLinkingAnnular_of_exactFrontier
      hlower hregular huncountable hL hNorm hdeltaBeta hbetaNotPhi D
        hrequest hrequestSmall hCroof D.terminalFrontier_eq
  obtain ⟨P, hP⟩ :=
    RegularWeakFullRowSplit.exists_weakSplitAnnularCandidate_of_terminalCleanStageRow
      hL hdeltaBeta.le
        (RegularCandidateProvider.stageWeb_isNormalized hNorm L B.baseStage)
        hW.1 hW.2 hrequest hlinks hrequestSmall hregion hmavericks
  exact ⟨beta, hbeta, hdeltaBeta, P, hP⟩

end RegularSliceCandidateConstructor
end CardinalInduction
end Erdos599
