/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SliceCandidate
import ErdosProblems.Erdos599.RegularSplitLegality
import ErdosProblems.Erdos599.SliceRestrictedDelta
import ErdosProblems.Erdos599.SliceDeltaLift
import ErdosProblems.Erdos599.SliceStageIntervalBridge
import ErdosProblems.Erdos599.RegularCleanExchange
import ErdosProblems.Erdos599.SingularExtension
import ErdosProblems.Erdos599.SingularFirstHitCleanPrefix

/-!
# The one-stage provider in the regular-cardinal construction

This file assembles the local graph construction in Assertion 9.10/9.15.
The first section strengthens the weak, trimmed half-way stop-over chosen
by the causal table to the canonical separating stop-over.  Importantly,
the strengthening retains the *same* height wave, rather than choosing a
new height witness which would not have been registered by the causal row.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace CardinalInduction
namespace RegularCandidateProvider

open DirectedPath
open SliceCandidate

universe u
variable {V : Type u}

/-- Every stage of a normalized ambient web is normalized. -/
theorem stageWeb_isNormalized
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hNorm : Gamma.IsNormalized) (L : Gamma.KappaLadder kappa)
    (delta : Ladder.Stage kappa) :
    (L.stageWeb delta).IsNormalized := by
  intro x y hxy
  let Q := Gamma.quotient
    (Gamma.terminalFrontier (L.warpAt delta))
  have hxyQ : Q.graph.Adj x y := Q.essentialPart_adj_imp hxy
  have hxyGamma : Gamma.graph.Adj x y := Gamma.quotient_adj_imp hxyQ
  refine ⟨?_, (hNorm hxyGamma).2⟩
  have hNoEnterQ : Q.NoEdgeEnters Q.source :=
    DWeb.NoEdgeEnters.quotient (G := Gamma)
      (fun {_ _} e hy ↦ (hNorm e).1 hy)
  exact fun hy ↦ hNoEnterQ hxyQ hy.1

/-- A later ladder frontier is still trimmed when it is viewed in the
earlier stage web.  This is the source identity hidden in the iterated
quotient calculation of Assertion 9.9. -/
theorem stageWeb_laterFrontier_isEssential
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} (hL : L.IsSplitLegal)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    {delta beta : Ladder.Stage kappa} (hdeltaBeta : delta < beta) :
    (L.stageWeb delta).essential (L.frontier beta) = L.frontier beta := by
  let Q := L.stageWeb delta
  let T := L.frontier beta
  have hsourceRoof : Q.source ⊆ Q.roof T := by
    intro x hx
    have hxGamma : x ∈ Gamma.roof T :=
      hL.frontierChronology hdeltaBeta hx
    exact roof_subset_of_adj_imp Gamma Q rfl
      (fun {_ _} e ↦ Gamma.quotient_adj_imp
        ((Gamma.quotient
          (Gamma.terminalFrontier (L.warpAt delta))).essentialPart_adj_imp e))
      T hxGamma
  have hessentialUnion : Q.essential (Q.source ∪ T) = Q.essential T :=
    calc
      Q.essential (Q.source ∪ T) = Q.essential (T ∪ Q.source) := by
        rw [Set.union_comm]
      _ = Q.essential T :=
        RelationalRoof.essential_union_eq_of_subset_roof
          Q.graph.Adj Q.target hsourceRoof
  have hstage := SliceCandidate.stageWeb_quotient_essentialPart_eq
    hL hNoEnter hdeltaBeta
  apply Set.Subset.antisymm
  · exact Q.essential_subset T
  · intro x hxT
    have hxStage : x ∈ ((Q.quotient T).essentialPart).source := by
      rw [hstage]
      exact hxT
    have hxUnion : x ∈ Q.essential (Q.source ∪ T) := by
      rw [DWeb.essentialPart_source, DWeb.quotient_source] at hxStage
      exact hxStage.1
    rwa [hessentialUnion] at hxUnion

/-- The canonical separating enlargement of a weak half-way payload.
Besides the separator certificate, this retains the original height set and
wave, which is the causal datum registered before the ladder was completed. -/
structure SeparatingPayload
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (delta : Ladder.Stage kappa)
    (U : Set V) where
  W : Set (L.stageWeb delta).DPath
  C : Set V
  X : Set V
  R : Set ((L.stageWeb delta).quotient X).DPath
  stopover : IsSeparatingHalfwayStopover (L.stageWeb delta) W C
  links : LinksToTarget (L.stageWeb delta) W U
  heightAwayFromSource : X ⊆ (L.frontier delta)ᶜ
  heightWave : ((L.stageWeb delta).quotient X).IsWave R
  stopoverRoof : C ⊆ (L.stageWeb delta).roof
    (((L.stageWeb delta).quotient X).terminalFrontier R)
  heightSmall : #X < kappa

/-- A chosen half-way payload already carries the separating stop-over from
Definition 9.1.  Repackage that exact stop-over without enlarging it to the
quotient source.  Retaining the original `C` is essential for the later
first-hit/normalized-Delta construction: arbitrary payload enlargement can
turn old source vertices into boundary vertices and destroy terminal
cleanliness. -/
theorem HalfwayPayload.exists_separatingPayload
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta : Ladder.Stage kappa}
    {U : Set V} (D : HalfwayPayload L delta U)
    (_hNorm : Gamma.IsNormalized) :
    Nonempty (SeparatingPayload L delta U) := by
  exact ⟨
    { W := D.W
      C := D.C
      X := D.X
      R := D.R
      stopover :=
        { stopover :=
            { linkage := D.linkage
              minimal := D.trimmed
              quotient_unhindered := D.quotientUnhindered }
          separator := D.separator }
      links := D.links
      heightAwayFromSource := D.heightAwayFromSource
      heightWave := D.heightWave
      stopoverRoof := D.stopoverRoof
      heightSmall := D.heightSmall }⟩

/-- If a trimmed stop-over is roofed by an essential later boundary, that
boundary avoids the old strict roof.  This is the short nested-roof
argument hidden in the displayed Delta construction: an essential target
path from a boundary point avoids every other boundary point; after its
first old-boundary hit, the same path witnesses that hit is not roofed by
the later boundary. -/
theorem disjoint_strictRoof_of_trimmed_of_essential_of_subset_roof
    (Q : DWeb V) {C T : Set V}
    (hCtrim : IsTrimmedSeparator Q C)
    (hTessential : Q.essential T = T)
    (hCroof : C ⊆ Q.roof T) :
    Disjoint (Q.strictRoof C) T := by
  apply Set.disjoint_left.2
  intro x hxStrict hxT
  have hxEssentialT : x ∈ Q.essential T := by
    rw [hTessential]
    exact hxT
  obtain ⟨p, hpTarget, hpAvoid⟩ :=
    (Q.not_mem_roof_iff (T \ {x}) x).1 hxEssentialT.2
  obtain ⟨c, hcp, hcC⟩ := hxStrict.1 p hpTarget
  by_cases hcx : c = x
  · subst c
    apply hxStrict.2
    rw [hCtrim]
    exact hcC
  · have hcNotRoof : c ∉ Q.roof T :=
      RelationalRoof.not_mem_roof_of_later_mem_targetPath
        Q.graph.Adj Q.target p hpTarget
          (by
            intro y hyp hyT
            exact Set.disjoint_left.1 hpAvoid hyp
              ⟨hyT.1, fun hyx ↦ hyT.2
                (hyx.trans hpTarget.1.symm)⟩)
          hcp (fun hcstart ↦ hcx (hcstart.trans hpTarget.1))
    exact hcNotRoof (hCroof hcC)

/-! ## Separating completed requests from the clean pending row -/

/-- In a normalized web, every component chosen to witness a requested
source starts at that source.  Thus the standard small target-linking
subfamily covers the request already at its initial set. -/
theorem exists_small_targetLinkingSubfamily_with_initials
    {kappa : Cardinal.{u}} (Q : DWeb V)
    {A C U : Set V} {W : Set Q.DPath}
    (hNorm : Q.IsNormalized)
    (_hW : IsLinkageBetween Q A C W)
    (hUsource : U ⊆ Q.source)
    (hlinks : LinksToTarget Q W U) (hUsmall : #U < kappa) :
    ∃ K : Set Q.DPath,
      K ⊆ SingularExtension.completedPart Q W ∧
        LinksToTarget Q K U ∧
        Q.initialSet K = U ∧ #K < kappa := by
  have hcompletedLinks : LinksToTarget Q
      (SingularExtension.completedPart Q W) U :=
    SingularExtension.linksToTarget_completedPart hNorm hlinks
  obtain ⟨K₀, hK₀W, hK₀links, hK₀small⟩ :=
    SliceCandidate.exists_targetLinkingSubfamily_mk_lt
      Q hcompletedLinks hUsmall
  let K := SliceSpliceSource.initialRestriction Q K₀ U
  have initial_eq_request {u : V} (hu : u ∈ U) :
      ∃ p ∈ K, p.initial = u := by
    obtain ⟨p, hpK₀, q, rfl, hqU, _hsuffix⟩ := hK₀links u hu
    have huSupport : u ∈ q.support := by
      have huSingleton : u ∈ ({u} : Set V) := Set.mem_singleton u
      rw [← hqU] at huSingleton
      exact huSingleton.1
    have huInitial : u = q.start :=
      hNorm.eq_initial_of_mem_path (Sum.inl q) huSupport (hUsource hu)
    have hqStartU : q.start ∈ U := huInitial ▸ hu
    exact ⟨Sum.inl q, ⟨hpK₀, hqStartU⟩, huInitial.symm⟩
  have hKlinks : LinksToTarget Q K U := by
    intro u hu
    obtain ⟨p, hpK₀, q, hpq, hqU, hsuffix⟩ := hK₀links u hu
    subst p
    have huSupport : u ∈ q.support := by
      have huSingleton : u ∈ ({u} : Set V) := Set.mem_singleton u
      rw [← hqU] at huSingleton
      exact huSingleton.1
    have huInitial : u = q.start :=
      hNorm.eq_initial_of_mem_path (Sum.inl q) huSupport (hUsource hu)
    have hqStartU : q.start ∈ U := huInitial ▸ hu
    exact ⟨Sum.inl q, ⟨hpK₀, hqStartU⟩,
      q, rfl, hqU, hsuffix⟩
  have hKinitial : Q.initialSet K = U := by
    apply Set.Subset.antisymm
    · rintro x ⟨p, hpK, rfl⟩
      exact hpK.2
    · intro u hu
      obtain ⟨p, hpK, hpu⟩ := initial_eq_request hu
      exact ⟨p, hpK, hpu⟩
  refine ⟨K, ?_, hKlinks, hKinitial, ?_⟩
  · exact fun _ hp ↦ hK₀W hp.1
  · exact (Cardinal.mk_subtype_mono
      (fun _ hp ↦ hp.1 : K ⊆ K₀)).trans_lt hK₀small

/-- Split a weak half-way row into a small completed target-linking part
and a terminal-clean pending linkage on all remaining sources.  The two
parts are vertex-disjoint.  This is the provider-side invariant needed by
the completed/pending splice architecture; it avoids the false assertion
that the target-linking paths themselves are terminal-clean at `C`. -/
theorem exists_completedPending_split
    {kappa : Cardinal.{u}} (Q : DWeb V)
    {C U : Set V} {W : Set Q.DPath}
    (hNorm : Q.IsNormalized)
    (hW : IsLinkageBetween Q Q.source C W)
    (hUsource : U ⊆ Q.source)
    (hlinks : LinksToTarget Q W U) (hUsmall : #U < kappa) :
    ∃ (K P : Set Q.DPath),
      K ⊆ SingularExtension.completedPart Q W ∧
        LinksToTarget Q K U ∧
        Q.initialSet K = U ∧ #K < kappa ∧
        IsLinkageBetween Q (Q.source \ U) C P ∧
        SingularContinuation.TerminalCleanAt Q P C ∧
        Disjoint (Q.vertexSet K) (Q.vertexSet P) := by
  obtain ⟨K, hKcompleted, hKlinks, hKinitial, hKsmall⟩ :=
    exists_small_targetLinkingSubfamily_with_initials
      Q hNorm hW hUsource hlinks hUsmall
  have hKW : K ⊆ W := fun _ hp ↦ (hKcompleted hp).1
  let Clean := SingularFirstHitCleanPrefix.firstHitCleanPrefix
    Q W C hW.isWarp hW.finiteCharacter hW.initialSet_eq
      hW.terminalFrontier_subset
  let P := SliceSpliceSource.initialRestriction Q Clean
    (Q.source \ U)
  have hClean : IsLinkageBetween Q Q.source C Clean :=
    SingularFirstHitCleanPrefix.firstHitCleanPrefix_isLinkageBetween
      hW.isWarp hW.finiteCharacter hW.initialSet_eq
        hW.terminalFrontier_subset
  have hCleanTerminal : SingularContinuation.TerminalCleanAt Q Clean C :=
    SingularFirstHitCleanPrefix.firstHitCleanPrefix_terminalClean
      hW.isWarp hW.finiteCharacter hW.initialSet_eq
        hW.terminalFrontier_subset
  have hP : IsLinkageBetween Q (Q.source \ U) C P :=
    SliceSpliceSource.isLinkageBetween_initialRestriction hClean
      Set.sdiff_subset
  have hPTerminal : SingularContinuation.TerminalCleanAt Q P C := by
    intro p hp
    exact hCleanTerminal p hp.1
  have hforward : Q.ForwardExtension Clean W :=
    SingularFirstHitCleanPrefix.forwardExtension_firstHitCleanPrefix
      hW.isWarp hW.finiteCharacter hW.initialSet_eq
        hW.terminalFrontier_subset
  have hdisjoint : Disjoint (Q.vertexSet K) (Q.vertexSet P) := by
    apply Set.disjoint_left.2
    intro x hxK hxP
    obtain ⟨p, hpK, hxp⟩ := hxK
    obtain ⟨q, hqP, hxq⟩ := hxP
    obtain ⟨r, hrW, hqr⟩ := hforward.1 q hqP.1
    have hpr : p ≠ r := by
      intro hpr
      subst r
      have hpInitialU : p.initial ∈ U := by
        rw [← hKinitial]
        exact ⟨p, hpK, rfl⟩
      exact hqP.2.2 ((Q.extends_initial hqr).symm ▸ hpInitialU)
    exact Set.disjoint_left.1 (hW.isWarp (hKW hpK) hrW hpr)
      hxp (Q.support_mono_of_extends hqr hxq)
  exact ⟨K, P, hKcompleted, hKlinks, hKinitial, hKsmall, hP,
    hPTerminal, hdisjoint⟩

/-! ## Filling the normalized annulus

The next lemma is the exact assembly point for the normalized-`Delta`
argument.  It is deliberately stated independently of the ladder: the
whole-component exchange supplies `W`, `E`, and `F`, while the lower
cardinal extension clause fills the missing sources in normalized
`Delta`. -/

/-- The normalized-`Delta` fill itself is independent of the stopped old
row.  The old row is used only to prove source purity of the retained suffix
family and, after the fill, star compatibility.  Isolating this middle step
allows the clean complementary source row to use the same construction. -/
theorem exists_normalizedDelta_completion
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (Q : DWeb V) {C D T E : Set V} {F : Set Q.DPath}
    (hDC : D ⊆ C)
    (hCtrim : IsTrimmedSeparator Q C)
    (hCsource : (Q.quotient C).source = C)
    (hCroof : C ⊆ Q.roof T)
    (hCQ : (Q.quotient C).IsUnhindered)
    (hTessential : Q.essential T = T)
    (hEsub : E ⊆ D) (hEsmall : #E < kappa)
    (hF : IsLinkageBetween Q (D \ E) T F)
    (hFtight : SliceSpliceSource.MeetsOnlyAtTerminal Q F T)
    (hsourcePure : ∀ p ∈ F, p.support ∩ D ⊆ {p.initial}) :
    ∃ R : Set (SliceRestrictedDelta.normalizedDelta Q C D T F).DPath,
      IsLinkageBetween (SliceRestrictedDelta.normalizedDelta Q C D T F)
          D T R ∧
        #(↥(R \ SliceDeltaLift.normalizedRestrictedFamily
            Q C D T hF hsourcePure hFtight)) < kappa := by
  have hTstrict : Disjoint (Q.strictRoof C) T :=
    disjoint_strictRoof_of_trimmed_of_essential_of_subset_roof
      Q hCtrim hTessential hCroof
  have hsuffix : Q.vertexSet F ∩ Q.strictRoof C ⊆
      (SliceRestrictedDelta.normalizedDelta Q C D T F).strictRoof
        (C \ D) :=
    SliceDeltaLift.suffix_strictRoof_subset_normalizedDelta_strictRoof
      Q F hDC hCtrim hTstrict
  have hFroof : Q.vertexSet F ⊆ Q.roof T := by
    apply SliceRestrictedDelta.linkage_vertexSet_subset_roof_of_initial
      Q hF
    · exact (Set.sdiff_subset.trans hDC).trans hCroof
    · exact hFtight
  let Fdelta := SliceDeltaLift.normalizedRestrictedFamily
    Q C D T hF hsourcePure hFtight
  have hFdelta : IsLinkageBetween
      (SliceRestrictedDelta.normalizedDelta Q C D T F)
      (D \ E) T Fdelta := by
    exact SliceDeltaLift.normalizedRestrictedFamily_isLinkageBetween
      Q C D T hF hsourcePure hFtight
  obtain ⟨R₀, hR₀⟩ :=
    SliceRestrictedDelta.exists_normalizedDeltaLinkage_of_suffixStrictRoof_lower
      hlower Q hDC hCtrim hFroof hsuffix hCsource hCroof hCQ
        hEsub hEsmall Fdelta hFdelta
  let Delta := SliceRestrictedDelta.normalizedDelta Q C D T F
  let R := SliceCandidate.componentMixedFamily Delta R₀ Fdelta E
  have hR : IsLinkageBetween Delta D T R :=
    SliceCandidate.componentMixedFamily_isLinkageBetween_of_complement
      Delta hR₀ hFdelta hEsub
  have hRsmall : #(↥(R \ Fdelta)) < kappa := by
    let X := SliceCandidate.exceptionalComponentVertices Delta R₀ Fdelta E
    let Rleft := SliceCandidate.initialPart Delta R₀ X
    have hdiff : R \ Fdelta ⊆ Rleft := by
      rintro p ⟨hpR, hpNotF⟩
      change p ∈ Rleft ∪
        SliceCandidate.initialPart Delta Fdelta Xᶜ at hpR
      rcases hpR with hpLeft | hpRight
      · exact hpLeft
      · exact (hpNotF hpRight.1).elim
    exact (Cardinal.mk_subtype_mono hdiff).trans_lt
      (SliceCandidate.mk_componentMixedFamily_left_lt Delta
        hregular huncountable
        hR₀.isWarp hFdelta.isWarp hR₀.finiteCharacter
        hFdelta.finiteCharacter hEsmall)
  exact ⟨R, hR, hRsmall⟩

/-- A whole-terminal exchange across a separating trimmed stop-over can be
completed through normalized `Delta`.  The resulting full continuation is
compatible with the stopped source linkage. -/
theorem exists_normalizedCompletion_of_exchange
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (Q : DWeb V) {C D T E : Set V} {W F : Set Q.DPath}
    (hNorm : Q.IsNormalized)
    (hW : IsLinkageBetween Q Q.source C W)
    (hWroof : Q.vertexSet W ⊆ Q.roof C)
    (hD : D = Q.terminalFrontier W)
    (hDC : D ⊆ C)
    (hCtrim : IsTrimmedSeparator Q C)
    (hCsource : (Q.quotient C).source = C)
    (hCroof : C ⊆ Q.roof T)
    (hCQ : (Q.quotient C).IsUnhindered)
    (hTessential : Q.essential T = T)
    (hEsub : E ⊆ D) (hEsmall : #E < kappa)
    (hF : IsLinkageBetween Q (D \ E) T F)
    (hFtight : SliceSpliceSource.MeetsOnlyAtTerminal Q F T)
    (hWF : Q.StarCompatible W F) :
    ∃ R : Set (SliceRestrictedDelta.normalizedDelta Q C D T F).DPath,
      IsLinkageBetween (SliceRestrictedDelta.normalizedDelta Q C D T F)
          D T R ∧
        Q.StarCompatible W
          (SliceDeltaLift.liftNormalizedFamily Q C D T F R) ∧
        #(↥(R \ SliceDeltaLift.normalizedRestrictedFamily
            Q C D T hF
              (SliceDeltaLift.sourcePure_of_starCompatible Q
                (hD.symm ▸ Set.Subset.rfl) hWF)
              hFtight)) < kappa := by
  have hTstrict : Disjoint (Q.strictRoof C) T :=
    disjoint_strictRoof_of_trimmed_of_essential_of_subset_roof
      Q hCtrim hTessential hCroof
  have hsuffix : Q.vertexSet F ∩ Q.strictRoof C ⊆
      (SliceRestrictedDelta.normalizedDelta Q C D T F).strictRoof
        (C \ D) :=
    SliceDeltaLift.suffix_strictRoof_subset_normalizedDelta_strictRoof
      Q F hDC hCtrim hTstrict
  have hFroof : Q.vertexSet F ⊆ Q.roof T := by
    apply SliceRestrictedDelta.linkage_vertexSet_subset_roof_of_initial
      Q hF
    · exact (Set.sdiff_subset.trans hDC).trans hCroof
    · exact hFtight
  have hsourcePure : ∀ p ∈ F, p.support ∩ D ⊆ {p.initial} := by
    exact SliceDeltaLift.sourcePure_of_starCompatible Q
      (hD.symm ▸ Set.Subset.rfl) hWF
  let Fdelta := SliceDeltaLift.normalizedRestrictedFamily
    Q C D T hF hsourcePure hFtight
  have hFdelta : IsLinkageBetween
      (SliceRestrictedDelta.normalizedDelta Q C D T F)
      (D \ E) T Fdelta := by
    exact SliceDeltaLift.normalizedRestrictedFamily_isLinkageBetween
      Q C D T hF hsourcePure hFtight
  obtain ⟨R₀, hR₀⟩ :=
    SliceRestrictedDelta.exists_normalizedDeltaLinkage_of_suffixStrictRoof_lower
      hlower Q hDC hCtrim hFroof hsuffix hCsource hCroof hCQ
        hEsub hEsmall Fdelta hFdelta
  let Delta := SliceRestrictedDelta.normalizedDelta Q C D T F
  let R := SliceCandidate.componentMixedFamily Delta R₀ Fdelta E
  have hR : IsLinkageBetween Delta D T R :=
    SliceCandidate.componentMixedFamily_isLinkageBetween_of_complement
      Delta hR₀ hFdelta hEsub
  have hRsmall : #(↥(R \ Fdelta)) < kappa := by
    let X := SliceCandidate.exceptionalComponentVertices Delta R₀ Fdelta E
    let Rleft := SliceCandidate.initialPart Delta R₀ X
    have hdiff : R \ Fdelta ⊆ Rleft := by
      rintro p ⟨hpR, hpNotF⟩
      change p ∈ Rleft ∪
        SliceCandidate.initialPart Delta Fdelta Xᶜ at hpR
      rcases hpR with hpLeft | hpRight
      · exact hpLeft
      · exact (hpNotF hpRight.1).elim
    exact (Cardinal.mk_subtype_mono hdiff).trans_lt
      (SliceCandidate.mk_componentMixedFamily_left_lt Delta
        hregular huncountable
        hR₀.isWarp hFdelta.isWarp hR₀.finiteCharacter
        hFdelta.finiteCharacter hEsmall)
  have hDcarrier : D ⊆ SliceRestrictedDelta.carrier Q C T F := by
    intro x hxD
    apply Or.inl
    refine ⟨hCroof (hDC hxD), ?_⟩
    intro hxStrict
    exact hxStrict.2 (by rw [hCtrim]; exact hDC hxD)
  refine ⟨R, hR, ?_, ?_⟩
  · exact SliceDeltaLift.starCompatible_liftNormalizedFamily_of_normalized
      Q hNorm hW hWroof hD hF hWF hDcarrier hR
  · exact hRsmall

/-- Source-exact terminal-clean wrapper for the normalized completion.
The roof containment used by the Delta compatibility proof is a consequence
of separation and terminal cleanliness; it is not an independent invariant
of a weak half-way linkage. -/
theorem exists_normalizedCompletion_of_clean_exchange
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (Q : DWeb V) {C D T E : Set V} {W F : Set Q.DPath}
    (hNorm : Q.IsNormalized)
    (hW : IsLinkageBetween Q Q.source C W)
    (hsep : IsSeparatorFrom Q Q.source C)
    (hWclean : SingularContinuation.TerminalCleanAt Q W C)
    (hD : D = Q.terminalFrontier W)
    (hDC : D ⊆ C)
    (hCtrim : IsTrimmedSeparator Q C)
    (hCsource : (Q.quotient C).source = C)
    (hCroof : C ⊆ Q.roof T)
    (hCQ : (Q.quotient C).IsUnhindered)
    (hTessential : Q.essential T = T)
    (hEsub : E ⊆ D) (hEsmall : #E < kappa)
    (hF : IsLinkageBetween Q (D \ E) T F)
    (hFtight : SliceSpliceSource.MeetsOnlyAtTerminal Q F T)
    (hWF : Q.StarCompatible W F) :
    ∃ R : Set (SliceRestrictedDelta.normalizedDelta Q C D T F).DPath,
      IsLinkageBetween (SliceRestrictedDelta.normalizedDelta Q C D T F)
          D T R ∧
        Q.StarCompatible W
          (SliceDeltaLift.liftNormalizedFamily Q C D T F R) ∧
        #(↥(R \ SliceDeltaLift.normalizedRestrictedFamily
            Q C D T hF
              (SliceDeltaLift.sourcePure_of_starCompatible Q
                (hD.symm ▸ Set.Subset.rfl) hWF)
              hFtight)) < kappa := by
  have hWroof : Q.vertexSet W ⊆ Q.roof C :=
    SingularContinuation.linkage_vertexSet_subset_roof
      Q hW hsep hWclean
  exact exists_normalizedCompletion_of_exchange
    hlower hregular huncountable Q hNorm hW hWroof hD hDC hCtrim
      hCsource hCroof hCQ hTessential hEsub hEsmall hF hFtight hWF

/-- A terminal-clean linkage whose sources are only a subset of the ambient
source still lies below a separating stop-over.  This is the partial-source
form needed after removing the small completed request track. -/
theorem partialLinkage_vertexSet_subset_roof
    (Q : DWeb V) {A C : Set V} {W : Set Q.DPath}
    (hW : IsLinkageBetween Q A C W)
    (hA : A ⊆ Q.source)
    (hsep : IsSeparatorFrom Q Q.source C)
    (hWclean : SingularContinuation.TerminalCleanAt Q W C) :
    Q.vertexSet W ⊆ Q.roof C := by
  rintro x ⟨p, hpW, hxp⟩
  apply Q.pathSupportRoof p C
  · apply hsep
    apply hA
    rw [← hW.initialSet_eq]
    exact ⟨p, hpW, rfl⟩
  · intro t ht
    apply hW.terminalFrontier_subset
    exact ⟨p, hpW, ht⟩
  · intro y hy
    rw [hWclean p hpW y hy.1 hy.2]
    exact Set.mem_singleton y
  · exact hxp

/-- Source-exact normalized completion for the clean complementary track.
Unlike `exists_normalizedCompletion_of_clean_exchange`, the old linkage may
start at a proper subset `A` of the ambient source.  Compatibility therefore
uses terminal cleanliness directly rather than the normalized full-source
shortcut. -/
theorem exists_normalizedCompletion_of_clean_partial_exchange
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (Q : DWeb V) {A C D T E : Set V} {W F : Set Q.DPath}
    (hA : A ⊆ Q.source)
    (hW : IsLinkageBetween Q A C W)
    (hsep : IsSeparatorFrom Q Q.source C)
    (hWclean : SingularContinuation.TerminalCleanAt Q W C)
    (hD : D = Q.terminalFrontier W)
    (hDC : D ⊆ C)
    (hCtrim : IsTrimmedSeparator Q C)
    (hCsource : (Q.quotient C).source = C)
    (hCroof : C ⊆ Q.roof T)
    (hCQ : (Q.quotient C).IsUnhindered)
    (hTessential : Q.essential T = T)
    (hEsub : E ⊆ D) (hEsmall : #E < kappa)
    (hF : IsLinkageBetween Q (D \ E) T F)
    (hFtight : SliceSpliceSource.MeetsOnlyAtTerminal Q F T)
    (hWF : Q.StarCompatible W F) :
    ∃ R : Set (SliceRestrictedDelta.normalizedDelta Q C D T F).DPath,
      IsLinkageBetween (SliceRestrictedDelta.normalizedDelta Q C D T F)
          D T R ∧
        Q.StarCompatible W
          (SliceDeltaLift.liftNormalizedFamily Q C D T F R) ∧
        #(↥(R \ SliceDeltaLift.normalizedRestrictedFamily
            Q C D T hF
              (SliceDeltaLift.sourcePure_of_starCompatible Q
                (hD.symm ▸ Set.Subset.rfl) hWF)
              hFtight)) < kappa := by
  have hWroof : Q.vertexSet W ⊆ Q.roof C :=
    partialLinkage_vertexSet_subset_roof Q hW hA hsep hWclean
  have hsourcePure : ∀ p ∈ F, p.support ∩ D ⊆ {p.initial} :=
    SliceDeltaLift.sourcePure_of_starCompatible Q
      (hD.symm ▸ Set.Subset.rfl) hWF
  obtain ⟨R, hR, hRsmall⟩ := exists_normalizedDelta_completion
    hlower hregular huncountable Q hDC hCtrim hCsource hCroof hCQ
      hTessential hEsub hEsmall hF hFtight hsourcePure
  have hDcarrier : D ⊆ SliceRestrictedDelta.carrier Q C T F := by
    intro x hxD
    apply Or.inl
    refine ⟨hCroof (hDC hxD), ?_⟩
    intro hxStrict
    exact hxStrict.2 (by rw [hCtrim]; exact hDC hxD)
  refine ⟨R, hR, ?_, ?_⟩
  · exact SliceDeltaLift.starCompatible_liftNormalizedFamily
      Q hWroof hWclean (hD.symm ▸ Set.Subset.rfl)
        hF hWF hDcarrier hR
  · exact hRsmall

/-- Star a tight row with a linkage whose source is exactly the old terminal
frontier.  The usual public star lemma asks the new linkage to cover the
entire old right boundary; normalized-`Delta` only needs, and only provides,
the terminals actually used by the clean row. -/
theorem tightLinkageBetween_star_terminalFrontier
    (Q : DWeb V) {A C D T : Set V} {W R : Set Q.DPath}
    (hNorm : Q.IsNormalized) (hA : A ⊆ Q.source)
    (hW : SliceSpliceSource.TightLinkageBetween Q A C W)
    (hR : SliceSpliceSource.TightLinkageBetween Q D T R)
    (hD : D = Q.terminalFrontier W)
    (hWT : SliceSpliceSource.MeetsOnlyAtTerminal Q W T)
    (hcompat : Q.StarCompatible W R) :
    SliceSpliceSource.TightLinkageBetween Q A T (Q.star hcompat) := by
  have hcover : Q.terminalFrontier W ⊆ Q.initialSet R := by
    rw [hR.1.initialSet_eq, hD]
  apply SliceSpliceSource.tightLinkageBetween_of_structural hNorm hA
  · exact Q.isWarp_star hW.1.isWarp hR.1.isWarp hcompat
  · exact SliceSpliceSource.hasFiniteCharacter_star
      hW.1.finiteCharacter hR.1.finiteCharacter hcompat
  · rw [SliceSpliceSource.initialSet_star_eq hcompat,
      hW.1.initialSet_eq]
  · exact (SliceSpliceSource.terminalFrontier_star_subset
      hW.1.finiteCharacter hcompat hcover).trans
        hR.1.terminalFrontier_subset
  · exact SliceSpliceSource.meetsOnlyAtTerminal_star
      hW.1.finiteCharacter hWT hR.2 hcompat hcover

/-- Every vertex of a tight path lying below an essential right boundary is
either in the strict roof of that boundary or is the path's terminal.  This
is the precise localization needed when a safely chosen quotient suffix is
frozen: deleting the old prefix interior is invisible after quotienting by
the right boundary. -/
theorem tightPath_support_subset_strictRoof_union_terminal
    (Q : DWeb V) {A T : Set V} {P : Set Q.DPath}
    (hTessential : Q.essential T = T)
    (hP : SliceSpliceSource.TightLinkageBetween Q A T P)
    (hbelow : Q.vertexSet P ⊆ Q.roof T)
    {p : DirectedPath.FinitePath Q.graph} (hp : Sum.inl p ∈ P) :
    p.support ⊆ Q.strictRoof T ∪ {p.finish} := by
  intro x hxp
  by_cases hxT : x ∈ T
  · right
    have hxTerminal : x = p.finish := by
      exact (Option.some.inj
        (hP.2 (Sum.inl p) hp x hxp hxT)).symm
    simpa only [Set.mem_singleton_iff] using hxTerminal
  · left
    refine ⟨hbelow ⟨Sum.inl p, hp, hxp⟩, ?_⟩
    intro hxEssential
    apply hxT
    rwa [hTessential] at hxEssential

/-- Full source-exact annular conclusion for the clean complementary track.
The returned star is a tight `A`--`T` linkage; target-linking components are
not included here and can therefore be frozen separately. -/
theorem exists_tightNormalizedCleanContinuation
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (Q : DWeb V) {A C D T E : Set V} {W F : Set Q.DPath}
    (hNorm : Q.IsNormalized)
    (hA : A ⊆ Q.source)
    (hW : IsLinkageBetween Q A C W)
    (hsep : IsSeparatorFrom Q Q.source C)
    (hWclean : SingularContinuation.TerminalCleanAt Q W C)
    (hD : D = Q.terminalFrontier W)
    (hDC : D ⊆ C)
    (hCtrim : IsTrimmedSeparator Q C)
    (hCsource : (Q.quotient C).source = C)
    (hCroof : C ⊆ Q.roof T)
    (hCQ : (Q.quotient C).IsUnhindered)
    (hTessential : Q.essential T = T)
    (hEsub : E ⊆ D) (hEsmall : #E < kappa)
    (hF : IsLinkageBetween Q (D \ E) T F)
    (hFtight : SliceSpliceSource.MeetsOnlyAtTerminal Q F T)
    (hWF : Q.StarCompatible W F) :
    ∃ (R : Set (SliceRestrictedDelta.normalizedDelta Q C D T F).DPath)
        (hcompat : Q.StarCompatible W
          (SliceDeltaLift.liftNormalizedFamily Q C D T F R)),
      IsLinkageBetween (SliceRestrictedDelta.normalizedDelta Q C D T F)
          D T R ∧
        SliceSpliceSource.TightLinkageBetween Q A T (Q.star hcompat) ∧
        #(↥(R \ SliceDeltaLift.normalizedRestrictedFamily
            Q C D T hF
              (SliceDeltaLift.sourcePure_of_starCompatible Q
                (hD.symm ▸ Set.Subset.rfl) hWF)
              hFtight)) < kappa := by
  obtain ⟨R, hR, hcompat, hRsmall⟩ :=
    exists_normalizedCompletion_of_clean_partial_exchange
      hlower hregular huncountable Q hA hW hsep hWclean hD hDC hCtrim
        hCsource hCroof hCQ hTessential hEsub hEsmall hF hFtight hWF
  have hWroof : Q.vertexSet W ⊆ Q.roof C :=
    partialLinkage_vertexSet_subset_roof Q hW hA hsep hWclean
  have hTstrict : Disjoint (Q.strictRoof C) T :=
    disjoint_strictRoof_of_trimmed_of_essential_of_subset_roof
      Q hCtrim hTessential hCroof
  have hWT : SliceSpliceSource.MeetsOnlyAtTerminal Q W T :=
    SliceSpliceSource.meetsOnlyAtTerminal_of_roof_of_disjoint_strictRoof
      hCtrim hWroof hWclean hTstrict
  have hRlift : IsLinkageBetween Q D T
      (SliceDeltaLift.liftNormalizedFamily Q C D T F R) :=
    SliceDeltaLift.IsLinkageBetween.liftNormalizedDelta Q C D T F hR
  have hRliftTight : SliceSpliceSource.TightLinkageBetween Q D T
      (SliceDeltaLift.liftNormalizedFamily Q C D T F R) :=
    ⟨hRlift,
      SliceDeltaLift.meetsOnlyAtTerminal_liftNormalizedFamily Q C D T F R⟩
  refine ⟨R, hcompat, hR, ?_, hRsmall⟩
  exact tightLinkageBetween_star_terminalFrontier Q hNorm hA
    ⟨hW, hWclean⟩ hRliftTight hD hWT hcompat

/-- Proof-carrying output of the clean one-stage annular construction.  It
retains both small exceptional sets needed by the causal carrier, while the
`resultTight` field is the actual clean row advanced to the later boundary. -/
structure CleanAnnularCompletion
    (Q : DWeb V) (A C T : Set V) (kappa : Cardinal.{u}) where
  stopped : Set Q.DPath
  exceptional : Set V
  suffix : Set Q.DPath
  stoppedLinkage : IsLinkageBetween Q A C stopped
  stoppedClean : SingularContinuation.TerminalCleanAt Q stopped C
  exceptional_subset : exceptional ⊆ Q.terminalFrontier stopped
  exceptional_small : #exceptional < kappa
  suffixLinkage : IsLinkageBetween Q
    (Q.terminalFrontier stopped \ exceptional) T suffix
  suffixTight : SliceSpliceSource.MeetsOnlyAtTerminal Q suffix T
  suffixCompatible : Q.StarCompatible stopped suffix
  filled : Set (SliceRestrictedDelta.normalizedDelta Q C
    (Q.terminalFrontier stopped) T suffix).DPath
  filledLinkage : IsLinkageBetween
    (SliceRestrictedDelta.normalizedDelta Q C
      (Q.terminalFrontier stopped) T suffix)
    (Q.terminalFrontier stopped) T filled
  filledCompatible : Q.StarCompatible stopped
    (SliceDeltaLift.liftNormalizedFamily Q C
      (Q.terminalFrontier stopped) T suffix filled)
  resultTight : SliceSpliceSource.TightLinkageBetween Q A T
    (Q.star filledCompatible)
  deviationSmall : #(↥(filled \
    SliceDeltaLift.normalizedRestrictedFamily Q C
      (Q.terminalFrontier stopped) T suffixLinkage
      (SliceDeltaLift.sourcePure_of_starCompatible Q
        Set.Subset.rfl suffixCompatible) suffixTight)) < kappa

/-- Whole-component replacement followed by the source-exact normalized
`Delta` fill.  This is the complete unconditional local provider for the
clean complementary row.  Protecting target components frozen at earlier
history stages is deliberately a separate, history-sensitive obligation. -/
theorem exists_cleanAnnularCompletion_of_componentReplacement
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (Q : DWeb V) {A C T E : Set V} {W Y : Set Q.DPath}
    (hNorm : Q.IsNormalized)
    (hA : A ⊆ Q.source)
    (hW : IsLinkageBetween Q A C W)
    (hWclean : SingularContinuation.TerminalCleanAt Q W C)
    (hsep : IsSeparatorFrom Q Q.source C)
    (hCtrim : IsTrimmedSeparator Q C)
    (hCsource : (Q.quotient C).source = C)
    (hCroof : C ⊆ Q.roof T)
    (hCQ : (Q.quotient C).IsUnhindered)
    (hTessential : Q.essential T = T)
    (hY : IsLinkageBetween Q (A \ E) T Y)
    (hYtight : SliceSpliceSource.MeetsOnlyAtTerminal Q Y T)
    (hYsep : RelationalRoof.Separates Q.graph.Adj (A \ E) T C)
    (hEsub : E ⊆ A) (hEsmall : #E < kappa) :
    Nonempty (CleanAnnularCompletion Q A C T kappa) := by
  obtain ⟨W', E', F, hW', hW'clean, hE'sub, hE'small,
      hF, hWF, hFtight⟩ :=
    RegularCleanExchange.exists_cleanWholeTerminalExchange_of_componentReplacement
      Q hW hWclean hY hYtight hYsep hEsub hregular huncountable hEsmall
  have hDC : Q.terminalFrontier W' ⊆ C := hW'.terminalFrontier_subset
  obtain ⟨R, hcompat, hR, hresult, hRsmall⟩ :=
    exists_tightNormalizedCleanContinuation
      hlower hregular huncountable Q hNorm hA hW' hsep hW'clean rfl
        hDC hCtrim hCsource hCroof hCQ hTessential hE'sub hE'small
        hF hFtight hWF
  exact ⟨
    { stopped := W'
      exceptional := E'
      suffix := F
      stoppedLinkage := hW'
      stoppedClean := hW'clean
      exceptional_subset := hE'sub
      exceptional_small := hE'small
      suffixLinkage := hF
      suffixTight := hFtight
      suffixCompatible := hWF
      filled := R
      filledLinkage := hR
      filledCompatible := hcompat
      resultTight := hresult
      deviationSmall := hRsmall }⟩

/-- Stage-specialized clean provider.  The ordinary ladder intervals supply
the complement linkage; only the inessential later extensions are removed,
and their source set is small outside `phi`. -/
theorem exists_stageCleanAnnularCompletion
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    {L : Gamma.KappaLadder kappa} (hL : L.IsSplitLegal)
    (hNorm : Gamma.IsNormalized)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    {delta beta : Ladder.Stage kappa} (hdeltaBeta : delta < beta)
    (hbeta : beta ∉ L.phi)
    {A C : Set V} {W : Set (L.stageWeb delta).DPath}
    (hA : A ⊆ L.frontier delta)
    (hW : IsLinkageBetween (L.stageWeb delta) A C W)
    (hWclean : SingularContinuation.TerminalCleanAt
      (L.stageWeb delta) W C)
    (hsep : IsSeparatorFrom (L.stageWeb delta)
      (L.frontier delta) C)
    (hCtrim : IsTrimmedSeparator (L.stageWeb delta) C)
    (hCQ : ((L.stageWeb delta).quotient C).IsUnhindered)
    (hCroof : C ⊆ (L.stageWeb delta).roof (L.frontier beta)) :
    Nonempty (CleanAnnularCompletion (L.stageWeb delta) A C
      (L.frontier beta) kappa) := by
  let Q := L.stageWeb delta
  let E₀ := inessentialExtensionSources hL.sliceGeometry hdeltaBeta.le
  let E := A ∩ E₀
  let Y₀ := SliceCandidate.ordinaryStageFamily hL.sliceGeometry hdeltaBeta.le
  let Y := SliceSpliceSource.initialRestriction Q Y₀ (A \ E)
  have hY₀ : IsLinkageBetween Q (L.frontier delta \ E₀)
      (L.frontier beta) Y₀ :=
    SliceCandidate.ordinaryStageFamily_isLinkageBetween
      hL hdeltaBeta.le
  have hAEsub : A \ E ⊆ L.frontier delta \ E₀ := by
    rintro x ⟨hxA, hxE⟩
    refine ⟨hA hxA, ?_⟩
    intro hxE₀
    exact hxE ⟨hxA, hxE₀⟩
  have hY : IsLinkageBetween Q (A \ E) (L.frontier beta) Y :=
    SliceSpliceSource.isLinkageBetween_initialRestriction hY₀ hAEsub
  have hYtight : SliceSpliceSource.MeetsOnlyAtTerminal Q Y
      (L.frontier beta) := by
    intro p hp
    exact SliceCandidate.ordinaryStageFamily_meetsOnlyAtTerminal
      hL hdeltaBeta.le p hp.1
  have hTessential : Q.essential (L.frontier beta) = L.frontier beta :=
    stageWeb_laterFrontier_isEssential hL hNoEnter hdeltaBeta
  have hYsep : RelationalRoof.Separates Q.graph.Adj (A \ E)
      (L.frontier beta) C := by
    have hfull : RelationalRoof.Separates Q.graph.Adj
        (L.frontier delta) (L.frontier beta) C :=
      SliceSegmentCore.separates_between_of_roofed Q
        hTessential hsep hCroof
    intro a t p ha ht
    exact hfull p (hA ha.1) ht
  have hEsub : E ⊆ A := Set.inter_subset_left
  have hEsmall : #E < kappa :=
    (Cardinal.mk_subtype_mono Set.inter_subset_right).trans_lt
      (mk_inessentialExtensionSources_lt_of_not_mem_phi
        hL hdeltaBeta.le hbeta)
  have hNormQ : Q.IsNormalized := stageWeb_isNormalized hNorm L delta
  have hCsource : (Q.quotient C).source = C :=
    SingularContinuation.quotient_source_eq_stopover Q hsep hCtrim
  exact exists_cleanAnnularCompletion_of_componentReplacement
    hlower hregular huncountable Q hNormQ hA hW hWclean hsep hCtrim
      hCsource hCroof hCQ hTessential hY hYtight hYsep hEsub hEsmall

/-! ## Ambient annulus transport

Every path of the old stage web is already represented in the quotient by
the accumulated old frontier.  Consequently its ambient lift avoids the
old strict roof.  This elementary fact is independent of the later
completion and is useful in both the small-frontier and half-way branches.
-/

/-- A noninitial vertex of a lifted stage path avoids the complete roof of
the accumulated terminal frontier.  This is the quotient calculation used
by the ambient lower-region transport below. -/
private theorem liftStagePath_not_mem_rawRoof_of_ne_initial
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (delta : Ladder.Stage kappa)
    (p : (L.stageWeb delta).DPath) {x : V}
    (hxp : x ∈ (L.liftStagePath delta p).support)
    (hxne : x ≠ p.initial) :
    x ∉ Gamma.roof (Gamma.terminalFrontier (L.warpAt delta)) := by
  let T := Gamma.terminalFrontier (L.warpAt delta)
  let Q := Gamma.quotient T
  let p' : Q.essentialPart.DPath := p
  let q : Q.DPath := Q.liftEssentialPartPath p'
  have hxq : x ∈ q.support := by
    dsimp only [q]
    rw [Q.support_liftEssentialPartPath]
    rwa [L.support_liftStagePath delta p] at hxp
  have hxqne : x ≠ q.initial := by
    dsimp only [q]
    rw [Q.initial_liftEssentialPartPath]
    exact hxne
  have hav := Gamma.quotientPath_avoids_after_initial T q hxq hxqne
  intro hxRoof
  by_cases hxEssential : x ∈ Gamma.essential T
  · exact hav.2 (Gamma.essential_subset _ hxEssential)
  · exact hav.1 ⟨hxRoof, hxEssential⟩

/-- The ambient lift of an arbitrary stage-web family is contained in the
lower region at that stage. -/
theorem liftStageFamily_vertexSet_subset_lowerRegion
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} (hL : L.IsSplitLegal)
    {delta : Ladder.Stage kappa} {A B : Set V}
    {W : Set (L.stageWeb delta).DPath}
    (hW : IsLinkageBetween (L.stageWeb delta) A B W)
    (hA : A ⊆ L.frontier delta) :
    Gamma.vertexSet (SliceSegmentCore.liftStageFamily L delta W) ⊆
      L.lowerRegion delta := by
  rintro x ⟨p, ⟨q, hqW, rfl⟩, hxp⟩
  change x ∉ Gamma.strictRoof (L.frontier delta)
  by_cases hxInitial : x = q.initial
  · subst x
    have hxFrontier : q.initial ∈ L.frontier delta := by
      apply hA
      rw [← hW.initialSet_eq]
      exact ⟨q, hqW, rfl⟩
    have hxEssential : q.initial ∈
        Gamma.essential (L.frontier delta) := by
      rw [hL.frontiersEssential delta]
      exact hxFrontier
    exact fun hxStrict ↦ Set.disjoint_left.1
      (Gamma.disjoint_strictRoof_essential (L.frontier delta))
      hxStrict hxEssential
  · have hxNotRawRoof : x ∉ Gamma.roof
        (Gamma.terminalFrontier (L.warpAt delta)) :=
      liftStagePath_not_mem_rawRoof_of_ne_initial
        L delta q hxp hxInitial
    intro hxStrict
    apply hxNotRawRoof
    rw [L.frontier_eq_essential_terminalFrontier
      hL.roofsSourceAtStages delta,
      Gamma.strictRoof_essential] at hxStrict
    exact hxStrict.1

end RegularCandidateProvider
end CardinalInduction
end Erdos599
