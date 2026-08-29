/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RoofedDeletionQuotient
import ErdosProblems.Erdos599.RegularFixedStageTargetLinkingAnnular
import ErdosProblems.Erdos599.RegularProtectedDeltaLift
import ErdosProblems.Erdos599.SingularCardinal

/-!
# Rebuilding a regular continuation away from a protected roofed carrier

This file isolates the truthful local replacement for the old exact-frontier
provider.  The protected carrier is deleted only in the ambient web in which
the annular continuation is built.  `RoofedDeletionQuotient` supplies the
unhindered quotient at the surviving boundary; no unhinderedness assertion is
made about the whole deleted web.

The normalized-`Delta` fill below uses only lower-cardinal extension clauses.
It deliberately does not assume the historical simultaneous lower induction,
whose exact-frontier half-way conjunct is false in general.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace CardinalInduction
namespace RegularProtectedAmbientRebuild

open DirectedPath
open SliceCandidate

universe u
variable {V : Type u}

/-- The exact lower-induction fragment used by normalized `Delta`: only the
extension clause is required. -/
def ExtensionBelowFor (Base : DWeb V) (kappa : Cardinal.{u}) : Prop :=
  ∀ rho, rho < kappa → ∀ G : DWeb V,
    (∀ {x y : V}, G.graph.Adj x y → Base.graph.Adj x y) →
    G.IsUnhindered → ExtensionClauseAt G rho

/-- Lower-cardinal filling of normalized `Delta`, with no half-way induction
assumption. -/
theorem exists_normalizedDeltaLinkage_of_extensionBelow
    {kappa : Cardinal.{u}}
    {Base : DWeb V} (hlower : ExtensionBelowFor Base kappa)
    (Q : DWeb V) {C D T E : Set V} {F : Set Q.DPath}
    (hQBase : ∀ {x y : V}, Q.graph.Adj x y → Base.graph.Adj x y)
    (hDC : D ⊆ C)
    (htrim : IsTrimmedSeparator
      (SliceRestrictedDelta.normalizedDelta Q C D T F) C)
    (hcarrier :
      SliceRestrictedDelta.carrier Q C T F \
          (SliceRestrictedDelta.normalizedDelta Q C D T F).strictRoof
            (C \ D) =
        Q.roof T \ Q.strictRoof C)
    (hsource : (Q.quotient C).source = C)
    (hCroof : C ⊆ Q.roof T)
    (hQ : (Q.quotient C).IsUnhindered)
    (hEsub : E ⊆ D) (hE : #E < kappa)
    (Fdelta : Set
      (SliceRestrictedDelta.normalizedDelta Q C D T F).DPath)
    (hFdelta : IsLinkageBetween
      (SliceRestrictedDelta.normalizedDelta Q C D T F)
      (D \ E) T Fdelta) :
    ∃ R : Set (SliceRestrictedDelta.normalizedDelta Q C D T F).DPath,
      IsLinkageBetween
        (SliceRestrictedDelta.normalizedDelta Q C D T F) D T R := by
  let Delta := SliceRestrictedDelta.normalizedDelta Q C D T F
  have hDelta : Delta.IsUnhindered :=
    SliceRestrictedDelta.normalizedDelta_isUnhindered_of_geometry
      Q F hDC htrim hcarrier hsource hCroof hQ
  have hDeltaBase : ∀ {x y : V},
      Delta.graph.Adj x y → Base.graph.Adj x y := by
    intro x y hxy
    exact hQBase hxy.1.1
  have hstep : ExtensionClauseAt Delta #E :=
    hlower #E hE Delta hDeltaBase hDelta
  have hcomplement : IsLinkageBetween Delta
      (Delta.source \ E) Delta.target Fdelta := by
    simpa only [Delta, SliceRestrictedDelta.normalizedDelta_source,
      SliceRestrictedDelta.normalizedDelta_target] using hFdelta
  obtain ⟨R, hR⟩ := hstep E
    (by simpa only [Delta, SliceRestrictedDelta.normalizedDelta_source]
      using hEsub)
    rfl ⟨Fdelta, hcomplement⟩
  exact ⟨R, by
    simpa only [Delta, SliceRestrictedDelta.normalizedDelta_source,
      SliceRestrictedDelta.normalizedDelta_target] using hR⟩

/-- The normalized completion, retaining its small deviation certificate,
under the extension-only lower hypothesis. -/
theorem exists_normalizedDelta_completion_of_extensionBelow
    {kappa : Cardinal.{u}}
    {Base : DWeb V} (hlower : ExtensionBelowFor Base kappa)
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (Q : DWeb V) {C D T E : Set V} {F : Set Q.DPath}
    (hQBase : ∀ {x y : V}, Q.graph.Adj x y → Base.graph.Adj x y)
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
    RegularCandidateProvider.disjoint_strictRoof_of_trimmed_of_essential_of_subset_roof
      Q hCtrim hTessential hCroof
  have hsuffix : Q.vertexSet F ∩ Q.strictRoof C ⊆
      (SliceRestrictedDelta.normalizedDelta Q C D T F).strictRoof
        (C \ D) :=
    SliceDeltaLift.suffix_strictRoof_subset_normalizedDelta_strictRoof
      Q F hDC hCtrim hTstrict
  have hFroof : Q.vertexSet F ⊆ Q.roof T := by
    apply SliceRestrictedDelta.linkage_vertexSet_subset_roof_of_initial Q hF
    · exact (Set.sdiff_subset.trans hDC).trans hCroof
    · exact hFtight
  let Fdelta := SliceDeltaLift.normalizedRestrictedFamily
    Q C D T hF hsourcePure hFtight
  have hFdelta : IsLinkageBetween
      (SliceRestrictedDelta.normalizedDelta Q C D T F)
      (D \ E) T Fdelta :=
    SliceDeltaLift.normalizedRestrictedFamily_isLinkageBetween
      Q C D T hF hsourcePure hFtight
  obtain ⟨R₀, hR₀⟩ := exists_normalizedDeltaLinkage_of_extensionBelow
    hlower Q hQBase hDC
      (SliceRestrictedDelta.normalizedDelta_isTrimmedSeparator
        Q F hDC hCtrim hCroof)
      (SliceRestrictedDelta.retainedCarrier_eq_of_suffix_strictRoof
        Q F hDC hFroof hsuffix)
      hCsource hCroof hCQ hEsub hEsmall Fdelta hFdelta
  let Delta := SliceRestrictedDelta.normalizedDelta Q C D T F
  let R := SliceCandidate.componentMixedFamily Delta R₀ Fdelta E
  have hR : IsLinkageBetween Delta D T R :=
    SliceCandidate.componentMixedFamily_isLinkageBetween_of_complement
      Delta hR₀ hFdelta hEsub
  have hRsmall : #(↥(R \ Fdelta)) < kappa := by
    let Z := SliceCandidate.exceptionalComponentVertices Delta R₀ Fdelta E
    let Rleft := SliceCandidate.initialPart Delta R₀ Z
    have hdiff : R \ Fdelta ⊆ Rleft := by
      rintro p ⟨hpR, hpNotF⟩
      change p ∈ Rleft ∪ SliceCandidate.initialPart Delta Fdelta Zᶜ at hpR
      rcases hpR with hpLeft | hpRight
      · exact hpLeft
      · exact (hpNotF hpRight.1).elim
    exact (Cardinal.mk_subtype_mono hdiff).trans_lt
      (SliceCandidate.mk_componentMixedFamily_left_lt Delta
        hregular huncountable hR₀.isWarp hFdelta.isWarp
        hR₀.finiteCharacter hFdelta.finiteCharacter hEsmall)
  exact ⟨R, hR, hRsmall⟩

/-- Clean partial-source normalized completion using only lower extension
clauses. -/
theorem exists_normalizedCompletion_of_clean_partial_extensionBelow
    {kappa : Cardinal.{u}}
    {Base : DWeb V} (hlower : ExtensionBelowFor Base kappa)
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (Q : DWeb V) {A C D T E : Set V} {W F : Set Q.DPath}
    (hQBase : ∀ {x y : V}, Q.graph.Adj x y → Base.graph.Adj x y)
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
    RegularCandidateProvider.partialLinkage_vertexSet_subset_roof
      Q hW hA hsep hWclean
  have hsourcePure : ∀ p ∈ F, p.support ∩ D ⊆ {p.initial} :=
    SliceDeltaLift.sourcePure_of_starCompatible Q
      (hD.symm ▸ Set.Subset.rfl) hWF
  obtain ⟨R, hR, hRsmall⟩ :=
    exists_normalizedDelta_completion_of_extensionBelow
      hlower hregular huncountable Q hQBase hDC hCtrim hCsource hCroof hCQ
        hTessential hEsub hEsmall hF hFtight hsourcePure
  have hDcarrier : D ⊆ SliceRestrictedDelta.carrier Q C T F := by
    intro x hxD
    apply Or.inl
    refine ⟨hCroof (hDC hxD), ?_⟩
    intro hxStrict
    exact hxStrict.2 (by rw [hCtrim]; exact hDC hxD)
  refine ⟨R, hR, ?_, hRsmall⟩
  exact SliceDeltaLift.starCompatible_liftNormalizedFamily
    Q hWroof hWclean (hD.symm ▸ Set.Subset.rfl)
      hF hWF hDcarrier hR

/-- Tight clean continuation under the extension-only lower hypothesis. -/
theorem exists_tightNormalizedCleanContinuation_of_extensionBelow
    {kappa : Cardinal.{u}}
    {Base : DWeb V} (hlower : ExtensionBelowFor Base kappa)
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (Q : DWeb V) {A C D T E : Set V} {W F : Set Q.DPath}
    (hQBase : ∀ {x y : V}, Q.graph.Adj x y → Base.graph.Adj x y)
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
    exists_normalizedCompletion_of_clean_partial_extensionBelow
      hlower hregular huncountable Q hQBase hA hW hsep hWclean hD hDC hCtrim
        hCsource hCroof hCQ hTessential hEsub hEsmall hF hFtight hWF
  have hWroof : Q.vertexSet W ⊆ Q.roof C :=
    RegularCandidateProvider.partialLinkage_vertexSet_subset_roof
      Q hW hA hsep hWclean
  have hTstrict : Disjoint (Q.strictRoof C) T :=
    RegularCandidateProvider.disjoint_strictRoof_of_trimmed_of_essential_of_subset_roof
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
  exact RegularCandidateProvider.tightLinkageBetween_star_terminalFrontier
    Q hNorm hA ⟨hW, hWclean⟩ hRliftTight hD hWT hcompat

/-- Whole-component exchange followed by an extension-only normalized fill.
This is the local annular constructor used inside the deleted ambient web. -/
theorem exists_cleanAnnularCompletion_of_extensionBelow
    {kappa : Cardinal.{u}}
    {Base : DWeb V} (hlower : ExtensionBelowFor Base kappa)
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (Q : DWeb V) {A C T E : Set V} {W Y : Set Q.DPath}
    (hQBase : ∀ {x y : V}, Q.graph.Adj x y → Base.graph.Adj x y)
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
    Nonempty (RegularCandidateProvider.CleanAnnularCompletion
      Q A C T kappa) := by
  obtain ⟨W', E', F, hW', hW'clean, hE'sub, hE'small,
      hF, hWF, hFtight⟩ :=
    RegularCleanExchange.exists_cleanWholeTerminalExchange_of_componentReplacement
      Q hW hWclean hY hYtight hYsep hEsub hregular huncountable hEsmall
  have hDC : Q.terminalFrontier W' ⊆ C := hW'.terminalFrontier_subset
  obtain ⟨R, hcompat, hR, hresult, hRsmall⟩ :=
    exists_tightNormalizedCleanContinuation_of_extensionBelow
      hlower hregular huncountable Q hQBase hNorm hA hW' hsep hW'clean rfl
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

/-- The proof-carrying protected rebuild.  `core` is the complete annular
construction in `Q.delete X`, including the small ordinary-deviation
certificate.  `lifted` restores that continuation to `Q`; it remains tight
and its carrier is disjoint from `X`. -/
structure ProtectedAmbientCompletion
    (Q : DWeb V) (X C T : Set V) (kappa : Cardinal.{u}) where
  core : RegularCandidateProvider.CleanAnnularCompletion
    (Q.delete X) (Q.delete X).source (C \ X) (T \ X) kappa
  lifted : Set Q.DPath
  lifted_eq : lifted = Q.liftDeleteFamily X
    ((Q.delete X).star core.filledCompatible)
  liftedTight : SliceSpliceSource.TightLinkageBetween
    Q (Q.delete X).source T lifted
  liftedAvoids : Disjoint (Q.vertexSet lifted) X

/-- Initial vertices are no more numerous than the paths of the family. -/
theorem mk_initialSet_le_family (G : DWeb V) (W : Set G.DPath) :
    #(G.initialSet W) ≤ #W := by
  let choosePath : G.initialSet W → W := fun x ↦
    ⟨Classical.choose x.2, (Classical.choose_spec x.2).1⟩
  apply Cardinal.mk_le_of_injective (f := choosePath)
  intro x y hxy
  apply Subtype.ext
  have hx := (Classical.choose_spec x.2).2
  have hy := (Classical.choose_spec y.2).2
  exact calc
    x.1 = (choosePath x).1.initial := hx.symm
    _ = (choosePath y).1.initial :=
      congrArg (fun p : W ↦ p.1.initial) hxy
    _ = y.1 := hy

/-- An ambient linkage avoiding `X` retypes to the deleted web and loses
only the deleted points from its right endpoint set. -/
theorem IsLinkageBetween.restrictDeleteFamily
    (G : DWeb V) (X : Set V) {A B : Set V} {W : Set G.DPath}
    (hW : IsLinkageBetween G A B W)
    (havoid : Disjoint (G.vertexSet W) X) :
    IsLinkageBetween (G.delete X) A (B \ X)
      (G.restrictDeleteFamily X W havoid) := by
  refine ⟨DWeb.IsWarp.restrictDeleteFamily G hW.isWarp havoid,
    G.fd_hasFiniteCharacter_restrictDeleteFamily hW.finiteCharacter havoid,
    ?_, ?_, ?_⟩
  · simpa only [G.initialSet_restrictDeleteFamily] using hW.initialSet_eq
  · rw [G.terminalFrontier_restrictDeleteFamily]
    rintro x hx
    refine ⟨hW.terminalFrontier_subset hx, ?_⟩
    obtain ⟨p, hpW, hpx⟩ := hx
    intro hxX
    exact Set.disjoint_left.1 havoid
      ⟨p, hpW, G.terminal_mem_support hpx⟩ hxX
  · rintro q ⟨p, _hp, rfl⟩
    obtain ⟨f, hpf, hends, hsource⟩ := hW.endpointPure p.1 p.2
    have hpfin : p.1 = (Sum.inl f : G.DPath) := hpf
    have hqmem : G.restrictDeleteMember X W havoid p ∈
        G.restrictDeleteFamily X W havoid := ⟨p, Set.mem_univ p, rfl⟩
    obtain ⟨f', hf'⟩ :=
      G.fd_hasFiniteCharacter_restrictDeleteFamily
        hW.finiteCharacter havoid hqmem
    refine ⟨f', hf', ?_, ?_⟩
    · have hsupport : f'.support = f.support := by
        calc
          f'.support = (G.restrictDeleteMember X W havoid p).support :=
            (congrArg Path.support hf').symm
          _ = p.1.support := G.support_restrictDeleteMember X W havoid p
          _ = f.support := congrArg Path.support hpfin
      have hstart : f'.start = f.start := by
        have hi' := congrArg Path.initial hf'
        have hi := G.initial_restrictDeleteMember X W havoid p
        exact hi'.symm.trans (hi.trans (congrArg Path.initial hpfin))
      have hfinish : f'.finish = f.finish := by
        have ht := G.terminal?_restrictDeleteMember X W havoid p
        rw [hf', hpfin] at ht
        exact Option.some.inj ht
      rw [hsupport, hstart, hfinish]
      calc
        f.support ∩ (A ∪ (B \ X)) = f.support ∩ (A ∪ B) := by
          ext x
          simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_sdiff]
          constructor
          · rintro ⟨hxf, hxA | ⟨hxB, _⟩⟩
            · exact ⟨hxf, Or.inl hxA⟩
            · exact ⟨hxf, Or.inr hxB⟩
          · rintro ⟨hxf, hxA | hxB⟩
            · exact ⟨hxf, Or.inl hxA⟩
            · refine ⟨hxf, Or.inr ⟨hxB, ?_⟩⟩
              intro hxX
              exact Set.disjoint_left.1 havoid
                ⟨p.1, p.2, hpfin ▸ hxf⟩ hxX
        _ = {f.start, f.finish} := hends
    · have hsupport : f'.support = f.support := by
        calc
          f'.support = (G.restrictDeleteMember X W havoid p).support :=
            (congrArg Path.support hf').symm
          _ = p.1.support := G.support_restrictDeleteMember X W havoid p
          _ = f.support := congrArg Path.support hpfin
      have hstart : f'.start = f.start := by
        have hi' := congrArg Path.initial hf'
        have hi := G.initial_restrictDeleteMember X W havoid p
        exact hi'.symm.trans (hi.trans (congrArg Path.initial hpfin))
      rw [hsupport, hstart]
      exact hsource

/-- Terminal cleanliness is unchanged by retyping an avoiding family into
the deleted web. -/
theorem terminalCleanAt_restrictDeleteFamily
    (G : DWeb V) (X C : Set V) {W : Set G.DPath}
    (havoid : Disjoint (G.vertexSet W) X)
    (hclean : SingularContinuation.TerminalCleanAt G W C) :
    SingularContinuation.TerminalCleanAt (G.delete X)
      (G.restrictDeleteFamily X W havoid) (C \ X) := by
  rintro _ ⟨p, _hp, rfl⟩ x hxp hxC
  rw [G.terminal?_restrictDeleteMember]
  apply hclean p.1 p.2 x
  · simpa only [G.support_restrictDeleteMember] using hxp
  · exact hxC.1

/-- Tightness is unchanged by retyping an avoiding family into the deleted
web. -/
theorem meetsOnlyAtTerminal_restrictDeleteFamily
    (G : DWeb V) (X T : Set V) {W : Set G.DPath}
    (havoid : Disjoint (G.vertexSet W) X)
    (htight : SliceSpliceSource.MeetsOnlyAtTerminal G W T) :
    SliceSpliceSource.MeetsOnlyAtTerminal (G.delete X)
      (G.restrictDeleteFamily X W havoid) (T \ X) := by
  rintro _ ⟨p, _hp, rfl⟩ x hxp hxT
  rw [G.terminal?_restrictDeleteMember]
  apply htight p.1 p.2 x
  · simpa only [G.support_restrictDeleteMember] using hxp
  · exact hxT.1

/-- Ordinary paths that meet the protected carrier are charged only by
their initial vertices.  Removing those initials leaves a literal
subfamily of the old ordinary linkage which avoids `X`. -/
structure AvoidingOrdinaryPreparation
    (Q : DWeb V) (X T E₀ : Set V) (Y₀ : Set Q.DPath)
    (kappa : Cardinal.{u}) where
  exceptional : Set V
  family : Set Q.DPath
  exceptional_subset : exceptional ⊆ (Q.delete X).source
  exceptional_small : #exceptional < kappa
  familyLinkage : IsLinkageBetween Q
    ((Q.delete X).source \ exceptional) T family
  familyTight : SliceSpliceSource.MeetsOnlyAtTerminal Q family T
  familyAvoids : Disjoint (Q.vertexSet family) X
  family_subset : family ⊆ Y₀

theorem exists_avoidingOrdinaryPreparation
    {kappa : Cardinal.{u}} (hregular : kappa.IsRegular)
    (Q : DWeb V) {X T E₀ : Set V} {Y₀ : Set Q.DPath}
    (hXsmall : #X < kappa) (hE₀small : #E₀ < kappa)
    (hY₀ : IsLinkageBetween Q (Q.source \ E₀) T Y₀)
    (hY₀tight : SliceSpliceSource.MeetsOnlyAtTerminal Q Y₀ T) :
    Nonempty (AvoidingOrdinaryPreparation Q X T E₀ Y₀ kappa) := by
  let M : Set Q.DPath :=
    {p | p ∈ Y₀ ∧ ¬ Disjoint p.support X}
  let E : Set V := (Q.delete X).source ∩ (E₀ ∪ Q.initialSet M)
  let A : Set V := (Q.delete X).source \ E
  let Y : Set Q.DPath := SliceSpliceSource.initialRestriction Q Y₀ A
  have hMsmall : #M < kappa :=
    (Q.mk_pathsMeeting_le Y₀ X hY₀.isWarp).trans_lt hXsmall
  have hEMsmall : #(Q.initialSet M) < kappa :=
    (mk_initialSet_le_family Q M).trans_lt hMsmall
  have hEsmall : #E < kappa := by
    refine (Cardinal.mk_subtype_mono Set.inter_subset_right).trans_lt ?_
    exact (Cardinal.mk_union_le E₀ (Q.initialSet M)).trans_lt
      (Cardinal.add_lt_of_lt hregular.aleph0_le hE₀small hEMsmall)
  have hAsub : A ⊆ Q.source \ E₀ := by
    rintro x ⟨hxSource, hxE⟩
    refine ⟨hxSource.1, ?_⟩
    intro hxE₀
    exact hxE ⟨hxSource, Or.inl hxE₀⟩
  have hY : IsLinkageBetween Q A T Y :=
    SliceSpliceSource.isLinkageBetween_initialRestriction hY₀ hAsub
  have hYtight : SliceSpliceSource.MeetsOnlyAtTerminal Q Y T := by
    intro p hp
    exact hY₀tight p hp.1
  have hYavoid : Disjoint (Q.vertexSet Y) X := by
    apply Set.disjoint_left.2
    rintro x ⟨p, hpY, hxp⟩ hxX
    have hpM : p ∈ M := by
      refine ⟨hpY.1, ?_⟩
      rw [Set.not_disjoint_iff]
      exact ⟨x, hxp, hxX⟩
    have hpInitialM : p.initial ∈ Q.initialSet M := ⟨p, hpM, rfl⟩
    exact hpY.2.2 ⟨hpY.2.1, Or.inr hpInitialM⟩
  exact ⟨
    { exceptional := E
      family := Y
      exceptional_subset := Set.inter_subset_left
      exceptional_small := hEsmall
      familyLinkage := hY
      familyTight := hYtight
      familyAvoids := hYavoid
      family_subset := fun _ hp ↦ hp.1 }⟩

/-- Widen the right endpoint of a linkage after restoring a deleted carrier.
Avoidance rules out a newly admitted right-endpoint vertex in the interior. -/
theorem IsLinkageBetween.mono_target_sdiff
    {G : DWeb V} {A B X : Set V} {W : Set G.DPath}
    (hW : IsLinkageBetween G A (B \ X) W)
    (havoid : Disjoint (G.vertexSet W) X) :
    IsLinkageBetween G A B W := by
  refine ⟨hW.isWarp, hW.finiteCharacter, hW.initialSet_eq,
    hW.terminalFrontier_subset.trans Set.sdiff_subset, ?_⟩
  intro p hp
  obtain ⟨f, rfl, hends, hsource⟩ := hW.endpointPure p hp
  refine ⟨f, rfl, ?_, hsource⟩
  calc
    f.support ∩ (A ∪ B) = f.support ∩ (A ∪ (B \ X)) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_sdiff]
      constructor
      · rintro ⟨hxf, hxA | hxB⟩
        · exact ⟨hxf, Or.inl hxA⟩
        · refine ⟨hxf, Or.inr ⟨hxB, ?_⟩⟩
          intro hxX
          exact Set.disjoint_left.1 havoid
            ⟨Sum.inl f, hp, hxf⟩ hxX
      · rintro ⟨hxf, hxA | ⟨hxB, _⟩⟩
        · exact ⟨hxf, Or.inl hxA⟩
        · exact ⟨hxf, Or.inr hxB⟩
    _ = {f.start, f.finish} := hends

/-- Tightness also survives lifting out of a vertex deletion and widening
the target from `T \ X` to `T`. -/
theorem tightLinkageBetween_liftDeleteFamily_mono_target
    (Q : DWeb V) (X A T : Set V)
    {W : Set (Q.delete X).DPath}
    (hW : SliceSpliceSource.TightLinkageBetween
      (Q.delete X) A (T \ X) W)
    (hA : A ⊆ (Q.delete X).source) :
    SliceSpliceSource.TightLinkageBetween Q A T
      (Q.liftDeleteFamily X W) := by
  have hlift : IsLinkageBetween Q A (T \ X)
      (Q.liftDeleteFamily X W) :=
    RegularProtectedDeltaLift.IsLinkageBetween.liftDeleteFamily Q X hW.1
  have hstart : (Q.delete X).initialSet W ⊆ (Q.delete X).source := by
    rw [hW.1.initialSet_eq]
    exact hA
  have havoid : Disjoint (Q.vertexSet (Q.liftDeleteFamily X W)) X :=
    Q.vertexSet_liftDeleteFamily_disjoint hstart
  refine ⟨IsLinkageBetween.mono_target_sdiff hlift havoid, ?_⟩
  rintro _ ⟨p, hpW, rfl⟩ x hxp hxT
  have hxNotX : x ∉ X := by
    exact fun hxX ↦ Set.disjoint_left.1 havoid
      ⟨Q.liftDeletePath X p, ⟨p, hpW, rfl⟩, hxp⟩ hxX
  rw [Q.terminal?_liftDeletePath]
  apply hW.2 p hpW x
  · simpa only [Q.support_liftDeletePath] using hxp
  · exact ⟨hxT, hxNotX⟩

/-- The concrete protected ambient rebuild.  Its hypotheses are all facts
about the original separator and two linkages in the genuinely deleted web.
In particular, no full-deletion unhinderedness and no exact-frontier
half-way clause is assumed. -/
theorem exists_protectedAmbientCompletion
    {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (Q : DWeb V) {X C T E : Set V}
    (hlower : ExtensionBelowFor Q kappa)
    {W Y : Set (Q.delete X).DPath}
    (hNorm : Q.IsNormalized)
    (hXroof : X ⊆ Q.roof C)
    (hCtrim : IsTrimmedSeparator Q C)
    (hsep : IsSeparatorFrom Q Q.source C)
    (hCQ : (Q.quotient C).IsUnhindered)
    (hCroof : C ⊆ Q.roof T)
    (hTessential : Q.essential T = T)
    (hW : IsLinkageBetween (Q.delete X) (Q.delete X).source
      (C \ X) W)
    (hWclean : SingularContinuation.TerminalCleanAt
      (Q.delete X) W (C \ X))
    (hY : IsLinkageBetween (Q.delete X)
      ((Q.delete X).source \ E) (T \ X) Y)
    (hYtight : SliceSpliceSource.MeetsOnlyAtTerminal
      (Q.delete X) Y (T \ X))
    (hEsub : E ⊆ (Q.delete X).source) (hEsmall : #E < kappa) :
    Nonempty (ProtectedAmbientCompletion Q X C T kappa) := by
  let H := Q.delete X
  let C' := C \ X
  let T' := T \ X
  have hXroofT : X ⊆ Q.roof T :=
    hXroof.trans (Q.roof_cut hCroof)
  have hNormH : H.IsNormalized :=
    SingularExtension.DWeb.IsNormalized.delete hNorm X
  have hCtrimH : IsTrimmedSeparator H C' := by
    exact Q.delete_essential_sdiff_eq_of_subset_roof hXroof hCtrim
  have hTtrimH : H.essential T' = T' := by
    exact Q.delete_essential_sdiff_eq_of_subset_roof hXroofT hTessential
  have hsepH : IsSeparatorFrom H H.source C' := by
    change H.source ⊆ H.roof C'
    rw [show H.roof C' = Q.roof C by
      exact Q.delete_roof_sdiff_eq_of_subset_roof hXroof hCtrim]
    exact Set.sdiff_subset.trans hsep
  have hCroofH : C' ⊆ H.roof T' := by
    rw [show H.roof T' = Q.roof T by
      exact Q.delete_roof_sdiff_eq_of_subset_roof hXroofT hTessential]
    exact Set.sdiff_subset.trans hCroof
  have hCQH : (H.quotient C').IsUnhindered := by
    rw [show H.quotient C' = (Q.quotient C).delete (X ∩ C) by
      exact Q.delete_quotient_sdiff_eq_quotient_delete_inter_of_subset_roof
        hXroof hCtrim hsep]
    apply SingularExtension.delete_sourceSet_isUnhindered
      (Q.quotient C) hCQ
    have hsourceQC : (Q.quotient C).source = C :=
      SingularContinuation.quotient_source_eq_stopover Q hsep hCtrim
    rw [hsourceQC]
    exact Set.inter_subset_right
  have hCsourceH : (H.quotient C').source = C' :=
    SingularContinuation.quotient_source_eq_stopover H hsepH hCtrimH
  have hYsep : RelationalRoof.Separates H.graph.Adj
      (H.source \ E) T' C' := by
    have hfull : RelationalRoof.Separates H.graph.Adj H.source T' C' :=
      SliceSegmentCore.separates_between_of_roofed
        H hTtrimH hsepH hCroofH
    intro a t p ha ht
    exact hfull p ha.1 ht
  obtain ⟨completion⟩ := exists_cleanAnnularCompletion_of_extensionBelow
    hlower hregular huncountable H
      (by intro x y hxy; exact hxy.1) hNormH
      (Set.Subset.rfl : H.source ⊆ H.source)
      hW hWclean hsepH hCtrimH hCsourceH hCroofH hCQH hTtrimH
      hY hYtight hYsep hEsub hEsmall
  let lifted := Q.liftDeleteFamily X (H.star completion.filledCompatible)
  have hliftedTight : SliceSpliceSource.TightLinkageBetween
      Q H.source T lifted :=
    tightLinkageBetween_liftDeleteFamily_mono_target
      Q X H.source T completion.resultTight Set.Subset.rfl
  have hstart : H.initialSet (H.star completion.filledCompatible) ⊆ H.source := by
    rw [completion.resultTight.1.initialSet_eq]
  have havoid : Disjoint (Q.vertexSet lifted) X :=
    Q.vertexSet_liftDeleteFamily_disjoint hstart
  exact ⟨
    { core := completion
      lifted := lifted
      lifted_eq := rfl
      liftedTight := hliftedTight
      liftedAvoids := havoid }⟩

/-- Assembly-facing protected rebuild.  The completed blueprint track is
represented by its carrier `X`; the clean remainder `W` and the ordinary
stage linkage `Y₀` are still ambient families.  Paths of `Y₀` meeting `X`
are charged to a small exceptional source set, both families are retyped in
`Q.delete X`, and `exists_protectedAmbientCompletion` performs the actual
annular reconstruction and lift. -/
theorem exists_protectedAmbientCompletion_of_ambientRemainder
    {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (Q : DWeb V) {X C T E₀ : Set V}
    (hlower : ExtensionBelowFor Q kappa)
    {W Y₀ : Set Q.DPath}
    (hNorm : Q.IsNormalized)
    (hXsmall : #X < kappa)
    (hXroof : X ⊆ Q.roof C)
    (hCtrim : IsTrimmedSeparator Q C)
    (hsep : IsSeparatorFrom Q Q.source C)
    (hCQ : (Q.quotient C).IsUnhindered)
    (hCroof : C ⊆ Q.roof T)
    (hTessential : Q.essential T = T)
    (hW : IsLinkageBetween Q (Q.delete X).source C W)
    (hWclean : SingularContinuation.TerminalCleanAt Q W C)
    (hWavoid : Disjoint (Q.vertexSet W) X)
    (hE₀small : #E₀ < kappa)
    (hY₀ : IsLinkageBetween Q (Q.source \ E₀) T Y₀)
    (hY₀tight : SliceSpliceSource.MeetsOnlyAtTerminal Q Y₀ T) :
    Nonempty (ProtectedAmbientCompletion Q X C T kappa) := by
  obtain ⟨ordinary⟩ := exists_avoidingOrdinaryPreparation
    hregular Q hXsmall hE₀small hY₀ hY₀tight
  let WR := Q.restrictDeleteFamily X W hWavoid
  let YR := Q.restrictDeleteFamily X ordinary.family ordinary.familyAvoids
  have hWR : IsLinkageBetween (Q.delete X) (Q.delete X).source
      (C \ X) WR :=
    IsLinkageBetween.restrictDeleteFamily Q X hW hWavoid
  have hWRclean : SingularContinuation.TerminalCleanAt
      (Q.delete X) WR (C \ X) :=
    terminalCleanAt_restrictDeleteFamily Q X C hWavoid hWclean
  have hYR : IsLinkageBetween (Q.delete X)
      ((Q.delete X).source \ ordinary.exceptional) (T \ X) YR :=
    IsLinkageBetween.restrictDeleteFamily
      Q X ordinary.familyLinkage ordinary.familyAvoids
  have hYRtight : SliceSpliceSource.MeetsOnlyAtTerminal
      (Q.delete X) YR (T \ X) :=
    meetsOnlyAtTerminal_restrictDeleteFamily
      Q X T ordinary.familyAvoids ordinary.familyTight
  exact exists_protectedAmbientCompletion
    hregular huncountable Q hlower hNorm hXroof hCtrim hsep hCQ hCroof
      hTessential hWR hWRclean hYR hYRtight ordinary.exceptional_subset
      ordinary.exceptional_small

#print axioms exists_protectedAmbientCompletion
#print axioms exists_protectedAmbientCompletion_of_ambientRemainder

end RegularProtectedAmbientRebuild
end CardinalInduction
end Erdos599
