/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularProtectedAmbientRebuild
import ErdosProblems.Erdos599.RegularStarMaverickBound
import ErdosProblems.Erdos599.SafeLinkGroundFinal
import ErdosProblems.Erdos599.BlueprintSplice

/-!
# Maverick control for the protected ambient rebuild

The basic protected rebuild deliberately stores only its completed clean
family.  This file retains the ordinary-family provenance while performing
that construction and proves the small-maverick conclusion before the local
whole-component witnesses are erased.  It then transports the conclusion
out of the vertex deletion.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace CardinalInduction
namespace RegularProtectedAmbientMaverick

open DirectedPath SliceCandidate SliceSpliceSource

universe u
variable {V : Type u}

private theorem liftNormalizedPath_normalizedRestrictedPath
    (Q : DWeb V) (C D T : Set V) {A : Set V} {F : Set Q.DPath}
    (hF : IsLinkageBetween Q A T F)
    (hsource : ∀ p ∈ F, p.support ∩ D ⊆ {p.initial})
    (htarget : MeetsOnlyAtTerminal Q F T) (p : F) :
    SliceDeltaLift.liftNormalizedPath Q C D T F
        (SliceDeltaLift.normalizedRestrictedPath Q C D T
          hF hsource htarget p) = p.1 := by
  obtain ⟨f, hpf⟩ := hF.finiteCharacter p.2
  have hfiniteMember :
      Q.finiteMemberPath F hF.finiteCharacter p = f := by
    apply Sum.inl.inj
    exact (Q.finiteMemberPath_eq F hF.finiteCharacter p).symm.trans hpf
  rw [hpf]
  apply congrArg Sum.inl
  let q := SliceDeltaLift.normalizedRestrictedFiniteMember Q C D T
    hF hsource htarget p
  let lifted := q.lift
    (fun {_ _} (e : (SliceRestrictedDelta.normalizedDelta
      Q C D T F).graph.Adj _ _) => e.1.1)
  change lifted = f
  have hstart : lifted.start = f.start := by
    change q.start = f.start
    rw [SliceDeltaLift.start_normalizedRestrictedFiniteMember, hpf]
    rfl
  have hfinish : lifted.finish = f.finish := by
    change q.finish = f.finish
    apply Option.some.inj
    rw [SliceDeltaLift.finish_normalizedRestrictedFiniteMember, hpf]
    rfl
  have hsupport : lifted.walk.support = f.walk.support := by
    rw [show lifted.walk.support = q.walk.support by
      exact DirectedPath.Walk.support_lift _ q.walk]
    dsimp only [q, SliceDeltaLift.normalizedRestrictedFiniteMember,
      SliceRestrictedDelta.normalizedDelta]
    change ((SliceRestrictedDelta.delta Q C D T F).normalizeWalk
      (SliceDeltaLift.restrictedFiniteMember Q C D T hF p).walk _ _).support =
        f.walk.support
    rw [(SliceRestrictedDelta.delta Q C D T F).support_normalizeWalk]
    dsimp only [SliceDeltaLift.restrictedFiniteMember]
    change ((Q.finiteMemberPath F hF.finiteCharacter p).walk
      |>.restrictGraphOnSupport _).support = f.walk.support
    rw [DirectedPath.Walk.support_restrictGraphOnSupport, hfiniteMember]
  rcases lifted with ⟨a, b, w, hw⟩
  rcases f with ⟨c, d, z, hz⟩
  dsimp only at hstart hfinish hsupport ⊢
  subst c
  subst d
  have hwz : w = z := Erdos599.DirectedPath.Walk.eq_of_support_eq w z hsupport
  subst z
  rfl

private theorem star_wholeExchange_suffix_isLadderFragment
    (Q : DWeb V) {A C T E : Set V} {W Y R : Set Q.DPath}
    (hW : IsLinkageBetween Q A C W)
    (hY : IsLinkageBetween Q (A \ E) T Y)
    (hsep : RelationalRoof.Separates Q.graph.Adj (A \ E) T C)
    (hEsub : E ⊆ A)
    (hRwarp : Q.IsWarp R)
    (hcompat : Q.StarCompatible
      (SliceCandidate.wholeComponentMixedFamily Q W
        (SliceCandidate.firstHitPrefixFamily hY hsep) Y E) R)
    (p : SliceCandidate.wholeComponentMixedFamily Q W
      (SliceCandidate.firstHitPrefixFamily hY hsep) Y E)
    (q : Q.DPath)
    (hqR : q ∈ R)
    (hq : q ∈ SliceCandidate.selectedSuffixFamily hY hsep
      (SliceCandidate.wholeNonexceptionalPrefixSources hY hsep W))
    (hpq : Q.terminal? p.1 = some q.initial) :
    ControlledSlices.IsLadderFragment Q Y
      (Q.starPath hcompat p) := by
  classical
  let D := SliceCandidate.exceptionalComponentVertices Q W Y E
  let P := SliceCandidate.firstHitPrefixFamily hY hsep
  let W' := SliceCandidate.wholeComponentMixedFamily Q W P Y E
  let S := SliceCandidate.wholeNonexceptionalPrefixSources hY hsep W
  let F := SliceCandidate.selectedSuffixFamily hY hsep S
  change q ∈ F at hq
  obtain ⟨a, hqa⟩ := hq
  have hqEq : q =
      (.inl (SliceCandidate.linkageSuffixAtFirstHit hY hsep a.1) :
        Q.DPath) := hqa.symm
  subst q
  rcases p.2 with hpOld | hpPrefix
  · have hpD : p.1.support ⊆ D :=
      SliceCandidate.path_support_subset_exceptionalComponents_left
        hW.finiteCharacter hpOld.1 p.1.initial_mem_support hpOld.2
    have hxP :
        (SliceCandidate.linkageSuffixAtFirstHit hY hsep a.1).start ∈
          p.1.support := by
      apply Q.terminal_mem_support
      change Q.terminal? p.1 = some
        (SliceCandidate.linkageSuffixAtFirstHit hY hsep a.1).start at hpq
      exact hpq
    have hwholeY :
        (.inl (SliceCandidate.linkageFiniteAt hY a.1) : Q.DPath) ∈ Y := by
      rw [← SliceCandidate.linkageMemberAt_eq_finite]
      exact (SliceCandidate.linkageMemberAt hY a.1).2
    have hxWhole :
        (SliceCandidate.linkageSuffixAtFirstHit hY hsep a.1).start ∈
          (SliceCandidate.linkageFiniteAt hY a.1).support :=
      SliceCandidate.linkageSuffixAtFirstHit_support_subset hY hsep a.1
        (SliceCandidate.linkageSuffixAtFirstHit hY hsep a.1).start_mem_support
    have hwholeD : (SliceCandidate.linkageFiniteAt hY a.1).support ⊆ D :=
      SliceCandidate.path_support_subset_exceptionalComponents_right
        hY.finiteCharacter hwholeY hxWhole (hpD hxP)
    exact False.elim <| a.2 <| by
      change a.1.1 ∈ D
      rw [← SliceCandidate.linkageFiniteAt_start hY a.1]
      exact hwholeD
        (SliceCandidate.linkageFiniteAt hY a.1).start_mem_support
  · obtain ⟨b, hpb⟩ := hpPrefix.1
    have hpEq : p.1 =
        (.inl (SliceCandidate.linkageFirstHitAt hY hsep b) : Q.DPath) :=
      hpb.symm
    have hxP :
        (SliceCandidate.linkageSuffixAtFirstHit hY hsep a.1).start ∈
          (SliceCandidate.linkageFirstHitAt hY hsep b).support := by
      have hxP' :
          (SliceCandidate.linkageSuffixAtFirstHit hY hsep a.1).start ∈
            p.1.support := by
        apply Q.terminal_mem_support
        change Q.terminal? p.1 = some
          (SliceCandidate.linkageSuffixAtFirstHit hY hsep a.1).start at hpq
        exact hpq
      rw [hpEq] at hxP'
      exact hxP'
    have hxWholeA :
        (SliceCandidate.linkageSuffixAtFirstHit hY hsep a.1).start ∈
          (SliceCandidate.linkageFiniteAt hY a.1).support :=
      SliceCandidate.linkageSuffixAtFirstHit_support_subset hY hsep a.1
        (SliceCandidate.linkageSuffixAtFirstHit hY hsep a.1).start_mem_support
    have hba : b = a.1 := by
      by_contra hne
      have hm : (SliceCandidate.linkageMemberAt hY b).1 ≠
          (SliceCandidate.linkageMemberAt hY a.1).1 := by
        intro heq
        apply hne
        apply SliceCandidate.linkageMemberAt_injective hY
        exact Subtype.ext heq
      exact False.elim <| Set.disjoint_left.1
        (hY.isWarp (SliceCandidate.linkageMemberAt hY b).2
          (SliceCandidate.linkageMemberAt hY a.1).2 hm)
        (by
          rw [SliceCandidate.linkageMemberAt_eq_finite]
          exact SliceCandidate.linkageFirstHitAt_support_subset hY hsep b hxP)
        (by
          rw [SliceCandidate.linkageMemberAt_eq_finite]
          exact hxWholeA)
    subst b
    let first := SliceCandidate.linkageFirstHitAt hY hsep a.1
    let suffix := SliceCandidate.linkageSuffixAtFirstHit hY hsep a.1
    let whole := SliceCandidate.linkageFiniteAt hY a.1
    have hpPrefix' : (.inl first : Q.DPath) ∈
        SliceCandidate.initialPart Q P Dᶜ := by
      change (.inl (SliceCandidate.linkageFirstHitAt hY hsep a.1) :
          Q.DPath) ∈ SliceCandidate.initialPart Q
            (SliceCandidate.firstHitPrefixFamily hY hsep)
            (SliceCandidate.exceptionalComponentVertices Q W Y E)ᶜ
      rw [← hpEq]
      exact hpPrefix
    let p' : W' := ⟨(.inl first : Q.DPath), Or.inr hpPrefix'⟩
    have hpp' : p = p' := Subtype.ext hpEq
    rw [hpp']
    change ControlledSlices.IsLadderFragment Q Y
      (Q.starPath hcompat p')
    have hmatch : ∃ r ∈ R, r.initial = first.finish := by
      exact ⟨.inl suffix, hqR, by
        change suffix.start = first.finish
        exact SliceCandidate.linkageSuffixAtFirstHit_start hY hsep a.1⟩
    dsimp only [p', DWeb.starPath]
    rw [dif_pos hmatch]
    let r := Classical.choose hmatch
    have hrR : r ∈ R := (Classical.choose_spec hmatch).1
    have hrStart : r.initial = first.finish :=
      (Classical.choose_spec hmatch).2
    have hsuffixStart :
        DirectedPath.Path.initial (.inl suffix : Q.DPath) = first.finish := by
      change suffix.start = first.finish
      exact SliceCandidate.linkageSuffixAtFirstHit_start hY hsep a.1
    have hrEq : r = (.inl suffix : Q.DPath) := by
      by_contra hne
      exact Set.disjoint_left.1
        (hRwarp hrR hqR hne)
        r.initial_mem_support
        (hrStart.trans hsuffixStart.symm ▸
          (show DirectedPath.Path.initial (.inl suffix : Q.DPath) ∈
            DirectedPath.Path.support (.inl suffix : Q.DPath) from
              DirectedPath.Path.initial_mem_support
                (.inl suffix : Q.DPath)))
    change Classical.choose hmatch = (.inl suffix : Q.DPath) at hrEq
    simp only [hrEq]
    have hinter : first.support ∩ suffix.support ⊆ {first.finish} := by
      intro x hx
      exact (hcompat (.inl first) (Or.inr hpPrefix')
        (.inl suffix) hqR x hx.1 hx.2).1 |> fun h ↦
          Set.mem_singleton_iff.2 (Option.some.inj h).symm
    refine ⟨.inl whole, ?_, ?_⟩
    · rw [← SliceCandidate.linkageMemberAt_eq_finite]
      exact (SliceCandidate.linkageMemberAt hY a.1).2
    · change DirectedPath.Path.IsSubpathOf
        (.inl (first.appendFinite suffix (by
          simpa only [first, suffix,
            SliceCandidate.linkageSuffixAtFirstHit_start]) hinter))
        (.inl whole)
      have hfirstSub : first.IsSubpathOf (.inl whole : Q.DPath) :=
        ⟨SliceCandidate.linkageFirstHitAt_support_subset hY hsep a.1,
          SliceCandidate.linkageFirstHitAt_edgeSet_subset hY hsep a.1⟩
      have hsuffixSub : suffix.IsSubpathOf (.inl whole : Q.DPath) := by
        dsimp only [suffix, whole, SliceCandidate.linkageSuffixAtFirstHit]
        exact DirectedPath.FinitePath.suffixFrom_isSubpathOf _ _ _
      constructor
      · change (first.appendFinite suffix _ hinter).support ⊆ whole.support
        rw [DirectedPath.FinitePath.support_appendFinite_eq_union]
        exact Set.union_subset hfirstSub.1 hsuffixSub.1
      · change (first.appendFinite suffix _ hinter).edgeSet ⊆ whole.edgeSet
        rw [Blueprint.LinkageBlueprint.FinitePath.edgeSet_appendFinite]
        exact Set.union_subset hfirstSub.2 hsuffixSub.2

private theorem mk_liftNormalizedFamily_sdiff_le
    (Q : DWeb V) (C D T : Set V) (F : Set Q.DPath)
    {R Good : Set (SliceRestrictedDelta.normalizedDelta Q C D T F).DPath} :
    #(Set.diff (SliceDeltaLift.liftNormalizedFamily Q C D T F R)
        (SliceDeltaLift.liftNormalizedFamily Q C D T F Good)) ≤
      #(↥(R \ Good)) := by
  let badLift := SliceDeltaLift.liftNormalizedFamily Q C D T F (R \ Good)
  have hsub : Set.diff (SliceDeltaLift.liftNormalizedFamily Q C D T F R)
      (SliceDeltaLift.liftNormalizedFamily Q C D T F Good) ⊆ badLift := by
    rintro q ⟨hqR, hqGood⟩
    obtain ⟨p, rfl⟩ := hqR
    refine ⟨⟨p.1, p.2, ?_⟩, rfl⟩
    intro hp
    exact hqGood ⟨⟨p.1, hp⟩, rfl⟩
  exact (Cardinal.mk_subtype_mono hsub).trans Cardinal.mk_range_le

/-- The extension-only whole-component completion, retaining the exact
ordinary-family maverick bound before the exchange witnesses are erased. -/
theorem exists_cleanAnnularCompletion_with_mavericks
    {kappa : Cardinal.{u}} {Base : DWeb V}
    (hlower : RegularProtectedAmbientRebuild.ExtensionBelowFor Base kappa)
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (Q : DWeb V) {C T E : Set V} {W Y : Set Q.DPath}
    (hQBase : ∀ {x y : V}, Q.graph.Adj x y → Base.graph.Adj x y)
    (hNorm : Q.IsNormalized)
    (hW : IsLinkageBetween Q Q.source C W)
    (hWclean : SingularContinuation.TerminalCleanAt Q W C)
    (hsep : IsSeparatorFrom Q Q.source C)
    (hCtrim : IsTrimmedSeparator Q C)
    (hCsource : (Q.quotient C).source = C)
    (hCroof : C ⊆ Q.roof T)
    (hCQ : (Q.quotient C).IsUnhindered)
    (hTessential : Q.essential T = T)
    (hY : IsLinkageBetween Q (Q.source \ E) T Y)
    (hYtight : MeetsOnlyAtTerminal Q Y T)
    (hYsep : RelationalRoof.Separates Q.graph.Adj (Q.source \ E) T C)
    (hEsub : E ⊆ Q.source) (hEsmall : #E < kappa) :
    ∃ K : RegularCandidateProvider.CleanAnnularCompletion
        Q Q.source C T kappa,
      #(ControlledSlices.sliceMavericks Q Y
        (Q.star K.filledCompatible)) < kappa := by
  let P := SliceCandidate.firstHitPrefixFamily hY hYsep
  let W' := SliceCandidate.wholeComponentMixedFamily Q W P Y E
  let E' := SliceCandidate.wholeExchangeExceptionalTerminals Q W Y E
  let S := SliceCandidate.wholeNonexceptionalPrefixSources hY hYsep W
  let F := SliceCandidate.selectedSuffixFamily hY hYsep S
  have hW' : IsLinkageBetween Q Q.source C W' :=
    SliceCandidate.wholeComponentMixedFamily_isLinkageBetween
      Q hW hY hYsep hEsub
  have hW'clean : SingularContinuation.TerminalCleanAt Q W' C :=
    RegularCleanExchange.wholeComponentMixedFamily_terminalClean
      hWclean hY hYsep
  have hE'sub : E' ⊆ Q.terminalFrontier W' := by
    intro x hx
    change x ∈ Q.terminalFrontier
      (SliceCandidate.initialPart Q W
        (SliceCandidate.exceptionalComponentVertices Q W Y E)) at hx
    change x ∈ Q.terminalFrontier
      (SliceCandidate.initialPart Q W
          (SliceCandidate.exceptionalComponentVertices Q W Y E) ∪
        SliceCandidate.initialPart Q P
          (SliceCandidate.exceptionalComponentVertices Q W Y E)ᶜ)
    rw [DWeb.terminalFrontier_union]
    exact Or.inl hx
  have hE'small : #E' < kappa :=
    SliceCandidate.wholeExchangeExceptionalTerminals_small Q hregular
      huncountable hW.isWarp hY.isWarp hW.finiteCharacter
        hY.finiteCharacter hEsmall
  have hsource : Q.terminalFrontier W' \ E' =
      SliceCandidate.selectedSuffixStartSet hY hYsep S := by
    exact (SliceCandidate.terminalFrontier_wholeMixed_sdiff_exceptional_eq
      Q hW hY hYsep).trans
        (SliceCandidate.terminalFrontier_wholeNonexceptionalPrefix_eq_suffixStartSet
          hY hYsep)
  have hF : IsLinkageBetween Q (Q.terminalFrontier W' \ E') T F := by
    rw [hsource]
    exact SliceCandidate.selectedSuffixFamily_isLinkageBetween hY hYsep S
  have hFtight : MeetsOnlyAtTerminal Q F T :=
    SliceCandidate.selectedSuffixFamily_meetsOnlyAtTerminal
      hY hYtight hYsep S
  have hWF : Q.StarCompatible W' F :=
    SliceCandidate.wholeComponentExchange_starCompatible Q hW hY hYsep
  have hDC : Q.terminalFrontier W' ⊆ C := hW'.terminalFrontier_subset
  obtain ⟨R, hcompat, hR, hresult, hRsmall⟩ :=
    RegularProtectedAmbientRebuild.exists_tightNormalizedCleanContinuation_of_extensionBelow
      hlower hregular huncountable Q hQBase hNorm Set.Subset.rfl hW'
        hsep hW'clean rfl
        hDC hCtrim hCsource hCroof hCQ hTessential hE'sub hE'small
        hF hFtight hWF
  let hsourcePure : ∀ p ∈ F,
      p.support ∩ Q.terminalFrontier W' ⊆ {p.initial} :=
    SliceDeltaLift.sourcePure_of_starCompatible Q Set.Subset.rfl hWF
  let Fdelta := SliceDeltaLift.normalizedRestrictedFamily Q C
    (Q.terminalFrontier W') T hF hsourcePure hFtight
  let GoodDelta := R ∩ Fdelta
  let Rlift := SliceDeltaLift.liftNormalizedFamily Q C
    (Q.terminalFrontier W') T F R
  let Good := SliceDeltaLift.liftNormalizedFamily Q C
    (Q.terminalFrontier W') T F GoodDelta
  have hRlift : IsLinkageBetween Q (Q.terminalFrontier W') T Rlift :=
    SliceDeltaLift.IsLinkageBetween.liftNormalizedDelta Q C
      (Q.terminalFrontier W') T F hR
  have hGood : Good ⊆ Rlift := by
    rintro _ ⟨r, rfl⟩
    exact ⟨⟨r.1, r.2.1⟩, rfl⟩
  have hbadDelta : #(↥(R \ GoodDelta)) < kappa := by
    simpa only [GoodDelta, Fdelta, Set.sdiff_self_inter] using hRsmall
  have hbad : #(↥(Rlift \ Good)) < kappa :=
    (mk_liftNormalizedFamily_sdiff_le Q C
      (Q.terminalFrontier W') T F).trans_lt hbadDelta
  have hordinary : ∀ (p : W') (q : Q.DPath), q ∈ Good →
      Q.terminal? p.1 = some q.initial →
        ControlledSlices.IsLadderFragment Q Y
          (Q.starPath hcompat p) := by
    intro p q hqGood hpq
    have hqRlift : q ∈ Rlift := hGood hqGood
    obtain ⟨r, hqr⟩ := hqGood
    have hrFdelta : r.1 ∈ Fdelta := r.2.2
    obtain ⟨f, hfr⟩ := hrFdelta
    have hliftEq : SliceDeltaLift.liftNormalizedPath Q C
        (Q.terminalFrontier W') T F r.1 = f.1 := by
      rw [← hfr]
      exact liftNormalizedPath_normalizedRestrictedPath Q C
        (Q.terminalFrontier W') T hF hsourcePure hFtight f
    have hqEq : q = f.1 := hqr.symm.trans hliftEq
    have hpq' : Q.terminal? p.1 = some f.1.initial := by
      rw [← hqEq]
      exact hpq
    have hfRlift : f.1 ∈ Rlift := by
      rw [← hqEq]
      exact hqRlift
    obtain ⟨owner, hownerY, hfragment⟩ :=
      star_wholeExchange_suffix_isLadderFragment Q hW hY hYsep hEsub
        hRlift.isWarp hcompat p f.1 hfRlift f.2 hpq'
    exact ⟨owner, hownerY, hfragment⟩
  have hW'exact : IsLinkageBetween Q Q.source (Q.terminalFrontier W') W' :=
    SingularFirstHitCleanPrefix.isLinkageBetween_terminalFrontier_of_finite_full
      hW'.isWarp hW'.finiteCharacter hW'.initialSet_eq
  have hmavericks :
      #(ControlledSlices.sliceMavericks Q Y (Q.star hcompat)) < kappa :=
    RegularStarMaverickBound.mk_sliceMavericks_star_lt
      hW'exact hRlift hcompat hGood hbad hordinary
  let K : RegularCandidateProvider.CleanAnnularCompletion
      Q Q.source C T kappa :=
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
      deviationSmall := hRsmall }
  exact ⟨K, by simpa only [K] using hmavericks⟩

private theorem walk_edgeSet_lift {D E : Digraph V}
    (hDE : ∀ {x y}, D.Adj x y → E.Adj x y) {a b : V}
    (p : DirectedPath.Walk D a b) :
    (p.lift hDE).edgeSet = p.edgeSet := by
  induction p with
  | nil => rfl
  | cons h p ih =>
      simp [DirectedPath.Walk.lift, DirectedPath.Walk.edgeSet_cons, ih]

private theorem edgeSet_liftDeletePath
    (G : DWeb V) (X : Set V) (p : (G.delete X).DPath) :
    (G.liftDeletePath X p).edgeSet = p.edgeSet := by
  rcases p with p | r
  · exact walk_edgeSet_lift _ p.walk
  · rfl

private theorem liftDeletePath_isSubpathOf
    (G : DWeb V) (X : Set V) {p q : (G.delete X).DPath}
    (hpq : p.IsSubpathOf q) :
    (G.liftDeletePath X p).IsSubpathOf (G.liftDeletePath X q) := by
  constructor
  · simpa only [G.support_liftDeletePath, G.support_liftDeletePath]
      using hpq.1
  · simpa only [edgeSet_liftDeletePath, edgeSet_liftDeletePath]
      using hpq.2

/-- Lift a protected completion and its ordinary-family maverick bound out
of the deleted web.  The only reference-family hypothesis says that every
ordinary deleted path becomes a member of the ambient reference family. -/
theorem exists_protectedAmbientCompletion_with_mavericks
    {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (Q : DWeb V) {X C T E : Set V}
    (hlower : RegularProtectedAmbientRebuild.ExtensionBelowFor Q kappa)
    {W Y : Set (Q.delete X).DPath} {Y₀ : Set Q.DPath}
    (hNorm : Q.IsNormalized)
    (hXroof : X ⊆ Q.roof C)
    (hCtrim : IsTrimmedSeparator Q C)
    (hsep : IsSeparatorFrom Q Q.source C)
    (hCQ : (Q.quotient C).IsUnhindered)
    (hCroof : C ⊆ Q.roof T)
    (hTessential : Q.essential T = T)
    (hW : IsLinkageBetween (Q.delete X) (Q.delete X).source (C \ X) W)
    (hWclean : SingularContinuation.TerminalCleanAt
      (Q.delete X) W (C \ X))
    (hY : IsLinkageBetween (Q.delete X)
      ((Q.delete X).source \ E) (T \ X) Y)
    (hYtight : MeetsOnlyAtTerminal (Q.delete X) Y (T \ X))
    (hEsub : E ⊆ (Q.delete X).source) (hEsmall : #E < kappa)
    (hYordinary : ∀ p ∈ Y, Q.liftDeletePath X p ∈ Y₀) :
    ∃ K : RegularProtectedAmbientRebuild.ProtectedAmbientCompletion
        Q X C T kappa,
      #(ControlledSlices.sliceMavericks Q Y₀ K.lifted) < kappa := by
  let H := Q.delete X
  let C' := C \ X
  let T' := T \ X
  have hXroofT : X ⊆ Q.roof T := hXroof.trans (Q.roof_cut hCroof)
  have hNormH : H.IsNormalized :=
    SingularExtension.DWeb.IsNormalized.delete hNorm X
  have hCtrimH : IsTrimmedSeparator H C' :=
    Q.delete_essential_sdiff_eq_of_subset_roof hXroof hCtrim
  have hTtrimH : H.essential T' = T' :=
    Q.delete_essential_sdiff_eq_of_subset_roof hXroofT hTessential
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
    apply SingularExtension.delete_sourceSet_isUnhindered (Q.quotient C) hCQ
    have hsourceQC : (Q.quotient C).source = C :=
      SingularContinuation.quotient_source_eq_stopover Q hsep hCtrim
    rw [hsourceQC]
    exact Set.inter_subset_right
  have hCsourceH : (H.quotient C').source = C' :=
    SingularContinuation.quotient_source_eq_stopover H hsepH hCtrimH
  have hYsep : RelationalRoof.Separates H.graph.Adj
      (H.source \ E) T' C' := by
    have hfull : RelationalRoof.Separates H.graph.Adj H.source T' C' :=
      SliceSegmentCore.separates_between_of_roofed H hTtrimH hsepH hCroofH
    intro a t p ha ht
    exact hfull p ha.1 ht
  obtain ⟨completion, hmavericksH⟩ :=
    exists_cleanAnnularCompletion_with_mavericks hlower hregular huncountable
      H (by intro x y hxy; exact hxy.1) hNormH
      hW hWclean hsepH hCtrimH hCsourceH hCroofH hCQH hTtrimH
      hY hYtight hYsep hEsub hEsmall
  let lifted := Q.liftDeleteFamily X (H.star completion.filledCompatible)
  have hliftedTight : TightLinkageBetween Q H.source T lifted :=
    RegularProtectedAmbientRebuild.tightLinkageBetween_liftDeleteFamily_mono_target
      Q X H.source T completion.resultTight Set.Subset.rfl
  have hstart : H.initialSet (H.star completion.filledCompatible) ⊆ H.source := by
    rw [completion.resultTight.1.initialSet_eq]
  have havoid : Disjoint (Q.vertexSet lifted) X :=
    Q.vertexSet_liftDeleteFamily_disjoint hstart
  let K : RegularProtectedAmbientRebuild.ProtectedAmbientCompletion
      Q X C T kappa :=
    { core := completion
      lifted := lifted
      lifted_eq := rfl
      liftedTight := hliftedTight
      liftedAvoids := havoid }
  have hsub : ControlledSlices.sliceMavericks Q Y₀ lifted ⊆
      Q.liftDeleteFamily X
        (ControlledSlices.sliceMavericks H Y
          (H.star completion.filledCompatible)) := by
    rintro p ⟨hpLifted, hpNotOrdinary⟩
    obtain ⟨q, hqStar, rfl⟩ := hpLifted
    refine ⟨q, ⟨hqStar, ?_⟩, rfl⟩
    rintro ⟨r, hrY, hqr⟩
    apply hpNotOrdinary
    exact ⟨Q.liftDeletePath X r, hYordinary r hrY,
      liftDeletePath_isSubpathOf Q X hqr⟩
  have hmavericks :
      #(ControlledSlices.sliceMavericks Q Y₀ lifted) < kappa :=
    ((Cardinal.mk_subtype_mono hsub).trans Cardinal.mk_image_le).trans_lt
      hmavericksH
  exact ⟨K, by simpa only [K] using hmavericks⟩

/-- Assembly-facing protected rebuild retaining the ambient ordinary-family
maverick bound. -/
theorem exists_protectedAmbientCompletion_of_ambientRemainder_with_mavericks
    {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (Q : DWeb V) {X C T E₀ : Set V}
    (hlower : RegularProtectedAmbientRebuild.ExtensionBelowFor Q kappa)
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
    (hY₀tight : MeetsOnlyAtTerminal Q Y₀ T) :
    ∃ K : RegularProtectedAmbientRebuild.ProtectedAmbientCompletion
        Q X C T kappa,
      #(ControlledSlices.sliceMavericks Q Y₀ K.lifted) < kappa := by
  obtain ⟨ordinary⟩ :=
    RegularProtectedAmbientRebuild.exists_avoidingOrdinaryPreparation
      hregular Q hXsmall hE₀small hY₀ hY₀tight
  let WR := Q.restrictDeleteFamily X W hWavoid
  let YR := Q.restrictDeleteFamily X ordinary.family ordinary.familyAvoids
  have hWR : IsLinkageBetween (Q.delete X) (Q.delete X).source (C \ X) WR :=
    RegularProtectedAmbientRebuild.IsLinkageBetween.restrictDeleteFamily
      Q X hW hWavoid
  have hWRclean : SingularContinuation.TerminalCleanAt
      (Q.delete X) WR (C \ X) :=
    RegularProtectedAmbientRebuild.terminalCleanAt_restrictDeleteFamily
      Q X C hWavoid hWclean
  have hYR : IsLinkageBetween (Q.delete X)
      ((Q.delete X).source \ ordinary.exceptional) (T \ X) YR :=
    RegularProtectedAmbientRebuild.IsLinkageBetween.restrictDeleteFamily
      Q X ordinary.familyLinkage ordinary.familyAvoids
  have hYRtight : MeetsOnlyAtTerminal (Q.delete X) YR (T \ X) :=
    RegularProtectedAmbientRebuild.meetsOnlyAtTerminal_restrictDeleteFamily
      Q X T ordinary.familyAvoids ordinary.familyTight
  have hYordinary : ∀ p ∈ YR, Q.liftDeletePath X p ∈ Y₀ := by
    intro p hp
    have hpLift : Q.liftDeletePath X p ∈ Q.liftDeleteFamily X YR :=
      ⟨p, hp, rfl⟩
    have hpFamily : Q.liftDeletePath X p ∈ ordinary.family := by
      simpa only [YR,
        SafeLinkGroundFinal.DWeb.liftDeleteFamily_restrictDeleteFamily]
        using hpLift
    exact ordinary.family_subset hpFamily
  exact exists_protectedAmbientCompletion_with_mavericks
    hregular huncountable Q hlower hNorm hXroof hCtrim hsep hCQ hCroof
      hTessential hWR hWRclean hYR hYRtight ordinary.exceptional_subset
      ordinary.exceptional_small hYordinary

#print axioms exists_protectedAmbientCompletion_with_mavericks
#print axioms exists_protectedAmbientCompletion_of_ambientRemainder_with_mavericks

end RegularProtectedAmbientMaverick
end CardinalInduction
end Erdos599
