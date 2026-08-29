/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayLaterLinkage
import ErdosProblems.Erdos599.HalfwayOutsideReference
import ErdosProblems.Erdos599.RegularProtectedDeltaLift
import ErdosProblems.Erdos599.LinkageUnion

/-!
# A later linkage which retains a safely deleted linkage

The current extension clause must not be applied by selecting an unrelated
fresh linkage: that loses the path which Assertion 9.23 chose with an
unhindered residual.  Instead delete the whole retained linkage, apply the
extension clause in that residual web, lift the resulting linkage, and unite
the two vertex-disjoint families.  The output literally contains the
retained family.

This is the precise positive use of the deletion-safety certificate.  Such a
certificate is indispensable: an arbitrary linkage need not be extendible
to a full linkage even when the ambient web has some full linkage.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath
open CardinalInduction
open CardinalInduction.ControlledSlices
open CardinalInduction.SliceCandidate
open _root_.Erdos599.Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V}
variable {kappa : Cardinal.{u}}

/-- A linkage lifted from a vertex-deleted web is still a linkage to the
ambient target.  The only new endpoint-purity case is an ambient target
vertex in the deleted set, and lifted paths avoid that set. -/
theorem IsLinkageBetween.liftDeleteFamily_toAmbientTarget
    {X A : Set V} {R : Set (Gamma.delete X).DPath}
    (hR : IsLinkageBetween (Gamma.delete X) A
      (Gamma.delete X).target R)
    (hA : A ⊆ (Gamma.delete X).source) :
    IsLinkageBetween Gamma A Gamma.target
      (Gamma.liftDeleteFamily X R) := by
  have hbase : IsLinkageBetween Gamma A (Gamma.delete X).target
      (Gamma.liftDeleteFamily X R) :=
    RegularProtectedDeltaLift.IsLinkageBetween.liftDeleteFamily
      Gamma X hR
  have havoid :
      Disjoint (Gamma.vertexSet (Gamma.liftDeleteFamily X R)) X :=
    Gamma.vertexSet_liftDeleteFamily_disjoint (hR.initialSet_eq.symm ▸ hA)
  refine ⟨hbase.isWarp, hbase.finiteCharacter, hbase.initialSet_eq,
    hbase.terminalFrontier_subset.trans Set.sdiff_subset, ?_⟩
  intro p hp
  obtain ⟨q, rfl, hends, hsource⟩ := hbase.endpointPure p hp
  refine ⟨q, rfl, ?_, hsource⟩
  calc
    q.support ∩ (A ∪ Gamma.target) =
        q.support ∩ (A ∪ (Gamma.target \ X)) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_sdiff]
      constructor
      · rintro ⟨hxq, hx⟩
        refine ⟨hxq, hx.elim Or.inl (fun hxT ↦ Or.inr ⟨hxT, ?_⟩)⟩
        intro hxX
        exact Set.disjoint_left.1 havoid
          ⟨Sum.inl q, hp, hxq⟩ hxX
      · rintro ⟨hxq, hx⟩
        exact ⟨hxq, hx.elim Or.inl (fun hxT ↦ Or.inr hxT.1)⟩
    _ = {q.start, q.finish} := hends

/-- In a normalized web, a linkage carrier meets the ambient source exactly
in its prescribed initial set. -/
theorem IsLinkageBetween.vertexSet_inter_source_eq
    (hGamma : Gamma.IsNormalized) {A : Set V} {P : Set Gamma.DPath}
    (hP : IsLinkageBetween Gamma A Gamma.target P)
    (hA : A ⊆ Gamma.source) :
    Gamma.vertexSet P ∩ Gamma.source = A := by
  apply Set.Subset.antisymm
  · rintro x ⟨⟨p, hpP, hxp⟩, hxsource⟩
    have hxinitial : x = p.initial :=
      hGamma.eq_initial_of_mem_path p hxp hxsource
    rw [hxinitial]
    rw [← hP.initialSet_eq]
    exact ⟨p, hpP, rfl⟩
  · intro x hxA
    have hxinitial : x ∈ Gamma.initialSet P :=
      hP.initialSet_eq.symm ▸ hxA
    obtain ⟨p, hpP, rfl⟩ := hxinitial
    exact ⟨⟨p, hpP, p.initial_mem_support⟩, hA hxA⟩

/-- Deleting a linkage with fewer than `kappa` initials does not change the
cardinality of an infinite source set of cardinality `kappa`.  Normalization
is used only to identify the source vertices in the linkage carrier with
its prescribed initial set. -/
theorem IsLinkageBetween.delete_vertexSet_source_card_eq
    (hGamma : Gamma.IsNormalized) {A : Set V} {P : Set Gamma.DPath}
    (hP : IsLinkageBetween Gamma A Gamma.target P)
    (hA : A ⊆ Gamma.source) (hsource : #Gamma.source = kappa)
    (hinfinite : aleph0 ≤ kappa) (hAcard : #A < kappa) :
    #(Gamma.delete (Gamma.vertexSet P)).source = kappa := by
  have hset : Gamma.source \ Gamma.vertexSet P = Gamma.source \ A := by
    ext x
    constructor
    · rintro ⟨hxsource, hxcarrier⟩
      refine ⟨hxsource, fun hxA ↦ hxcarrier ?_⟩
      have hxinter : x ∈ Gamma.vertexSet P ∩ Gamma.source := by
        rw [IsLinkageBetween.vertexSet_inter_source_eq hGamma hP hA]
        exact hxA
      exact hxinter.1
    · rintro ⟨hxsource, hxA⟩
      refine ⟨hxsource, fun hxcarrier ↦ hxA ?_⟩
      have hxinter : x ∈ Gamma.vertexSet P ∩ Gamma.source :=
        ⟨hxcarrier, hxsource⟩
      rwa [IsLinkageBetween.vertexSet_inter_source_eq hGamma hP hA] at hxinter
  change #((Gamma.source \ Gamma.vertexSet P : Set V)) = kappa
  rw [hset]
  apply le_antisymm
  · rw [← hsource]
    exact Cardinal.mk_subtype_mono Set.sdiff_subset
  · apply le_of_not_gt
    intro hsmall
    have hcover : kappa ≤ #(Gamma.source \ A : Set V) + #A := by
      rw [← hsource]
      exact Cardinal.le_mk_sdiff_add_mk Gamma.source A
    exact (not_le_of_gt
      (Cardinal.add_lt_of_lt hinfinite hsmall hAcard)) hcover

/-- If the web left after deleting a linkage carrier is linkable, its
solution can be lifted and adjoined to the deleted linkage.  The resulting
full linkage literally contains the retained family.

This is the cardinal-free core of the retention argument.  Keeping it
separate is important at a ladder stage: the residual stage source can have
cardinality strictly below the current cardinal, in which case it is solved
by the lower induction hypothesis rather than the current extension
clause. -/
theorem exists_fullLinkage_containing_of_delete_linkable
    (hGamma : Gamma.IsNormalized)
    {A : Set V} {P : Set Gamma.DPath}
    (hA : A ⊆ Gamma.source)
    (hP : IsLinkageBetween Gamma A Gamma.target P)
    (hlinkable : IsLinkable (Gamma.delete (Gamma.vertexSet P))) :
    ∃ W : Set Gamma.DPath,
      IsLinkageBetween Gamma Gamma.source Gamma.target W ∧ P ⊆ W := by
  let H : DWeb V := Gamma.delete (Gamma.vertexSet P)
  obtain ⟨R, hR⟩ := hlinkable
  let L : Set Gamma.DPath :=
    Gamma.liftDeleteFamily (Gamma.vertexSet P) R
  have hL : IsLinkageBetween Gamma H.source Gamma.target L := by
    exact IsLinkageBetween.liftDeleteFamily_toAmbientTarget hR
      (Set.Subset.rfl)
  have hdisjoint : Disjoint (Gamma.vertexSet P) (Gamma.vertexSet L) := by
    exact (Gamma.vertexSet_liftDeleteFamily_disjoint
      (hR.initialSet_eq.symm ▸ (Set.Subset.rfl : H.source ⊆ H.source))).symm
  have hunion : IsLinkageBetween Gamma (A ∪ H.source) Gamma.target
      (P ∪ L) :=
    SingularRetargetedRow.linkageBetween_union_of_vertexSet_disjoint
      Gamma hP hL hdisjoint
  have hsources : A ∪ H.source = Gamma.source := by
    change A ∪ (Gamma.source \ Gamma.vertexSet P) = Gamma.source
    ext x
    constructor
    · rintro (hxA | ⟨hxsource, _hxP⟩)
      · exact hA hxA
      · exact hxsource
    · intro hxsource
      by_cases hxA : x ∈ A
      · exact Or.inl hxA
      · exact Or.inr ⟨hxsource, fun hxP ↦ hxA (by
          have hxinter : x ∈ Gamma.vertexSet P ∩ Gamma.source :=
            ⟨hxP, hxsource⟩
          rwa [IsLinkageBetween.vertexSet_inter_source_eq
            hGamma hP hA] at hxinter)⟩
  refine ⟨P ∪ L, ?_, Set.subset_union_left⟩
  rwa [hsources] at hunion

/-- Deleting the carrier of a safely retained linkage, solving the residual
web with the current extension clause, and lifting back produces a full
linkage which literally contains the retained linkage. -/
theorem exists_fullLinkage_containing_of_delete_unhindered
    (hext : UniversalExtensionClauseAt V kappa)
    (hGamma : Gamma.IsNormalized)
    {A : Set V} {P : Set Gamma.DPath}
    (hA : A ⊆ Gamma.source)
    (hP : IsLinkageBetween Gamma A Gamma.target P)
    (hresidual : (Gamma.delete (Gamma.vertexSet P)).IsUnhindered)
    (hcard : #(Gamma.delete (Gamma.vertexSet P)).source = kappa) :
    ∃ W : Set Gamma.DPath,
      IsLinkageBetween Gamma Gamma.source Gamma.target W ∧ P ⊆ W := by
  apply exists_fullLinkage_containing_of_delete_linkable hGamma hA hP
  apply linkable_of_extension_at_source_card
  simpa only [hcard] using
    (hext (Gamma.delete (Gamma.vertexSet P)) hresidual)

/-! ## Retention by first-hit truncation -/

private theorem FinitePath.eq_of_prefix_of_finish_eq_retained
    {D : Digraph V} {p q : FinitePath D} (hpq : p.IsPrefixOf q)
    (hfinish : p.finish = q.finish) : p = q := by
  have hstart : p.start = q.start := hpq.start_eq
  cases p with
  | mk ps pf pw ppath =>
      cases q with
      | mk qs qf qw qpath =>
          dsimp at hstart hfinish hpq ⊢
          subst qs
          subst qf
          have hs : pw.support = qw.support :=
            FinitePath.IsPrefixOf.eq_support_of_finish_eq hpq rfl
          have hw : pw = qw := Walk.eq_of_support_eq pw qw hs
          subst qw
          rfl

/-- First-hit truncation leaves a tight retained subfamily literally
unchanged.  This is the precise bridge needed after the extension clause
has produced an ambient linkage containing the safely deleted row: the
unretained components may be stopped at the later frontier, while every
retained component remains an element of the stopped family.

The right-tightness hypothesis is essential.  Merely knowing that a
retained path ends on `C` does not prevent it from meeting `C` earlier. -/
theorem firstHitPrefixFamily_contains_of_subset_of_meetsOnlyAtTerminal
    {A C T : Set V} {P Y : Set Gamma.DPath}
    (hP : IsLinkageBetween Gamma A T P)
    (hsep : RelationalRoof.Separates Gamma.graph.Adj A T C)
    (hYP : Y ⊆ P)
    (hYtight : SliceSpliceSource.MeetsOnlyAtTerminal Gamma Y C) :
    Y ⊆ firstHitPrefixFamily hP hsep := by
  intro p hpY
  have hpP : p ∈ P := hYP hpY
  obtain ⟨f, rfl⟩ := hP.finiteCharacter hpP
  have hfA : f.start ∈ A := by
    rw [← hP.initialSet_eq]
    exact ⟨Sum.inl f, hpP, rfl⟩
  let a : A := ⟨f.start, hfA⟩
  have hmember : (linkageMemberAt hP a).1 =
      (Sum.inl f : Gamma.DPath) := by
    apply DWeb.IsWarp.eq_of_mem_support hP.isWarp
      (linkageMemberAt hP a).2 hpP
    · exact (linkageMemberAt hP a).1.initial_mem_support
    · have hinitial : (linkageMemberAt hP a).1.initial = f.start := by
        simpa only [a] using linkageMemberAt_initial hP a
      exact hinitial.symm ▸ f.start_mem_support
  have hfinite : linkageFiniteAt hP a = f := by
    have hm := linkageMemberAt_eq_finite hP a
    rw [hmember] at hm
    exact Sum.inl.inj hm.symm
  have hfinish : (linkageFirstHitAt hP hsep a).finish = f.finish := by
    have htight := hYtight (Sum.inl f : Gamma.DPath) hpY
      (linkageFirstHitAt hP hsep a).finish
    have hsupport : (linkageFirstHitAt hP hsep a).finish ∈ f.support := by
      rw [← hfinite]
      exact linkageFirstHitAt_support_subset hP hsep a
        (linkageFirstHitAt hP hsep a).finish_mem_support
    have hterminal := htight hsupport
      (linkageFirstHitAt_finish_mem hP hsep a)
    change some f.finish = some (linkageFirstHitAt hP hsep a).finish at hterminal
    exact (Option.some.inj hterminal).symm
  have hpref : (linkageFirstHitAt hP hsep a).IsPrefixOf
      (linkageFiniteAt hP a) := by
    exact (linkageFiniteAt hP a).walk.firstHit C
      (linkageFiniteAt_meets hP hsep a) |>.support_prefix
  have hpref' : (linkageFirstHitAt hP hsep a).IsPrefixOf f := by
    simpa only [hfinite] using hpref
  have heq : linkageFirstHitAt hP hsep a = f := by
    exact FinitePath.eq_of_prefix_of_finish_eq_retained hpref' hfinish
  change (Sum.inl f : Gamma.DPath) ∈
    SliceSegmentCore.segmentFamily (firstHitSegmentRealization hP hsep)
  exact ⟨a, congrArg Sum.inl heq⟩

/-- First-hit truncation is monotone under literal inclusion of target
linkages.  The two linkage witnesses may have different prescribed initial
sets; inclusion of those sets identifies the corresponding component by
warp disjointness. -/
theorem firstHitPrefixFamily_mono_of_subset
    {A B C T : Set V} {P W : Set Gamma.DPath}
    (hP : IsLinkageBetween Gamma A T P)
    (hW : IsLinkageBetween Gamma B T W)
    (hAB : A ⊆ B) (hPW : P ⊆ W)
    (hsepP : RelationalRoof.Separates Gamma.graph.Adj A T C)
    (hsepW : RelationalRoof.Separates Gamma.graph.Adj B T C) :
    firstHitPrefixFamily hP hsepP ⊆
      firstHitPrefixFamily hW hsepW := by
  rintro r ⟨a, rfl⟩
  let b : B := ⟨a.1, hAB a.2⟩
  have hmember : (linkageMemberAt hP a).1 =
      (linkageMemberAt hW b).1 := by
    apply DWeb.IsWarp.eq_of_mem_support hW.isWarp
      (hPW (linkageMemberAt hP a).2)
      (linkageMemberAt hW b).2
    · exact (linkageMemberAt hP a).1.initial_mem_support
    · simpa only [b, linkageMemberAt_initial] using
        (linkageMemberAt hW b).1.initial_mem_support
  have hfinite : linkageFiniteAt hP a = linkageFiniteAt hW b := by
    have hp := linkageMemberAt_eq_finite hP a
    have hw := linkageMemberAt_eq_finite hW b
    rw [hmember] at hp
    exact Sum.inl.inj (hp.symm.trans hw)
  have hfirst : linkageFirstHitAt hP hsepP a =
      linkageFirstHitAt hW hsepW b := by
    simp only [linkageFirstHitAt, hfinite]
  exact ⟨b, congrArg Sum.inl hfirst.symm⟩

/-! ## A containing current-later linkage -/

/-- The deletion-safe retained family can be preserved through the exact
current-later-linkage construction.

First the extension clause is applied in the complement of the retained
carrier, producing an ambient source--target linkage which literally
contains `Y`.  Then all ambient members are stopped at their first visit to
the selected later frontier.  The tightness premise says precisely that the
members of `Y` were already stopped there, so they remain literal members of
the later family rather than merely prefixes of related paths. -/
theorem ClubStageGeometry.exists_currentLaterLinkage_containing
    {theta : Cardinal.{u}} {Yref : Set Gamma.DPath}
    (C : ClubStageGeometry Gamma Yref kappa theta)
    (hext : UniversalExtensionClauseAt V kappa)
    (hGamma : Gamma.IsNormalized)
    {A : Set V} {Y : Set Gamma.DPath}
    (hA : A ⊆ Gamma.source)
    (hY : IsLinkageBetween Gamma A Gamma.target Y)
    (hresidual : (Gamma.delete (Gamma.vertexSet Y)).IsUnhindered)
    (hcard : #(Gamma.delete (Gamma.vertexSet Y)).source = kappa)
    (htight : SliceSpliceSource.MeetsOnlyAtTerminal
      Gamma Y C.newSlice) :
    ∃ D : CurrentLaterLinkage C Gamma.source, Y ⊆ D.later := by
  obtain ⟨P, hP, hYP⟩ :=
    exists_fullLinkage_containing_of_delete_unhindered
      hext hGamma hA hY hresidual hcard
  have hsourceRoof : Gamma.source ⊆ C.outerRoof :=
    C.source_subset_outerRoof
  let hsep : RelationalRoof.Separates Gamma.graph.Adj
      Gamma.source Gamma.target C.newSlice :=
    separates_target_of_subset_roof hsourceRoof
  let W : Set Gamma.DPath := firstHitPrefixFamily hP hsep
  have hW : IsLinkageBetween Gamma Gamma.source C.newSlice W :=
    firstHitPrefixFamily_isLinkageBetween hP hsep
  have hWroof : ∀ q ∈ W, q.support ⊆ C.outerRoof := by
    rintro q hq
    change q ∈ SliceSegmentCore.segmentFamily
      (firstHitSegmentRealization hP hsep) at hq
    obtain ⟨a, rfl⟩ := hq
    change (linkageFirstHitAt hP hsep a).support ⊆ C.outerRoof
    exact SliceRestrictedDelta.firstHit_support_subset_roof_ambient
      Gamma C.newSlice (linkageFiniteAt hP a)
      (by simpa only [linkageFiniteAt_start] using hsourceRoof a.2)
      (linkageFiniteAt_meets hP hsep a)
  have hWfragment : ∀ q ∈ W, IsLadderFragment Gamma P q := by
    change ∀ q ∈ SliceSegmentCore.segmentFamily
        (firstHitSegmentRealization hP hsep),
      IsLadderFragment Gamma P q
    exact SliceSegmentCore.segmentFamily_isLadderFragment
      (firstHitSegmentRealization hP hsep)
  have hYW : Y ⊆ W :=
    firstHitPrefixFamily_contains_of_subset_of_meetsOnlyAtTerminal
      hP hsep hYP htight
  exact ⟨{
    ambient := P
    later := W
    ambient_linkage := hP
    later_linkage := hW
    later_in_outerRoof := hWroof
    later_is_ambient_fragment := hWfragment }, hYW⟩

/-- Dependency-preserving prefix-retaining form of the deletion-safe
construction.

In addition to the stopped prefixes, the result retains the literal
inclusion of the complete safely deleted family in the ambient linkage.
This second inclusion is what permits the suffix after the selected
frontier to be recovered as the suffix of the *chosen* safe path, rather
than merely as some unrelated ambient continuation. -/
theorem ClubStageGeometry.exists_currentLaterLinkage_containing_prefixes_with_ambient
    {theta : Cardinal.{u}} {Yref : Set Gamma.DPath}
    (C : ClubStageGeometry Gamma Yref kappa theta)
    (hext : UniversalExtensionClauseAt V kappa)
    (hGamma : Gamma.IsNormalized)
    {A : Set V} {P R : Set Gamma.DPath}
    (hA : A ⊆ Gamma.source)
    (hP : IsLinkageBetween Gamma A Gamma.target P)
    (hresidual : (Gamma.delete (Gamma.vertexSet P)).IsUnhindered)
    (hcard : #(Gamma.delete (Gamma.vertexSet P)).source = kappa)
    (hsepP : RelationalRoof.Separates Gamma.graph.Adj
      A Gamma.target C.newSlice)
    (hR : R ⊆ firstHitPrefixFamily hP hsepP) :
    ∃ D : CurrentLaterLinkage C Gamma.source,
      P ⊆ D.ambient ∧ R ⊆ D.later := by
  obtain ⟨W, hW, hPW⟩ :=
    exists_fullLinkage_containing_of_delete_unhindered
      hext hGamma hA hP hresidual hcard
  have hsourceRoof : Gamma.source ⊆ C.outerRoof :=
    C.source_subset_outerRoof
  let hsepW : RelationalRoof.Separates Gamma.graph.Adj
      Gamma.source Gamma.target C.newSlice :=
    separates_target_of_subset_roof hsourceRoof
  let later : Set Gamma.DPath := firstHitPrefixFamily hW hsepW
  have hlater : IsLinkageBetween Gamma Gamma.source C.newSlice later :=
    firstHitPrefixFamily_isLinkageBetween hW hsepW
  have hlaterRoof : ∀ q ∈ later, q.support ⊆ C.outerRoof := by
    rintro q hq
    change q ∈ SliceSegmentCore.segmentFamily
      (firstHitSegmentRealization hW hsepW) at hq
    obtain ⟨a, rfl⟩ := hq
    change (linkageFirstHitAt hW hsepW a).support ⊆ C.outerRoof
    exact SliceRestrictedDelta.firstHit_support_subset_roof_ambient
      Gamma C.newSlice (linkageFiniteAt hW a)
      (by simpa only [linkageFiniteAt_start] using hsourceRoof a.2)
      (linkageFiniteAt_meets hW hsepW a)
  have hlaterFragment : ∀ q ∈ later, IsLadderFragment Gamma W q := by
    change ∀ q ∈ SliceSegmentCore.segmentFamily
        (firstHitSegmentRealization hW hsepW),
      IsLadderFragment Gamma W q
    exact SliceSegmentCore.segmentFamily_isLadderFragment
      (firstHitSegmentRealization hW hsepW)
  have hprefixMono : firstHitPrefixFamily hP hsepP ⊆ later :=
    firstHitPrefixFamily_mono_of_subset hP hW hA hPW hsepP hsepW
  exact ⟨{
    ambient := W
    later := later
    ambient_linkage := hW
    later_linkage := hlater
    later_in_outerRoof := hlaterRoof
    later_is_ambient_fragment := hlaterFragment }, hPW,
      hR.trans hprefixMono⟩

/-- Prefix-retaining form of the deletion-safe construction.

The safely deleted family `P` consists of complete paths to the ambient
target.  A separately specified family `R` may consist only of their
first-hit prefixes at the selected later frontier.  After completing the
residual source and adjoining it to `P`, first-hit monotonicity shows that
all of `R` still occurs literally in the final later row. -/
theorem ClubStageGeometry.exists_currentLaterLinkage_containing_prefixes
    {theta : Cardinal.{u}} {Yref : Set Gamma.DPath}
    (C : ClubStageGeometry Gamma Yref kappa theta)
    (hext : UniversalExtensionClauseAt V kappa)
    (hGamma : Gamma.IsNormalized)
    {A : Set V} {P R : Set Gamma.DPath}
    (hA : A ⊆ Gamma.source)
    (hP : IsLinkageBetween Gamma A Gamma.target P)
    (hresidual : (Gamma.delete (Gamma.vertexSet P)).IsUnhindered)
    (hcard : #(Gamma.delete (Gamma.vertexSet P)).source = kappa)
    (hsepP : RelationalRoof.Separates Gamma.graph.Adj
      A Gamma.target C.newSlice)
    (hR : R ⊆ firstHitPrefixFamily hP hsepP) :
    ∃ D : CurrentLaterLinkage C Gamma.source, R ⊆ D.later := by
  obtain ⟨D, _hPambient, hRD⟩ :=
    C.exists_currentLaterLinkage_containing_prefixes_with_ambient
      hext hGamma hA hP hresidual hcard hsepP hR
  exact ⟨D, hRD⟩

/-! ## Recovering the ambient target continuation -/

/-- Every vertex on the stopped later row has a concrete continuation to
the ambient target along the corresponding member of the ambient linkage.

This is the information lost if a `CurrentLaterLinkage` is immediately
projected to its `later` field.  The continuation need not lie in the
first-hit prefix family: after its initial vertex it normally runs beyond
the selected frontier, so the ambient carrier and edge relation are exposed
explicitly. -/
theorem CurrentLaterLinkage.exists_ambientTargetSuffix_of_mem_laterVertex
    {theta : Cardinal.{u}} {Yref : Set Gamma.DPath}
    {C : ClubStageGeometry Gamma Yref kappa theta} {A0 : Set V}
    (D : CurrentLaterLinkage C A0) {x : V}
    (hx : x ∈ Gamma.vertexSet D.later) :
    ∃ p : FinitePath Gamma.graph,
      p.start = x ∧ p.finish ∈ Gamma.target ∧
        p.support ⊆ Gamma.vertexSet D.ambient ∧
        p.edgeSet ⊆ familyEdges D.ambient := by
  obtain ⟨q, hqLater, hxq⟩ := hx
  obtain ⟨r, hrAmbient, hqr⟩ := D.exists_ambient_support hqLater
  obtain ⟨rf, rfl⟩ := D.ambient_linkage.finiteCharacter hrAmbient
  have hxrf : x ∈ rf.support := hqr hxq
  let p : FinitePath Gamma.graph := rf.suffixFrom x hxrf
  refine ⟨p, rf.suffixFrom_start x hxrf, ?_, ?_, ?_⟩
  · change (rf.suffixFrom x hxrf).finish ∈ Gamma.target
    rw [rf.suffixFrom_finish]
    exact D.ambient_linkage.terminalFrontier_subset
      ⟨Sum.inl rf, hrAmbient, rfl⟩
  · intro y hyp
    exact ⟨Sum.inl rf, hrAmbient,
      rf.suffixFrom_support_subset x hxrf hyp⟩
  · intro e hep
    simp only [familyEdges, Set.mem_iUnion]
    exact ⟨Sum.inl rf, hrAmbient,
      rf.suffixFrom_edgeSet_subset x hxrf hep⟩

/-- Small-retained-row specialization which derives the residual source
cardinality instead of asking the caller to supply it. -/
theorem ClubStageGeometry.exists_currentLaterLinkage_containing_of_small
    {theta : Cardinal.{u}} {Yref : Set Gamma.DPath}
    (C : ClubStageGeometry Gamma Yref kappa theta)
    (hext : UniversalExtensionClauseAt V kappa)
    (hGamma : Gamma.IsNormalized)
    {A : Set V} {Y : Set Gamma.DPath}
    (hA : A ⊆ Gamma.source)
    (hY : IsLinkageBetween Gamma A Gamma.target Y)
    (hresidual : (Gamma.delete (Gamma.vertexSet Y)).IsUnhindered)
    (hsource : #Gamma.source = kappa) (hAcard : #A < kappa)
    (htight : SliceSpliceSource.MeetsOnlyAtTerminal
      Gamma Y C.newSlice) :
    ∃ D : CurrentLaterLinkage C Gamma.source, Y ⊆ D.later := by
  apply C.exists_currentLaterLinkage_containing hext hGamma hA hY
    hresidual
  · exact IsLinkageBetween.delete_vertexSet_source_card_eq
      hGamma hY hA hsource C.capacity_infinite hAcard
  · exact htight

end LinkageBlueprint
end Blueprint
end Erdos599
