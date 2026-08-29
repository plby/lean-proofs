/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularQuotientReentry
import ErdosProblems.Erdos599.SingularExtension

/-!
# Target-link transport through a singular quotient continuation

The future-safe re-entry construction deliberately drops quotient paths
whose initial vertex belongs to the newly enlarged stop-over.  That is the
right operation for terminal cleanliness, but it is not the right operation
for a target row: a requested quotient source may itself belong to the new
stop-over, and its quotient path may be the path which witnesses that the
source is linked to the target.

This file keeps the two outputs separate.  The ordinary, unrestricted
quotient continuation composes every quotient path with its old ambient
component and therefore preserves the requested target links.  The
frozen/restricted construction remains available in parallel as the clean
geometric state for the next quotient step.  No assertion is made that the
unrestricted target row is terminal-clean at the enlarged stop-over; that
assertion is false when a nontrivial requested path starts in that stop-over.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularTargetLinkTransfer

open SingularContinuation SingularQuotientReentry

universe u

variable {V : Type u}

/-! ## The single hybrid target row -/

/-- Old components ending in the new stop-over are frozen unless their
terminal is one of the quotient sources whose target link is requested. -/
def frozenUnrequested (G : DWeb V) (W : Set G.DPath)
    (E A : Set V) : Set G.DPath :=
  {p | p ∈ W ∧ ∃ e ∈ E \ A, G.terminal? p = some e}

/-- The complementary old components.  It contains every component whose
terminal lies outside `E`, and also the components ending at `A ∩ E`
which must be continued all the way to the target. -/
def pendingRequested (G : DWeb V) (W : Set G.DPath)
    (E A : Set V) : Set G.DPath :=
  W \ frozenUnrequested G W E A

/-- Retain quotient components starting outside `E` together with every
requested component, whether or not its start lies in `E`. -/
def quotientRequested (G : DWeb V) (D E A : Set V)
    (U : Set (G.quotient D).DPath) : Set (G.quotient D).DPath :=
  (G.quotient D).startPaths U (Eᶜ ∪ A)

theorem frozenUnrequested_union_pendingRequested
    (G : DWeb V) (W : Set G.DPath) (E A : Set V) :
    frozenUnrequested G W E A ∪ pendingRequested G W E A = W := by
  ext p
  simp only [frozenUnrequested, pendingRequested, Set.mem_union,
    Set.mem_ofPred_eq, Set.mem_sdiff]
  tauto

theorem quotientRequested_subset
    (G : DWeb V) (D E A : Set V)
    (U : Set (G.quotient D).DPath) :
    quotientRequested G D E A U ⊆ U :=
  fun _ hp ↦ hp.1

/-- The actual hybrid row. -/
noncomputable def hybridContinuation
    (G : DWeb V) {W : Set G.DPath} {D E A : Set V}
    (hD : IsSeparatingHalfwayStopover G W D)
    (hclean : TerminalCleanAt G W D)
    {U : Set (G.quotient D).DPath}
    (hE : IsSeparatingHalfwayStopover (G.quotient D) U E) :
    Set G.DPath := by
  let F := frozenUnrequested G W E A
  let P := pendingRequested G W E A
  let R := quotientRequested G D E A U
  have hWroof : G.vertexSet W ⊆ G.roof D :=
    linkage_vertexSet_subset_roof G hD.linkage hD.separator hclean
  have hProof : G.vertexSet P ⊆ G.roof D := by
    rintro x ⟨p, hp, hxp⟩
    exact hWroof ⟨p, hp.1, hxp⟩
  have hPclean : TerminalCleanAt G P D :=
    fun p hp ↦ hclean p hp.1
  have hRstart : (G.quotient D).initialSet R ⊆ D := by
    rintro x ⟨q, hqR, hqx⟩
    have hxU : x ∈ (G.quotient D).initialSet U := ⟨q, hqR.1, hqx⟩
    rw [hE.linkage.initialSet_eq, hD.quotient_source_eq] at hxU
    exact hxU
  exact frozenPendingContinuation
    G F hProof hD.stopover.minimal hPclean R hRstart

/-- Structural facts for the hybrid row.  Its terminal frontier remains in
the enlarged stop-over even though requested components starting there are
continued rather than frozen. -/
theorem hybridContinuation_structural
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {D E A : Set V}
    (hD : IsSeparatingHalfwayStopover G W D)
    (hclean : TerminalCleanAt G W D)
    {U : Set (G.quotient D).DPath}
    (hE : IsSeparatingHalfwayStopover (G.quotient D) U E) :
    G.IsWarp (hybridContinuation G hD hclean (A := A) hE) ∧
      G.HasFiniteCharacter
        (hybridContinuation G hD hclean (A := A) hE) ∧
      G.ForwardExtension W
        (hybridContinuation G hD hclean (A := A) hE) ∧
      G.initialSet (hybridContinuation G hD hclean (A := A) hE) =
        G.source ∧
      G.terminalFrontier
        (hybridContinuation G hD hclean (A := A) hE) ⊆ E := by
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  let F := frozenUnrequested G W E A
  let P := pendingRequested G W E A
  let R := quotientRequested G D E A U
  have hFsub : F ⊆ W := fun _ hp ↦ hp.1
  have hPsub : P ⊆ W := fun _ hp ↦ hp.1
  have hRsub : R ⊆ U := quotientRequested_subset G D E A U
  have hFwarp : G.IsWarp F := by
    intro p hp q hq hpq
    exact hD.linkage.isWarp (hFsub hp) (hFsub hq) hpq
  have hPwarp : G.IsWarp P := by
    intro p hp q hq hpq
    exact hD.linkage.isWarp (hPsub hp) (hPsub hq) hpq
  have hRwarp : (G.quotient D).IsWarp R := by
    intro p hp q hq hpq
    exact hE.linkage.isWarp (hRsub hp) (hRsub hq) hpq
  have hFfinite : G.HasFiniteCharacter F := by
    intro p hp
    exact hD.linkage.finiteCharacter (hFsub hp)
  have hPfinite : G.HasFiniteCharacter P := by
    intro p hp
    exact hD.linkage.finiteCharacter (hPsub hp)
  have hRfinite : (G.quotient D).HasFiniteCharacter R := by
    intro p hp
    exact hE.linkage.finiteCharacter (hRsub hp)
  have hWroof : G.vertexSet W ⊆ G.roof D :=
    linkage_vertexSet_subset_roof G hD.linkage hD.separator hclean
  have hProof : G.vertexSet P ⊆ G.roof D := by
    rintro x ⟨p, hp, hxp⟩
    exact hWroof ⟨p, hPsub hp, hxp⟩
  have hPclean : TerminalCleanAt G P D :=
    fun p hp ↦ hclean p (hPsub hp)
  have hRstart : (G.quotient D).initialSet R ⊆ D := by
    rintro x ⟨q, hqR, hqx⟩
    have hxU : x ∈ (G.quotient D).initialSet U :=
      ⟨q, hRsub hqR, hqx⟩
    rw [hE.linkage.initialSet_eq, hD.quotient_source_eq] at hxU
    exact hxU
  have hcover : G.terminalFrontier P ⊆
      (G.quotient D).initialSet R := by
    rintro x ⟨p, hpP, hpx⟩
    have hxD : x ∈ D := hD.linkage.terminalFrontier_subset
      ⟨p, hPsub hpP, hpx⟩
    have hxSource : x ∈ (G.quotient D).source := by
      rw [hD.quotient_source_eq]
      exact hxD
    have hxInitial : x ∈ (G.quotient D).initialSet U := by
      rw [hE.linkage.initialSet_eq]
      exact hxSource
    obtain ⟨q, hqU, hqx⟩ := hxInitial
    have hxSelected : x ∈ Eᶜ ∪ A := by
      by_cases hxE : x ∈ E
      · right
        by_contra hxA
        exact hpP.2 ⟨hPsub hpP, x, ⟨hxE, hxA⟩, hpx⟩
      · exact Or.inl hxE
    exact ⟨q, ⟨hqU, hqx ▸ hxSelected⟩, hqx⟩
  have hFP : Disjoint (G.vertexSet F) (G.vertexSet P) := by
    apply Set.disjoint_left.2
    intro x hxF hxP
    obtain ⟨p, hpF, hxp⟩ := hxF
    obtain ⟨q, hqP, hxq⟩ := hxP
    have hpq : p ≠ q := by
      intro hpq
      subst q
      exact hqP.2 hpF
    exact Set.disjoint_left.1
      (hD.linkage.isWarp (hFsub hpF) (hPsub hqP) hpq) hxp hxq
  have hFR : Disjoint (G.vertexSet F)
      (G.vertexSet (liftedQuotientFamily G D R)) := by
    have hcompat :=
      starCompatible_liftQuotientFamily_of_roof
        G hWroof hD.stopover.minimal hclean hRstart
    apply Set.disjoint_left.2
    intro x hxF hxR
    obtain ⟨p, hpF, hxp⟩ := hxF
    obtain ⟨q, hqLift, hxq⟩ := hxR
    have hxGlue := hcompat p (hFsub hpF) q hqLift x hxp hxq
    obtain ⟨e, heEA, hpterm⟩ := hpF.2
    have hxe : x = e := Option.some.inj (hxGlue.1.symm.trans hpterm)
    obtain ⟨q₀, hq₀R, rfl⟩ := hqLift
    have hqStartSelected : q₀.initial ∈ Eᶜ ∪ A := hq₀R.2
    rw [G.initial_liftQuotientPath] at hxGlue
    have hqStartE : q₀.initial ∈ E := hxGlue.2.symm ▸ hxe ▸ heEA.1
    rcases hqStartSelected with hnotE | hA
    · exact hnotE hqStartE
    · apply heEA.2
      rw [← hxGlue.2.trans hxe]
      exact hA
  let W' : Set G.DPath :=
    frozenPendingContinuation
      G F hProof hD.stopover.minimal hPclean R hRstart
  have hW'warp : G.IsWarp W' :=
    frozenPendingContinuation_isWarp
      G hFwarp hPwarp hProof hD.stopover.minimal hPclean
        hRwarp hRstart
        (disjoint_vertexSet_pendingContinuation
          G hProof hD.stopover.minimal hPclean R hRstart hFP hFR)
  have hW'finite : G.HasFiniteCharacter W' :=
    frozenPendingContinuation_finiteCharacter
      G hFfinite hPfinite hProof hD.stopover.minimal hPclean
        hRfinite hRstart
  have hforwardFP : G.ForwardExtension (F ∪ P) W' :=
    forwardExtension_frozenPendingContinuation
      G F hProof hD.stopover.minimal hPclean R hRstart
  have hforward : G.ForwardExtension W W' := by
    rw [← frozenUnrequested_union_pendingRequested G W E A]
    exact hforwardFP
  have hinitial : G.initialSet W' = G.source := by
    rw [← hD.linkage.initialSet_eq]
    exact (G.initialSet_eq_of_forwardExtension hforward).symm
  have hterminal : G.terminalFrontier W' ⊆ E := by
    have hfront : G.terminalFrontier W' ⊆
        G.terminalFrontier F ∪ (G.quotient D).terminalFrontier R :=
      terminalFrontier_frozenPendingContinuation_subset
        (F := F) G hPfinite hProof hD.stopover.minimal hPclean
          hRstart hcover
    intro x hx
    rcases hfront hx with hxF | hxR
    · obtain ⟨p, hpF, hpx⟩ := hxF
      obtain ⟨e, heEA, hpterm⟩ := hpF.2
      exact Option.some.inj (hpx.symm.trans hpterm) ▸ heEA.1
    · exact hE.linkage.terminalFrontier_subset
        ⟨hxR.choose, hRsub hxR.choose_spec.1, hxR.choose_spec.2⟩
  change G.IsWarp W' ∧ G.HasFiniteCharacter W' ∧
    G.ForwardExtension W W' ∧ G.initialSet W' = G.source ∧
    G.terminalFrontier W' ⊆ E
  exact ⟨hW'warp, hW'finite, hforward, hinitial, hterminal⟩

/-- Quotient target links pull back along an old source--stop-over linkage.

`RoutesTerminals G W B A` is the exact boundary correspondence: the old
component starting at `b ∈ B` ends at a quotient source in `A`.  The
unrestricted source-star then appends the unique quotient component starting
there.  In particular this proof does not discard the component when that
quotient source happens to lie in a later enlarged stop-over. -/
theorem linksToTarget_continuation
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {D : Set V}
    (hD : IsSeparatingHalfwayStopover G W D)
    (hclean : TerminalCleanAt G W D)
    {U : Set (G.quotient D).DPath}
    (hUwarp : (G.quotient D).IsWarp U)
    (hUfinite : (G.quotient D).HasFiniteCharacter U)
    (hUinitial : (G.quotient D).initialSet U =
      (G.quotient D).source)
    {A B : Set V}
    (hA : A ⊆ (G.quotient D).source)
    (hB : B ⊆ G.source)
    (hroute : RoutesTerminals G W B A)
    (hlinks : LinksToTarget (G.quotient D) U A) :
    LinksToTarget G
      (continuation G hD.linkage hD.separator hD.stopover.minimal
        hclean U hUinitial) B := by
  intro b hb
  obtain ⟨f, hfW, hfStart, hfFinishA⟩ := hroute b hb
  obtain ⟨p, hpU, q, hpq, hpure, before, after, hsupport,
    t, htTarget, htAfter⟩ := hlinks f.finish hfFinishA
  have hpq' : p =
      (Sum.inl q : (G.quotient D).DPath) := hpq
  subst p
  have hfinishQ : f.finish ∈ q.support := by
    have hsingleton : f.finish ∈ ({f.finish} : Set V) :=
      Set.mem_singleton f.finish
    rw [← hpure] at hsingleton
    exact hsingleton.1
  have hfinishInitial : f.finish ∈
      (G.quotient D).initialSet U := by
    rw [hUinitial]
    exact hA hfFinishA
  obtain ⟨q₀, hq₀U, hq₀Initial⟩ := hfinishInitial
  have hq₀eq : q₀ =
      (Sum.inl q : (G.quotient D).DPath) := by
    by_contra hne
    exact Set.disjoint_left.1
      (hUwarp hq₀U hpU hne)
      (hq₀Initial.symm ▸ q₀.initial_mem_support) hfinishQ
  subst q₀
  have hqStart : q.start = f.finish := hq₀Initial
  have hWroof : G.vertexSet W ⊆ G.roof D :=
    linkage_vertexSet_subset_roof
      G hD.linkage hD.separator hclean
  let L := liftedQuotientFamily G D U
  have hcompat : G.StarCompatible W L :=
    starCompatible_liftQuotientFamily_of_linkage
      G hD.linkage hD.separator hD.stopover.minimal hclean hUinitial
  let qLift : G.DPath := G.liftQuotientPath D (.inl q)
  have hqLiftL : qLift ∈ L := ⟨.inl q, hpU, rfl⟩
  have hqLiftInitial : qLift.initial = f.finish := by
    change q.start = f.finish
    exact hqStart
  have hmatch : ∃ r ∈ L, r.initial = f.finish :=
    ⟨qLift, hqLiftL, hqLiftInitial⟩
  let chosen : G.DPath := Classical.choose hmatch
  have hchosenL : chosen ∈ L := (Classical.choose_spec hmatch).1
  have hchosenInitial : chosen.initial = f.finish :=
    (Classical.choose_spec hmatch).2
  have hLwarp : G.IsWarp L :=
    DWeb.IsWarp.liftQuotientFamily G hUwarp
  have hchosenEq : chosen = qLift := by
    by_contra hne
    exact Set.disjoint_left.1 (hLwarp hchosenL hqLiftL hne)
      (hchosenInitial.symm ▸ chosen.initial_mem_support)
      (hqLiftInitial.symm ▸ qLift.initial_mem_support)
  let rStar : G.DPath := G.starPath hcompat ⟨.inl f, hfW⟩
  have hrMem : rStar ∈
      continuation G hD.linkage hD.separator hD.stopover.minimal
        hclean U hUinitial :=
    ⟨⟨.inl f, hfW⟩, rfl⟩
  have htQ : t ∈ q.support := by
    change t ∈ q.walk.support
    rw [hsupport]
    exact List.mem_append_right before htAfter
  have htLift : t ∈ qLift.support := by
    dsimp only [qLift]
    rw [G.support_liftQuotientPath]
    exact htQ
  have htChosen : t ∈ chosen.support := hchosenEq ▸ htLift
  have htStar : t ∈ rStar.support := by
    dsimp only [rStar]
    simp only [DWeb.starPath]
    split
    next hmatch' =>
      let chosen' : G.DPath := Classical.choose hmatch'
      have hchosen'L : chosen' ∈ L :=
        (Classical.choose_spec hmatch').1
      have hchosen'Initial : chosen'.initial = f.finish :=
        (Classical.choose_spec hmatch').2
      have hchosen'Eq : chosen' = qLift := by
        by_contra hne
        exact Set.disjoint_left.1 (hLwarp hchosen'L hqLiftL hne)
          (hchosen'Initial.symm ▸ chosen'.initial_mem_support)
          (hqLiftInitial.symm ▸ qLift.initial_mem_support)
      have htChosen' : t ∈ chosen'.support := hchosen'Eq ▸ htLift
      have hinter : f.support ∩ chosen'.support ⊆ {f.finish} := by
        intro x hx
        have hx' := hcompat (.inl f) hfW chosen' hchosen'L x hx.1 hx.2
        exact Set.mem_singleton_iff.2 (Option.some.inj hx'.1).symm
      rw [DirectedPath.Path.support_appendFinite f chosen'
        hchosen'Initial hinter]
      exact Or.inr htChosen'
    next hnone =>
      exact (hnone hmatch).elim
  have hContinuedFinite : G.HasFiniteCharacter
      (continuation G hD.linkage hD.separator hD.stopover.minimal
        hclean U hUinitial) :=
    continuation_finiteCharacter G hD.linkage hD.separator
      hD.stopover.minimal hclean hUfinite hUinitial
  obtain ⟨g, hrg⟩ := hContinuedFinite hrMem
  have hgMem : (Sum.inl g : G.DPath) ∈
      continuation G hD.linkage hD.separator hD.stopover.minimal
        hclean U hUinitial := hrg ▸ hrMem
  have htG : t ∈ g.support := by
    rw [hrg] at htStar
    exact htStar
  have hgStart : g.start = b := by
    have hstart := G.initial_starPath hcompat
      ⟨(.inl f : G.DPath), hfW⟩
    dsimp only [rStar] at hrg
    rw [hrg] at hstart
    exact hstart.trans hfStart
  have htFinish : t = g.finish :=
    hNorm.eq_finish_of_mem_walk g.walk htG htTarget
  have hgSourcePure : g.support ∩ B = {b} := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxg, hxB⟩
      exact Set.mem_singleton_iff.2
        ((hNorm.eq_start_of_mem_walk g.walk hxg (hB hxB)).trans hgStart)
    · intro x hx
      have hxb : x = b := Set.mem_singleton_iff.1 hx
      subst x
      refine ⟨?_, hb⟩
      exact hgStart ▸ g.start_mem_support
  refine ⟨.inl g, hgMem, g, rfl, hgSourcePure, ?_⟩
  refine ⟨[], g.walk.support.tail, ?_, g.finish, ?_, ?_⟩
  · simp only [List.nil_append]
    calc
      g.walk.support =
          g.walk.support.head g.walk.support_ne_nil ::
            g.walk.support.tail :=
        (g.walk.support.cons_head_tail g.walk.support_ne_nil).symm
      _ = b :: g.walk.support.tail := by
        congr 1
        rw [g.walk.head_support]
        exact hgStart
  · exact htFinish ▸ htTarget
  · have hcons : b :: g.walk.support.tail = g.walk.support := by
      have hhead :
          g.walk.support.head g.walk.support_ne_nil = b :=
        g.walk.head_support.trans hgStart
      calc
        b :: g.walk.support.tail =
            g.walk.support.head g.walk.support_ne_nil ::
              g.walk.support.tail :=
          congrArg (fun x ↦ x :: g.walk.support.tail) hhead.symm
        _ = g.walk.support :=
          g.walk.support.cons_head_tail g.walk.support_ne_nil
    change g.finish ∈ b :: g.walk.support.tail
    rw [hcons]
    exact g.finish_mem_support

/-- Paired singular re-entry output.  `Wclean` is the terminal-clean
frozen/restricted family used for the next quotient geometry.  `Wtarget`
is the unrestricted continuation used as the next target row; it retains
all quotient target witnesses, including witnesses whose quotient path
starts in the newly enlarged stop-over `E`. -/
theorem exists_reenteredContinuation_of_halfway_with_targetLinks
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {D : Set V}
    (hD : IsSeparatingHalfwayStopover G W D)
    (hclean : TerminalCleanAt G W D)
    {A B : Set V} (hA : A ⊆ (G.quotient D).source)
    (hB : B ⊆ G.source)
    (hroute : RoutesTerminals G W B A)
    {kappa : Cardinal.{u}}
    {U : Set (G.quotient D).DPath}
    (hU : IsHalfwayLinkageOfAltitude (G.quotient D) A kappa U) :
    ∃ (E : Set V) (Wclean Wtarget : Set G.DPath),
      IsSeparatingHalfwayStopover (G.quotient D) U E ∧
      HeightAtMost (G.quotient D) E kappa ∧
      IsSeparatingHalfwayStopover G Wclean E ∧
      TerminalCleanAt G Wclean E ∧
      G.ForwardExtension W Wclean ∧
      G.initialSet Wclean = G.source ∧
      G.IsWarp Wtarget ∧
      G.HasFiniteCharacter Wtarget ∧
      G.ForwardExtension W Wtarget ∧
      G.initialSet Wtarget = G.source ∧
      LinksToTarget G Wtarget B := by
  obtain ⟨C, hC⟩ := hU.1
  let Wtarget : Set G.DPath :=
    continuation G hD.linkage hD.separator hD.stopover.minimal
      hclean U hC.linkage.initialSet_eq
  have hTargetWarp : G.IsWarp Wtarget :=
    continuation_isWarp G hD.linkage hD.separator hD.stopover.minimal
      hclean hC.linkage.isWarp hC.linkage.initialSet_eq
  have hTargetFinite : G.HasFiniteCharacter Wtarget :=
    continuation_finiteCharacter G hD.linkage hD.separator
      hD.stopover.minimal hclean hC.linkage.finiteCharacter
      hC.linkage.initialSet_eq
  have hTargetForward : G.ForwardExtension W Wtarget :=
    forwardExtension_continuation G hD.linkage hD.separator
      hD.stopover.minimal hclean U hC.linkage.initialSet_eq
  have hTargetInitial : G.initialSet Wtarget = G.source :=
    initialSet_continuation G hD.linkage hD.separator
      hD.stopover.minimal hclean U hC.linkage.initialSet_eq
  have hTargetLinks : LinksToTarget G Wtarget B :=
    linksToTarget_continuation hNorm hD hclean
      hC.linkage.isWarp hC.linkage.finiteCharacter
      hC.linkage.initialSet_eq hA hB hroute hU.2.1
  obtain ⟨E, Wclean, hE, hheightE, hWclean, hWcleanClean,
      hCleanForward, hCleanInitial⟩ :=
    exists_reenteredContinuation_of_halfway hNorm hD hclean hU
  exact ⟨E, Wclean, Wtarget, hE, hheightE, hWclean, hWcleanClean,
    hCleanForward, hCleanInitial, hTargetWarp, hTargetFinite,
    hTargetForward, hTargetInitial, hTargetLinks⟩

end SingularTargetLinkTransfer
end CardinalInduction
end Erdos599
