/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularTargetLinkTransfer

/-!
# Target links for the hybrid singular continuation

`hybridContinuation` retains every quotient component whose initial vertex
is requested, even when that vertex belongs to the new stop-over.  This file
proves that the retained components transport all requested target links.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularHybridTargetTransfer

open SingularContinuation SingularQuotientReentry
  SingularTargetLinkTransfer

universe u

variable {V : Type u}

/-- Quotient target links pull back through the hybrid continuation.  The
key point is that `quotientRequested` contains all components starting in
`A`, including the ones starting in the new stop-over `E`. -/
theorem linksToTarget_hybridContinuation
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {D E : Set V}
    (hD : IsSeparatingHalfwayStopover G W D)
    (hclean : TerminalCleanAt G W D)
    {U : Set (G.quotient D).DPath}
    (hE : IsSeparatingHalfwayStopover (G.quotient D) U E)
    {A B : Set V} (hB : B ⊆ G.source)
    (hA : A ⊆ (G.quotient D).source)
    (hroute : RoutesTerminals G W B A)
    (hlinks : LinksToTarget (G.quotient D) U A) :
    LinksToTarget G
      (hybridContinuation G hD hclean (A := A) hE) B := by
  intro b hb
  obtain ⟨f, hfW, hfStart, hfFinishA⟩ := hroute b hb
  let P := pendingRequested G W E A
  let R := quotientRequested G D E A U
  have hfP : (Sum.inl f : G.DPath) ∈ P := by
    refine ⟨hfW, ?_⟩
    rintro ⟨_hfW, e, heEA, hfterm⟩
    have hef : e = f.finish := Option.some.inj hfterm.symm
    exact heEA.2 (hef ▸ hfFinishA)
  obtain ⟨p, hpU, q, hpq, hpure, before, after, hsupport,
    t, htTarget, htAfter⟩ := hlinks f.finish hfFinishA
  have hpq' : p = (Sum.inl q : (G.quotient D).DPath) := hpq
  subst p
  have hfinishQ : f.finish ∈ q.support := by
    have hsingleton : f.finish ∈ ({f.finish} : Set V) :=
      Set.mem_singleton f.finish
    rw [← hpure] at hsingleton
    exact hsingleton.1
  have hfinishInitial : f.finish ∈ (G.quotient D).initialSet U := by
    rw [hE.linkage.initialSet_eq]
    exact hA hfFinishA
  obtain ⟨q₀, hq₀U, hq₀Initial⟩ := hfinishInitial
  have hq₀eq : q₀ = (Sum.inl q : (G.quotient D).DPath) := by
    by_contra hne
    exact Set.disjoint_left.1
      (hE.linkage.isWarp hq₀U hpU hne)
      (hq₀Initial.symm ▸ q₀.initial_mem_support) hfinishQ
  subst q₀
  have hqStart : q.start = f.finish := hq₀Initial
  have hqR : (Sum.inl q : (G.quotient D).DPath) ∈ R := by
    refine ⟨hpU, ?_⟩
    change q.start ∈ Eᶜ ∪ A
    exact Or.inr (hqStart ▸ hfFinishA)
  have hWroof : G.vertexSet W ⊆ G.roof D :=
    linkage_vertexSet_subset_roof G hD.linkage hD.separator hclean
  have hProof : G.vertexSet P ⊆ G.roof D := by
    rintro x ⟨r, hr, hxr⟩
    exact hWroof ⟨r, hr.1, hxr⟩
  have hPclean : TerminalCleanAt G P D :=
    fun r hr ↦ hclean r hr.1
  have hRstart : (G.quotient D).initialSet R ⊆ D := by
    rintro x ⟨r, hr, hrx⟩
    have hxU : x ∈ (G.quotient D).initialSet U := ⟨r, hr.1, hrx⟩
    rw [hE.linkage.initialSet_eq, hD.quotient_source_eq] at hxU
    exact hxU
  let L := liftedQuotientFamily G D R
  have hcompat : G.StarCompatible P L :=
    starCompatible_liftQuotientFamily_of_roof
      G hProof hD.stopover.minimal hPclean hRstart
  let qLift : G.DPath := G.liftQuotientPath D (.inl q)
  have hqLiftL : qLift ∈ L := ⟨.inl q, hqR, rfl⟩
  have hqLiftInitial : qLift.initial = f.finish := by
    change q.start = f.finish
    exact hqStart
  have hmatch : ∃ r ∈ L, r.initial = f.finish :=
    ⟨qLift, hqLiftL, hqLiftInitial⟩
  have hLwarp : G.IsWarp L := by
    apply DWeb.IsWarp.liftQuotientFamily G
    intro r hr s hs hrs
    exact hE.linkage.isWarp hr.1 hs.1 hrs
  let rStar : G.DPath := G.starPath hcompat ⟨.inl f, hfP⟩
  have hrPending : rStar ∈
      pendingContinuation
        G hProof hD.stopover.minimal hPclean R hRstart :=
    ⟨⟨.inl f, hfP⟩, rfl⟩
  have hrMem : rStar ∈
      hybridContinuation G hD hclean (A := A) hE := by
    change rStar ∈
      frozenUnrequested G W E A ∪
        pendingContinuation
          G hProof hD.stopover.minimal hPclean R hRstart
    exact Or.inr hrPending
  have htQ : t ∈ q.support := by
    change t ∈ q.walk.support
    rw [hsupport]
    exact List.mem_append_right before htAfter
  have htLift : t ∈ qLift.support := by
    dsimp only [qLift]
    rw [G.support_liftQuotientPath]
    exact htQ
  have htStar : t ∈ rStar.support := by
    dsimp only [rStar]
    simp only [DWeb.starPath]
    split
    next hmatch' =>
      let chosen : G.DPath := Classical.choose hmatch'
      have hchosenL : chosen ∈ L :=
        (Classical.choose_spec hmatch').1
      have hchosenInitial : chosen.initial = f.finish :=
        (Classical.choose_spec hmatch').2
      have hchosenEq : chosen = qLift := by
        by_contra hne
        exact Set.disjoint_left.1 (hLwarp hchosenL hqLiftL hne)
          (hchosenInitial.symm ▸ chosen.initial_mem_support)
          (hqLiftInitial.symm ▸ qLift.initial_mem_support)
      have htChosen : t ∈ chosen.support := hchosenEq ▸ htLift
      have hinter : f.support ∩ chosen.support ⊆ {f.finish} := by
        intro x hx
        have hx' := hcompat (.inl f) hfP chosen hchosenL x hx.1 hx.2
        exact Set.mem_singleton_iff.2 (Option.some.inj hx'.1).symm
      rw [DirectedPath.Path.support_appendFinite f chosen
        hchosenInitial hinter]
      exact Or.inr htChosen
    next hnone =>
      exact (hnone hmatch).elim
  have hPfinite : G.HasFiniteCharacter P := by
    intro r hr
    exact hD.linkage.finiteCharacter hr.1
  have hRfinite : (G.quotient D).HasFiniteCharacter R := by
    intro r hr
    exact hE.linkage.finiteCharacter hr.1
  have hPendingFinite : G.HasFiniteCharacter
      (pendingContinuation
        G hProof hD.stopover.minimal hPclean R hRstart) :=
    pendingContinuation_finiteCharacter
      G hPfinite hProof hD.stopover.minimal hPclean hRfinite hRstart
  obtain ⟨g, hrg⟩ := hPendingFinite hrPending
  have hgMem : (Sum.inl g : G.DPath) ∈
      hybridContinuation G hD hclean (A := A) hE := hrg ▸ hrMem
  have htG : t ∈ g.support := by
    rw [hrg] at htStar
    exact htStar
  have hgStart : g.start = b := by
    have hstart := G.initial_starPath hcompat ⟨(.inl f : G.DPath), hfP⟩
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

end SingularHybridTargetTransfer
end CardinalInduction
end Erdos599
