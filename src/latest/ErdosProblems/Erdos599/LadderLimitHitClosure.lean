/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LadderPersistence
import ErdosProblems.Erdos599.RegularSplitLegality

/-!
# Closure of the hit stages of a limiting ladder path

This file supplies the path-local input in source Lemma 7.28.  The key
point is that a component which is already inessential is preserved
literally by every later successor, and at a limit its eventually constant
thread has the same direct limit.
-/

noncomputable section

open Cardinal Order Set Erdos599.DirectedPath

namespace Erdos599
namespace DWeb

universe u v

variable {V : Type u} {G : DWeb V}

namespace DirectedPath

private theorem Walk.eq_of_support_eq_limitHitClosure
    {D : Digraph V} {a b : V} (p q : Walk D a b)
    (h : p.support = q.support) : p = q := by
  induction p with
  | nil =>
      cases q with
      | nil => rfl
      | @cons _ c _ e q =>
          simp only [Walk.support_nil, Walk.support_cons] at h
          have hlen := congrArg List.length h
          simp at hlen
  | @cons a c b e p ih =>
      cases q with
      | nil =>
          simp only [Walk.support_cons, Walk.support_nil] at h
          have hlen := congrArg List.length h
          simp at hlen
      | @cons _ d _ f q =>
          simp only [Walk.support_cons] at h
          have htail : p.support = q.support := (List.cons.inj h).2
          have hhead := congrArg List.head? htail
          rw [List.head?_eq_some_head p.support_ne_nil, p.head_support,
            List.head?_eq_some_head q.support_ne_nil, q.head_support] at hhead
          have hcd : c = d := Option.some.inj hhead
          subst d
          have hpq : p = q := ih q htail
          subst q
          rfl

private theorem FinitePath.eq_of_prefix_of_finish_eq_limitHitClosure
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
          have hw : pw = qw :=
            Walk.eq_of_support_eq_limitHitClosure pw qw hs
          subst qw
          rfl

private theorem Path.eq_of_extends_of_same_terminal_limitHitClosure
    {D : Digraph V} {p q : Path D} {x : V}
    (hpq : Path.Extends p q)
    (hp : p.terminal? = some x) (hq : q.terminal? = some x) : p = q := by
  rcases p with p | r <;> rcases q with q | s
  · congr 1
    apply FinitePath.eq_of_prefix_of_finish_eq_limitHitClosure hpq
    exact Option.some.inj (hp.trans hq.symm)
  · simp at hq
  · exact hpq.elim
  · simp at hp

end DirectedPath

namespace GrowingWarpChain

variable {I : Type v} [LinearOrder I] [IsDirectedOrder I]

/-- A path which occurs literally at every stage of a tail occurs literally
in the genuine threadwise direct limit. -/
theorem mem_limitPaths_of_tail (C : G.GrowingWarpChain I) (i : I)
    {p : G.DPath} (hp : p ∈ C.stage i)
    (htail : ∀ j, i ≤ j → p ∈ C.stage j) :
    p ∈ C.limitPaths G := by
  have hpInitial : p.initial ∈ C.initialUnion :=
    Set.mem_iUnion.2 ⟨i, p, hp, rfl⟩
  let a : C.initialUnion := ⟨p.initial, hpInitial⟩
  have hpThread : p ∈ C.thread G a.1 := ⟨i, hp, rfl⟩
  have hpExtends : G.Extends p (C.threadLimit G a) :=
    DirectedPath.Path.extends_chainLimit (C.thread G a.1)
      (C.thread_nonempty G a) (C.thread_isChain G a.1) hpThread
  have hlimitEq : C.threadLimit G a = p := by
    rcases p with p | r
    · have hcofinal : DirectedPath.Path.TerminalCofinal
          (C.thread G a.1) p.finish := by
        intro q hqThread
        obtain ⟨j, hqj, hqInitial⟩ := hqThread
        obtain ⟨k, hjk, hik⟩ := exists_ge_ge j i
        obtain ⟨s, hsk, hqs⟩ := C.grows hjk q hqj
        have hpK : (Sum.inl p : G.DPath) ∈ C.stage k :=
          htail k hik
        have hsInitial : s.initial = a.1 :=
          (G.extends_initial hqs).symm.trans hqInitial
        have hsp : s = (Sum.inl p : G.DPath) :=
          DWeb.IsWarp.eq_of_initial_eq G (C.isWarp k) hsk hpK hsInitial
        exact ⟨.inl p, ⟨k, hpK, rfl⟩, hsp ▸ hqs, rfl⟩
      have hterminal : (C.threadLimit G a).terminal? = some p.finish :=
        DirectedPath.Path.terminal_chainLimit_of_cofinal
          (C.thread G a) (C.thread_nonempty G a)
          (C.thread_isChain G a) hcofinal
      exact (DirectedPath.Path.eq_of_extends_of_same_terminal_limitHitClosure
        hpExtends rfl hterminal).symm
    · cases hq : C.threadLimit G a with
      | inl q =>
          rw [hq] at hpExtends
          exact hpExtends.elim
      | inr s =>
          rw [hq] at hpExtends
          change r = s at hpExtends
          congr 1
          exact hpExtends.symm
  exact ⟨a, hlimitEq⟩

end GrowingWarpChain

namespace KappaLadder

open Ladder

variable {κ : Cardinal.{u}} {L : G.KappaLadder κ}

/-- Inessential components persist between ordinary stages of every legal
ladder.  Successors use the explicit legality clause; limits use the genuine
threadwise limit and strict-frontier chronology. -/
theorem IsSplitLegal.inessentialPaths_mono_stage (hL : L.IsSplitLegal)
    {a b : Stage κ} (hab : a ≤ b) :
    G.inessentialPaths (L.warpAt a) ⊆
      G.inessentialPaths (L.warpAt b) := by
  let accumulatedAt (o : Ordinal.{u}) (ho : o < κ.ord) :=
    L.accumulated (⟨o, ho.le⟩ : ExtendedStage κ)
  have hmain : ∀ o : Ordinal.{u}, ∀ ho : o < κ.ord,
      ∀ c : Ordinal.{u}, c ≤ o → ∀ hc : c < κ.ord,
        G.inessentialPaths (accumulatedAt c hc) ⊆
          G.inessentialPaths (accumulatedAt o ho) := by
    intro o
    induction o using Ordinal.limitRecOn with
    | zero =>
        intro ho c hc hcκ
        have hc0 : c = 0 := le_antisymm hc bot_le
        subst c
        exact Set.Subset.rfl
    | add_one o ih =>
        intro ho c hc hcκ p hp
        rcases hc.lt_or_eq with hc | rfl
        · have hco : c ≤ o := (Order.lt_add_one_iff).1 hc
          have hoκ : o < κ.ord :=
            (show o < o + 1 by
              rw [← Order.succ_eq_add_one]
              exact Order.lt_succ o).trans ho
          have hpO := ih hoκ c hco hcκ hp
          let os : Stage κ := ⟨o, hoκ⟩
          have hpNext := hL.currentInessentialPersists os hpO
          exact hpNext
        · exact hp
    | limit o hoLimit ih =>
        intro hoκ c hc hcκ p hp
        rcases hc.lt_or_eq with hc | rfl
        · let oe : ExtendedStage κ := ⟨o, hoκ.le⟩
          obtain ⟨C, hstage, hlimit⟩ := hL.limitStages oe hoLimit
          let : Nonempty (Set.Iio o) := hoLimit.nonempty_Iio.to_subtype
          let ci : Set.Iio o := ⟨c, hc⟩
          have hpCi : p ∈ G.inessentialPaths (C.stage ci) := by
            rw [hstage ci]
            exact hp
          have hpTail : ∀ d, ci ≤ d →
              p ∈ G.inessentialPaths (C.stage d) := by
            intro d hcd
            rw [hstage d]
            apply ih d.1 d.2 (d.2.trans hoκ) c hcd hcκ
            exact hp
          have hstrict :
              G.strictRoof (G.terminalFrontier (C.stage ci)) ⊆
                G.strictRoof (G.terminalFrontier (C.limitPaths G)) := by
            rw [hstage ci, ← hlimit]
            let cs : Stage κ := ⟨c, hcκ⟩
            let os : Stage κ := ⟨o, hoκ⟩
            change
              G.strictRoof (G.terminalFrontier (L.warpAt cs)) ⊆
                G.strictRoof (G.terminalFrontier (L.warpAt os))
            have hfront := hL.strictRoof_frontier_mono
              (show cs ≤ os from hc.le)
            simpa only [
              L.frontier_eq_essential_terminalFrontier
                hL.roofsSourceAtStages,
              G.strictRoof_essential] using hfront
          change p ∈ G.inessentialPaths (L.accumulated oe)
          rw [hlimit]
          exact C.mem_inessentialPaths_limitPaths_of_tail
            ci hpCi hpTail hstrict
        · exact hp
  exact hmain b.1 b.2 a.1 hab a.2

/-- An inessential ordinary-stage component occurs literally in the final
ladder warp.  At the final direct limit its thread is eventually constant. -/
theorem IsSplitLegal.mem_limitWarp_of_mem_inessential (hL : L.IsSplitLegal)
    {a : Stage κ} {p : G.DPath}
    (hp : p ∈ G.inessentialPaths (L.warpAt a)) :
    p ∈ L.limitWarp := by
  have hκLimit : Order.IsSuccLimit κ.ord :=
    Cardinal.isSuccLimit_ord hL.regular.aleph0_le
  obtain ⟨C, hstage, hlimit⟩ :=
    hL.limitStages (Ladder.finalStage κ) hκLimit
  let : Nonempty (Set.Iio κ.ord) := hκLimit.nonempty_Iio.to_subtype
  let ai : Set.Iio κ.ord := ⟨a.1, a.2⟩
  have hpAi : p ∈ C.stage ai := by
    rw [hstage ai]
    exact hp.1
  have hpTail : ∀ b, ai ≤ b → p ∈ C.stage b := by
    intro b hab
    rw [hstage b]
    let bs : Stage κ := ⟨b.1, b.2⟩
    exact (hL.inessentialPaths_mono_stage
      (a := a) (b := bs) hab hp).1
  change p ∈ L.accumulated (Ladder.finalStage κ)
  rw [hlimit]
  exact C.mem_limitPaths_of_tail ai hpAi hpTail

/-- A component of an ordinary stage which meets a component of the final
warp extends to that very final component.  Both extensions belong to the
final warp, where path disjointness makes the continuation unique. -/
theorem IsSplitLegal.extends_limitWarp_of_stage_intersects (hL : L.IsSplitLegal)
    {a : Stage κ} {q p : G.DPath}
    (hq : q ∈ L.warpAt a) (hp : p ∈ L.limitWarp)
    (hqp : (q.support ∩ p.support).Nonempty) :
    G.Extends q p := by
  have hκLimit : Order.IsSuccLimit κ.ord :=
    Cardinal.isSuccLimit_ord hL.regular.aleph0_le
  obtain ⟨r, hr, hqr⟩ := hL.limitStages.grows_to_limit
    (Ladder.finalStage κ) hκLimit ⟨a.1, a.2⟩ q hq
  have hrpMeet : (r.support ∩ p.support).Nonempty := by
    obtain ⟨x, hxq, hxp⟩ := hqp
    exact ⟨x, G.support_mono_of_extends hqr hxq, hxp⟩
  have hrp : r = p := by
    by_contra hne
    obtain ⟨x, hxr, hxp⟩ := hrpMeet
    exact Set.disjoint_left.1
      (hL.warpStages (Ladder.finalStage κ) hr hp hne) hxr hxp
  rwa [hrp] at hqr

/-- Every hit of a limiting ladder path is witnessed by an essential
component of the corresponding accumulated warp. -/
theorem IsSplitLegal.limitWarp_hitStages_essential_prefix (hL : L.IsSplitLegal)
    {p : G.DPath} (hp : p ∈ L.limitWarp)
    (Sigma : Set (Stage κ)) :
    ∀ a ∈ L.hitStages Sigma p,
      ∃ q ∈ G.essentialWarpPart (L.warpAt a),
        (p.support ∩ q.support).Nonempty := by
  intro a ha
  obtain ⟨x, hxFrontier, hxp⟩ := ha.2
  have hxEssential :
      x ∈ G.essential (G.terminalFrontier (L.warpAt a)) := by
    rwa [← L.frontier_eq_essential_terminalFrontier
      hL.roofsSourceAtStages a]
  have hxTerminal :
      x ∈ G.terminalFrontier (G.essentialWarpPart (L.warpAt a)) := by
    rwa [G.terminalFrontier_essentialWarpPart]
  obtain ⟨q, hq, hqx⟩ := hxTerminal
  exact ⟨q, hq, x, hxp, G.terminal_mem_support hqx⟩

end KappaLadder
end DWeb
end Erdos599
