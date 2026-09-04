/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LadderStrictChronology

/-!
# Persistence of inessential paths in the canonical ladder

This file proves the pathwise persistence assertion of source Lemma 7.4.
The crucial local observation is that a canonical rung lives in the
quotient vertex region, whereas the terminal of a finite inessential old
component lies in the old strict roof.  Hence the source arrow leaves that
component literally fixed.  At a limit, the whole thread with its initial
vertex is eventually this same component, so its genuine thread limit is
again the same path.
-/

noncomputable section

open Cardinal Set Erdos599.DirectedPath

namespace Erdos599
namespace DWeb

universe u v

variable {V : Type u} {G : DWeb V}

namespace DirectedPath

/-- A directed walk is determined by its ordered support list. -/
private theorem Walk.eq_of_support_eq {D : Digraph V} {a b : V}
    (p q : Walk D a b) (h : p.support = q.support) : p = q := by
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

/-- A finite directed path cannot be a proper prefix of another finite
path with the same terminal. -/
private theorem FinitePath.eq_of_prefix_of_finish_eq {D : Digraph V}
    {p q : FinitePath D} (hpq : p.IsPrefixOf q)
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

/-- An extension with the same finite terminal is the original path. -/
private theorem Path.eq_of_extends_of_same_terminal {D : Digraph V}
    {p q : Path D} {x : V}
    (hpq : Erdos599.DirectedPath.Path.Extends p q)
    (hp : p.terminal? = some x) (hq : q.terminal? = some x) : p = q := by
  rcases p with p | r <;> rcases q with q | s
  · congr 1
    apply FinitePath.eq_of_prefix_of_finish_eq hpq
    exact Option.some.inj (hp.trans hq.symm)
  · simp at hq
  · exact hpq.elim
  · simp at hp

end DirectedPath

/-- A walk in the essential quotient whose initial point survives the
quotient has all of its vertices in the quotient vertex region. -/
private theorem essentialQuotientWalk_support_subset_quotientVertexSet
    (T : Set V) {a b : V}
    (p : DirectedPath.Walk (G.quotient T).essentialPart.graph a b)
    (ha : a ∈ G.quotientVertexSet T) :
    ∀ {x}, x ∈ p.support → x ∈ G.quotientVertexSet T := by
  induction p with
  | nil =>
      intro x hx
      simp only [DirectedPath.Walk.support_nil, List.mem_singleton] at hx
      subst x
      exact ha
  | @cons a c b e p ih =>
      intro x hx
      simp only [DirectedPath.Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ha
      · apply ih
        · exact (G.quotient_adj_endpoints
            ((G.quotient T).essentialPart_adj_imp e)).2.1
        · exact hx

/-- A path in the essential quotient whose initial point survives the
quotient has all of its vertices in the quotient vertex region. -/
private theorem essentialQuotientPath_support_subset_quotientVertexSet
    (T : Set V) (p : (G.quotient T).essentialPart.DPath)
    (ha : p.initial ∈ G.quotientVertexSet T) :
    p.support ⊆ G.quotientVertexSet T := by
  rcases p with p | r
  · intro x hx
    exact G.essentialQuotientWalk_support_subset_quotientVertexSet
      T p.walk ha hx
  · rintro x ⟨n, rfl⟩
    cases n with
    | zero => exact ha
    | succ n =>
        exact (G.quotient_adj_endpoints
          ((G.quotient T).essentialPart_adj_imp (r.adj_succ n))).2.1

/-- Every lifted canonical rung avoids the strict roof of the accumulated
terminal frontier.  This is the exact local fact that makes inessential
old components fixed points of the source-arrow operation. -/
theorem disjoint_vertexSet_liftedLadderRungOfState_strictRoof
    (s : G.LadderAccumulationState) :
    Disjoint (G.vertexSet (G.liftedLadderRungOfState s))
      (G.strictRoof (G.terminalFrontier s.1)) := by
  let T := G.terminalFrontier s.1
  let Q := G.quotient T
  apply Set.disjoint_left.2
  rintro x ⟨q, ⟨r, hr, rfl⟩, hxq⟩ hxStrict
  have hrInitial : r.initial ∈ (G.stageWebOf s.1).source :=
    (G.stageWebOf s.1).chosenMaximalWave.property.2.1 ⟨r, hr, rfl⟩
  have hrInitialSurvives : r.initial ∈ G.quotientVertexSet T := by
    have hrQSource : r.initial ∈ Q.source := hrInitial.1
    have hdis : Disjoint (G.essential (T ∪ G.source)) (G.strictRoof T) :=
      G.disjoint_essential_union_strictRoof_left T G.source
    apply fun h ↦ Set.disjoint_left.1 hdis ?_ h
    simpa only [Q, T, G.quotient_source, Set.union_comm] using hrQSource
  have hxSurvives : x ∈ G.quotientVertexSet T := by
    apply G.essentialQuotientPath_support_subset_quotientVertexSet
      T r hrInitialSurvives
    unfold liftLadderStagePathOf at hxq
    rw [G.support_liftQuotientPath] at hxq
    let rQ : (G.quotient
        (G.terminalFrontier s.1)).essentialPart.DPath := r
    have hxq' : x ∈ Path.support
        ((G.quotient (G.terminalFrontier s.1)).liftEssentialPartPath rQ) := hxq
    rw [(G.quotient
      (G.terminalFrontier s.1)).support_liftEssentialPartPath] at hxq'
    exact hxq'
  exact hxSurvives hxStrict

/-- A finite old component whose terminal is strictly roofed is left
literally fixed by the canonical source arrow. -/
theorem arrowPath_eq_of_terminal_mem_strictRoof_liftedRung
    (s : G.LadderAccumulationState) (p : DirectedPath.FinitePath G.graph)
    (hp : (Sum.inl p : G.DPath) ∈ s.1)
    (hfinish : p.finish ∈ G.strictRoof (G.terminalFrontier s.1)) :
    G.arrowPath s.1 (G.liftedLadderRungOfState s) ⟨.inl p, hp⟩ = .inl p := by
  have hnone : ¬ Nonempty
      (G.ArrowCandidate s.1 (G.liftedLadderRungOfState s) p) := by
    rintro ⟨c⟩
    exact Set.disjoint_left.1
      (G.disjoint_vertexSet_liftedLadderRungOfState_strictRoof s)
      ⟨c.path, c.mem_path, c.finish_mem⟩ hfinish
  simp [arrowPath, arrowFinite, hnone]

/-- Any inessential member of the current accumulator is still literally a
member after one canonical successor step. -/
theorem mem_ladderSuccessorState_of_mem_inessentialPaths
    (preferred : Ordinal.{u} → Option V) (o : Ordinal.{u})
    (s : G.LadderAccumulationState) {p : G.DPath}
    (hp : p ∈ G.inessentialPaths s.1) :
    p ∈ (G.ladderSuccessorState preferred o s).1 := by
  classical
  by_cases hs : s.2 = true
  · rw [ladderSuccessorState, dif_pos hs]
    apply Or.inl
    rcases p with p | r
    · have hfinish := G.terminal_mem_strictRoof_of_mem_inessentialPaths
        hp (by rfl : G.terminal? (Sum.inl p : G.DPath) = some p.finish)
      exact ⟨⟨.inl p, hp.1⟩,
        G.arrowPath_eq_of_terminal_mem_strictRoof_liftedRung
          s p hp.1 hfinish⟩
    · exact ⟨⟨.inr r, hp.1⟩, G.arrowPath_ray s.1
        (G.liftedLadderRungOfState s) r hp.1⟩
  · rw [ladderSuccessorState, dif_neg hs]
    exact hp.1

/-- A finite warp member whose terminal is in the strict roof of the
warp's terminal frontier is inessential. -/
theorem mem_inessentialPaths_of_terminal_mem_strictRoof
    {W : Set G.DPath} {p : G.DPath} {x : V}
    (hp : p ∈ W) (hpx : G.terminal? p = some x)
    (hx : x ∈ G.strictRoof (G.terminalFrontier W)) :
    p ∈ G.inessentialPaths W := by
  refine ⟨hp, ?_⟩
  rintro ⟨_hp, y, hpy, hyEssential⟩
  have hyx : y = x := Option.some.inj (hpy.symm.trans hpx)
  exact hx.2 (hyx ▸ hyEssential)

/-- One canonical recursion step preserves every inessential component
literally and preserves its inessentiality. -/
theorem inessentialPaths_ladderSuccessorState
    (hNoEnter : G.NoEdgeEnters G.source)
    (preferred : Ordinal.{u} → Option V) (o : Ordinal.{u})
    (s : G.LadderAccumulationState)
    (hwarp : G.IsWarp s.1)
    (hself : G.vertexSet s.1 ⊆ G.roof (G.terminalFrontier s.1))
    (hsource : G.source ⊆ G.roof (G.terminalFrontier s.1)) :
    G.inessentialPaths s.1 ⊆
      G.inessentialPaths (G.ladderSuccessorState preferred o s).1 := by
  intro p hp
  have hpNext :=
    G.mem_ladderSuccessorState_of_mem_inessentialPaths preferred o s hp
  rcases p with p | r
  · apply G.mem_inessentialPaths_of_terminal_mem_strictRoof hpNext rfl
    exact G.strictRoof_terminalFrontier_subset_ladderSuccessorState
      hNoEnter preferred o s hwarp hself hsource
      (G.terminal_mem_strictRoof_of_mem_inessentialPaths hp rfl)
  · exact G.ray_mem_inessentialPaths hpNext

namespace GrowingWarpChain

variable {I : Type v} [LinearOrder I] [Nonempty I] [IsDirectedOrder I]

/-- If an inessential component occurs literally at every stage of a tail,
then it occurs literally and inessentially in the genuine threadwise direct
limit, provided its old strict roof persists to that limit. -/
theorem mem_inessentialPaths_limitPaths_of_tail
    (C : G.GrowingWarpChain I) (i : I) {p : G.DPath}
    (hp : p ∈ G.inessentialPaths (C.stage i))
    (htail : ∀ j, i ≤ j → p ∈ G.inessentialPaths (C.stage j))
    (hstrict : G.strictRoof (G.terminalFrontier (C.stage i)) ⊆
      G.strictRoof (G.terminalFrontier (C.limitPaths G))) :
    p ∈ G.inessentialPaths (C.limitPaths G) := by
  have hpInitial : p.initial ∈ C.initialUnion :=
    Set.mem_iUnion.2 ⟨i, p, hp.1, rfl⟩
  let a : C.initialUnion := ⟨p.initial, hpInitial⟩
  have hpThread : p ∈ C.thread G a.1 := ⟨i, hp.1, rfl⟩
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
          (htail k hik).1
        have hsInitial : s.initial = a.1 :=
          (G.extends_initial hqs).symm.trans hqInitial
        have hsp : s = (Sum.inl p : G.DPath) :=
          DWeb.IsWarp.eq_of_initial_eq G (C.isWarp k) hsk hpK hsInitial
        refine ⟨.inl p, ⟨k, hpK, rfl⟩, hsp ▸ hqs, rfl⟩
      have hterminal : (C.threadLimit G a).terminal? = some p.finish :=
        DirectedPath.Path.terminal_chainLimit_of_cofinal
          (C.thread G a.1) (C.thread_nonempty G a)
          (C.thread_isChain G a.1) hcofinal
      exact (_root_.Erdos599.DWeb.DirectedPath.Path.eq_of_extends_of_same_terminal
        hpExtends
        rfl hterminal).symm
    · cases hq : C.threadLimit G a with
      | inl q =>
          rw [hq] at hpExtends
          exact hpExtends.elim
      | inr s =>
          rw [hq] at hpExtends
          change r = s at hpExtends
          congr 1
          exact hpExtends.symm
  have hpLimit : p ∈ C.limitPaths G := ⟨a, hlimitEq⟩
  rcases p with p | r
  · apply G.mem_inessentialPaths_of_terminal_mem_strictRoof hpLimit rfl
    exact hstrict
      (G.terminal_mem_strictRoof_of_mem_inessentialPaths hp rfl)
  · exact G.ray_mem_inessentialPaths hpLimit

end GrowingWarpChain

namespace KappaLadder

open Ladder

variable {κ : Cardinal.{u}}

/-- Source Lemma 7.4 at one successor: every current inessential path is
still an inessential path of the canonical successor. -/
theorem canonicalLadder_currentInessentialPersists
    (preferred : Stage κ → Option V)
    (hNoEnter : G.NoEdgeEnters G.source) :
    (canonicalLadder G κ preferred).CurrentInessentialPersists := by
  intro a p hp
  let s := G.canonicalLadderState κ preferred (Stage.toExtended a)
  change p ∈ G.inessentialPaths
    (G.canonicalLadderAccumulated κ preferred (Stage.succExtended a))
  rw [canonicalLadderAccumulated, canonicalLadderState,
    G.ladderAccumulatedState_succ]
  have hinv := canonicalRecursionInvariant_all hNoEnter
    (extendLadderPreference κ preferred) a.1
  exact G.inessentialPaths_ladderSuccessorState hNoEnter
    (extendLadderPreference κ preferred) a.1 s
      hinv.warp hinv.selfRoof hinv.sourceRoof hp

/-- Inessential components of the canonical accumulator persist literally
through all later successor and genuine direct-limit stages. -/
theorem canonicalAccumulated_inessential_mono
    (preferred : Stage κ → Option V)
    (hNoEnter : G.NoEdgeEnters G.source)
    {a b : ExtendedStage κ} (hab : a ≤ b) :
    G.inessentialPaths (G.canonicalLadderAccumulated κ preferred a) ⊆
      G.inessentialPaths (G.canonicalLadderAccumulated κ preferred b) := by
  let step := G.ladderSuccessorState
    (extendLadderPreference κ preferred)
  have hinv (o : Ordinal.{u}) :
      CanonicalRecursionInvariant (G := G) step o :=
    canonicalRecursionInvariant_all hNoEnter
      (extendLadderPreference κ preferred) o
  have hmain : ∀ o : Ordinal.{u}, ∀ ho : o ≤ κ.ord,
      ∀ c : Ordinal.{u}, c ≤ o →
        G.inessentialPaths (G.ladderAccumulatedStateAux step c).1 ⊆
          G.inessentialPaths (G.ladderAccumulatedStateAux step o).1 := by
    intro o
    induction o using Ordinal.limitRecOn with
    | zero =>
        intro _ho c hc
        have hc0 : c = 0 := le_antisymm hc bot_le
        subst c
        exact Set.Subset.rfl
    | add_one o ih =>
        intro ho c hc p hp
        rcases hc.lt_or_eq with hc | rfl
        · have hco : c ≤ o := (Order.lt_add_one_iff).1 hc
          have hoκ : o ≤ κ.ord :=
            (show o ≤ o + 1 by
              rw [← Order.succ_eq_add_one]
              exact Order.le_succ o).trans ho
          have hpO := ih hoκ c hco hp
          have hstep := G.inessentialPaths_ladderSuccessorState hNoEnter
            (extendLadderPreference κ preferred) o
            (G.ladderAccumulatedStateAux step o)
            (hinv o).warp (hinv o).selfRoof (hinv o).sourceRoof hpO
          change p ∈ G.inessentialPaths
            (G.ladderAccumulatedStateAux step (o + 1)).1
          rw [ladderAccumulatedStateAux, Ordinal.limitRecOn_add_one]
          exact hstep
        · exact hp
    | limit o hoLimit ih =>
        intro hoκ c hc p hp
        rcases hc.lt_or_eq with hc | rfl
        · have ihStructural : ∀ d, d < o →
              G.LadderRecursionInvariant step d := by
            intro d hd
            exact ⟨(hinv d).warp, (hinv d).grows⟩
          let hchain : G.HasMatchingLadderChain o
              (fun d _hd ↦ G.ladderAccumulatedStateAux step d) :=
            G.hasMatchingLadderChain_of_invariants step o ihStructural
          let C : G.GrowingWarpChain (Set.Iio o) := Classical.choose hchain
          let : Nonempty (Set.Iio o) := hoLimit.nonempty_Iio.to_subtype
          have hstage (d : Set.Iio o) :
              C.stage d = (G.ladderAccumulatedStateAux step d.1).1 :=
            Classical.choose_spec hchain d
          have hstate :
              (G.ladderAccumulatedStateAux step o).1 = C.limitPaths G := by
            rw [ladderAccumulatedStateAux,
              Ordinal.limitRecOn_limit _ _ _ _ hoLimit]
            simp only [ladderLimitState]
            split
            · rfl
            · rename_i h
              exact (h hchain).elim
          let ci : Set.Iio o := ⟨c, hc⟩
          have hpCi : p ∈ G.inessentialPaths (C.stage ci) := by
            rw [hstage ci]
            exact hp
          have hpTail : ∀ d, ci ≤ d →
              p ∈ G.inessentialPaths (C.stage d) := by
            intro d hcd
            rw [hstage d]
            apply ih d.1 d.2 (d.2.le.trans hoκ) c hcd
            exact hp
          have hstrict :
              G.strictRoof (G.terminalFrontier (C.stage ci)) ⊆
                G.strictRoof (G.terminalFrontier (C.limitPaths G)) := by
            rw [hstage ci, ← hstate]
            let ce : ExtendedStage κ := ⟨c, hc.le.trans hoκ⟩
            let oe : ExtendedStage κ := ⟨o, hoκ⟩
            have hs := canonicalAccumulated_strictRoof_mono
              preferred hNoEnter (show ce ≤ oe from hc.le)
            simpa only [canonicalLadderAccumulated, canonicalLadderState,
              ladderAccumulatedState, ce, oe, step] using hs
          rw [hstate]
          exact C.mem_inessentialPaths_limitPaths_of_tail
            ci hpCi hpTail hstrict
        · exact hp
  change G.inessentialPaths
      (G.ladderAccumulatedStateAux step a.1).1 ⊆
    G.inessentialPaths (G.ladderAccumulatedStateAux step b.1).1
  exact hmain b.1 b.2 a.1 hab

/-- Source Lemma 7.4 with the exact successor-normalized bookkeeping:
a path recorded at `a` belongs to `IE(Y_b)` at every `b ≥ a+1`. -/
theorem canonicalLadder_recordedPathsPersist
    (preferred : Stage κ → Option V)
    (hNoEnter : G.NoEdgeEnters G.source) :
    (canonicalLadder G κ preferred).RecordedPathsPersist := by
  let L := canonicalLadder G κ preferred
  have hvalid : L.HasValidBookkeeping :=
    (G.canonicalLadderCore κ preferred).withValidBookkeeping_hasValidBookkeeping
  intro a p hp b hab
  have hpNext : p ∈ G.inessentialPaths (L.successorWarp a) :=
    (L.bookkeeping.chosen_mem_available hvalid hp).1
  exact canonicalAccumulated_inessential_mono preferred hNoEnter hab hpNext

end KappaLadder
end DWeb
end Erdos599
