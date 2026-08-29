/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingSuccessorRoofTransport

/-!
# First-target-normalized chronology for the grounding auxiliary web

The decoded route of a Lambda path propagates membership in a successor
ladder roof.  A backward ladder edge turns roof membership into strict-roof
membership, while a forward original edge only preserves the (closed) roof.
Thus the only potentially problematic pattern is two consecutive forward steps
through an internal target marker.  Cutting a Lambda path at its first target
hit removes exactly that pattern.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

namespace PopularAuxiliary

open Alternating DirectedPath

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}

namespace Input

variable (L : Input Gamma I)

/-- A finite Lambda path reaches the Lambda target for the first time at its
terminal vertex. -/
def IsTargetPure (p : FinitePath L.lambda.graph) : Prop :=
  p.support ∩ L.lambda.target ⊆ {p.finish}

/-- Between consecutive forward signed steps, strictness is recovered either
because their common endpoint is off the ladder, or because the first step
is a degenerate selected loop and hence did not move at all. -/
def ForwardPairsRecoverStrict (L : Input Gamma I) :
    List (SignedEdge V) → Prop
  | s :: t :: q =>
      (s.direction = .forward → t.direction = .forward →
        s.exit ∈ L.offLadder ∨ s.entry = s.exit) ∧
      ForwardPairsRecoverStrict L (t :: q)
  | _ => True

@[simp]
theorem forwardPairsRecoverStrict_nil :
    L.ForwardPairsRecoverStrict [] := by
  trivial

@[simp]
theorem forwardPairsRecoverStrict_singleton (s : SignedEdge V) :
    L.ForwardPairsRecoverStrict [s] := by
  trivial

/-- A backward step may always be prepended: the new adjacent pair cannot
be a forward--forward pair. -/
theorem ForwardPairsRecoverStrict.cons_backward
    {q : List (SignedEdge V)} (h : L.ForwardPairsRecoverStrict q)
    (s : SignedEdge V) (hs : s.direction = .backward) :
    L.ForwardPairsRecoverStrict (s :: q) := by
  cases q with
  | nil => trivial
  | cons t rest =>
      change
        (s.direction = .forward → t.direction = .forward →
          s.exit ∈ L.offLadder ∨ s.entry = s.exit) ∧
          L.ForwardPairsRecoverStrict (t :: rest)
      exact ⟨fun hf _ ↦ by simp [hs] at hf, h⟩

/-- A forward step may be prepended when its boundary with the old list
recovers strictness. -/
theorem ForwardPairsRecoverStrict.cons_forward
    {q : List (SignedEdge V)} (h : L.ForwardPairsRecoverStrict q)
    (s : SignedEdge V) (_hs : s.direction = .forward)
    (hboundary : ∀ t, q.head? = some t → t.direction = .forward →
      s.exit ∈ L.offLadder ∨ s.entry = s.exit) :
    L.ForwardPairsRecoverStrict (s :: q) := by
  cases hq : q with
  | nil => trivial
  | cons t rest =>
      change
        (s.direction = .forward → t.direction = .forward →
          s.exit ∈ L.offLadder ∨ s.entry = s.exit) ∧
          L.ForwardPairsRecoverStrict (t :: rest)
      refine ⟨fun _ ht ↦ hboundary t ?_ ht, ?_⟩
      · simp [hq]
      · simpa only [hq] using h

theorem RunsFromTo.terminal_mem_roof_of_forwardPairsRecoverStrict
    {x y : V} {q : List (SignedEdge V)}
    (h_run : RunsFromTo x y q)
    {R Rs : Set V}
    (hRsR : Rs ⊆ R)
    (hxR : x ∈ R)
    (hxReady : ∀ s, q.head? = some s → s.direction = .forward → x ∈ Rs)
    (hback : ∀ s ∈ q, s.direction = .backward → s.entry ∈ R → s.exit ∈ Rs)
    (hforward : ∀ s ∈ q, s.direction = .forward → s.entry ∈ Rs → s.exit ∈ R)
    (hoff : ∀ z, z ∈ R → z ∈ L.offLadder → z ∈ Rs)
    (hpairs : L.ForwardPairsRecoverStrict q) :
    y ∈ R := by
  induction h_run with
  | nil z => exact hxR
  | @cons s z q tail ih =>
      have hsMem : s ∈ s :: q := by simp
      have hsExitR : s.exit ∈ R := by
        cases hsd : s.direction with
        | backward =>
            exact hRsR (hback s hsMem hsd hxR)
        | forward =>
            apply hforward s hsMem hsd
            simpa [hsd] using hxReady
      have htailReady : ∀ t, q.head? = some t →
          t.direction = .forward → s.exit ∈ Rs := by
        intro t htHead htForward
        cases htail : q with
        | nil => simp [htail] at htHead
        | cons t₀ rest =>
            simp only [htail, List.head?_cons, Option.some.injEq] at htHead
            subst t
            cases hsd : s.direction with
            | backward =>
                exact hback s hsMem hsd hxR
            | forward =>
                have hsSafe : s.exit ∈ L.offLadder ∨
                    s.entry = s.exit := by
                  rw [htail] at hpairs
                  change
                    (s.direction = .forward → t₀.direction = .forward →
                      s.exit ∈ L.offLadder ∨ s.entry = s.exit) ∧
                      L.ForwardPairsRecoverStrict (t₀ :: rest) at hpairs
                  exact hpairs.1 hsd htForward
                rcases hsSafe with hsOff | hsEq
                · exact hoff s.exit hsExitR hsOff
                · rw [← hsEq]
                  exact hxReady s rfl hsd
      refine ih hsExitR htailReady ?_ ?_ ?_
      · intro t ht htd htR
        exact hback t (List.mem_cons_of_mem s ht) htd htR
      · intro t ht htd htR
        exact hforward t (List.mem_cons_of_mem s ht) htd htR
      · cases hq : q with
        | nil => trivial
        | cons t rest =>
            rw [hq] at hpairs
            change
              (s.direction = .forward → t.direction = .forward →
                s.exit ∈ L.offLadder ∨ s.entry = s.exit) ∧
                L.ForwardPairsRecoverStrict (t :: rest) at hpairs
            exact hpairs.2

/-- If a selected connector is followed by another decoded signed step,
then its endpoint is either off the ladder or the connector was a loop.
The only other possible endpoint is an old target marker; target purity and
the outgoing auxiliary edge rule that case out. -/
theorem connector_boundary_recovers_strict
    (p : FinitePath L.lambda.graph) (hpure : L.IsTargetPure p)
    {a b : L.LV} (hab : (a, b) ∈ p.edgeSet)
    {e : V × V} (he : L.chosenConnector? a b = some e)
    {z : L.LV} (w : Walk L.lambda.graph b z)
    (hw : w.edgeSet ⊆ p.edgeSet)
    (t : SignedEdge V)
    (hhead : (L.decodeWalkSteps w).head? = some t)
    (htForward : t.direction = .forward) :
    e.2 ∈ L.offLadder ∨ e.1 = e.2 := by
  have hAdj : L.lambda.graph.Adj a b := p.edgeSet_subset_adj hab
  have hconnector := L.chosenConnector?_eq_some he
  cases b with
  | edge u v =>
      have hheadEdge : ∀ {z : L.LV}
          (q : Walk L.lambda.graph (.edge u v) z),
          (L.decodeWalkSteps q).head? =
            some (SignedEdge.backward (u, v)) := by
        intro z q
        cases q <;> simp [decodeWalkSteps, gadgetSteps]
      have ht : t = SignedEdge.backward (u, v) :=
        Option.some.inj (hhead.symm.trans (hheadEdge w))
      subst t
      simp at htForward
  | proxy i =>
      have hnone : (none : Option V) = some e.2 := by
        simpa only [gadgetEntry_proxy] using hconnector.2.1
      cases hnone
  | old x =>
      have heExit : e.2 = x := by
        exact (Option.some.inj hconnector.2.1).symm
      have hxNotTarget : x ∉ L.targetMarkers := by
        intro hxTarget
        have hOldTarget : (LambdaVertex.old x : L.LV) ∈ L.lambda.target :=
          (L.mem_lambda_target_old x).2 hxTarget
        have hOldFinish : (LambdaVertex.old x : L.LV) = p.finish :=
          Set.mem_singleton_iff.1 <| hpure
            ⟨(p.edgeSet_subset_support_prod hab).2, hOldTarget⟩
        have hne : L.decodeWalkSteps w ≠ [] := by
          intro hnil
          simp [hnil] at hhead
        have hexistsFirst : ∀ {z : L.LV}
            (q : Walk L.lambda.graph (.old x) z),
            L.decodeWalkSteps q ≠ [] →
            ∃ (c : L.LV) (hxc : L.lambda.graph.Adj (.old x) c)
                (tail : Walk L.lambda.graph c z),
              q = Walk.cons hxc tail := by
          intro z q hq
          cases q with
          | nil => simp [decodeWalkSteps, gadgetSteps] at hq
          | @cons _ c _ hxc tail => exact ⟨c, hxc, tail, rfl⟩
        obtain ⟨c, hxc, tail, hwEq⟩ := hexistsFirst w hne
        have hbcWalk : ((LambdaVertex.old x : L.LV), c) ∈
            w.edgeSet := by rw [hwEq]; simp
        have hbcPath : ((LambdaVertex.old x : L.LV), c) ∈
            p.edgeSet := hw hbcWalk
        exact (_root_.Erdos599.Alternating.FinitePath.source_ne_finish_of_mem_edgeSet
          p hbcPath) hOldFinish
      rw [heExit]
      cases a with
      | old z =>
          have hxClass := (L.lambda_adj_old_old z x).1 hAdj |>.2.1
          exact Or.inl (hxClass.resolve_right hxNotTarget)
      | proxy i =>
          have hxClass := (L.lambda_adj_proxy_old i x).1 hAdj |>.1
          exact Or.inl (hxClass.resolve_right hxNotTarget)
      | edge u v =>
          have hclass := (L.lambda_adj_edge_old u v x).1 hAdj |>.2
          rcases hclass with hux | hxClass
          · apply Or.inr
            have heEntry : e.1 = u := by
              rcases hconnector.1 with hExit | hProxy
              · exact (Option.some.inj hExit).symm
              · rcases hProxy with ⟨i, hi, _⟩
                cases hi
            exact heEntry.trans hux
          · exact Or.inl (hxClass.1.resolve_right hxNotTarget)

/-- The deterministic decoder of a target-pure path has no forbidden pair of
successive forward steps. -/
theorem decodeWalkSteps_forwardPairsRecoverStrict
    (p : FinitePath L.lambda.graph) (hpure : L.IsTargetPure p) :
    L.ForwardPairsRecoverStrict (L.decodeWalkSteps p.walk) := by
  have aux : ∀ {a z : L.LV} (w : Walk L.lambda.graph a z),
      w.edgeSet ⊆ p.edgeSet →
      L.ForwardPairsRecoverStrict (L.decodeWalkSteps w) := by
    intro a z w
    induction w with
    | @nil x =>
        intro _
        cases x <;> simp [decodeWalkSteps, gadgetSteps]
    | @cons a b _ hab tail ih =>
        intro hw
        have habPath : (a, b) ∈ p.edgeSet := hw (by simp)
        have htail : tail.edgeSet ⊆ p.edgeSet := by
          intro e he
          exact hw (by simp [he])
        have hrest := ih htail
        cases hopt : L.chosenConnector? a b with
        | none =>
            cases a with
            | old x =>
                simpa [decodeWalkSteps, gadgetSteps, connectorSteps, hopt]
                  using hrest
            | proxy i =>
                simpa [decodeWalkSteps, gadgetSteps, connectorSteps, hopt]
                  using hrest
            | edge u v =>
                have hprepend := ForwardPairsRecoverStrict.cons_backward L hrest
                  (SignedEdge.backward (u, v)) rfl
                simpa [decodeWalkSteps, gadgetSteps, connectorSteps, hopt]
                  using hprepend
        | some e =>
            have hforward := ForwardPairsRecoverStrict.cons_forward L hrest
              (SignedEdge.forward e) rfl (by
                intro t htHead htForward
                exact L.connector_boundary_recovers_strict p hpure
                  habPath hopt tail htail t htHead htForward)
            cases a with
            | old x =>
                simpa [decodeWalkSteps, gadgetSteps, connectorSteps, hopt]
                  using hforward
            | proxy i =>
                simpa [decodeWalkSteps, gadgetSteps, connectorSteps, hopt]
                  using hforward
            | edge u v =>
                have hprepend := ForwardPairsRecoverStrict.cons_backward L hforward
                  (SignedEdge.backward (u, v)) rfl
                simpa [decodeWalkSteps, gadgetSteps, connectorSteps, hopt]
                  using hprepend
  exact aux p.walk Set.Subset.rfl

/-- Cutting at the first target hit produces a target-pure path. -/
theorem firstHit_target_isTargetPure
    (p : FinitePath L.lambda.graph)
    (hmeet : p.walk.Meets L.lambda.target) :
    L.IsTargetPure (p.firstHit L.lambda.target hmeet) := by
  intro x hx
  apply Set.mem_singleton_iff.2
  by_contra hxf
  have hxlast : x ≠
      (p.firstHit L.lambda.target hmeet).walk.support.getLast
        (p.firstHit L.lambda.target hmeet).walk.support_ne_nil := by
    intro h
    apply hxf
    exact h.trans
      (p.firstHit L.lambda.target hmeet).walk.getLast_support
  have hxdrop : x ∈
      (p.firstHit L.lambda.target hmeet).walk.support.dropLast :=
    List.mem_dropLast_of_mem_of_ne_getLast hx.1 hxlast
  exact (p.firstHit_no_mem_before L.lambda.target hmeet hxdrop) hx.2

/-- Every first-hit prefix of a target-pure path is target-pure.  If the
prefix contains the old terminal, nodup and the prefix relation force it to
be the whole path. -/
theorem IsTargetPure.firstHit
    {p : FinitePath L.lambda.graph} (hpure : L.IsTargetPure p)
    (C : Set L.LV) (hmeet : p.walk.Meets C) :
    L.IsTargetPure (p.firstHit C hmeet) := by
  intro z hz
  have hzFinish : z = p.finish :=
    Set.mem_singleton_iff.1 (hpure
      ⟨p.firstHit_support_subset C hmeet hz.1, hz.2⟩)
  have hprefix : (p.firstHit C hmeet).walk.support <+:
      p.walk.support :=
    (p.walk.firstHit C hmeet).support_prefix
  have hlastMem : p.walk.support.getLast p.walk.support_ne_nil ∈
      (p.firstHit C hmeet).walk.support := by
    rw [p.walk.getLast_support]
    exact hzFinish ▸ hz.1
  have hwhole : (p.firstHit C hmeet).walk.support = p.walk.support :=
    List.Nodup.eq_of_getLast_mem_of_prefix hprefix hlastMem p.isPath
  apply Set.mem_singleton_iff.2
  calc
    z = p.finish := hzFinish
    _ = p.walk.support.getLast p.walk.support_ne_nil :=
      p.walk.getLast_support.symm
    _ = (p.firstHit C hmeet).walk.support.getLast
        (p.firstHit C hmeet).walk.support_ne_nil :=
      (List.getLast_congr p.walk.support_ne_nil
        (p.firstHit C hmeet).walk.support_ne_nil hwhole.symm)
    _ = (p.firstHit C hmeet).finish :=
      (p.firstHit C hmeet).walk.getLast_support

end Input
end PopularAuxiliary

namespace PopularAuxiliary.Input

universe w

open _root_.Erdos599.DirectedPath

variable {W J : Type w} {Delta : DWeb W}
variable {M : Input Delta J}

/-- A path in a local request fan is target-pure.  Its non-apex vertices
lie in the strict roof of the popular cut, while no target vertex can lie
in a strict roof; the only remaining possible target is the common apex,
which is the path's terminal vertex. -/
theorem requestFan_path_isTargetPure
    {kappa : Cardinal.{w}}
    {U : Popular.KappaIndexed M.lambda kappa}
    (S : Popular.PopularSeparator U)
    (r : PopularGroundingBridge.Request M S.cut)
    {p : FinitePath M.lambda.graph}
    (hp : p ∈ (PopularGroundingBridge.requestFan S r).paths) :
    M.IsTargetPure p := by
  have htargetNotStrict : ∀ {z : M.LV}, z ∈ M.lambda.target →
      z ∉ M.lambda.strictRoof S.cut := by
    intro z hzTarget hzStrict
    have hzCut : z ∈ S.cut := by
      let q : FinitePath M.lambda.graph :=
        FinitePath.trivial M.lambda.graph z
      obtain ⟨x, hxq, hxCut⟩ := hzStrict.1 q ⟨rfl, hzTarget⟩
      have hxz : x = z := by
        simpa [q, FinitePath.trivial, FinitePath.support] using hxq
      exact hxz ▸ hxCut
    apply hzStrict.2
    rw [M.lambda.mem_essential_iff]
    refine ⟨hzCut, (M.lambda.not_mem_roof_iff (S.cut \ {z}) z).2 ?_⟩
    let q : FinitePath M.lambda.graph :=
      FinitePath.trivial M.lambda.graph z
    refine ⟨q, ⟨rfl, hzTarget⟩, ?_⟩
    apply Set.disjoint_left.2
    intro x hxq hxDiff
    have hxz : x = z := by
      simpa [q, FinitePath.trivial, FinitePath.support] using hxq
    exact hxDiff.2 hxz
  intro z hz
  rcases PopularGroundingBridge.requestFan_support_subset S r hp hz.1 with
      hzStrict | hzApex
  · exact (htargetNotStrict hz.2 hzStrict).elim
  · have hfinish :=
      (PopularGroundingBridge.requestFan S r).ends_in_join hp
    exact Set.mem_singleton_iff.2
      ((Set.mem_singleton_iff.1 hzApex).trans
        (Set.mem_singleton_iff.1 hfinish).symm)

end PopularAuxiliary.Input

namespace DWeb

open _root_.Erdos599.DirectedPath Ladder

namespace KappaLadder

universe w

variable {W : Type w} {Delta : DWeb W} {kappa : Cardinal.{w}}

/-- The core successor-roof transport for a target-pure decoded run. -/
theorem IsLegal.targetPure_run_terminal_mem_roof
    {K : Delta.KappaLadder kappa} (hlegal : K.IsLegal)
    (c : Stage kappa)
    (p : FinitePath (K.popularAuxiliaryInput hlegal).lambda.graph)
    (hs : p.start ∈ (K.popularAuxiliaryInput hlegal).lambda.source)
    (hpure : (K.popularAuxiliaryInput hlegal).IsTargetPure p)
    {x y : W}
    (hrun : PopularAuxiliary.Input.RunsFromTo x y
      ((K.popularAuxiliaryInput hlegal).decodeWalkSteps p.walk))
    (hx : x ∈ Delta.strictRoof (K.frontier c)) :
    y ∈ Delta.roof (K.frontier c) := by
  let I := K.popularAuxiliaryInput hlegal
  apply PopularAuxiliary.Input.RunsFromTo.terminal_mem_roof_of_forwardPairsRecoverStrict
      (L := I) hrun
      (R := Delta.roof (K.frontier c))
      (Rs := Delta.strictRoof (K.frontier c))
  · exact fun _ hz ↦ hz.1
  · exact hx.1
  · intro _ _ _
    exact hx
  · intro s hsmem hback hsEntry
    have hedge : s.edge ∈ I.familyEdges :=
      I.decodeWalkSteps_backward_on_ladder p hs hsmem hback
    have htail := hlegal.familyEdge_tail_mem_strictRoof_frontier
      c hedge (by simpa [PopularAuxiliary.Input.SignedEdge.entry, hback]
        using hsEntry)
    simpa [PopularAuxiliary.Input.SignedEdge.exit, hback] using htail
  · intro s hsmem hforward hsEntry
    have hadj : Delta.graph.Adj s.edge.1 s.edge.2 :=
      I.decodeWalkSteps_valid p hs hsmem
    have hhead := hlegal.edge_head_mem_roof_frontier_of_tail_mem_strictRoof
      c hadj (by simpa [PopularAuxiliary.Input.SignedEdge.entry, hforward]
        using hsEntry)
    simpa [PopularAuxiliary.Input.SignedEdge.exit, hforward] using hhead
  · intro z hzRoof hzOff
    exact hlegal.mem_strictRoof_frontier_of_mem_roof_of_mem_offLadder
      c hzRoof hzOff
  · exact I.decodeWalkSteps_forwardPairsRecoverStrict p hpure

/-- Target-pure paths beginning at a selected finite terminal transport
every old endpoint into the successor roof of that terminal's stage. -/
theorem IsLegal.targetPure_finite_successorRoofTransport
    {K : Delta.KappaLadder kappa} (hlegal : K.IsLegal)
    (q : FinitePath (K.popularAuxiliaryInput hlegal).lambda.graph)
    (hs : q.start ∈ (K.popularAuxiliaryInput hlegal).lambda.source)
    (hpure : (K.popularAuxiliaryInput hlegal).IsTargetPure q)
    (x : K.finiteTerminalSet) (y : W)
    (hqx : q.start = .old x.1) (hqy : q.finish = .old y) :
    y ∈ Delta.roof
      (K.frontier (K.successorStage hlegal (K.finiteTerminalStage x))) := by
  let I := K.popularAuxiliaryInput hlegal
  have hrun : PopularAuxiliary.Input.RunsFromTo x.1 y
      (I.decodeWalkSteps q.walk) :=
    I.decodeWalkSteps_runs_from_entry q.walk (by rw [hqx]; rfl)
      (by rw [hqy]; rfl)
  exact hlegal.targetPure_run_terminal_mem_roof
    (K.successorStage hlegal (K.finiteTerminalStage x)) q hs hpure hrun
    (K.finiteTerminal_mem_strictRoof_successorFrontier hlegal x)

/-- Target-pure paths beginning at a proxy transport every old endpoint
into the successor roof of the represented grounded ray's record stage. -/
theorem IsLegal.targetPure_proxy_successorRoofTransport
    {K : Delta.KappaLadder kappa} (hlegal : K.IsLegal)
    (q : FinitePath (K.popularAuxiliaryInput hlegal).lambda.graph)
    (hs : q.start ∈ (K.popularAuxiliaryInput hlegal).lambda.source)
    (hpure : (K.popularAuxiliaryInput hlegal).IsTargetPure q)
    (i : K.groundedInfiniteRecords) (y : W)
    (hqi : q.start = .proxy i) (hqy : q.finish = .old y) :
    y ∈ Delta.roof
      (K.frontier
        (K.successorStage hlegal (K.groundedInfiniteStage i))) := by
  let I := K.popularAuxiliaryInput hlegal
  obtain ⟨z, hzProxy, hrun⟩ :=
    I.decodeWalkSteps_runs_from_eq_proxy q.walk hqi (by
      rw [hqy]
      rfl)
  exact hlegal.targetPure_run_terminal_mem_roof
    (K.successorStage hlegal (K.groundedInfiniteStage i)) q hs hpure hrun
    (K.popularAuxiliary_proxyPath_support_subset_strictRoof_successorFrontier
      hlegal i hzProxy)

/-- Gadget-endpoint form of finite-source successor-roof transport.  It is
needed for Assertion 8.19 because an off-apex contact may be an edge gadget,
whose decoded exit is the tail of the represented ladder edge. -/
theorem IsLegal.targetPure_finite_gadgetExit_successorRoofTransport
    {K : Delta.KappaLadder kappa} (hlegal : K.IsLegal)
    (q : FinitePath (K.popularAuxiliaryInput hlegal).lambda.graph)
    (hs : q.start ∈ (K.popularAuxiliaryInput hlegal).lambda.source)
    (hpure : (K.popularAuxiliaryInput hlegal).IsTargetPure q)
    (x : K.finiteTerminalSet)
    (z : (K.popularAuxiliaryInput hlegal).LV) (y : W)
    (hqx : q.start = .old x.1) (hqz : q.finish = z)
    (hzexit : (K.popularAuxiliaryInput hlegal).gadgetExit z = some y) :
    y ∈ Delta.roof
      (K.frontier (K.successorStage hlegal (K.finiteTerminalStage x))) := by
  let I := K.popularAuxiliaryInput hlegal
  have hrun : PopularAuxiliary.Input.RunsFromTo x.1 y
      (I.decodeWalkSteps q.walk) :=
    I.decodeWalkSteps_runs_from_entry q.walk (by rw [hqx]; rfl)
      (by rw [hqz]; exact hzexit)
  exact hlegal.targetPure_run_terminal_mem_roof
    (K.successorStage hlegal (K.finiteTerminalStage x)) q hs hpure hrun
    (K.finiteTerminal_mem_strictRoof_successorFrontier hlegal x)

/-- Gadget-endpoint form of proxy-source successor-roof transport. -/
theorem IsLegal.targetPure_proxy_gadgetExit_successorRoofTransport
    {K : Delta.KappaLadder kappa} (hlegal : K.IsLegal)
    (q : FinitePath (K.popularAuxiliaryInput hlegal).lambda.graph)
    (hs : q.start ∈ (K.popularAuxiliaryInput hlegal).lambda.source)
    (hpure : (K.popularAuxiliaryInput hlegal).IsTargetPure q)
    (i : K.groundedInfiniteRecords)
    (z : (K.popularAuxiliaryInput hlegal).LV) (y : W)
    (hqi : q.start = .proxy i) (hqz : q.finish = z)
    (hzexit : (K.popularAuxiliaryInput hlegal).gadgetExit z = some y) :
    y ∈ Delta.roof
      (K.frontier
        (K.successorStage hlegal (K.groundedInfiniteStage i))) := by
  let I := K.popularAuxiliaryInput hlegal
  obtain ⟨w, hwProxy, hrun⟩ :=
    I.decodeWalkSteps_runs_from_eq_proxy q.walk hqi (by
      rw [hqz]
      exact hzexit)
  exact hlegal.targetPure_run_terminal_mem_roof
    (K.successorStage hlegal (K.groundedInfiniteStage i)) q hs hpure hrun
    (K.popularAuxiliary_proxyPath_support_subset_strictRoof_successorFrontier
      hlegal i hwProxy)

/-- Exact weak source--target chronology for one target-pure auxiliary
path. -/
theorem targetPure_auxiliaryNonincreasing
    (K : Delta.KappaLadder kappa) (hK : K.IsKappaHindrance)
    (q : FinitePath (K.popularAuxiliaryInput hK.legal).lambda.graph)
    (hs : q.start ∈ (K.popularAuxiliaryInput hK.legal).lambda.source)
    (ht : q.finish ∈ (K.popularAuxiliaryInput hK.legal).lambda.target)
    (hpure : (K.popularAuxiliaryInput hK.legal).IsTargetPure q) :
    (K.popularAuxiliaryIndexed hK).g ⟨q.finish, ht⟩ ≤
      (K.popularAuxiliaryIndexed hK).f ⟨q.start, hs⟩ := by
  let I := K.popularAuxiliaryInput hK.legal
  obtain ⟨y, hyTarget, hqy⟩ := I.finish_of_mem_lambda_target q ht
  have hyMarker : y ∈ K.markerSet := hyTarget.1
  let b : Stage kappa := K.markerStage ⟨y, hyMarker⟩
  have hmarker : K.marker b = some y := K.markerStage_spec ⟨y, hyMarker⟩
  have hyNotRoof : y ∉ Delta.roof (K.frontier b) :=
    K.marker_not_mem_roof_frontier hK.legal hmarker
  rcases I.start_of_mem_lambda_source q hs with
      ⟨x, hxSource, hqx⟩ | ⟨i, hqi⟩
  · let xs : K.finiteTerminalSet :=
      ⟨x, K.groundedFiniteTerminalSet_subset_finiteTerminalSet hxSource⟩
    let a : Stage kappa := K.finiteTerminalStage xs
    have hyRoofSucc : y ∈ Delta.roof
        (K.frontier (K.successorStage hK.legal a)) :=
      hK.legal.targetPure_finite_successorRoofTransport
        q hs hpure xs y hqx hqy
    have hba : b ≤ a := by
      by_contra hnot
      have hab : a < b := lt_of_not_ge hnot
      have hsuccle : K.successorStage hK.legal a ≤ b :=
        (K.successorStage_le_iff_lt hK.legal).2 hab
      apply hyNotRoof
      rcases hsuccle.lt_or_eq with hlt | heq
      · exact Delta.roof_cut (hK.legal.frontierChronology hlt) hyRoofSucc
      · rwa [heq] at hyRoofSucc
    have htEq : (⟨q.finish, ht⟩ : I.lambda.target) =
        ⟨.old y, (I.mem_lambda_target_old y).2 hyTarget⟩ :=
      Subtype.ext hqy
    have hsEq : (⟨q.start, hs⟩ : I.lambda.source) =
        ⟨.old x, (I.mem_lambda_source_old x).2 hxSource⟩ :=
      Subtype.ext hqx
    rw [htEq, hsEq]
    exact hba
  · let a : Stage kappa := K.groundedInfiniteStage i
    have hyRoofSucc : y ∈ Delta.roof
        (K.frontier (K.successorStage hK.legal a)) :=
      hK.legal.targetPure_proxy_successorRoofTransport
        q hs hpure i y hqi hqy
    have hba : b ≤ a := by
      by_contra hnot
      have hab : a < b := lt_of_not_ge hnot
      have hsuccle : K.successorStage hK.legal a ≤ b :=
        (K.successorStage_le_iff_lt hK.legal).2 hab
      apply hyNotRoof
      rcases hsuccle.lt_or_eq with hlt | heq
      · exact Delta.roof_cut (hK.legal.frontierChronology hlt) hyRoofSucc
      · rwa [heq] at hyRoofSucc
    have htEq : (⟨q.finish, ht⟩ : I.lambda.target) =
        ⟨.old y, (I.mem_lambda_target_old y).2 hyTarget⟩ :=
      Subtype.ext hqy
    have hsEq : (⟨q.start, hs⟩ : I.lambda.source) =
        ⟨.proxy i, I.mem_lambda_source_proxy i⟩ :=
      Subtype.ext hqi
    rw [htEq, hsEq]
    exact hba

/-- Every hanging collision contact selected in Assertion 8.19 lies in the
successor roof of the auxiliary source index. -/
theorem assertion819CollisionOwner_contact_mem_successorRoof
    (K : Delta.KappaLadder kappa) (hK : K.IsKappaHindrance)
    (S : Popular.PopularSeparator (K.popularAuxiliaryIndexed hK))
    (r : PopularGroundingBridge.Request
      (K.popularAuxiliaryInput hK.legal) S.cut)
    (a : Stationary.Below kappa)
    (d : K.Assertion819CollisionOwner hK S r a) :
    d.contact ∈ Delta.roof
      (K.frontier (K.successorStage hK.legal a)) := by
  let I := K.popularAuxiliaryInput hK.legal
  let U := K.popularAuxiliaryIndexed hK
  have hpFan : d.path ∈
      (PopularGroundingBridge.requestFan S r).paths := d.path_mem.1
  have hsPath : d.path.start ∈ I.lambda.source :=
    (PopularSwitching.restrictPaths
      (PopularGroundingBridge.requestFan S r)
      {q | GroundingConcreteControls.hangingLadderCollision I S.cut r q})
      |>.starts_in_source d.path_mem
  let contactVertex : I.LV := d.traceContact
  have hmeet : d.path.walk.Meets ({contactVertex} : Set I.LV) :=
    ⟨contactVertex, d.traceContact_mem_path,
      Set.mem_singleton contactVertex⟩
  let q : FinitePath I.lambda.graph :=
    d.path.firstHit ({contactVertex} : Set I.LV) hmeet
  have hqStart : q.start = d.path.start := rfl
  have hqFinish : q.finish = contactVertex := by
    exact Set.mem_singleton_iff.1
      (d.path.firstHit_finish_mem ({contactVertex} : Set I.LV) hmeet)
  have hqSource : q.start ∈ I.lambda.source := by
    rw [hqStart]
    exact hsPath
  have hpurePath : I.IsTargetPure d.path :=
    I.requestFan_path_isTargetPure S r hpFan
  have hpureQ : I.IsTargetPure q :=
    PopularAuxiliary.Input.IsTargetPure.firstHit I hpurePath
      ({contactVertex} : Set I.LV) hmeet
  rcases I.start_of_mem_lambda_source d.path hsPath with
      ⟨x, hxSource, hpx⟩ | ⟨i, hpi⟩
  · let xs : K.finiteTerminalSet :=
      ⟨x, K.groundedFiniteTerminalSet_subset_finiteTerminalSet hxSource⟩
    have hsourceIndex :
        U.f ⟨d.path.start, hsPath⟩ = K.finiteTerminalStage xs := by
      have hsEq :
          U.f ⟨d.path.start, hsPath⟩ =
            U.f ⟨.old x, (I.mem_lambda_source_old x).2 hxSource⟩ := by
        apply congrArg U.f
        exact Subtype.ext hpx
      exact hsEq
    have hstage : K.finiteTerminalStage xs = a :=
      hsourceIndex.symm.trans d.index_eq
    have hroof := hK.legal.targetPure_finite_gadgetExit_successorRoofTransport
      q hqSource hpureQ xs contactVertex d.contact
      (hqStart.trans hpx) hqFinish d.traceContact_exit
    simpa only [hstage] using hroof
  · have hsourceIndex :
        U.f ⟨d.path.start, hsPath⟩ = K.groundedInfiniteStage i := by
      have hsEq :
          U.f ⟨d.path.start, hsPath⟩ =
            U.f ⟨.proxy i, I.mem_lambda_source_proxy i⟩ := by
        apply congrArg U.f
        exact Subtype.ext hpi
      exact hsEq
    have hstage : K.groundedInfiniteStage i = a :=
      hsourceIndex.symm.trans d.index_eq
    have hroof := hK.legal.targetPure_proxy_gadgetExit_successorRoofTransport
      q hqSource hpureQ i contactVertex d.contact
      (hqStart.trans hpi) hqFinish d.traceContact_exit
    simpa only [hstage] using hroof

end KappaLadder
end DWeb
end Erdos599
