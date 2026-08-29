/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingErasedSwitchRelation
import ErdosProblems.Erdos599.GroundingSourceRootTransfer

/-!
# Source provenance for the erased grounding switch

The auxiliary source of every path retained by the grounded simultaneous
selector represents a grounded obstruction record.  The endpoint-relaxed
decoder starts at a vertex of that record.  This file makes that fact
available at the original-web level, before any relation decomposition is
performed.
-/

noncomputable section

open Set

namespace Erdos599

open DirectedPath PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode

universe u

namespace PopularAuxiliary.Input

variable {V I : Type u} {Gamma : DWeb V}
variable (J : PopularAuxiliary.Input Gamma I)

/-- An endpoint-relaxed decoding which starts at an old auxiliary source
starts at the represented original vertex. -/
theorem decodeFinitePathToExit_initial_of_start_old
    (p : FinitePath J.lambda.graph)
    (hsource : p.start ∈ J.lambda.source) (z x : V)
    (hexit : J.gadgetExit p.finish = some z)
    (hstart : p.start = .old x) :
    (J.decodeFinitePathToExit p hsource z hexit).initial = x := by
  classical
  unfold decodeFinitePathToExit
  split
  · rename_i y hy
    have hyx : y.1 = x := by
      exact PopularAuxiliary.Input.LambdaVertex.old.inj
        (y.2.2.symm.trans hstart)
    exact hyx
  · rename_i i hi
    exact False.elim (by
      have : (PopularAuxiliary.Input.LambdaVertex.proxy i.1 : J.LV) =
          .old x := i.2.symm.trans hstart
      cases this)

/-- An endpoint-relaxed decoding which starts at a proxy starts somewhere
on the original path represented by that same proxy. -/
theorem decodeFinitePathToExit_initial_mem_proxyPath_of_start_proxy
    (p : FinitePath J.lambda.graph)
    (hsource : p.start ∈ J.lambda.source) (z : V) (i : I)
    (hexit : J.gadgetExit p.finish = some z)
    (hstart : p.start = .proxy i) :
    (J.decodeFinitePathToExit p hsource z hexit).initial ∈
      (J.proxyPath i).support := by
  classical
  unfold decodeFinitePathToExit
  split
  · rename_i x hx
    exact False.elim (by
      have : (PopularAuxiliary.Input.LambdaVertex.old x.1 : J.LV) =
          .proxy i := x.2.2.symm.trans hstart
      cases this)
  · rename_i j hj
    have hji : j.1 = i := by
      exact PopularAuxiliary.Input.LambdaVertex.proxy.inj
        (j.2.symm.trans hstart)
    subst i
    unfold decodeFinitePathToExitFromProxy
    exact (Classical.choose_spec
      (J.decodeWalkSteps_runs_from_eq_proxy p.walk j.2 hexit)).1

/-- Stopping an edge request at the entry of its final edge gadget does not
change the decoded source endpoint. -/
theorem decodeFinitePathToEdgeEntry_initial_of_start_old
    (p : FinitePath J.lambda.graph)
    (hsource : p.start ∈ J.lambda.source) (u v x : V)
    (hfinish : p.finish = .edge u v)
    (hstart : p.start = .old x) :
    (J.decodeFinitePathToEdgeEntry p hsource u v hfinish).initial = x := by
  classical
  unfold decodeFinitePathToEdgeEntry
  apply J.decodeFinitePathToExit_initial_of_start_old
  exact hstart

/-- The proxy-source counterpart of
`decodeFinitePathToEdgeEntry_initial_of_start_old`. -/
theorem decodeFinitePathToEdgeEntry_initial_mem_proxyPath_of_start_proxy
    (p : FinitePath J.lambda.graph)
    (hsource : p.start ∈ J.lambda.source) (u v : V) (i : I)
    (hfinish : p.finish = .edge u v)
    (hstart : p.start = .proxy i) :
    (J.decodeFinitePathToEdgeEntry p hsource u v hfinish).initial ∈
      (J.proxyPath i).support := by
  classical
  unfold decodeFinitePathToEdgeEntry
  apply J.decodeFinitePathToExit_initial_mem_proxyPath_of_start_proxy
  exact hstart

end PopularAuxiliary.Input

namespace DWeb.KappaLadder

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Final-stage specialization of persistence for a recorded ladder
component.  This source-geometry copy keeps the endpoint decoder independent
of the equal-subwarp branch. -/
theorem recorded_mem_limitWarp_inessential_sourceGeometry
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    {a : Ladder.Stage kappa} {p : Gamma.DPath}
    (hp : L.chosen a = some p) :
    p ∈ Gamma.inessentialPaths L.limitWarp := by
  apply L.recorded_mem_inessential hlegal.recordedPathsPersist hp
  change a.1 + 1 ≤ kappa.ord
  exact (Order.add_one_le_iff).2 a.2

/-- The selected decoder preserves an ordinary old source endpoint.  This
uniform statement covers both old-vertex requests and edge requests, the
latter being stopped at the entry of their final edge gadget. -/
theorem selectedRequestTrace_initial_of_start_old
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : Request (L.popularAuxiliaryInput hL.legal) S.cut) (x : V)
    (hstart : (strongSelectedPath (L.popularAuxiliaryIndexed hL) S
      (L.groundedConcreteControls hL S) r).start = .old x) :
    (selectedRequestTrace (L.popularAuxiliaryIndexed hL) S
      (L.groundedConcreteControls hL S) r).initial = x := by
  let J := L.popularAuxiliaryInput hL.legal
  let U := L.popularAuxiliaryIndexed hL
  let K := L.groundedConcreteControls hL S
  let p := strongSelectedPath U S K r
  have hp : p ∈ (strongSelectedWarp U S K).paths := ⟨r, rfl⟩
  have hpSource : p.start ∈ J.lambda.source :=
    (strongSelectedWarp U S K).starts_in_source hp
  cases r with
  | inl y =>
      change (J.decodeFinitePathToExit p hpSource y.1 _).initial = x
      apply J.decodeFinitePathToExit_initial_of_start_old
      exact hstart
  | inr e =>
      change (J.decodeFinitePathToEdgeEntry p hpSource e.1.1 e.1.2 _).initial = x
      apply J.decodeFinitePathToEdgeEntry_initial_of_start_old
      exact hstart

/-- A selected decoder whose auxiliary source is a proxy starts on the
original limiting-ladder component represented by that proxy. -/
theorem selectedRequestTrace_initial_mem_proxyPath_of_start_proxy
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : Request (L.popularAuxiliaryInput hL.legal) S.cut)
    (i : L.groundedInfiniteRecords)
    (hstart : (strongSelectedPath (L.popularAuxiliaryIndexed hL) S
      (L.groundedConcreteControls hL S) r).start = .proxy i) :
    (selectedRequestTrace (L.popularAuxiliaryIndexed hL) S
      (L.groundedConcreteControls hL S) r).initial ∈ i.1.support := by
  let J := L.popularAuxiliaryInput hL.legal
  let U := L.popularAuxiliaryIndexed hL
  let K := L.groundedConcreteControls hL S
  let p := strongSelectedPath U S K r
  have hp : p ∈ (strongSelectedWarp U S K).paths := ⟨r, rfl⟩
  have hpSource : p.start ∈ J.lambda.source :=
    (strongSelectedWarp U S K).starts_in_source hp
  cases r with
  | inl y =>
      change (J.decodeFinitePathToExit p hpSource y.1 _).initial ∈
        (J.proxyPath i).support
      apply J.decodeFinitePathToExit_initial_mem_proxyPath_of_start_proxy
      exact hstart
  | inr e =>
      change (J.decodeFinitePathToEdgeEntry p hpSource e.1.1 e.1.2 _).initial ∈
        (J.proxyPath i).support
      apply J.decodeFinitePathToEdgeEntry_initial_mem_proxyPath_of_start_proxy
      exact hstart

/-- Full source provenance of a selected erased request route.  Besides the
grounded parent, this records the exact auxiliary source index and the
finite-terminal/proxy representation from which it was computed. -/
theorem selectedRequestTrace_grounded_record_data
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : Request (L.popularAuxiliaryInput hL.legal) S.cut) :
    ∃ (a : Ladder.Stage kappa) (parent : Gamma.DPath),
      a ∈ L.phiGround ∧ L.chosen a = some parent ∧
        parent ∈ Gamma.inessentialPaths L.limitWarp ∧
        (selectedRequestTrace (L.popularAuxiliaryIndexed hL) S
          (L.groundedConcreteControls hL S) r).initial ∈ parent.support ∧
        parent.initial ∈ Gamma.source ∧
        a = (L.popularAuxiliaryIndexed hL).f
          ⟨(strongSelectedPath (L.popularAuxiliaryIndexed hL) S
            (L.groundedConcreteControls hL S) r).start,
            (strongSelectedWarp (L.popularAuxiliaryIndexed hL) S
              (L.groundedConcreteControls hL S)).starts_in_source ⟨r, rfl⟩⟩ ∧
        ((∃ x : L.groundedFiniteTerminalSet,
            (strongSelectedPath (L.popularAuxiliaryIndexed hL) S
              (L.groundedConcreteControls hL S) r).start = .old x.1 ∧
            Gamma.terminal? parent = some x.1) ∨
          ∃ i : L.groundedInfiniteRecords,
            (strongSelectedPath (L.popularAuxiliaryIndexed hL) S
              (L.groundedConcreteControls hL S) r).start = .proxy i ∧
            parent = i.1) := by
  let J := L.popularAuxiliaryInput hL.legal
  let U := L.popularAuxiliaryIndexed hL
  let K := L.groundedConcreteControls hL S
  let p := strongSelectedPath U S K r
  let T := selectedRequestTrace U S K r
  have hp : p ∈ (strongSelectedWarp U S K).paths := ⟨r, rfl⟩
  have hpSelectedSource : p.start ∈ J.lambda.source :=
    (strongSelectedWarp U S K).starts_in_source hp
  have hpGround := L.strongSelectedPath_mem_groundedSourcePaths hL S r
  obtain ⟨hpSource, haGround⟩ := hpGround
  rcases J.start_of_mem_lambda_source p hpSource with
      ⟨x, hxFinite, hstart⟩ | ⟨i, hstart⟩
  ·
      let xs : L.groundedFiniteTerminalSet :=
        ⟨x, hxFinite⟩
      have hindex : U.f ⟨p.start, hpSource⟩ =
          L.finiteTerminalIndex xs := by
        have hs :
            (⟨p.start, hpSource⟩ : J.lambda.source) =
              ⟨.old xs.1, (J.mem_lambda_source_old xs.1).2 xs.2⟩ := by
          exact Subtype.ext hstart
        rw [congrArg U.f hs]
        rfl
      have ha : L.finiteTerminalIndex xs ∈ L.phiGround :=
        L.finiteTerminalStage_mem_phiGround hL.legal xs
      let xs' : L.finiteTerminalSet :=
        ⟨xs.1, L.groundedFiniteTerminalSet_subset_finiteTerminalSet xs.2⟩
      obtain ⟨_hfinite, parent, hchosen, hterminal⟩ :=
        L.finiteTerminalStage_spec xs'
      have hstage : L.finiteTerminalStage xs' = L.finiteTerminalIndex xs := rfl
      rw [hstage] at hchosen
      have hparentSource : parent.initial ∈ Gamma.source := by
        obtain ⟨q, hq, hqSource⟩ := ha
        have hpq : parent = q := Option.some.inj (hchosen.symm.trans hq)
        exact hpq ▸ hqSource
      have hTinitial : T.initial = x := by
        exact L.selectedRequestTrace_initial_of_start_old hL S r x hstart
      have hindexSelected : U.f ⟨p.start, hpSelectedSource⟩ =
          L.finiteTerminalIndex xs := by
        simpa only using hindex
      refine ⟨L.finiteTerminalIndex xs, parent, ha, hchosen,
        L.recorded_mem_limitWarp_inessential_sourceGeometry
          hL.legal hchosen, ?_,
        hparentSource, hindexSelected.symm, Or.inl ⟨xs, hstart, hterminal⟩⟩
      rw [hTinitial]
      exact Gamma.terminal_mem_support hterminal
  ·
      have hindex : U.f ⟨p.start, hpSource⟩ =
          L.groundedInfiniteStage i := by
        have hs :
            (⟨p.start, hpSource⟩ : J.lambda.source) =
              ⟨.proxy i, J.mem_lambda_source_proxy i⟩ := by
          exact Subtype.ext hstart
        rw [congrArg U.f hs]
        rfl
      have ha : L.groundedInfiniteStage i ∈ L.phiGround :=
        (L.groundedInfiniteStage_spec i).1.1
      have hchosen := (L.groundedInfiniteStage_spec i).2
      have hparentSource : i.1.initial ∈ Gamma.source := by
        obtain ⟨q, hq, hqSource⟩ := ha
        have hiq : i.1 = q := Option.some.inj (hchosen.symm.trans hq)
        exact hiq ▸ hqSource
      have hTinitial : T.initial ∈ i.1.support := by
        exact L.selectedRequestTrace_initial_mem_proxyPath_of_start_proxy
          hL S r i hstart
      have hindexSelected : U.f ⟨p.start, hpSelectedSource⟩ =
          L.groundedInfiniteStage i := by
        simpa only using hindex
      refine ⟨L.groundedInfiniteStage i, i.1, ha, hchosen,
        L.recorded_mem_limitWarp_inessential_sourceGeometry
          hL.legal hchosen, ?_,
        hparentSource, hindexSelected.symm, Or.inr ⟨i, hstart, rfl⟩⟩
      simpa only [J, KappaLadder.popularAuxiliaryInput,
        KappaLadder.groundedInfinitePath, T, U, K, p] using hTinitial

/-- The erased route selected at a grounding request starts on a grounded
recorded component of the limiting ladder.  In particular the parent
component starts in the original source and is already an inessential
member of the limiting warp. -/
theorem selectedRequestTrace_initial_mem_grounded_record
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : Request (L.popularAuxiliaryInput hL.legal) S.cut) :
    ∃ (a : Ladder.Stage kappa) (parent : Gamma.DPath),
      a ∈ L.phiGround ∧ L.chosen a = some parent ∧
        parent ∈ Gamma.inessentialPaths L.limitWarp ∧
        (selectedRequestTrace (L.popularAuxiliaryIndexed hL) S
          (L.groundedConcreteControls hL S) r).initial ∈ parent.support ∧
        parent.initial ∈ Gamma.source := by
  obtain ⟨a, parent, ha, hchosen, hinessential, hinitial, hsource,
    _hindex, _hdescription⟩ :=
      L.selectedRequestTrace_grounded_record_data hL S r
  exact ⟨a, parent, ha, hchosen, hinessential, hinitial, hsource⟩

/-- Under the standard no-edge-enters-source normalization, every genuine
original source is a root of the concrete switched relation.  This is the
`HasIncoming` half of the rooted-reachability witness used in the final
Assertion 8.22 assembly. -/
theorem erasedSelectedSwitchedEdges_noIncoming_of_mem_source
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    {a : V} (ha : a ∈ Gamma.source) :
    ¬ Alternating.HasIncoming
      (erasedSelectedSwitchedEdges (L.popularAuxiliaryIndexed hL) S
        (L.groundedConcreteControls hL S)) a := by
  rintro ⟨x, hxa⟩
  exact hNoEnter
    (erasedSelectedSwitchedEdges_subset_adj
      (L.popularAuxiliaryIndexed hL) S
      (L.groundedConcreteControls hL S) hxa) ha

end DWeb.KappaLadder

end Erdos599
