/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularRows
import ErdosProblems.Erdos599.HalfwayIndexedRelationScheduler

/-!
# Dynamic terminal scheduling for indexed half-way blueprints

This module schedules the real terminals which are born during the moving
half-way construction.  It does not enumerate one global closing-up set.
Instead, every stage contributes its bounded real-terminal row and the next
stage selects the least unserved row entry in the shell-first priority from
`RegularRows`.

The starvation argument below only uses that the run cardinal is infinite.
In particular it remains valid at a singular cardinal: a full final segment
of the initial ordinal cannot inject into one bounded priority initial
segment.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace CardinalInduction
namespace RegularRows

universe u

open RegularCardinal

/-- Every final segment of the stage order below an infinite cardinal has
the full cardinality of that stage order.  No regularity hypothesis is
needed. -/
theorem mk_stage_Ici_eq_lift {kappa : Cardinal.{u}}
    (hkappa : aleph0 ≤ kappa) (a : Stage kappa) :
    #(Set.Ici a) = Cardinal.lift.{u + 1, u} kappa := by
  apply le_antisymm
  · exact (Cardinal.mk_set_le (Set.Ici a)).trans_eq
      (Stationary.mk_below kappa)
  · by_contra hnot
    have htail : #(Set.Ici a) < Cardinal.lift.{u + 1, u} kappa :=
      lt_of_not_ge hnot
    have hhead : #(Set.Iio a) < Cardinal.lift.{u + 1, u} kappa := by
      apply (Cardinal.mk_le_mk_of_subset Set.Iio_subset_Iic_self).trans_lt
      exact RowSystem.mk_stage_Iic_lt hkappa a
    have hunion :
        #((Set.Iio a ∪ Set.Ici a : Set (Stage kappa))) <
          Cardinal.lift.{u + 1, u} kappa :=
      (Cardinal.mk_union_le _ _).trans_lt
        (Cardinal.add_lt_of_lt (Cardinal.aleph0_le_lift.mpr hkappa)
          hhead htail)
    have hcover : Set.Iio a ∪ Set.Ici a = (Set.univ : Set (Stage kappa)) := by
      ext b
      simp only [Set.mem_union, Set.mem_Iio, Set.mem_Ici, Set.mem_univ,
        iff_true]
      exact lt_or_ge b a
    rw [hcover, Cardinal.mk_univ, Stationary.mk_below] at hunion
    exact hunion.false

namespace CausalRowRule

/-- Singular-cardinal version of causal-row fairness.  The existing proof
uses stationarity to identify the size of a tail and consequently assumes
regularity; `mk_stage_Ici_eq_lift` supplies exactly that equality directly. -/
theorem exists_preferred_eq_some_of_mem_state_row_of_infinite
    {X : Type u} {kappa : Cardinal.{u}}
    (Q : CausalRowRule kappa X) (hkappa : aleph0 ≤ kappa)
    {b : Stage kappa} {x : X}
    (hx : x ∈ (Q.state hkappa b).row) :
    ∃ a, Q.preferred hkappa a = some x := by
  let xs : (Q.state hkappa b).row := ⟨x, hx⟩
  by_contra hstarves
  push Not at hstarves
  let a0 := Q.activationStage hkappa b xs
  have htailCard : #(Set.Ici a0) = Cardinal.lift.{u + 1, u} kappa :=
    mk_stage_Ici_eq_lift hkappa a0
  change #(Set.Ici (Q.activationStage hkappa b xs)) =
    Cardinal.lift.{u + 1, u} kappa at htailCard
  have hinj := Cardinal.mk_le_of_injective
    (Q.starvationCoordinateEmbedding hkappa xs hstarves).injective
  have hsmall := mk_coordinatePredecessors_lt hkappa
    (Q.entryCoordinate hkappa b xs)
  have hinj' :
      Cardinal.lift.{u + 1, u} kappa ≤
        #({d : Stage kappa × Stage kappa //
          RowSystem.CoordinatePriority d (Q.entryCoordinate hkappa b xs)}) := by
    simpa only [htailCard] using hinj
  exact (not_lt_of_ge hinj') hsmall

end CausalRowRule
end RegularRows
end CardinalInduction
end Erdos599

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint
namespace IndexedTerminalResolutionState
namespace ReachableResolutionRecursor

universe u w

open CardinalInduction.RegularRows
open RegularCardinal

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {persistent B : Set V}
variable {Stage : Type w} [LinearOrder Stage]
variable {slice closure : Stage → Set V}

local notation "ResolutionState" => IndexedTerminalResolutionState
  (Gamma := Gamma) (Y := Y) (kappa := kappa)
  (persistent := persistent) (B := B) slice closure

/-- Inputs for the bounded dynamic scheduler.  Its run has the initial
ordinal of `kappa` as length; the ladder index stored in a resolution state
is independent and may live in another universe. -/
structure DynamicResolutionRecursor where
  kappa_infinite : aleph0 ≤ kappa
  seed : ResolutionState
  bootstrap : V
  bootstrap_terminal : bootstrap ∈ seed.blueprint.realPart.terminals
  successor : SchedulerSuccessor
    (Gamma := Gamma) (Y := Y) (kappa := kappa)
    (persistent := persistent) (B := B) slice closure
  properLimit : ProperLimitCompiler
    (Gamma := Gamma) (Y := Y) (kappa := kappa)
    (persistent := persistent) (B := B) slice closure kappa.ord

namespace DynamicResolutionRecursor

/-- The ordinary ordinal recursor used only to compile honest proper
limits.  Dynamic requests are supplied by the joint recursion below. -/
noncomputable def ordinalRecursor (D : DynamicResolutionRecursor
    (Gamma := Gamma) (Y := Y) (kappa := kappa)
    (persistent := persistent) (B := B)
    (slice := slice) (closure := closure)) :
    ReachableResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure :=
  .ofCompilers D.seed D.successor kappa.ord D.properLimit

/-- One state of the joint resolution/terminal-row recursion. -/
structure DynamicState (D : DynamicResolutionRecursor
    (Gamma := Gamma) (Y := Y) (kappa := kappa)
    (persistent := persistent) (B := B)
    (slice := slice) (closure := closure)) where
  resolution : ResolutionState
  emitted : Option V

theorem realTerminalRow_mk_le (D : DynamicResolutionRecursor
    (Gamma := Gamma) (Y := Y) (kappa := kappa)
    (persistent := persistent) (B := B)
    (slice := slice) (closure := closure))
    (S : ResolutionState) :
    #S.blueprint.realPart.terminals ≤ kappa := by
  have hsub : S.blueprint.realPart.terminals ⊆ S.blueprint.vertexSet := by
    intro x hx
    simpa only [realPart_vertices] using hx.1
  exact (Cardinal.mk_le_mk_of_subset hsub).trans
    (S.blueprint.mk_vertexSet_le_of_mk_paths_le
      D.kappa_infinite S.isBlueprint.card_paths)

/-- Forget the blueprint payload and retain the row/scheduler data consumed
by the shell-priority queue. -/
def DynamicState.toCausalState (D : DynamicResolutionRecursor
    (Gamma := Gamma) (Y := Y) (kappa := kappa)
    (persistent := persistent) (B := B)
    (slice := slice) (closure := closure))
    (S : D.DynamicState) : CausalState kappa V where
  row := S.resolution.blueprint.realPart.terminals
  row_mk_le := D.realTerminalRow_mk_le S.resolution
  chosen := S.emitted

/-- A field-free row rule used solely to instantiate the queue operations.
Those operations depend on the supplied prior states, not on `nextRow`. -/
def terminalQueueSelector : CausalRowRule kappa V where
  nextRow := fun _ _ ↦ ∅
  nextRow_mk_le := by simp

theorem chooseTask_rule_irrel
    (Q R : CausalRowRule kappa V) (hkappa : aleph0 ≤ kappa)
    (a : RegularCardinal.Stage kappa)
    (prior : ∀ b : RegularCardinal.Stage kappa,
      b < a → CausalState kappa V) :
    Q.chooseTask hkappa a prior = R.chooseTask hkappa a prior := by
  rfl

/-- Least currently visible unserved born terminal. -/
noncomputable def select
    (D : DynamicResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure))
    (a : RegularCardinal.Stage kappa)
    (prior : ∀ b : RegularCardinal.Stage kappa,
      b < a → D.DynamicState) : Option V :=
  (terminalQueueSelector.chooseTask D.kappa_infinite a
    (fun b hba ↦ (prior b hba).toCausalState D)).map fun t ↦ t.2.1

/-- The request actually sent to the moving successor.  Empty queue stages
repeat the already linked bootstrap request. -/
noncomputable def request
    (D : DynamicResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure))
    (a : RegularCardinal.Stage kappa)
    (prior : ∀ b : RegularCardinal.Stage kappa,
      b < a → D.DynamicState) : V :=
  (D.select a prior).getD D.bootstrap

/-- The state before executing the request at `a`: the seed at zero, the
immediate predecessor at a successor, and the honest relation limit at a
nonzero limit.  Fallback branches in `limitOrSeed` are unreachable for the
actual coherent recursion and make this definition total on arbitrary
strict-prior families. -/
noncomputable def base
    (D : DynamicResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure))
    (a : RegularCardinal.Stage kappa)
    (prior : ∀ b : RegularCardinal.Stage kappa,
      b < a → D.DynamicState) :
    ResolutionState := by
  classical
  if hzero : a.1 = 0 then
    exact D.seed
  else if hsucc : ∃ o, o + 1 = a.1 then
    let o : Ordinal.{u} := Classical.choose hsucc
    have ho : o + 1 = a.1 := Classical.choose_spec hsucc
    let b : RegularCardinal.Stage kappa := ⟨o, by
      exact (show o < a.1 by simpa only [← ho] using
        ((Order.lt_add_one_iff).2 (le_refl o))).trans a.2⟩
    exact (prior b (by
      change o < a.1
      simpa only [← ho] using
        ((Order.lt_add_one_iff).2 (le_refl o)))).resolution
  else
    have hlimit : IsSuccLimit a.1 := by
      rcases Ordinal.zero_or_succ_or_isSuccLimit a.1 with h | h | h
      · exact (hzero h).elim
      · rcases h with ⟨o, ho⟩
        exact (hsucc ⟨o, by simpa only [ho]⟩).elim
      · exact h
    exact D.ordinalRecursor.limitOrSeed a.1 hlimit
      (fun o ho ↦ (prior ⟨o, ho.trans a.2⟩ (by exact ho)).resolution)

/-- One simultaneous queue/scheduler step. -/
noncomputable def nextState
    (D : DynamicResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure))
    (a : RegularCardinal.Stage kappa)
    (prior : ∀ b : RegularCardinal.Stage kappa,
      b < a → D.DynamicState) :
    D.DynamicState where
  resolution := D.successor.step (D.base a prior) (D.request a prior)
  emitted := D.select a prior

/-- The actual dynamic terminal-resolution run. -/
noncomputable def state
    (D : DynamicResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure)) :
    RegularCardinal.Stage kappa → D.DynamicState :=
  WellFoundedLT.fix fun a prior ↦ D.nextState a prior

theorem state_eq
    (D : DynamicResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure))
    (a : RegularCardinal.Stage kappa) :
    D.state a = D.nextState a (fun b _hba ↦ D.state b) := by
  rw [state, WellFoundedLT.fix_eq]

@[simp] theorem state_emitted
    (D : DynamicResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure))
    (a : RegularCardinal.Stage kappa) :
    (D.state a).emitted = D.select a (fun b _hba ↦ D.state b) := by
  rw [D.state_eq a]
  rfl

@[simp] theorem state_resolution
    (D : DynamicResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure))
    (a : RegularCardinal.Stage kappa) :
    (D.state a).resolution = D.successor.step
      (D.base a (fun b _hba ↦ D.state b))
      (D.request a (fun b _hba ↦ D.state b)) := by
  rw [D.state_eq a]
  rfl

/-- Eliminate the defensive branches of `limitOrSeed` when the history is
known to be in range and coherent. -/
theorem limitOrSeed_eq_properLimit
    (R : ReachableResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure)
    (o : Ordinal.{u}) (ho : IsSuccLimit o) (hoLength : o < R.length)
    (prior : ∀ a : Ordinal.{u}, a < o → ResolutionState)
    (hcoherent : PriorCoherent (fun a : Set.Iio o ↦ prior a.1 a.2)) :
    R.limitOrSeed o ho prior =
      (R.properLimit o hoLength ho (fun a : Set.Iio o ↦ prior a.1 a.2)
        hcoherent).limit := by
  unfold ReachableResolutionRecursor.limitOrSeed
  rw [dif_pos hoLength, dif_pos hcoherent]

/-- The terminal rows produced by the joint recursion, exposed through the
generic causal-row API.  Its `nextRow` ignores the erased prior payload;
causality was already enforced by `state`. -/
noncomputable def terminalRowRule
    (D : DynamicResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure)) :
    CausalRowRule kappa V where
  nextRow := fun a _ ↦
    (D.state a).resolution.blueprint.realPart.terminals
  nextRow_mk_le := fun a _ ↦
    D.realTerminalRow_mk_le (D.state a).resolution

/-- Queue recursion on the exposed row rule agrees with the queue component
of the simultaneous scheduler recursion. -/
theorem terminalRowRule_state_eq
    (D : DynamicResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure))
    (a : RegularCardinal.Stage kappa) :
    (D.terminalRowRule.state D.kappa_infinite a) =
      (D.state a).toCausalState D := by
  induction a using WellFoundedLT.induction with
  | ind a ih =>
      rw [CausalRowRule.state_eq, D.state_eq]
      simp only [CausalRowRule.nextState,
        DynamicState.toCausalState, nextState]
      rw [CausalState.mk.injEq]
      refine ⟨by simp only [terminalRowRule]; rw [D.state_resolution], ?_⟩
      simp only [select]
      let priorQ : ∀ b : RegularCardinal.Stage kappa,
          b < a → CausalState kappa V :=
        fun b _hba ↦ D.terminalRowRule.state D.kappa_infinite b
      let priorD : ∀ b : RegularCardinal.Stage kappa,
          b < a → CausalState kappa V :=
        fun b _hba ↦ (D.state b).toCausalState D
      have hprior : priorQ = priorD := by
        funext b hba
        exact ih b hba
      change (D.terminalRowRule.chooseTask D.kappa_infinite a priorQ).map
          (fun t ↦ t.2.1) =
        (terminalQueueSelector.chooseTask D.kappa_infinite a priorD).map
          (fun t ↦ t.2.1)
      rw [hprior, chooseTask_rule_irrel D.terminalRowRule
        terminalQueueSelector D.kappa_infinite a priorD]

@[simp] theorem terminalRowRule_preferred
    (D : DynamicResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure))
    (a : RegularCardinal.Stage kappa) :
    D.terminalRowRule.preferred D.kappa_infinite a =
      (D.state a).emitted := by
  change (D.terminalRowRule.state D.kappa_infinite a).chosen = _
  rw [D.terminalRowRule_state_eq a]
  rfl

/-- Every real terminal born in the dynamic run is eventually emitted by
the queue, without a global closure enumeration. -/
theorem exists_state_emitted_eq_some_of_realTerminal
    (D : DynamicResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure))
    {b : RegularCardinal.Stage kappa} {x : V}
    (hx : x ∈ (D.state b).resolution.blueprint.realPart.terminals) :
    ∃ a, (D.state a).emitted = some x := by
  have hxrow : x ∈
      (D.terminalRowRule.state D.kappa_infinite b).row := by
    rw [D.terminalRowRule_state_eq b]
    exact hx
  obtain ⟨a, ha⟩ :=
    D.terminalRowRule.exists_preferred_eq_some_of_mem_state_row_of_infinite
      D.kappa_infinite hxrow
  exact ⟨a, by simpa only [D.terminalRowRule_preferred] using ha⟩

/-- The dynamically generated resolution states form a refining chain. -/
theorem state_refiningExtends
    (D : DynamicResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure)) :
    ∀ b : RegularCardinal.Stage kappa,
      ∀ a : RegularCardinal.Stage kappa, a ≤ b →
        (D.state a).resolution.RefiningExtends (D.state b).resolution := by
  classical
  intro b
  induction b using WellFoundedLT.induction with
  | ind b ih =>
      intro a hab
      rcases hab.lt_or_eq with hab | rfl
      · rw [D.state_resolution b]
        refine (show (D.state a).resolution.RefiningExtends
            (D.base b (fun c _hcb ↦ D.state c)) from ?_).trans
          (D.successor.step_extends _ _)
        unfold base
        split
        next hzero =>
          have habv : a.1 < b.1 := hab
          rw [hzero] at habv
          exact (not_lt_of_ge (bot_le : (0 : Ordinal.{u}) ≤ a.1) habv).elim
        next hnotzero =>
          split
          next hsucc =>
            let o : Ordinal.{u} := Classical.choose hsucc
            have ho : o + 1 = b.1 := Classical.choose_spec hsucc
            let c : RegularCardinal.Stage kappa := ⟨o, by
              exact (show o < b.1 by simpa only [← ho] using
                ((Order.lt_add_one_iff).2 (le_refl o))).trans b.2⟩
            have hcb : c < b := by
              change o < b.1
              simpa only [← ho] using
                ((Order.lt_add_one_iff).2 (le_refl o))
            have hac : a ≤ c := by
              change a.1 ≤ o
              apply (Order.lt_add_one_iff).1
              have habv : a.1 < b.1 := hab
              simpa only [ho] using habv
            simpa only [c, o] using ih c hcb a hac
          next hnotsucc =>
            have hlimit : IsSuccLimit b.1 := by
              rcases Ordinal.zero_or_succ_or_isSuccLimit b.1 with h | h | h
              · exact (hnotzero h).elim
              · rcases h with ⟨o, ho⟩
                exact (hnotsucc ⟨o, by simpa only [ho]⟩).elim
              · exact h
            let limitPrior : ∀ o : Ordinal.{u}, o < b.1 → ResolutionState :=
              fun o ho ↦ (D.state ⟨o, by
                change o < kappa.ord
                exact ho.trans (show b.1 < kappa.ord from b.2)⟩).resolution
            let family : Set.Iio b.1 → ResolutionState := fun c ↦
              limitPrior c.1 c.2
            have hcoherent : PriorCoherent family := by
              intro c d hcd
              have hdb : (⟨d.1, by
                  change d.1 < kappa.ord
                  exact d.2.trans (show b.1 < kappa.ord from b.2)⟩ :
                    RegularCardinal.Stage kappa) < b := d.2
              exact ih _ hdb _ hcd
            have hlength : b.1 < D.ordinalRecursor.length := by
              change b.1 < kappa.ord
              exact b.2
            change (D.state a).resolution.RefiningExtends
              (D.ordinalRecursor.limitOrSeed b.1 hlimit limitPrior)
            rw [limitOrSeed_eq_properLimit D.ordinalRecursor b.1 hlimit
              hlength limitPrior hcoherent]
            exact (D.ordinalRecursor.properLimit b.1 hlength hlimit family
              hcoherent).extension ⟨a.1, hab⟩
      · exact RefiningExtends.refl _

/-- Linked requests are retained throughout the dynamic run. -/
theorem state_linked_mono
    (D : DynamicResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure)) :
    ∀ b : RegularCardinal.Stage kappa,
      ∀ a : RegularCardinal.Stage kappa, a ≤ b →
        (D.state a).resolution.linked ⊆ (D.state b).resolution.linked := by
  classical
  intro b
  induction b using WellFoundedLT.induction with
  | ind b ih =>
      intro a hab
      rcases hab.lt_or_eq with hab | rfl
      · rw [D.state_resolution b]
        refine (show (D.state a).resolution.linked ⊆
            (D.base b (fun c _hcb ↦ D.state c)).linked from ?_).trans
          (D.successor.linked_mono _ _)
        unfold base
        split
        next hzero =>
          have habv : a.1 < b.1 := hab
          rw [hzero] at habv
          exact (not_lt_of_ge (bot_le : (0 : Ordinal.{u}) ≤ a.1) habv).elim
        next hnotzero =>
          split
          next hsucc =>
            let o : Ordinal.{u} := Classical.choose hsucc
            have ho : o + 1 = b.1 := Classical.choose_spec hsucc
            let c : RegularCardinal.Stage kappa := ⟨o, by
              exact (show o < b.1 by simpa only [← ho] using
                ((Order.lt_add_one_iff).2 (le_refl o))).trans b.2⟩
            have hcb : c < b := by
              change o < b.1
              simpa only [← ho] using
                ((Order.lt_add_one_iff).2 (le_refl o))
            have hac : a ≤ c := by
              change a.1 ≤ o
              apply (Order.lt_add_one_iff).1
              have habv : a.1 < b.1 := hab
              simpa only [ho] using habv
            simpa only [c, o] using ih c hcb a hac
          next hnotsucc =>
            have hlimit : IsSuccLimit b.1 := by
              rcases Ordinal.zero_or_succ_or_isSuccLimit b.1 with h | h | h
              · exact (hnotzero h).elim
              · rcases h with ⟨o, ho⟩
                exact (hnotsucc ⟨o, by simpa only [ho]⟩).elim
              · exact h
            let limitPrior : ∀ o : Ordinal.{u}, o < b.1 → ResolutionState :=
              fun o ho ↦ (D.state ⟨o, by
                change o < kappa.ord
                exact ho.trans (show b.1 < kappa.ord from b.2)⟩).resolution
            let family : Set.Iio b.1 → ResolutionState := fun c ↦
              limitPrior c.1 c.2
            have hcoherent : PriorCoherent family := by
              intro c d hcd
              exact D.state_refiningExtends _ _ hcd
            have hlength : b.1 < D.ordinalRecursor.length := by
              change b.1 < kappa.ord
              exact b.2
            change (D.state a).resolution.linked ⊆
              (D.ordinalRecursor.limitOrSeed b.1 hlimit limitPrior).linked
            rw [limitOrSeed_eq_properLimit D.ordinalRecursor b.1 hlimit
              hlength limitPrior hcoherent]
            exact (D.ordinalRecursor.properLimit b.1 hlength hlimit family
              hcoherent).linked ⟨a.1, hab⟩
      · exact Set.Subset.rfl

/-- Every strict-prior state refines the pre-successor base at the current
stage. -/
theorem state_refiningExtends_base_of_lt
    (D : DynamicResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure))
    {a b : RegularCardinal.Stage kappa} (hab : a < b) :
    (D.state a).resolution.RefiningExtends
      (D.base b (fun c _hcb ↦ D.state c)) := by
  classical
  unfold base
  split
  next hzero =>
    have habv : a.1 < b.1 := hab
    rw [hzero] at habv
    exact (not_lt_of_ge (bot_le : (0 : Ordinal.{u}) ≤ a.1) habv).elim
  next hnotzero =>
    split
    next hsucc =>
      let o : Ordinal.{u} := Classical.choose hsucc
      have ho : o + 1 = b.1 := Classical.choose_spec hsucc
      let c : RegularCardinal.Stage kappa := ⟨o, by
        exact (show o < b.1 by simpa only [← ho] using
          ((Order.lt_add_one_iff).2 (le_refl o))).trans b.2⟩
      have hac : a ≤ c := by
        change a.1 ≤ o
        apply (Order.lt_add_one_iff).1
        have habv : a.1 < b.1 := hab
        simpa only [ho] using habv
      simpa only [c, o] using D.state_refiningExtends c a hac
    next hnotsucc =>
      have hlimit : IsSuccLimit b.1 := by
        rcases Ordinal.zero_or_succ_or_isSuccLimit b.1 with h | h | h
        · exact (hnotzero h).elim
        · rcases h with ⟨o, ho⟩
          exact (hnotsucc ⟨o, by simpa only [ho]⟩).elim
        · exact h
      let limitPrior : ∀ o : Ordinal.{u}, o < b.1 → ResolutionState :=
        fun o ho ↦ (D.state ⟨o, by
          change o < kappa.ord
          exact ho.trans (show b.1 < kappa.ord from b.2)⟩).resolution
      let family : Set.Iio b.1 → ResolutionState := fun c ↦
        limitPrior c.1 c.2
      have hcoherent : PriorCoherent family := by
        intro c d hcd
        exact D.state_refiningExtends _ _ hcd
      have hlength : b.1 < D.ordinalRecursor.length := by
        change b.1 < kappa.ord
        exact b.2
      change (D.state a).resolution.RefiningExtends
        (D.ordinalRecursor.limitOrSeed b.1 hlimit limitPrior)
      rw [limitOrSeed_eq_properLimit D.ordinalRecursor b.1 hlimit
        hlength limitPrior hcoherent]
      exact (D.ordinalRecursor.properLimit b.1 hlength hlimit family
        hcoherent).extension ⟨a.1, hab⟩

/-- The first stage of the bounded dynamic run. -/
def zeroStage
    (D : DynamicResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure)) :
    RegularCardinal.Stage kappa :=
  ⟨0, (Cardinal.isSuccLimit_ord D.kappa_infinite).pos⟩

/-- The seed is absorbed by every dynamic stage. -/
theorem seed_refiningExtends_state
    (D : DynamicResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure))
    (a : RegularCardinal.Stage kappa) :
    D.seed.RefiningExtends (D.state a).resolution := by
  have hzero : D.seed.RefiningExtends (D.state D.zeroStage).resolution := by
    rw [D.state_resolution D.zeroStage]
    have hbase : D.base D.zeroStage (fun b _hba ↦ D.state b) = D.seed := by
      unfold base zeroStage
      simp only [↓reduceDIte]
    rw [hbase]
    refine D.successor.step_extends _ _
  exact hzero.trans (D.state_refiningExtends a D.zeroStage (by
    change (0 : Ordinal.{u}) ≤ a.1
    exact bot_le))

/-- The seed is also absorbed by the pre-successor base at every stage. -/
theorem seed_refiningExtends_base
    (D : DynamicResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure))
    (a : RegularCardinal.Stage kappa) :
    D.seed.RefiningExtends (D.base a (fun b _hba ↦ D.state b)) := by
  by_cases hzero : a.1 = 0
  · unfold base
    simp only [hzero, ↓reduceDIte]
    exact RefiningExtends.refl _
  · have hpos : D.zeroStage < a := by
      change (0 : Ordinal.{u}) < a.1
      exact (pos_iff_ne_zero.mpr hzero)
    exact (D.seed_refiningExtends_state D.zeroStage).trans
      (D.state_refiningExtends_base_of_lt hpos)

/-- Ambient-valued schedule of the dynamic run. -/
noncomputable def scheduled
    (D : DynamicResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure))
    (a : RegularCardinal.Stage kappa) : V :=
  D.request a (fun b _hba ↦ D.state b)

theorem scheduled_eq_of_emitted
    (D : DynamicResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure))
    {a : RegularCardinal.Stage kappa} {x : V}
    (h : (D.state a).emitted = some x) :
    D.scheduled a = x := by
  unfold scheduled request
  rw [← D.state_emitted a, h]
  rfl

/-- An emitted task really came from a strictly earlier real-terminal row. -/
theorem exists_prior_realTerminal_of_emitted
    (D : DynamicResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure))
    {a : RegularCardinal.Stage kappa} {x : V}
    (h : (D.state a).emitted = some x) :
    ∃ b < a, x ∈ (D.state b).resolution.blueprint.realPart.terminals := by
  have hselect : D.select a (fun b _hba ↦ D.state b) = some x := by
    rw [← D.state_emitted a]
    exact h
  unfold select at hselect
  cases htask : terminalQueueSelector.chooseTask D.kappa_infinite a
      (fun b hba ↦ (D.state b).toCausalState D) with
  | none =>
      simp only [htask, Option.map_none] at hselect
      cases hselect
  | some t =>
      have htx : t.2.1 = x := by
        simpa only [htask, Option.map_some, Option.some.injEq] using hselect
      refine ⟨t.1.1, t.1.2, ?_⟩
      simpa only [DynamicState.toCausalState, htx] using t.2.2

/-- A task emitted at `a` is still terminal in the pre-successor base or
has already acquired a real link to the target. -/
theorem emitted_ready_in_base
    (D : DynamicResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure))
    {a : RegularCardinal.Stage kappa} {x : V}
    (h : (D.state a).emitted = some x) :
    x ∈ (D.base a (fun b _hba ↦ D.state b)).blueprint.realPart.terminals ∨
      (D.base a (fun b _hba ↦ D.state b)).blueprint.RealLinksTo x B := by
  obtain ⟨b, hba, hxb⟩ := D.exists_prior_realTerminal_of_emitted h
  exact TerminalResolutionState.realTerminal_or_realLinksTo_of_realExtends
    (D.state_refiningExtends_base_of_lt hba).realExtends hxb

/-- Every named request is linked in its own output stage. -/
theorem scheduled_mem_linked
    (D : DynamicResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure))
    (a : RegularCardinal.Stage kappa) :
    D.scheduled a ∈ (D.state a).resolution.linked := by
  rw [D.state_resolution a]
  change D.request a (fun b _hba ↦ D.state b) ∈
    (D.successor.step (D.base a (fun b _hba ↦ D.state b))
      (D.request a (fun b _hba ↦ D.state b))).linked
  cases h : (D.state a).emitted with
  | none =>
      have hrequest : D.request a (fun b _hba ↦ D.state b) =
          D.bootstrap := by
        unfold request
        rw [← D.state_emitted a, h]
        rfl
      rw [hrequest]
      apply D.successor.terminal_or_completed_linked
      exact TerminalResolutionState.realTerminal_or_realLinksTo_of_realExtends
        (D.seed_refiningExtends_base a).realExtends D.bootstrap_terminal
  | some x =>
      have hrequest : D.request a (fun b _hba ↦ D.state b) = x := by
        exact D.scheduled_eq_of_emitted h
      rw [hrequest]
      exact D.successor.terminal_or_completed_linked _ _
        (D.emitted_ready_in_base h)

/-- The refining chain generated by the dynamic run. -/
noncomputable def dynamicChain
    (D : DynamicResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure)) :
    ResolutionChain
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure)
      (RegularCardinal.Stage kappa) where
  stage := fun a ↦ (D.state a).resolution
  refiningExtends := fun {_ _} hab ↦ D.state_refiningExtends _ _ hab

/-- The dynamic run is a successful all-real-terminal enumeration. -/
noncomputable def successfulDynamicEnumeration
    (D : DynamicResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure)) :
    SuccessfulResolutionEnumeration D.dynamicChain D.seed where
  scheduled := D.scheduled
  seed_absorbed := fun a ↦ (D.seed_refiningExtends_state a).realExtends
  scheduled_linked := D.scheduled_mem_linked
  covers_stage_realTerminals := by
    intro b x hx
    obtain ⟨a, ha⟩ := D.exists_state_emitted_eq_some_of_realTerminal hx
    exact ⟨a, D.scheduled_eq_of_emitted ha⟩

#print axioms CardinalInduction.RegularRows.mk_stage_Ici_eq_lift
#print axioms state_refiningExtends
#print axioms successfulDynamicEnumeration

end DynamicResolutionRecursor
end ReachableResolutionRecursor
end IndexedTerminalResolutionState
end LinkageBlueprint
end Blueprint
end Erdos599
