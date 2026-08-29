/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCompatibleCertifiedScheduler

/-!
# Ladder-indexed reachable half-way scheduler

The printed Assertions 9.31 and 9.34 do not preserve one ladder slice: an
alpha-linkage-blueprint is advanced to a beta-linkage-blueprint for some
beta greater than alpha.  This module retains that index in the scheduler
state.  Both the slice and the closure set therefore depend on the current
stage.

The order-theoretic recursion uses the source-faithful pair
`RealExtends + PredecessorRefines`.  At a proper limit, the actual
linkage-blueprint and stability proof at the supremum slice are packaged in
`IndexedProperLimitConclusion`; this is the exact geometry boundary still
needed from the ladder construction, rather than an invalid fixed-slice
transport.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

universe u v w

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {persistent B : Set V}
variable {Stage : Type w} [LinearOrder Stage]
variable {slice closure : Stage → Set V}

/-- A scheduler state at its honest ladder index. -/
structure IndexedTerminalResolutionState
    (slice closure : Stage → Set V) where
  stageIndex : Stage
  blueprint : LinkageBlueprint Gamma Y kappa
  isBlueprint : blueprint.IsLinkageBlueprint
    (slice stageIndex) (closure stageIndex) persistent
  stable : blueprint.Stable (slice stageIndex) persistent
  linked : Set V
  links : ∀ x ∈ linked, blueprint.RealLinksTo x B

namespace IndexedTerminalResolutionState

/-- The heterogeneous composable transition invariant. -/
structure RefiningExtends
    (S U : IndexedTerminalResolutionState
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure) : Prop where
  realExtends : S.blueprint.RealExtends U.blueprint B
  predecessorRefines : S.blueprint.PredecessorRefines U.blueprint
  stage_mono : S.stageIndex ≤ U.stageIndex

@[refl] theorem RefiningExtends.refl
    (S : IndexedTerminalResolutionState
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure) :
    S.RefiningExtends S where
  realExtends := realExtends_refl S.blueprint B
  predecessorRefines := PredecessorRefines.refl S.blueprint
  stage_mono := le_rfl

@[trans] theorem RefiningExtends.trans
    {S U R : IndexedTerminalResolutionState
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure}
    (hSU : S.RefiningExtends U) (hUR : U.RefiningExtends R) :
    S.RefiningExtends R where
  realExtends := TerminalResolutionState.realExtends_trans
    hSU.realExtends hUR.realExtends
  predecessorRefines := PredecessorRefines.trans
    hSU.predecessorRefines hUR.predecessorRefines
      hSU.realExtends.1.1 hUR.realExtends.1.2
  stage_mono := hSU.stage_mono.trans hUR.stage_mono

/-- The indexed successor boundary.  In the terminal case it advances the
ladder index strictly; bookkeeping-only cases may retain it. -/
structure SchedulerSuccessor (slice closure : Stage → Set V) where
  step : IndexedTerminalResolutionState
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure → V →
    IndexedTerminalResolutionState
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure
  step_extends : ∀
      (S : IndexedTerminalResolutionState
        (Gamma := Gamma) (Y := Y) (kappa := kappa)
        (persistent := persistent) (B := B) slice closure) u,
    RefiningExtends S (step S u)
  stage_mono : ∀
      (S : IndexedTerminalResolutionState
        (Gamma := Gamma) (Y := Y) (kappa := kappa)
        (persistent := persistent) (B := B) slice closure) u,
    S.stageIndex ≤ (step S u).stageIndex
  stage_strict_of_terminal : ∀
      (S : IndexedTerminalResolutionState
        (Gamma := Gamma) (Y := Y) (kappa := kappa)
        (persistent := persistent) (B := B) slice closure) u,
    u ∈ S.blueprint.realPart.terminals →
      S.stageIndex < (step S u).stageIndex
  linked_mono : ∀
      (S : IndexedTerminalResolutionState
        (Gamma := Gamma) (Y := Y) (kappa := kappa)
        (persistent := persistent) (B := B) slice closure) u,
    S.linked ⊆ (step S u).linked
  terminal_or_completed_linked : ∀
      (S : IndexedTerminalResolutionState
        (Gamma := Gamma) (Y := Y) (kappa := kappa)
        (persistent := persistent) (B := B) slice closure) u,
    (u ∈ S.blueprint.realPart.terminals ∨ S.blueprint.RealLinksTo u B) →
      u ∈ (step S u).linked

/-- Coherence of a heterogeneous proper initial history. -/
def PriorCoherent {o : Ordinal.{u}}
    (prior : Set.Iio o → IndexedTerminalResolutionState
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure) : Prop :=
  ∀ a b, a ≤ b → (prior a).RefiningExtends (prior b)

/-- Coherent histories are automatically monotone in their actual ladder
indices. -/
theorem PriorCoherent.index_mono {o : Ordinal.{u}}
    {prior : Set.Iio o → IndexedTerminalResolutionState
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure}
    (h : PriorCoherent prior) {a b : Set.Iio o} (hab : a ≤ b) :
    (prior a).stageIndex ≤ (prior b).stageIndex :=
  (h a b hab).stage_mono

/-- The exact output required from the moving-slice version of Assertion
9.33 at one proper limit. -/
structure ProperLimitConclusion {o : Ordinal.{u}}
    (prior : Set.Iio o → IndexedTerminalResolutionState
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure) where
  limit : IndexedTerminalResolutionState
    (Gamma := Gamma) (Y := Y) (kappa := kappa)
    (persistent := persistent) (B := B) slice closure
  extension : ∀ a, (prior a).RefiningExtends limit
  linked : ∀ a, (prior a).linked ⊆ limit.linked
  index_upper : ∀ a, (prior a).stageIndex ≤ limit.stageIndex
  index_least : ∀ b : Stage,
    (∀ a, (prior a).stageIndex ≤ b) → limit.stageIndex ≤ b

/-- Reachable-history form of the heterogeneous proper-limit compiler. -/
def ProperLimitCompiler (slice closure : Stage → Set V)
    (length : Ordinal.{u}) : Prop :=
  ∀ (o : Ordinal.{u}), o < length → IsSuccLimit o →
    (prior : Set.Iio o → IndexedTerminalResolutionState
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure) →
    PriorCoherent prior → Nonempty (ProperLimitConclusion prior)

/-- A bounded heterogeneous reachable-state recursor. -/
structure ReachableResolutionRecursor
    (slice closure : Stage → Set V) where
  length : Ordinal.{u}
  seed : IndexedTerminalResolutionState
    (Gamma := Gamma) (Y := Y) (kappa := kappa)
    (persistent := persistent) (B := B) slice closure
  successor : SchedulerSuccessor
    (Gamma := Gamma) (Y := Y) (kappa := kappa)
    (persistent := persistent) (B := B) slice closure
  properLimit : ∀ (o : Ordinal.{u}), o < length → IsSuccLimit o →
    (prior : Set.Iio o → IndexedTerminalResolutionState
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure) →
    PriorCoherent prior → ProperLimitConclusion prior

namespace ReachableResolutionRecursor

noncomputable def ofCompilers
    (seed : IndexedTerminalResolutionState
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure)
    (successor : SchedulerSuccessor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure)
    (length : Ordinal.{u})
    (limit : ProperLimitCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure length) :
    ReachableResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure where
  length := length
  seed := seed
  successor := successor
  properLimit := fun o hoLength ho prior hcoherent ↦
    (limit o hoLength ho prior hcoherent).some

noncomputable def limitOrSeed
    (R : ReachableResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure)
    (o : Ordinal.{u}) (ho : IsSuccLimit o)
    (prior : ∀ a : Ordinal.{u}, a < o →
      IndexedTerminalResolutionState
        (Gamma := Gamma) (Y := Y) (kappa := kappa)
        (persistent := persistent) (B := B) slice closure) :
    IndexedTerminalResolutionState
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure := by
  classical
  let family : Set.Iio o → IndexedTerminalResolutionState
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure :=
    fun a ↦ prior a.1 a.2
  exact if hoLength : o < R.length then
    if h : PriorCoherent family then
      (R.properLimit o hoLength ho family h).limit
    else R.seed
  else R.seed

noncomputable def state
    (R : ReachableResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure)
    (request : Ordinal.{u} → V) (o : Ordinal.{u}) :
    IndexedTerminalResolutionState
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure :=
  Ordinal.limitRecOn o R.seed
    (fun a state ↦ R.successor.step state (request a))
    (fun o ho prior ↦ R.limitOrSeed o ho prior)

@[simp] theorem state_zero
    (R : ReachableResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure)
    (request : Ordinal.{u} → V) :
    R.state request 0 = R.seed := by
  simp [state]

@[simp] theorem state_add_one
    (R : ReachableResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure)
    (request : Ordinal.{u} → V) (o : Ordinal.{u}) :
    R.state request (o + 1) =
      R.successor.step (R.state request o) (request o) := by
  simp [state]

theorem state_limit
    (R : ReachableResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure)
    (request : Ordinal.{u} → V) (o : Ordinal.{u}) (ho : IsSuccLimit o) :
    R.state request o = R.limitOrSeed o ho
      (fun a ha ↦ R.state request a) := by
  simpa [state] using
    (Ordinal.limitRecOn_limit o R.seed
      (fun a state ↦ R.successor.step state (request a))
      (fun o ho prior ↦ R.limitOrSeed o ho prior) ho)

theorem state_extends_below
    (R : ReachableResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure)
    (request : Ordinal.{u} → V) :
    ∀ b, b < R.length → ∀ a, a ≤ b →
      (R.state request a).RefiningExtends (R.state request b) := by
  classical
  intro b hbLength
  induction b using Ordinal.limitRecOn with
  | zero =>
      intro a ha
      have : a = 0 := bot_unique ha
      subst a
      exact RefiningExtends.refl _
  | add_one b ih =>
      intro a ha
      rcases ha.lt_or_eq with hab | rfl
      · have hab' : a ≤ b := (Order.lt_add_one_iff).1 hab
        rw [R.state_add_one request b]
        have hb : b < b + 1 := (Order.lt_add_one_iff).2 le_rfl
        exact (ih (hb.trans hbLength) a hab').trans
          (R.successor.step_extends _ _)
      · exact RefiningExtends.refl _
  | limit b hb ih =>
      intro a ha
      rcases ha.lt_or_eq with hab | rfl
      · let prior : Set.Iio b → IndexedTerminalResolutionState
            (Gamma := Gamma) (Y := Y) (kappa := kappa)
            (persistent := persistent) (B := B) slice closure :=
          fun c ↦ R.state request c.1
        have hcoherent : PriorCoherent prior := by
          intro c d hcd
          exact ih d.1 d.2 (d.2.trans hbLength) c.1 hcd
        rw [R.state_limit request b hb]
        rw [limitOrSeed, dif_pos hbLength]
        change (R.state request a).RefiningExtends
          (if h : PriorCoherent prior then
            (R.properLimit b hbLength hb prior h).limit else R.seed)
        rw [dif_pos hcoherent]
        exact (R.properLimit b hbLength hb prior hcoherent).extension ⟨a, hab⟩
      · exact RefiningExtends.refl _

theorem state_linked_mono_below
    (R : ReachableResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure)
    (request : Ordinal.{u} → V) :
    ∀ b, b < R.length → ∀ a, a ≤ b →
      (R.state request a).linked ⊆ (R.state request b).linked := by
  classical
  intro b hbLength
  induction b using Ordinal.limitRecOn with
  | zero =>
      intro a ha
      have : a = 0 := bot_unique ha
      subst a
      exact Set.Subset.rfl
  | add_one b ih =>
      intro a ha
      rcases ha.lt_or_eq with hab | rfl
      · have hab' : a ≤ b := (Order.lt_add_one_iff).1 hab
        rw [R.state_add_one request b]
        have hb : b < b + 1 := (Order.lt_add_one_iff).2 le_rfl
        exact (ih (hb.trans hbLength) a hab').trans
          (R.successor.linked_mono _ _)
      · exact Set.Subset.rfl
  | limit b hb ih =>
      intro a ha
      rcases ha.lt_or_eq with hab | rfl
      · let prior : Set.Iio b → IndexedTerminalResolutionState
            (Gamma := Gamma) (Y := Y) (kappa := kappa)
            (persistent := persistent) (B := B) slice closure :=
          fun c ↦ R.state request c.1
        have hcoherent : PriorCoherent prior := by
          intro c d hcd
          exact R.state_extends_below request d.1
            (d.2.trans hbLength) c.1 hcd
        rw [R.state_limit request b hb]
        rw [limitOrSeed, dif_pos hbLength]
        change (R.state request a).linked ⊆
          (if h : PriorCoherent prior then
            (R.properLimit b hbLength hb prior h).limit else R.seed).linked
        rw [dif_pos hcoherent]
        exact (R.properLimit b hbLength hb prior hcoherent).linked ⟨a, hab⟩
      · exact Set.Subset.rfl


/-! ## Cofinal repeated-request run -/

/-- The repeated request order used by the indexed run. -/
abbrev repeatedRequestLength (X : Type u) [LinearOrder X]
    [WellFoundedLT X] : Ordinal.{u} :=
  TerminalResolutionState.ReachableResolutionRecursor.repeatedRequestLength X

/-- Bootstrap the indexed run by resolving one actual real terminal. -/
noncomputable def repeatedRecursor
    {Request : Set V} [LinearOrder Request] [WellFoundedLT Request]
    (successor : SchedulerSuccessor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure)
    (seed : IndexedTerminalResolutionState
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure)
    (u₀ : V) (hu₀ : u₀ ∈ seed.blueprint.realPart.terminals)
    (limit : ProperLimitCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure
      (repeatedRequestLength Request)) :
    ReachableResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure :=
  ofCompilers (successor.step seed u₀) successor
    (repeatedRequestLength Request) limit

/-- The state immediately after one repeated request. -/
noncomputable def repeatedStage
    {Request : Set V} [LinearOrder Request] [WellFoundedLT Request]
    (R : ReachableResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure)
    (fallback : V)
    (i : TerminalResolutionState.RepeatedRequestIndex Request) :
    IndexedTerminalResolutionState
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure :=
  R.state
    (TerminalResolutionState.ReachableResolutionRecursor.repeatedOrdinalRequest
      (Z := Request) fallback)
    (Ordinal.typein
      (fun a b : TerminalResolutionState.RepeatedRequestIndex Request ↦ a < b) i + 1)

/-- A chain of genuinely indexed scheduler states. -/
structure ResolutionChain
    (I : Type v) [LinearOrder I] where
  stage : I → IndexedTerminalResolutionState
    (Gamma := Gamma) (Y := Y) (kappa := kappa)
    (persistent := persistent) (B := B) slice closure
  refiningExtends : ∀ ⦃i j : I⦄, i ≤ j →
    (stage i).RefiningExtends (stage j)

/-- Successor states of the repeated run form a refining chain. -/
noncomputable def repeatedChain
    {Request : Set V} [LinearOrder Request] [WellFoundedLT Request]
    (successor : SchedulerSuccessor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure)
    (seed : IndexedTerminalResolutionState
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure)
    (u₀ : V) (hu₀ : u₀ ∈ seed.blueprint.realPart.terminals)
    (limit : ProperLimitCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure
      (repeatedRequestLength Request)) :
    ResolutionChain
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure)
      (TerminalResolutionState.RepeatedRequestIndex Request) := by
  let R := repeatedRecursor successor seed u₀ hu₀ limit
  exact {
    stage := repeatedStage R u₀
    refiningExtends := by
      intro i j hij
      have hordinal :
          Ordinal.typein
              (fun a b : TerminalResolutionState.RepeatedRequestIndex Request ↦ a < b) i + 1 ≤
            Ordinal.typein
              (fun a b : TerminalResolutionState.RepeatedRequestIndex Request ↦ a < b) j + 1 := by
        simpa using
          ((Ordinal.add_le_add_iff_right 1).2
            ((Ordinal.typein_le_typein
              (fun a b : TerminalResolutionState.RepeatedRequestIndex Request ↦ a < b)).2
                (not_lt_of_ge hij)))
      exact R.state_extends_below
        (TerminalResolutionState.ReachableResolutionRecursor.repeatedOrdinalRequest
          (Z := Request) u₀) _
        (TerminalResolutionState.ReachableResolutionRecursor.typein_add_one_lt_repeatedRequestLength j)
        _ hordinal }

/-- Name the actual request whenever it is currently terminal or already
completed; otherwise name the permanently linked bootstrap request. -/
noncomputable def repeatedScheduled
    {Request : Set V} [LinearOrder Request] [WellFoundedLT Request]
    (successor : SchedulerSuccessor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure)
    (seed : IndexedTerminalResolutionState
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure)
    (u₀ : V) (hu₀ : u₀ ∈ seed.blueprint.realPart.terminals)
    (limit : ProperLimitCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure
      (repeatedRequestLength Request))
    (i : TerminalResolutionState.RepeatedRequestIndex Request) : V := by
  classical
  let R := repeatedRecursor successor seed u₀ hu₀ limit
  let pre := R.state
    (TerminalResolutionState.ReachableResolutionRecursor.repeatedOrdinalRequest
      (Z := Request) u₀)
    (Ordinal.typein
      (fun a b : TerminalResolutionState.RepeatedRequestIndex Request ↦ a < b) i)
  let u : V := (TerminalResolutionState.repeatedRequest i : Request)
  exact if u ∈ pre.blueprint.realPart.terminals ∨
      pre.blueprint.RealLinksTo u B then u else u₀

theorem repeatedScheduled_mem_linked
    {Request : Set V} [LinearOrder Request] [WellFoundedLT Request]
    (successor : SchedulerSuccessor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure)
    (seed : IndexedTerminalResolutionState
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure)
    (u₀ : V) (hu₀ : u₀ ∈ seed.blueprint.realPart.terminals)
    (limit : ProperLimitCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure
      (repeatedRequestLength Request))
    (i : TerminalResolutionState.RepeatedRequestIndex Request) :
    repeatedScheduled successor seed u₀ hu₀ limit i ∈
      ((repeatedChain successor seed u₀ hu₀ limit).stage i).linked := by
  classical
  let R := repeatedRecursor successor seed u₀ hu₀ limit
  let request :=
    TerminalResolutionState.ReachableResolutionRecursor.repeatedOrdinalRequest
      (Z := Request) u₀
  let rank := Ordinal.typein
    (fun a b : TerminalResolutionState.RepeatedRequestIndex Request ↦ a < b) i
  let u : V := (TerminalResolutionState.repeatedRequest i : Request)
  by_cases hready : u ∈ (R.state request rank).blueprint.realPart.terminals ∨
      (R.state request rank).blueprint.RealLinksTo u B
  · change (if _ then u else u₀) ∈ _
    rw [if_pos hready]
    change u ∈ (R.state request (rank + 1)).linked
    rw [R.state_add_one request rank]
    have hrequest : request rank = u := by
      simpa only [request, rank, u] using
        TerminalResolutionState.ReachableResolutionRecursor.repeatedOrdinalRequest_typein
          (Z := Request) u₀ i
    rw [hrequest]
    exact successor.terminal_or_completed_linked _ u hready
  · change (if _ then u else u₀) ∈ _
    rw [if_neg hready]
    have hu₀linked : u₀ ∈ R.seed.linked :=
      successor.terminal_or_completed_linked seed u₀ (Or.inl hu₀)
    have hmono := R.state_linked_mono_below request (rank + 1)
      (TerminalResolutionState.ReachableResolutionRecursor.typein_add_one_lt_repeatedRequestLength i)
      0 bot_le
    exact hmono (by simpa only [R.state_zero request] using hu₀linked)

theorem repeatedChain_seed_absorbed
    {Request : Set V} [LinearOrder Request] [WellFoundedLT Request]
    (successor : SchedulerSuccessor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure)
    (seed : IndexedTerminalResolutionState
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure)
    (u₀ : V) (hu₀ : u₀ ∈ seed.blueprint.realPart.terminals)
    (limit : ProperLimitCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure
      (repeatedRequestLength Request))
    (i : TerminalResolutionState.RepeatedRequestIndex Request) :
    seed.blueprint.RealExtends
      ((repeatedChain successor seed u₀ hu₀ limit).stage i).blueprint B := by
  let R := repeatedRecursor successor seed u₀ hu₀ limit
  let request :=
    TerminalResolutionState.ReachableResolutionRecursor.repeatedOrdinalRequest
      (Z := Request) u₀
  change seed.blueprint.RealExtends
    (R.state request
      (Ordinal.typein
        (fun a b : TerminalResolutionState.RepeatedRequestIndex Request ↦ a < b) i + 1)).blueprint B
  have hseed := (successor.step_extends seed u₀).realExtends
  have hrun := R.state_extends_below request
    (Ordinal.typein
      (fun a b : TerminalResolutionState.RepeatedRequestIndex Request ↦ a < b) i + 1)
    (TerminalResolutionState.ReachableResolutionRecursor.typein_add_one_lt_repeatedRequestLength i)
    0 bot_le
  exact TerminalResolutionState.realExtends_trans hseed
    (by
      simpa [R, repeatedRecursor, ofCompilers] using hrun.realExtends)

/-- Every real terminal at a repeated stage is named by a later request. -/
theorem repeatedChain_covers_stage_realTerminals
    {Request : Set V} [LinearOrder Request] [WellFoundedLT Request]
    (successor : SchedulerSuccessor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure)
    (seed : IndexedTerminalResolutionState
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure)
    (u₀ : V) (hu₀ : u₀ ∈ seed.blueprint.realPart.terminals)
    (limit : ProperLimitCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure
      (repeatedRequestLength Request))
    (hclosure : ∀ s, closure s ⊆ Request)
    (i : TerminalResolutionState.RepeatedRequestIndex Request) (x : V)
    (hx : x ∈ ((repeatedChain successor seed u₀ hu₀ limit).stage i).blueprint.realPart.terminals) :
    ∃ j, repeatedScheduled successor seed u₀ hu₀ limit j = x := by
  classical
  let R := repeatedRecursor successor seed u₀ hu₀ limit
  let request :=
    TerminalResolutionState.ReachableResolutionRecursor.repeatedOrdinalRequest
      (Z := Request) u₀
  have hxvertex : x ∈
      ((repeatedChain successor seed u₀ hu₀ limit).stage i).blueprint.vertexSet := by
    simpa only [realPart_vertices] using hx.1
  have hxRequest : x ∈ Request := hclosure _
    (((repeatedChain successor seed u₀ hu₀ limit).stage i).isBlueprint.vertices_closed
      hxvertex)
  let xRequest : Request := ⟨x, hxRequest⟩
  obtain ⟨j, hij, hjrequest⟩ :=
    TerminalResolutionState.ReachableResolutionRecursor.exists_strictly_later_repeatedRequest
      i xRequest
  have hord :
      Ordinal.typein
          (fun a b : TerminalResolutionState.RepeatedRequestIndex Request ↦ a < b) i + 1 ≤
        Ordinal.typein
          (fun a b : TerminalResolutionState.RepeatedRequestIndex Request ↦ a < b) j :=
    (add_one_le_iff).2 ((Ordinal.typein_lt_typein _).2 hij)
  have hextends := R.state_extends_below request
    (Ordinal.typein
      (fun a b : TerminalResolutionState.RepeatedRequestIndex Request ↦ a < b) j)
    (Ordinal.typein_lt_type _ j)
    (Ordinal.typein
      (fun a b : TerminalResolutionState.RepeatedRequestIndex Request ↦ a < b) i + 1) hord
  have hready : x ∈
      (R.state request
        (Ordinal.typein
          (fun a b : TerminalResolutionState.RepeatedRequestIndex Request ↦ a < b) j)).blueprint.realPart.terminals ∨
      (R.state request
        (Ordinal.typein
          (fun a b : TerminalResolutionState.RepeatedRequestIndex Request ↦ a < b) j)).blueprint.RealLinksTo x B := by
    apply TerminalResolutionState.realTerminal_or_realLinksTo_of_realExtends
      hextends.realExtends
    simpa only [repeatedChain, repeatedStage, R, request] using hx
  refine ⟨j, ?_⟩
  have hjvalue : (TerminalResolutionState.repeatedRequest j : Request).1 = x :=
    congrArg Subtype.val hjrequest
  simp only [repeatedScheduled]
  change (if (TerminalResolutionState.repeatedRequest j : Request).1 ∈
      (R.state request
        (Ordinal.typein
          (fun a b : TerminalResolutionState.RepeatedRequestIndex Request ↦ a < b) j)).blueprint.realPart.terminals ∨
      (R.state request
        (Ordinal.typein
          (fun a b : TerminalResolutionState.RepeatedRequestIndex Request ↦ a < b) j)).blueprint.RealLinksTo
            (TerminalResolutionState.repeatedRequest j : Request).1 B
    then (TerminalResolutionState.repeatedRequest j : Request).1 else u₀) = x
  rw [hjvalue, if_pos hready]

/-- Execution-only output of the indexed cofinal sweep. -/
structure SuccessfulResolutionEnumeration
    {I : Type v} [LinearOrder I]
    (C : ResolutionChain
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B)
      (slice := slice) (closure := closure) I)
    (seed : IndexedTerminalResolutionState
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure) where
  scheduled : I → V
  seed_absorbed : ∀ i,
    seed.blueprint.RealExtends (C.stage i).blueprint B
  scheduled_linked : ∀ i, scheduled i ∈ (C.stage i).linked
  covers_stage_realTerminals : ∀ i x,
    x ∈ (C.stage i).blueprint.realPart.terminals →
      ∃ j, scheduled j = x

noncomputable def successfulRepeatedEnumeration
    {Request : Set V} [LinearOrder Request] [WellFoundedLT Request]
    (successor : SchedulerSuccessor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure)
    (seed : IndexedTerminalResolutionState
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure)
    (u₀ : V) (hu₀ : u₀ ∈ seed.blueprint.realPart.terminals)
    (limit : ProperLimitCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := persistent) (B := B) slice closure
      (repeatedRequestLength Request))
    (hclosure : ∀ s, closure s ⊆ Request) :
    SuccessfulResolutionEnumeration
      (slice := slice) (closure := closure)
      (repeatedChain successor seed u₀ hu₀ limit) seed where
  scheduled := repeatedScheduled successor seed u₀ hu₀ limit
  seed_absorbed :=
    repeatedChain_seed_absorbed successor seed u₀ hu₀ limit
  scheduled_linked :=
    repeatedScheduled_mem_linked successor seed u₀ hu₀ limit
  covers_stage_realTerminals :=
    repeatedChain_covers_stage_realTerminals successor seed u₀ hu₀ limit hclosure

end ReachableResolutionRecursor
end IndexedTerminalResolutionState
end LinkageBlueprint
end Blueprint
end Erdos599

