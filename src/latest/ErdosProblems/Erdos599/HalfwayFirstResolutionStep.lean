/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayInitialCertificate

/-!
# The first forward-only terminal-resolution step

This file connects the stable singleton start of the half-way scheduler to
the predecessor-preserving form of Assertion 9.34.  A genuine terminal
request produces a stable successor which links the request to `B`, really
extends the seed, and does not insert a new real predecessor before a vertex
already present in the seed.

The two states are packaged as a `ResolutionChain (Fin 2)`.  The local
predecessor condition is also promoted to the global chain condition needed
by the relation-limit construction.  Thus even the first nontrivial chain is
already accepted by `ResolutionChain.relationLimitCore`; no reverse-ray
assumption is postponed or hidden in the successor construction.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {T Z persistent B : Set V}

namespace TerminalResolutionState

/-- A universe-lifted two-point order.  `ResolutionChain` deliberately keeps
its index in the vertex universe, so the ordinary `Fin 2` must be lifted. -/
abbrev FirstResolutionIndex : Type u := ULift (Fin 2)

def firstResolutionZero : FirstResolutionIndex := ULift.up 0

def firstResolutionOne : FirstResolutionIndex := ULift.up 1

/-- A predecessor-preserving 9.34 successor really extends its input. -/
theorem realExtends_predecessorAdvance
    (compiler : PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) (hu : u ∈ S.blueprint.realPart.terminals) (huT : u ∈ T) :
    S.blueprint.RealExtends
      (S.predecessorAdvance compiler hpersistent u hu huT).blueprint B :=
  (predecessorAdvanceBlueprint_spec compiler hpersistent S u hu huT)
    |>.conclusion.realExtends

/-- The request executed by a predecessor-preserving successor is tracked. -/
@[simp] theorem linked_predecessorAdvance
    (compiler : PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) (hu : u ∈ S.blueprint.realPart.terminals) (huT : u ∈ T) :
    (S.predecessorAdvance compiler hpersistent u hu huT).linked =
      insert u S.linked :=
  rfl

theorem request_mem_linked_predecessorAdvance
    (compiler : PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) (hu : u ∈ S.blueprint.realPart.terminals) (huT : u ∈ T) :
    u ∈ (S.predecessorAdvance compiler hpersistent u hu huT).linked := by
  simp

/-- The successor contains the real `u`--`B` path supplied by 9.34. -/
theorem links_predecessorAdvance_request
    (compiler : PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) (hu : u ∈ S.blueprint.realPart.terminals) (huT : u ∈ T) :
    (S.predecessorAdvance compiler hpersistent u hu huT).blueprint.RealLinksTo
      u B :=
  (predecessorAdvanceBlueprint_spec compiler hpersistent S u hu huT)
    |>.conclusion.links

/-- The total predecessor-preserving step really extends its input; in the
nonterminal case this is reflexivity. -/
theorem realExtends_predecessorStep
    (compiler : PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) :
    S.blueprint.RealExtends
      (S.predecessorStep compiler hpersistent u).blueprint B := by
  by_cases hu : u ∈ S.blueprint.realPart.terminals ∧ u ∈ T
  · simpa [predecessorStep, hu] using
      S.realExtends_predecessorAdvance compiler hpersistent u hu.1 hu.2
  · simpa [predecessorStep, hu] using realExtends_refl S.blueprint B

/-- Execute a finite list using the strengthened successor selector.  This
is the coherent finite provenance for a predecessor-preserving chain: unlike
the ordinary `run`, it does not make a second independent classical choice
after forgetting the predecessor certificate. -/
noncomputable def predecessorRun
    (compiler : PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T) :
    List V → TerminalResolutionState Gamma Y kappa T Z persistent B →
      TerminalResolutionState Gamma Y kappa T Z persistent B
  | [], S => S
  | u :: requests, S =>
      predecessorRun compiler hpersistent requests
        (S.predecessorStep compiler hpersistent u)

@[simp] theorem predecessorRun_nil
    (compiler : PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B) :
    predecessorRun compiler hpersistent [] S = S :=
  rfl

@[simp] theorem predecessorRun_cons
    (compiler : PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) (requests : List V) :
    predecessorRun compiler hpersistent (u :: requests) S =
      predecessorRun compiler hpersistent requests
        (S.predecessorStep compiler hpersistent u) :=
  rfl

/-- A total predecessor step never forgets an already discharged request. -/
theorem linked_subset_predecessorStep
    (compiler : PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) :
    S.linked ⊆ (S.predecessorStep compiler hpersistent u).linked := by
  by_cases hu : u ∈ S.blueprint.realPart.terminals ∧ u ∈ T
  · simpa [predecessorStep, hu] using Set.subset_insert u S.linked
  · simp [predecessorStep, hu]

/-- Every finite predecessor run retains all requests discharged before it. -/
theorem linked_subset_predecessorRun
    (compiler : PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (requests : List V)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B) :
    S.linked ⊆ (predecessorRun compiler hpersistent requests S).linked := by
  induction requests generalizing S with
  | nil => exact Set.Subset.rfl
  | cons u requests ih =>
      exact (S.linked_subset_predecessorStep compiler hpersistent u).trans
        (ih (S.predecessorStep compiler hpersistent u))

/-- A finite predecessor run is a genuine real extension of its input. -/
theorem realExtends_predecessorRun
    (compiler : PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (requests : List V)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B) :
    S.blueprint.RealExtends
      (predecessorRun compiler hpersistent requests S).blueprint B := by
  induction requests generalizing S with
  | nil => exact realExtends_refl S.blueprint B
  | cons u requests ih =>
      exact realExtends_trans
        (S.realExtends_predecessorStep compiler hpersistent u)
        (ih (S.predecessorStep compiler hpersistent u))

/-- The local no-new-predecessor invariant composes along every finite
history selected by `predecessorRun`. -/
theorem noNewRealPredecessors_predecessorRun
    (compiler : PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (requests : List V)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B) :
    S.blueprint.NoNewRealPredecessorsTo
      (predecessorRun compiler hpersistent requests S).blueprint := by
  induction requests generalizing S with
  | nil => exact NoNewRealPredecessorsTo.refl S.blueprint
  | cons u requests ih =>
      exact NoNewRealPredecessorsTo.trans
        (S.noNewRealPredecessors_predecessorStep compiler hpersistent u)
        (ih (S.predecessorStep compiler hpersistent u))
        (S.realExtends_predecessorStep compiler hpersistent u).vertices_mono

/-- Executing a request which is currently eligible records it immediately,
and every later request in the same finite history preserves that record. -/
theorem request_mem_linked_predecessorRun_cons
    (compiler : PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) (requests : List V)
    (hu : u ∈ S.blueprint.realPart.terminals) (huT : u ∈ T) :
    u ∈ (predecessorRun compiler hpersistent (u :: requests) S).linked := by
  apply linked_subset_predecessorRun compiler hpersistent requests
  simp [predecessorStep, hu, huT]

/-- The seed and its first genuinely executed request, indexed in their
chronological order. -/
noncomputable def firstResolutionStage
    (compiler : PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (seed : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) (hu : u ∈ seed.blueprint.realPart.terminals) (huT : u ∈ T) :
    FirstResolutionIndex →
      TerminalResolutionState Gamma Y kappa T Z persistent B :=
  fun i ↦ Fin.cases seed
    (fun _ ↦ seed.predecessorAdvance compiler hpersistent u hu huT) i.down

@[simp] theorem firstResolutionStage_zero
    (compiler : PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (seed : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) (hu : u ∈ seed.blueprint.realPart.terminals) (huT : u ∈ T) :
    firstResolutionStage compiler hpersistent seed u hu huT
      firstResolutionZero = seed :=
  rfl

@[simp] theorem firstResolutionStage_one
    (compiler : PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (seed : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) (hu : u ∈ seed.blueprint.realPart.terminals) (huT : u ∈ T) :
    firstResolutionStage compiler hpersistent seed u hu huT
      firstResolutionOne =
      seed.predecessorAdvance compiler hpersistent u hu huT :=
  rfl

/-- The first genuine request is a two-node resolution chain.  Its phantom
ordinary compiler parameter is obtained by forgetting only the extra
predecessor-preservation proof from the same 9.34 compiler. -/
noncomputable def firstResolutionChain
    (compiler : PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (seed : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) (hu : u ∈ seed.blueprint.realPart.terminals) (huT : u ∈ T) :
    ResolutionChain FirstResolutionIndex
      (stable934Compiler_of_predecessorPreserving compiler) hpersistent where
  stage := firstResolutionStage compiler hpersistent seed u hu huT
  realExtends := by
    intro i j hij
    rcases i with ⟨i⟩
    rcases j with ⟨j⟩
    have hi : i = 0 ∨ i = 1 := by omega
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact realExtends_refl seed.blueprint B
    · exact seed.realExtends_predecessorAdvance compiler hpersistent u hu huT
    · change (1 : Fin 2) ≤ 0 at hij
      omega
    · exact realExtends_refl
        (seed.predecessorAdvance compiler hpersistent u hu huT).blueprint B

@[simp] theorem firstResolutionChain_stage_zero
    (compiler : PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (seed : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) (hu : u ∈ seed.blueprint.realPart.terminals) (huT : u ∈ T) :
    (firstResolutionChain compiler hpersistent seed u hu huT).stage
      firstResolutionZero = seed :=
  rfl

@[simp] theorem firstResolutionChain_stage_one
    (compiler : PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (seed : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) (hu : u ∈ seed.blueprint.realPart.terminals) (huT : u ∈ T) :
    (firstResolutionChain compiler hpersistent seed u hu huT).stage
      firstResolutionOne =
      seed.predecessorAdvance compiler hpersistent u hu huT :=
  rfl

/-- Both nodes have executable provenance through the strengthened finite
runner: the seed uses no requests and the successor uses the singleton
request list. -/
theorem firstResolutionChain_predecessorRun_reachable
    (compiler : PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (seed : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) (hu : u ∈ seed.blueprint.realPart.terminals) (huT : u ∈ T) :
    ∀ i, ∃ requests : List V,
      (firstResolutionChain compiler hpersistent seed u hu huT).stage i =
        predecessorRun compiler hpersistent requests seed := by
  intro i
  rcases i with ⟨i⟩
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · exact ⟨[], rfl⟩
  · refine ⟨[u], ?_⟩
    change
      (firstResolutionChain compiler hpersistent seed u hu huT).stage
          firstResolutionOne =
        predecessorRun compiler hpersistent [u] seed
    rw [firstResolutionChain_stage_one]
    simp [predecessorRun, predecessorStep, hu, huT]

/-- The local successor invariant is enough to certify the complete
two-stage real-extension chain. -/
theorem firstResolutionChain_noNewRealPredecessors
    (compiler : PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (seed : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) (hu : u ∈ seed.blueprint.realPart.terminals) (huT : u ∈ T) :
    (firstResolutionChain compiler hpersistent seed u hu huT).toRealExtensionChain
      |>.NoNewRealPredecessors := by
  constructor
  intro i j hij x y hx hyx
  rcases i with ⟨i⟩
  rcases j with ⟨j⟩
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact hyx
  · exact seed.noNewRealPredecessors_predecessorAdvance
      compiler hpersistent u hu huT hx hyx
  · change (1 : Fin 2) ≤ 0 at hij
    omega
  · exact hyx

/-- The first nontrivial chain already meets the well-foundedness side of
the relation-limit construction: finite-stage capture excludes directed
cycles and predecessor preservation excludes reverse rays. -/
theorem firstResolutionChain_relationLimitCore
    (compiler : PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (seed : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) (hu : u ∈ seed.blueprint.realPart.terminals) (huT : u ∈ T) :
    (firstResolutionChain compiler hpersistent seed u hu huT).toRealExtensionChain
      |>.RelationLimitCore :=
  (firstResolutionChain compiler hpersistent seed u hu huT).relationLimitCore
    (firstResolutionChain_noNewRealPredecessors
      compiler hpersistent seed u hu huT)

/-- All executable information produced by the first request, bundled for
the successor stage of a fair scheduler construction. -/
structure FirstResolutionStep
    (compiler : PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (seed : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) (hu : u ∈ seed.blueprint.realPart.terminals)
    (huT : u ∈ T) : Type u where
  successor : TerminalResolutionState Gamma Y kappa T Z persistent B
  successor_eq : successor =
    seed.predecessorAdvance compiler hpersistent u hu huT
  chain : ResolutionChain FirstResolutionIndex
    (stable934Compiler_of_predecessorPreserving compiler) hpersistent
  chain_eq : chain = firstResolutionChain compiler hpersistent seed u hu huT
  seed_realExtends : seed.blueprint.RealExtends successor.blueprint B
  no_new_real_predecessors :
    seed.blueprint.NoNewRealPredecessorsTo successor.blueprint
  request_linked : u ∈ successor.linked
  request_links : successor.blueprint.RealLinksTo u B
  chain_no_new_real_predecessors :
    chain.toRealExtensionChain.NoNewRealPredecessors
  chain_reachable : ∀ i, ∃ requests : List V,
    chain.stage i = predecessorRun compiler hpersistent requests seed

/-- Construct the first-step bundle without any input beyond the exact
predecessor-preserving 9.34 compiler and the fact that the request is a
current real terminal. -/
noncomputable def firstResolutionStep
    (compiler : PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (seed : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) (hu : u ∈ seed.blueprint.realPart.terminals) (huT : u ∈ T) :
    FirstResolutionStep compiler hpersistent seed u hu huT where
  successor := seed.predecessorAdvance compiler hpersistent u hu huT
  successor_eq := rfl
  chain := firstResolutionChain compiler hpersistent seed u hu huT
  chain_eq := rfl
  seed_realExtends :=
    seed.realExtends_predecessorAdvance compiler hpersistent u hu huT
  no_new_real_predecessors :=
    seed.noNewRealPredecessors_predecessorAdvance compiler hpersistent u hu huT
  request_linked :=
    seed.request_mem_linked_predecessorAdvance compiler hpersistent u hu huT
  request_links :=
    seed.links_predecessorAdvance_request compiler hpersistent u hu huT
  chain_no_new_real_predecessors :=
    firstResolutionChain_noNewRealPredecessors
      compiler hpersistent seed u hu huT
  chain_reachable :=
    firstResolutionChain_predecessorRun_reachable
      compiler hpersistent seed u hu huT

end TerminalResolutionState
end LinkageBlueprint
end Blueprint
end Erdos599
