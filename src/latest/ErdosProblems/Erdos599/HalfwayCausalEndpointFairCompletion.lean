/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointSmallSweep
import ErdosProblems.Erdos599.HalfwayCausalEndpointStageSuccessor

/-!
# Fair completion in the actual causal endpoint graph

The countable sequence consists of complete sweeps of the preceding small
carrier. The exact final union therefore contains no unprocessed auxiliary
vertices. The successor is instantiated with the checked causal construction;
only its genuine cardinal-induction and subdivision premises remain explicit.
Initialization of the first stable club state is a separate obligation.
-/

namespace Erdos599.Blueprint.ColouredSafeEndpointBlueprint.StableState

open Set Cardinal Order DirectedPath Ladder LinkageBlueprint

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)} {Z : Set V}

/-- Every vertex of the output carrier, including those added during any
batch, has an actual finite real completion to the original target. -/
theorem exists_fullyCompleted (advance : HasCompletionSuccessor C Z) (seed : StableState C Z) :
    ∃ U : StableState C Z, seed.Extends U ∧ U.carrier ⊆ U.completed := by
  classical
  let batch : StableState C Z → StableState C Z :=
    fun S ↦ (exists_completedBatch advance S).choose
  have hbatch : ∀ S, S.Extends (batch S) ∧ S.carrier ⊆ (batch S).completed :=
    fun S ↦ (exists_completedBatch advance S).choose_spec
  let seq : Nat → StableState C Z := Nat.rec seed (fun _ S ↦ batch S)
  have hsucc : ∀ n, (seq n).Extends (seq (n + 1)) := fun n ↦ (hbatch (seq n)).1
  have hmono : ∀ ⦃i j⦄, i ≤ j → (seq i).Extends (seq j) := by
    intro i j hij
    induction hij with
    | refl => exact Extends.refl _
    | @step j _ ih => exact ih.trans (hsucc j)
  have hNat : Cardinal.lift.{u} #Nat ≤ Cardinal.lift.{0} kappa := by
    simpa only [Cardinal.mk_nat, Cardinal.lift_aleph0] using
      (Cardinal.aleph0_le_lift.mpr C.capacity_infinite : aleph0 ≤ Cardinal.lift.{0} kappa)
  obtain ⟨U, hU, hUV⟩ := exists_exactUpper seq hmono hNat
  refine ⟨U, hU 0, ?_⟩
  intro x hx
  obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp (hUV ▸ hx)
  have hdone : x ∈ (seq (n + 1)).completed := (hbatch (seq n)).2 hxn
  exact (hU (n + 1)).completed_mono hdone

#print axioms exists_fullyCompleted

end Erdos599.Blueprint.ColouredSafeEndpointBlueprint.StableState

namespace Erdos599.Blueprint.LinkageBlueprint.CausalSection9Rows

open Set Cardinal Order DirectedPath Ladder ColouredSafeEndpointBlueprint
open ColouredSafeEndpointBlueprint.StableState

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

theorem has_endpointCompletionSuccessor
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hC : C.ladder = finalLadder Gamma kappa hkappa hGamma seed hseed)
    (hext : _root_.Erdos599.CardinalInduction.ProtectedCardinalAssembly.ExtensionThroughFor
      Gamma kappa) (hsub : HasHereditarySubdivisionIncidence Gamma.graph) :
    HasCompletionSuccessor C (globalCarrier Gamma kappa hkappa hGamma seed hseed) := by
  intro S x hx
  obtain ⟨b, W, hb, hSb, hW, hWZ, hV, hE, hI, _hpop, hstable, hdone, haccount,
    _hterm, hpred⟩ := exists_endpointAdvance_to_target_at hkappa hGamma hseed C hC
      S.index_mem S.old_lt S.blueprint S.contained S.stable hext hsub hx
  let T : StableState C (globalCarrier Gamma kappa hkappa hGamma seed hseed) :=
    ⟨b, hb, S.old_lt.trans hSb, W, hW, hstable, hWZ⟩
  exact ⟨T, ⟨hSb.le, hV, hE, hI, haccount, hpred⟩, hdone⟩

/-- Fair completion with a constructed successor, not an assumed scheduling
or proper-limit provider. The supplied initial stable state is explicit. -/
theorem exists_endpointFullyCompleted
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hC : C.ladder = finalLadder Gamma kappa hkappa hGamma seed hseed)
    (hext : _root_.Erdos599.CardinalInduction.ProtectedCardinalAssembly.ExtensionThroughFor
      Gamma kappa) (hsub : HasHereditarySubdivisionIncidence Gamma.graph)
    (S : StableState C (globalCarrier Gamma kappa hkappa hGamma seed hseed)) :
    ∃ U : StableState C (globalCarrier Gamma kappa hkappa hGamma seed hseed),
      S.Extends U ∧ U.carrier ⊆ U.completed :=
  exists_fullyCompleted (has_endpointCompletionSuccessor hkappa hGamma hseed C hC hext hsub) S

#print axioms has_endpointCompletionSuccessor
#print axioms exists_endpointFullyCompleted

end Erdos599.Blueprint.LinkageBlueprint.CausalSection9Rows
