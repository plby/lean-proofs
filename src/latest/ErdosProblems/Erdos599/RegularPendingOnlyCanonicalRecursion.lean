/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularDirectInstalledStage

/-!
# Pending-only canonical recursion for the regular splice

The recursive payload already records the two invariants which genuinely
survive a selected/clean successor: tightness and roof containment of its
pending subfamily. Completed target components need not remain below later
ladder roofs. This module removes the obsolete whole-row roof field from the
canonical scheduler and retains the exact installed stage which proves the
ordinary recursive validity contract.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularPendingOnlyCanonicalRecursion

universe u

variable {V : Type u}

structure CanonicalStage
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z A : Set V) (request : Ladder.Stage kappa → Option A)
    (i : Ladder.Stage kappa)
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A) where
  installed : RegularDirectInstalledStage.DirectInstalledStage
    G L Sigma Z A request i previous

namespace CanonicalStage

def payload
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (S : CanonicalStage G L Sigma Z A request i previous) :
    RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A :=
  S.installed.payload

theorem payload_valid
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (S : CanonicalStage G L Sigma Z A request i previous) :
    RegularCompletedPendingSplice.IsValidRecursiveStage request i previous
      S.payload :=
  S.installed.valid

end CanonicalStage

structure CanonicalState
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z A : Set V) (request : Ladder.Stage kappa → Option A) where
  producerIndex : Ladder.Stage kappa
  producerPrevious : ∀ j : Ladder.Stage kappa, j < producerIndex →
    RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A
  producer : CanonicalStage G L Sigma Z A request producerIndex
    producerPrevious

namespace CanonicalState

def payload
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    (S : CanonicalState G L Sigma Z A request) :
    RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A :=
  S.producer.payload

def ofStage
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (S : CanonicalStage G L Sigma Z A request i previous) :
    CanonicalState G L Sigma Z A request where
  producerIndex := i
  producerPrevious := previous
  producer := S

@[simp] theorem payload_ofStage
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (S : CanonicalStage G L Sigma Z A request i previous) :
    (ofStage S).payload = S.payload :=
  rfl

end CanonicalState

def projectedHistory
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    (i : Ladder.Stage kappa)
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      CanonicalState G L Sigma Z A request) :
    ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A :=
  fun j hji ↦ (previous j hji).payload

def IsCanonicalAt
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    (i : Ladder.Stage kappa)
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      CanonicalState G L Sigma Z A request)
    (state : CanonicalState G L Sigma Z A request) : Prop :=
  ∃ S : CanonicalStage G L Sigma Z A request i
      (projectedHistory i previous),
    state = CanonicalState.ofStage S

def HasCanonicalStageProvider
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z A : Set V) (request : Ladder.Stage kappa → Option A) : Prop :=
  ∀ (i : Ladder.Stage kappa)
      (previous : ∀ j : Ladder.Stage kappa, j < i →
        CanonicalState G L Sigma Z A request),
    (∀ j (hji : j < i),
      IsCanonicalAt j
        (fun l hlj ↦ previous l (lt_trans hlj hji))
        (previous j hji)) →
      Nonempty (CanonicalStage G L Sigma Z A request i
        (projectedHistory i previous))

structure CanonicalSpliceOperation
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z A : Set V) (request : Ladder.Stage kappa → Option A) where
  build : ∀ i : Ladder.Stage kappa,
    (∀ j : Ladder.Stage kappa, j < i →
      CanonicalState G L Sigma Z A request) →
      CanonicalState G L Sigma Z A request
  valid : ∀ i previous,
    (∀ j (hji : j < i),
      IsCanonicalAt j
        (fun l hlj ↦ previous l (lt_trans hlj hji))
        (previous j hji)) →
      ∃ S : CanonicalStage G L Sigma Z A request i
          (projectedHistory i previous),
        build i previous = CanonicalState.ofStage S

theorem exists_canonicalSpliceOperation
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    (fallback : CanonicalState G L Sigma Z A request)
    (hprovider : HasCanonicalStageProvider G L Sigma Z A request) :
    ∃ _R : CanonicalSpliceOperation G L Sigma Z A request, True := by
  let build : ∀ i : Ladder.Stage kappa,
      (∀ j : Ladder.Stage kappa, j < i →
        CanonicalState G L Sigma Z A request) →
        CanonicalState G L Sigma Z A request :=
    fun i previous ↦ by
      classical
      exact if h : ∃ S : CanonicalStage G L Sigma Z A request i
          (projectedHistory i previous), True then
        CanonicalState.ofStage (Classical.choose h)
      else fallback
  let R : CanonicalSpliceOperation G L Sigma Z A request :=
    { build := build
      valid := by
        intro i previous hprevious
        obtain ⟨S⟩ := hprovider i previous hprevious
        have hexists : ∃ S : CanonicalStage G L Sigma Z A request i
            (projectedHistory i previous), True := ⟨S, trivial⟩
        refine ⟨Classical.choose hexists, ?_⟩
        dsimp only [build]
        rw [dif_pos hexists] }
  exact ⟨R, trivial⟩

namespace CanonicalSpliceOperation

variable {kappa : Cardinal.{u}} {G : DWeb V}
variable {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
variable {Z A : Set V} {request : Ladder.Stage kappa → Option A}

noncomputable def state
    (R : CanonicalSpliceOperation G L Sigma Z A request)
    (i : Ladder.Stage kappa) : CanonicalState G L Sigma Z A request :=
  WellFounded.fix wellFounded_lt
    (fun i previous ↦ R.build i previous) i

theorem state_eq
    (R : CanonicalSpliceOperation G L Sigma Z A request)
    (i : Ladder.Stage kappa) :
    R.state i = R.build i (fun j _hji ↦ R.state j) := by
  exact WellFounded.fix_eq wellFounded_lt
    (fun i previous ↦ R.build i previous) i

theorem state_provenance
    (R : CanonicalSpliceOperation G L Sigma Z A request)
    (i : Ladder.Stage kappa) :
    ∃ S : CanonicalStage G L Sigma Z A request i
        (fun j _hji ↦ (R.state j).payload),
      R.state i = CanonicalState.ofStage S := by
  rw [R.state_eq i]
  apply R.valid
  intro j hji
  exact R.state_provenance j
termination_by i.1
decreasing_by exact hji

noncomputable def payload
    (R : CanonicalSpliceOperation G L Sigma Z A request)
    (i : Ladder.Stage kappa) :
    RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A :=
  (R.state i).payload

theorem payload_valid
    (R : CanonicalSpliceOperation G L Sigma Z A request)
    (i : Ladder.Stage kappa) :
    RegularCompletedPendingSplice.IsValidRecursiveStage request i
      (fun j _hji ↦ R.payload j) (R.payload i) := by
  obtain ⟨S, hS⟩ := R.state_provenance i
  rw [payload, hS]
  exact S.payload_valid

noncomputable def growingChain
    (R : CanonicalSpliceOperation G L Sigma Z A request) :
    G.GrowingWarpChain (Ladder.Stage kappa) where
  stage i := (R.payload i).row
  isWarp i := (R.payload i).isWarp
  grows := by
    intro i j hij p hp
    rcases hij.lt_or_eq with hij | rfl
    · exact (R.payload_valid j).extends_previous i hij |>.1 p hp
    · exact ⟨p, hp, G.extends_refl p⟩

@[simp] theorem growingChain_stage
    (R : CanonicalSpliceOperation G L Sigma Z A request)
    (i : Ladder.Stage kappa) :
    R.growingChain.stage i = (R.payload i).row :=
  rfl

theorem initialUnion_growingChain
    (R : CanonicalSpliceOperation G L Sigma Z A request)
    (i0 : Ladder.Stage kappa) :
    R.growingChain.initialUnion = A := by
  apply Set.Subset.antisymm
  · rintro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx
    change x ∈ G.initialSet (R.payload i).row at hxi
    rw [(R.payload i).initialSet_eq] at hxi
    exact hxi
  · intro x hx
    exact Set.mem_iUnion.2 ⟨i0,
      (R.payload i0).initialSet_eq.symm ▸ hx⟩

theorem isCompletedPendingSplice
    (R : CanonicalSpliceOperation G L Sigma Z A request)
    (i0 : Ladder.Stage kappa)
    (hrequest : ∀ a : A, ∃ i, request i = some a) :
    RegularCompletedPendingSplice.IsCompletedPendingSplice
      G A Z R.growingChain := by
  refine
    { initialUnion_eq := R.initialUnion_growingChain i0
      vertices_closed := ?_
      eventually_completed := ?_ }
  · intro i
    exact (R.payload i).vertices_closed
  · intro a
    obtain ⟨i, hi⟩ := hrequest a
    obtain ⟨p, hp, hpinitial⟩ :=
      (R.payload_valid i).realizes_request a hi
    exact ⟨i, p, hp.1, hpinitial, hp.2⟩

theorem exists_internal_linkage
    (R : CanonicalSpliceOperation G L Sigma Z A request)
    (hNorm : G.IsNormalized) (hA : A ⊆ G.source)
    (i0 : Ladder.Stage kappa)
    (hrequest : ∀ a : A, ∃ i, request i = some a) :
    ∃ P : Set G.DPath,
      IsLinkageBetween G A G.target P ∧ G.vertexSet P ⊆ Z := by
  exact (R.isCompletedPendingSplice i0 hrequest).exists_internal_linkage
    hNorm hA

end CanonicalSpliceOperation

theorem exists_internal_linkage_of_canonicalStageProvider
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z : Set V}
    (hNorm : G.IsNormalized)
    (hAcard : #↑(G.source ∩ Z) ≤ kappa)
    (i0 : Ladder.Stage kappa)
    (hi0 : ∀ j : Ladder.Stage kappa, ¬ j < i0)
    (hprovider : ∀ request :
      Ladder.Stage kappa → Option ↑(G.source ∩ Z),
      HasCanonicalStageProvider G L Sigma Z (G.source ∩ Z) request) :
    ∃ P : Set G.DPath,
      IsLinkageBetween G (G.source ∩ Z) G.target P ∧
        G.vertexSet P ⊆ Z := by
  obtain ⟨request, hrequest⟩ :=
    SliceSpliceConstructor.exists_coveringSourceRequest hAcard
  let previous : ∀ j : Ladder.Stage kappa, j < i0 →
      CanonicalState G L Sigma Z (G.source ∩ Z) request :=
    fun j hji ↦ (hi0 j hji).elim
  have hprevious : ∀ j (hji : j < i0),
      IsCanonicalAt j
        (fun l hlj ↦ previous l (lt_trans hlj hji))
        (previous j hji) := by
    intro j hji
    exact (hi0 j hji).elim
  obtain ⟨S0⟩ := hprovider request i0 previous hprevious
  let fallback : CanonicalState G L Sigma Z
      (G.source ∩ Z) request := CanonicalState.ofStage S0
  obtain ⟨R, _⟩ := exists_canonicalSpliceOperation fallback
    (hprovider request)
  exact R.exists_internal_linkage hNorm Set.inter_subset_left i0 hrequest

end RegularPendingOnlyCanonicalRecursion
end CardinalInduction
end Erdos599
