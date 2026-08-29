/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularGlobalAdmissibleProvider

/-!
# Canonical source-9.15 recursion

The public completed/pending provider accepts arbitrary valid payload
histories.  That interface is useful as a consumer, but it is too weak as a
construction principle: a bare payload has forgotten the comparison warp and
the stage-relative mavericks which made its installed family admissible.

This file keeps that provenance in the recursive value itself.  A canonical
stage contains the actual `TargetedComparisonStage` which produced its row,
the clean-track maverick family, its literal stage-interval certificate, and
the equality identifying the next small request with the terminals of those
mavericks.  The next-stage selector therefore receives only canonical
histories; it is never asked to reconstruct history-sensitive avoidance from
an arbitrary payload.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularCanonicalAdmissibleProvider

open SingularExtension SliceSpliceSource

universe u

variable {V : Type u}

/-- A source-faithful targeted comparison stage with the exact provenance of
its next pending request.  The target track is completed immediately.  The
clean track is split into literal ladder intervals and the stage-relative
mavericks whose terminals are scheduled at the next recursive step. -/
structure CanonicalStage
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z A : Set V)
    (request : Ladder.Stage kappa → Option A)
    (i : Ladder.Stage kappa)
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A)
    extends RegularGlobalAdmissibleProvider.TargetedComparisonStage
      G L Sigma Z A request i previous where
  cleanMavericks : Set G.DPath
  cleanMavericks_eq : cleanMavericks =
    ControlledSlices.sliceMavericks G (L.warpAt stageIndex) slice.clean
  cleanIntervals : SliceCandidate.HasStageIntervalSegments
    G L slice.clean baseStage stageIndex
  cleanMavericks_small : #cleanMavericks < kappa
  cleanMavericks_closed : G.vertexSet cleanMavericks ⊆ Z
  pendingRequest_eq : pendingRequest = G.terminalFrontier cleanMavericks
  result_tight : TightLinkageBetween G A (L.frontier stageIndex)
    (RegularCompletedPendingSplice.freezeCompletedStar
      G base installed compatible)
  result_below_roof : G.vertexSet
      (RegularCompletedPendingSplice.freezeCompletedStar
        G base installed compatible) ⊆ G.roof (L.frontier stageIndex)

namespace CanonicalStage

/-- Forget only the explicit maverick provenance, retaining the targeted
comparison stage consumed by the already checked normalization adapter. -/
def targeted
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (S : CanonicalStage G L Sigma Z A request i previous) :
    RegularGlobalAdmissibleProvider.TargetedComparisonStage
      G L Sigma Z A request i previous :=
  S.toTargetedComparisonStage

/-- The installed comparison stage derived from canonical source data. -/
def installedStage
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (S : CanonicalStage G L Sigma Z A request i previous)
    (hNorm : G.IsNormalized) :
    RegularGlobalAdmissibleProvider.InstalledComparisonStage
      G L Sigma Z A request i previous :=
  S.targeted.toInstalledComparisonStage hNorm

/-- The ordinary recursive payload is a projection of canonical provenance,
not an input from which that provenance is later reconstructed. -/
def payload
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (S : CanonicalStage G L Sigma Z A request i previous)
    (hNorm : G.IsNormalized) :
    RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A :=
  (S.installedStage hNorm).payload

theorem payload_valid
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (S : CanonicalStage G L Sigma Z A request i previous)
    (hNorm : G.IsNormalized) :
    RegularCompletedPendingSplice.IsValidRecursiveStage request i previous
      (S.payload hNorm) :=
  (S.installedStage hNorm).valid

end CanonicalStage

/-- A recursive value together with the actual canonical stage which
produced it.  Its producer may refer to its own projected earlier payloads;
the next constructor sees this full object rather than only `payload`. -/
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

/-- The payload projected from the state's actual producer. -/
def payload
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    (hNorm : G.IsNormalized)
    (S : CanonicalState G L Sigma Z A request) :
    RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A :=
  S.producer.payload hNorm

/-- Package a stage constructed from the current canonical history. -/
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
    (hNorm : G.IsNormalized)
    (S : CanonicalStage G L Sigma Z A request i previous) :
    (ofStage S).payload hNorm = S.payload hNorm :=
  rfl

end CanonicalState

/-- Project the ordinary payload family from a canonical strict history. -/
def projectedHistory
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    (hNorm : G.IsNormalized) (i : Ladder.Stage kappa)
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      CanonicalState G L Sigma Z A request) :
    ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A :=
  fun j hji ↦ (previous j hji).payload hNorm

/-- A state occurs canonically at `i` in `previous` when it is literally the
projection of a targeted comparison stage constructed over the restriction
of that same history below `i`.  This rules out states whose producer merely
happens to project to a valid payload but came from unrelated provenance. -/
def IsCanonicalAt
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    (hNorm : G.IsNormalized) (i : Ladder.Stage kappa)
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      CanonicalState G L Sigma Z A request)
    (state : CanonicalState G L Sigma Z A request) : Prop :=
  ∃ S : CanonicalStage G L Sigma Z A request i
      (projectedHistory hNorm i previous),
    state = CanonicalState.ofStage S

/-- The source-faithful stage-provider boundary.  In contrast with
`HasTargetedComparisonStageProvider`, the history argument still contains
the comparison and maverick provenance of every earlier actual choice.  Its
premise demands literal recursive provenance, not merely validity of the
payload projections. -/
def HasCanonicalStageProvider
    {kappa : Cardinal.{u}} (G : DWeb V) (hNorm : G.IsNormalized)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z A : Set V) (request : Ladder.Stage kappa → Option A) : Prop :=
  ∀ (i : Ladder.Stage kappa)
      (previous : ∀ j : Ladder.Stage kappa, j < i →
        CanonicalState G L Sigma Z A request),
    (∀ j (hji : j < i),
      IsCanonicalAt hNorm j
        (fun l hlj ↦ previous l (lt_trans hlj hji))
        (previous j hji)) →
      Nonempty (CanonicalStage G L Sigma Z A request i
        (projectedHistory hNorm i previous))

/-- A total operation on canonical histories.  Its `valid` law only promises
canonical provenance on certified histories, which is exactly the branch
followed by the well-founded recursion below. -/
structure CanonicalSpliceOperation
    {kappa : Cardinal.{u}} (G : DWeb V) (hNorm : G.IsNormalized)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z A : Set V) (request : Ladder.Stage kappa → Option A) where
  build : ∀ i : Ladder.Stage kappa,
    (∀ j : Ladder.Stage kappa, j < i →
      CanonicalState G L Sigma Z A request) →
      CanonicalState G L Sigma Z A request
  valid : ∀ i previous,
    (∀ j (hji : j < i),
      IsCanonicalAt hNorm j
        (fun l hlj ↦ previous l (lt_trans hlj hji))
        (previous j hji)) →
      ∃ S : CanonicalStage G L Sigma Z A request i
          (projectedHistory hNorm i previous),
        build i previous = CanonicalState.ofStage S

/-- Choice totalizes a canonical provider.  The fallback is used only on
invalid hypothetical canonical histories; it is never inspected by the
actual recursive history. -/
theorem exists_canonicalSpliceOperation
    {kappa : Cardinal.{u}} {G : DWeb V} {hNorm : G.IsNormalized}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    (fallback : CanonicalState G L Sigma Z A request)
    (hprovider : HasCanonicalStageProvider G hNorm L Sigma Z A request) :
    ∃ _R : CanonicalSpliceOperation G hNorm L Sigma Z A request, True := by
  let build : ∀ i : Ladder.Stage kappa,
      (∀ j : Ladder.Stage kappa, j < i →
        CanonicalState G L Sigma Z A request) →
        CanonicalState G L Sigma Z A request :=
    fun i previous ↦ by
      classical
      exact if h : ∃ S : CanonicalStage G L Sigma Z A request i
          (projectedHistory hNorm i previous), True then
        CanonicalState.ofStage (Classical.choose h)
      else fallback
  let R : CanonicalSpliceOperation G hNorm L Sigma Z A request :=
    { build := build
      valid := by
        intro i previous hprevious
        obtain ⟨S⟩ := hprovider i previous hprevious
        have hexists : ∃ S : CanonicalStage G L Sigma Z A request i
            (projectedHistory hNorm i previous), True := ⟨S, trivial⟩
        refine ⟨Classical.choose hexists, ?_⟩
        dsimp only [build]
        rw [dif_pos hexists] }
  exact ⟨R, trivial⟩

namespace CanonicalSpliceOperation

variable {kappa : Cardinal.{u}} {G : DWeb V} {hNorm : G.IsNormalized}
variable {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
variable {Z A : Set V} {request : Ladder.Stage kappa → Option A}

/-- The actual canonical recursive state. -/
noncomputable def state
    (R : CanonicalSpliceOperation G hNorm L Sigma Z A request)
    (i : Ladder.Stage kappa) : CanonicalState G L Sigma Z A request :=
  WellFounded.fix wellFounded_lt
    (fun i previous ↦ R.build i previous) i

theorem state_eq
    (R : CanonicalSpliceOperation G hNorm L Sigma Z A request)
    (i : Ladder.Stage kappa) :
    R.state i = R.build i (fun j _hji ↦ R.state j) := by
  exact WellFounded.fix_eq wellFounded_lt
    (fun i previous ↦ R.build i previous) i

/-- Every actual recursive value is produced by a canonical stage over the
literal earlier actual values. -/
theorem state_provenance
    (R : CanonicalSpliceOperation G hNorm L Sigma Z A request)
    (i : Ladder.Stage kappa) :
    ∃ S : CanonicalStage G L Sigma Z A request i
        (fun j _hji ↦ (R.state j).payload hNorm),
      R.state i = CanonicalState.ofStage S := by
  rw [R.state_eq i]
  apply R.valid
  intro j hji
  exact R.state_provenance j
termination_by i.1
decreasing_by exact hji

/-- The ordinary payload at an actual canonical stage. -/
noncomputable def payload
    (R : CanonicalSpliceOperation G hNorm L Sigma Z A request)
    (i : Ladder.Stage kappa) :
    RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A :=
  (R.state i).payload hNorm

theorem payload_valid
    (R : CanonicalSpliceOperation G hNorm L Sigma Z A request)
    (i : Ladder.Stage kappa) :
    RegularCompletedPendingSplice.IsValidRecursiveStage request i
      (fun j _hji ↦ R.payload j) (R.payload i) := by
  obtain ⟨S, hS⟩ := R.state_provenance i
  rw [payload, hS]
  exact S.payload_valid hNorm

/-- The growing chain obtained by forgetting provenance only after the
canonical recursion has been constructed. -/
noncomputable def growingChain
    (R : CanonicalSpliceOperation G hNorm L Sigma Z A request) :
    G.GrowingWarpChain (Ladder.Stage kappa) where
  stage i := (R.payload i).row
  isWarp i := (R.payload i).isWarp
  grows := by
    intro i j hij p hp
    rcases hij.lt_or_eq with hij | rfl
    · exact (R.payload_valid j).extends_previous i hij |>.1 p hp
    · exact ⟨p, hp, G.extends_refl p⟩

@[simp] theorem growingChain_stage
    (R : CanonicalSpliceOperation G hNorm L Sigma Z A request)
    (i : Ladder.Stage kappa) :
    R.growingChain.stage i = (R.payload i).row :=
  rfl

theorem initialUnion_growingChain
    (R : CanonicalSpliceOperation G hNorm L Sigma Z A request)
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
    (R : CanonicalSpliceOperation G hNorm L Sigma Z A request)
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
    (R : CanonicalSpliceOperation G hNorm L Sigma Z A request)
    (hA : A ⊆ G.source) (i0 : Ladder.Stage kappa)
    (hrequest : ∀ a : A, ∃ i, request i = some a) :
    ∃ P : Set G.DPath,
      IsLinkageBetween G A G.target P ∧ G.vertexSet P ⊆ Z := by
  exact (R.isCompletedPendingSplice i0 hrequest).exists_internal_linkage
    hNorm hA

end CanonicalSpliceOperation

/-- Public assembly for the canonical source-9.15 recursion.  The provider
is invoked only on histories which retain their actual comparison and
maverick witnesses. -/
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
      HasCanonicalStageProvider G hNorm L Sigma Z (G.source ∩ Z)
        request) :
    ∃ P : Set G.DPath,
      IsLinkageBetween G (G.source ∩ Z) G.target P ∧
        G.vertexSet P ⊆ Z := by
  obtain ⟨request, hrequest⟩ :=
    SliceSpliceConstructor.exists_coveringSourceRequest hAcard
  let previous : ∀ j : Ladder.Stage kappa, j < i0 →
      CanonicalState G L Sigma Z (G.source ∩ Z) request :=
    fun j hji ↦ (hi0 j hji).elim
  have hprevious : ∀ j (hji : j < i0),
      IsCanonicalAt hNorm j
        (fun l hlj ↦ previous l (lt_trans hlj hji))
        (previous j hji) := by
    intro j hji
    exact (hi0 j hji).elim
  obtain ⟨S0⟩ := hprovider request i0 previous hprevious
  let fallback : CanonicalState G L Sigma Z (G.source ∩ Z) request :=
    CanonicalState.ofStage S0
  obtain ⟨R, _⟩ := exists_canonicalSpliceOperation fallback
    (hprovider request)
  exact R.exists_internal_linkage Set.inter_subset_left i0 hrequest

end RegularCanonicalAdmissibleProvider
end CardinalInduction
end Erdos599
