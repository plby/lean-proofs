/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularGlobalAdmissibleProvider

/-!
# Direct installed stages for the regular split recursion

The recursive splice only consumes the row that is installed, the proof
that this installation is a clean completed/pending step, and the resulting
pending/request data.  A comparison warp is one way to prove the clean-step
fact, but it is not part of the recursive state.  Keeping that proof direct
also permits the source-faithful last-roof suffix argument, whose shadow
certificate is deliberately weaker than the older strict-roof certificate.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularDirectInstalledStage

open SingularExtension SliceSpliceSource

universe u

variable {V : Type u}

/-- The exact installed-stage data used by the canonical recursion.  The
history-sensitive comparison construction has already been discharged into
`cleanStep`; no comparison family is retained here. -/
structure DirectInstalledStage
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z A : Set V)
    (request : Ladder.Stage kappa → Option A)
    (i : Ladder.Stage kappa)
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A) where
  baseStage : Ladder.Stage kappa
  base : Set G.DPath
  base_warp : G.IsWarp base
  base_finite : G.HasFiniteCharacter base
  base_initial : G.initialSet base = A
  base_extends : ∀ j (hji : j < i),
    G.ForwardExtension (previous j hji).row base
  base_freezes : ∀ j (hji : j < i),
    completedPart G (previous j hji).row ⊆ completedPart G base

  stageIndex : Ladder.Stage kappa
  stageIndex_mem : stageIndex ∈ Sigma
  index_strict : ∀ j (hji : j < i),
    (previous j hji).stageIndex < stageIndex

  installed : Set G.DPath
  compatible : G.StarCompatible (pendingPart G base) installed
  cleanStep : RegularCompletedPendingSplice.IsCleanTargetStep
    G base installed compatible
  installed_star_finite : G.HasFiniteCharacter (G.star compatible)

  vertices_closed : G.vertexSet
    (RegularCompletedPendingSplice.freezeCompletedStar
      G base installed compatible) ⊆ Z
  pending_tight : TightLinkageBetween G
    (G.initialSet (pendingPart G
      (RegularCompletedPendingSplice.freezeCompletedStar
        G base installed compatible)))
    (L.frontier stageIndex)
    (pendingPart G (RegularCompletedPendingSplice.freezeCompletedStar
      G base installed compatible))
  pending_below_roof : G.vertexSet (pendingPart G
    (RegularCompletedPendingSplice.freezeCompletedStar
      G base installed compatible)) ⊆ G.roof (L.frontier stageIndex)
  pendingRequest : Set V
  pendingRequest_subset : pendingRequest ⊆ L.frontier stageIndex ∩ Z
  pendingRequest_small : #pendingRequest < kappa
  pending_status : ∀ p ∈ pendingPart G
      (RegularCompletedPendingSplice.freezeCompletedStar
        G base installed compatible),
    SliceSpliceConstructor.IsStagePrefix G L stageIndex p ∨
      ∃ x ∈ pendingRequest, G.terminal? p = some x

  resolves_pending : ∀ j (hji : j < i) p,
    p ∈ pendingPart G (previous j hji).row →
    (∃ x ∈ (previous j hji).pendingRequest,
      G.terminal? p = some x) →
      ∃ q ∈ completedPart G
        (RegularCompletedPendingSplice.freezeCompletedStar
          G base installed compatible), q.initial = p.initial
  realizes_request : ∀ a : A, request i = some a →
    ∃ p ∈ completedPart G
      (RegularCompletedPendingSplice.freezeCompletedStar
        G base installed compatible), p.initial = a.1

namespace DirectInstalledStage

/-- An older comparison-based stage canonically forgets to the direct
interface after its comparison has proved the clean-step fact. -/
def ofInstalledComparisonStage
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (S : RegularGlobalAdmissibleProvider.InstalledComparisonStage
      G L Sigma Z A request i previous) :
    DirectInstalledStage G L Sigma Z A request i previous where
  baseStage := S.baseStage
  base := S.base
  base_warp := S.base_warp
  base_finite := S.base_finite
  base_initial := S.base_initial
  base_extends := S.base_extends
  base_freezes := S.base_freezes
  stageIndex := S.stageIndex
  stageIndex_mem := S.stageIndex_mem
  index_strict := S.index_strict
  installed := S.installed
  compatible := S.compatible
  cleanStep := S.cleanStep
  installed_star_finite := S.installed_star_finite
  vertices_closed := S.vertices_closed
  pending_tight := S.pending_tight
  pending_below_roof := S.pending_below_roof
  pendingRequest := S.pendingRequest
  pendingRequest_subset := S.pendingRequest_subset
  pendingRequest_small := S.pendingRequest_small
  pending_status := S.pending_status
  resolves_pending := S.resolves_pending
  realizes_request := S.realizes_request

/-- Forget the one-step geometry after forming the recursive payload. -/
def payload
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (S : DirectInstalledStage G L Sigma Z A request i previous) :
    RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A where
  stageIndex := S.stageIndex
  stageIndex_mem := S.stageIndex_mem
  row := RegularCompletedPendingSplice.freezeCompletedStar
    G S.base S.installed S.compatible
  isWarp := S.cleanStep.result_isWarp
  finiteCharacter := S.cleanStep.result_finiteCharacter
    S.base_finite S.installed_star_finite
  initialSet_eq := S.cleanStep.result_initialSet.trans S.base_initial
  vertices_closed := S.vertices_closed
  pending_tight := S.pending_tight
  pending_below_roof := S.pending_below_roof
  pendingRequest := S.pendingRequest
  pendingRequest_subset := S.pendingRequest_subset
  pendingRequest_small := S.pendingRequest_small
  pending_status := S.pending_status

/-- The direct installed stage satisfies the ordinary recursive validity
contract. -/
theorem valid
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (S : DirectInstalledStage G L Sigma Z A request i previous) :
    RegularCompletedPendingSplice.IsValidRecursiveStage request i previous
      S.payload := by
  refine
    { index_strict := S.index_strict
      extends_previous := ?_
      freezes_completed := ?_
      resolves_pending := S.resolves_pending
      realizes_request := S.realizes_request }
  · intro j hji
    exact G.forwardExtension_trans (S.base_extends j hji)
      S.cleanStep.result_forwardExtension
  · intro j hji
    exact (S.base_freezes j hji).trans
      (RegularCompletedPendingSplice.completedPart_subset_completedPart_freezeCompletedStar
        G S.base S.installed S.compatible)

end DirectInstalledStage

end RegularDirectInstalledStage
end CardinalInduction
end Erdos599
