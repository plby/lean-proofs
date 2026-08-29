/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayIntervalGlobalReferenceEmbedding

/-!
# Embedding the outside interval reference in the limiting warp

Restrict the actual interval-to-limit owner embedding to interval members
which avoid the closing set.  This is the precise local reference used by
the post-closure fractured assignment and matching orbit.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint.PostClosureIntervalTransaction

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ X0 : Set V} {z : V}
variable {R : DynamicMoving931GlobalClosure C globalZ X0}

/-- The outside interval members keep their actual, injectively chosen
limiting owners. -/
noncomputable def outsideIntervalGlobalReferenceEmbedding
    (T : PostClosureIntervalTransaction C globalZ X0 z R) :
    _root_.Erdos599.Blueprint.ReferenceSubpathEmbedding Gamma
      (outsideReference T.intervalReference R.closedSet)
      C.ladder.limitWarp where
  owner q := T.intervalGlobalReferenceEmbedding.owner
    ⟨q.1, q.2.1⟩
  owner_injective := by
    intro q r hqr
    apply Subtype.ext
    have hfull : (⟨q.1, q.2.1⟩ : T.intervalReference) =
        ⟨r.1, r.2.1⟩ :=
      T.intervalGlobalReferenceEmbedding.owner_injective hqr
    exact congrArg (fun s : T.intervalReference => s.1) hfull
  support_subset q :=
    T.intervalGlobalReferenceEmbedding.support_subset ⟨q.1, q.2.1⟩
  edgeSet_subset q :=
    T.intervalGlobalReferenceEmbedding.edgeSet_subset ⟨q.1, q.2.1⟩
  global_isWarp := T.intervalGlobalReferenceEmbedding.global_isWarp

/-- Every outside-local reference edge is a literal limiting-reference
edge. -/
theorem outsideIntervalReference_familyEdges_subset_limitWarp
    (T : PostClosureIntervalTransaction C globalZ X0 z R) :
    familyEdges (outsideReference T.intervalReference R.closedSet) ⊆
      familyEdges C.ladder.limitWarp :=
  T.outsideIntervalGlobalReferenceEmbedding.familyEdges_subset

/-- Internal safeness of an outside-local matching route transports to the
actual limiting reference.  Exposed endpoints remain intentionally
unclassified. -/
theorem internallySafe_limitWarp_of_outsideIntervalReference
    (T : PostClosureIntervalTransaction C globalZ X0 z R)
    {Q : AltPath Gamma.graph}
    (hQ : _root_.Erdos599.Blueprint.InternallySafe
      (outsideReference T.intervalReference R.closedSet) Q) :
    _root_.Erdos599.Blueprint.InternallySafe C.ladder.limitWarp Q :=
  T.outsideIntervalGlobalReferenceEmbedding.internallySafe hQ

#print axioms outsideIntervalGlobalReferenceEmbedding
#print axioms outsideIntervalReference_familyEdges_subset_limitWarp
#print axioms internallySafe_limitWarp_of_outsideIntervalReference

end Erdos599.Blueprint.LinkageBlueprint.PostClosureIntervalTransaction
