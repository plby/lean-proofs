/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredStageHammockTransport
import ErdosProblems.Erdos599.HalfwayDeferredStageIntervalBridge

/-!
# Convexity of safeness along deferred ladder stages

Safeness of one fixed alternating path cannot disappear at an intermediate
full reference stage and then reappear later.  Internal safeness transports
from the earlier stage through the path-extension embedding.  The only
remaining conditions concern exposed endpoints; if an endpoint were covered
at the intermediate stage, monotonicity of the full stage carrier would
make it covered at the later stage as well.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

open DirectedPath Alternating Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace Blueprint.ReferenceSubpathEmbedding

variable {Local Global : Set Gamma.DPath}

/-- A pathwise growing relation between two warps gives the honest
injective subpath embedding between their members.  Injectivity follows
from preservation of the initial vertex and disjointness in the source
warp. -/
noncomputable def ofLadderGrows
    (hLocal : Gamma.IsWarp Local) (hGlobal : Gamma.IsWarp Global)
    (hgrows : Gamma.LadderGrows Local Global) :
    ReferenceSubpathEmbedding Gamma Local Global := by
  let owner : Local → Gamma.DPath := fun p ↦
    Classical.choose (hgrows p.1 p.2)
  have owner_mem (p : Local) : owner p ∈ Global :=
    (Classical.choose_spec (hgrows p.1 p.2)).1
  have extends_owner (p : Local) : Gamma.Extends p.1 (owner p) :=
    (Classical.choose_spec (hgrows p.1 p.2)).2
  refine
    { owner := fun p ↦ ⟨owner p, owner_mem p⟩
      owner_injective := ?_
      support_subset := fun p ↦
        Gamma.support_mono_of_extends (extends_owner p)
      edgeSet_subset := fun p ↦
        DirectedPath.Path.edgeSet_mono_of_extends (extends_owner p)
      global_isWarp := hGlobal }
  intro p q hpq
  apply Subtype.ext
  apply DWeb.IsWarp.eq_of_initial_eq Gamma hLocal p.2 q.2
  calc
    p.1.initial = (owner p).initial := Gamma.extends_initial (extends_owner p)
    _ = (owner q).initial :=
      congrArg (fun r : Global ↦ r.1.initial) hpq
    _ = q.1.initial := (Gamma.extends_initial (extends_owner q)).symm

#print axioms ofLadderGrows

end Blueprint.ReferenceSubpathEmbedding

namespace DWeb.KappaLadder.Deferred

variable {L : Gamma.KappaLadder kappa}

/-- Every ordered pair of ordinary deferred stages has an injective
reference-owner embedding induced by the genuine ladder extension
relation. -/
noncomputable def HalfwayGeometry.stageReferenceEmbeddingOfLE
    (hL : HalfwayGeometry L) {a b : Ladder.Stage kappa} (hab : a ≤ b) :
    Blueprint.ReferenceSubpathEmbedding Gamma (L.warpAt a) (L.warpAt b) :=
  Blueprint.ReferenceSubpathEmbedding.ofLadderGrows
    (hL.warpStages (Ladder.Stage.toExtended a))
    (hL.warpStages (Ladder.Stage.toExtended b))
    (CardinalInduction.DeferredStageInterval.warpAt_grows_of_le hL hab)

/-- Stage safeness is order-convex: if a fixed alternating path is safe at
an earlier and a later full stage, it is safe at every stage between them.

The early certificate supplies all internal conditions.  The late
certificate rules out newly covered exposed endpoints, because full stage
carriers are monotone. -/
theorem HalfwayGeometry.isSafe_warpAt_of_le_of_le
    (hL : HalfwayGeometry L) {a b c : Ladder.Stage kappa}
    (hab : a ≤ b) (hbc : b ≤ c) {Q : AltPath Gamma.graph}
    (hQa : IsSafe (L.warpAt a) Q) (hQc : IsSafe (L.warpAt c) Q) :
    IsSafe (L.warpAt b) Q := by
  have hInternal : Blueprint.InternallySafe (L.warpAt b) Q :=
    (hL.stageReferenceEmbeddingOfLE hab).internallySafe
      (Blueprint.InternallySafe.of_isSafe hQa)
  refine ⟨⟨hInternal.1, hInternal.2.1, ?_, ?_⟩,
    hInternal.2.2.1, hInternal.2.2.2.1, hInternal.2.2.2.2⟩
  · intro hfirst hinitial
    exact hQc.1.2.2.1 hfirst
      (hL.vertexSet_warpAt_monotone hbc hinitial)
  · intro t hterminal hlast hterminalCovered
    exact hQc.1.2.2.2 t hterminal hlast
      (hL.vertexSet_warpAt_monotone hbc hterminalCovered)

/-- Predicate-level formulation of the no-loss-and-recovery law. -/
theorem HalfwayGeometry.isSafe_warpAt_orderConvex
    (hL : HalfwayGeometry L) (Q : AltPath Gamma.graph) :
    Set.OrdConnected {a : Ladder.Stage kappa | IsSafe (L.warpAt a) Q} := by
  refine ⟨?_⟩
  intro a ha c hc b hbetween
  exact hL.isSafe_warpAt_of_le_of_le hbetween.1 hbetween.2 ha hc

/-- If a path is already safe at one stage and is safe for the limiting
reference, it remains safe at every later stage.  Choose a stage beyond the
requested stage at which global safeness has reflected locally, then apply
stage convexity. -/
theorem HalfwayGeometry.isSafe_warpAt_of_le_of_limitWarp
    (hL : HalfwayGeometry L) {a b : Ladder.Stage kappa} (hab : a ≤ b)
    {Q : AltPath Gamma.graph} (hQa : IsSafe (L.warpAt a) Q)
    (hQlimit : IsSafe L.limitWarp Q) :
    IsSafe (L.warpAt b) Q := by
  obtain ⟨c₀, hc₀⟩ := hL.exists_eventually_isSafe_warpAt Q hQlimit
  let c : Ladder.Stage kappa := max b c₀
  exact hL.isSafe_warpAt_of_le_of_le hab (le_max_left b c₀) hQa
    (hc₀ c (le_max_right b c₀))

/-- After one uniform endpoint-incidence stage, safeness for fixed endpoints
is upward persistent along the full stage references.  The path itself is
not fixed: the same bound works for every alternating path with these
endpoints. -/
theorem HalfwayGeometry.exists_eventually_isSafe_warpAt_upward_of_endpoints
    (hL : HalfwayGeometry L) (x : V) (e : AltEnd V) :
    ∃ delta : Ladder.Stage kappa, ∀ a, delta ≤ a → ∀ b, a ≤ b →
      ∀ Q : AltPath Gamma.graph, Q.initial = x → HasEnd Q e →
        IsSafe (L.warpAt a) Q → IsSafe (L.warpAt b) Q := by
  obtain ⟨delta, hdelta⟩ :=
    hL.exists_eventually_isSafe_limitWarp_of_endpoints x e
  refine ⟨delta, ?_⟩
  intro a hdeltaA b hab Q hstart hend hsafe
  exact hL.isSafe_warpAt_of_le_of_limitWarp hab hsafe
    (hdelta a hdeltaA Q hstart hend hsafe)

#print axioms HalfwayGeometry.stageReferenceEmbeddingOfLE
#print axioms HalfwayGeometry.isSafe_warpAt_of_le_of_le
#print axioms HalfwayGeometry.isSafe_warpAt_orderConvex
#print axioms HalfwayGeometry.isSafe_warpAt_of_le_of_limitWarp
#print axioms HalfwayGeometry.exists_eventually_isSafe_warpAt_upward_of_endpoints

end DWeb.KappaLadder.Deferred
end Erdos599
