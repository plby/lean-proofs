/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredHalfwayGeometry
import ErdosProblems.Erdos599.ReferenceSubpathEmbedding

/-!
# Embedding every deferred ladder stage in the limiting reference

Every member of an accumulated stage has an extension in the genuine final
direct limit.  Choosing that extension gives an injective reference-owner
embedding of the *full* stage warp into the limiting warp.  Injectivity is
not an additional choice principle: extensions preserve initial vertices,
and the stage family is a warp.

The second part records the endpoint incidence needed to transport ordinary
safeness through such an embedding.  Every fixed vertex of the limiting
carrier occurs at an ordinary stage, by the exact vertex-union theorem for
the final `GrowingWarpChain`; two vertices occur together after taking a
common stage.  Consequently every alternating path has some stage at which
all globally covered exposed endpoints are already locally visible.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

open DirectedPath Alternating Ladder

universe u

variable {V : Type u} {Gamma : DWeb V}
variable {kappa : Cardinal.{u}}

namespace Blueprint.ReferenceSubpathEmbedding

variable {Local Global : Set Gamma.DPath}

/-- Exact exposed-endpoint incidence for local-to-global safeness.  Internal
reference contacts do not enter this predicate. -/
def ExposedEndpointIncidence
    (_E : ReferenceSubpathEmbedding Gamma Local Global)
    (Q : AltPath Gamma.graph) : Prop :=
  (Q.firstDirection? = some .forward →
    Q.initial ∈ Gamma.vertexSet Global →
    Q.initial ∈ Gamma.vertexSet Local) ∧
  (∀ t, Q.terminal? = some t →
    Q.lastDirection? = some .forward →
    t ∈ Gamma.vertexSet Global →
    t ∈ Gamma.vertexSet Local)

/-- An injective subpath embedding transports full safeness once the two
exposed endpoint clauses can be reflected to the local reference. -/
theorem isSafe_of_exposedEndpointIncidence
    (E : ReferenceSubpathEmbedding Gamma Local Global)
    {Q : AltPath Gamma.graph} (hQ : IsSafe Local Q)
    (hincidence : E.ExposedEndpointIncidence Q) :
    IsSafe Global Q := by
  have hInternal : InternallySafe Global Q :=
    E.internallySafe (InternallySafe.of_isSafe hQ)
  refine ⟨⟨hInternal.1, hInternal.2.1, ?_, ?_⟩,
    hInternal.2.2.1, hInternal.2.2.2.1, hInternal.2.2.2.2⟩
  · intro hfirst hglobal
    exact hQ.1.2.2.1 hfirst (hincidence.1 hfirst hglobal)
  · intro t hterminal hlast hglobal
    exact hQ.1.2.2.2 t hterminal hlast
      (hincidence.2 t hterminal hlast hglobal)

end Blueprint.ReferenceSubpathEmbedding

namespace DWeb.KappaLadder.Deferred

variable {L : Gamma.KappaLadder kappa}

/-- Every full stage member has a continuation in the genuine final ladder
warp. -/
theorem HalfwayGeometry.exists_limitWarp_owner
    (hL : HalfwayGeometry L) (a : Ladder.Stage kappa)
    (p : L.warpAt a) :
    ∃ q ∈ L.limitWarp, Gamma.Extends p.1 q := by
  have hlimit : Order.IsSuccLimit kappa.ord :=
    Cardinal.isSuccLimit_ord hL.regular.aleph0_le
  exact hL.limitStages.grows_to_limit
    (Ladder.finalStage kappa) hlimit ⟨a.1, a.2⟩ p.1 p.2

/-- A fixed limiting owner of one full stage member. -/
noncomputable def HalfwayGeometry.limitOwner
    (hL : HalfwayGeometry L) (a : Ladder.Stage kappa)
    (p : L.warpAt a) : Gamma.DPath :=
  Classical.choose (hL.exists_limitWarp_owner a p)

theorem HalfwayGeometry.limitOwner_mem
    (hL : HalfwayGeometry L) (a : Ladder.Stage kappa)
    (p : L.warpAt a) :
    hL.limitOwner a p ∈ L.limitWarp :=
  (Classical.choose_spec (hL.exists_limitWarp_owner a p)).1

theorem HalfwayGeometry.extends_limitOwner
    (hL : HalfwayGeometry L) (a : Ladder.Stage kappa)
    (p : L.warpAt a) :
    Gamma.Extends p.1 (hL.limitOwner a p) :=
  (Classical.choose_spec (hL.exists_limitWarp_owner a p)).2

/-- Distinct full stage members have distinct limiting owners. -/
theorem HalfwayGeometry.limitOwner_injective
    (hL : HalfwayGeometry L) (a : Ladder.Stage kappa) :
    Function.Injective (hL.limitOwner a) := by
  intro p q hpq
  apply Subtype.ext
  apply DWeb.IsWarp.eq_of_initial_eq Gamma
    (hL.warpStages (Ladder.Stage.toExtended a)) p.2 q.2
  calc
    p.1.initial = (hL.limitOwner a p).initial :=
      Gamma.extends_initial (hL.extends_limitOwner a p)
    _ = (hL.limitOwner a q).initial :=
      congrArg DirectedPath.Path.initial hpq
    _ = q.1.initial :=
      (Gamma.extends_initial (hL.extends_limitOwner a q)).symm

/-- The full accumulated reference at every ordinary stage embeds
injectively, member by member, into the limiting warp. -/
noncomputable def HalfwayGeometry.stageReferenceEmbedding
    (hL : HalfwayGeometry L) (a : Ladder.Stage kappa) :
    Blueprint.ReferenceSubpathEmbedding Gamma (L.warpAt a) L.limitWarp where
  owner p := ⟨hL.limitOwner a p, hL.limitOwner_mem a p⟩
  owner_injective := by
    intro p q hpq
    apply hL.limitOwner_injective a
    exact congrArg Subtype.val hpq
  support_subset p :=
    Gamma.support_mono_of_extends (hL.extends_limitOwner a p)
  edgeSet_subset p :=
    DirectedPath.Path.edgeSet_mono_of_extends (hL.extends_limitOwner a p)
  global_isWarp := hL.warpStages (Ladder.finalStage kappa)

/-- Every fixed limiting-reference vertex occurs in a full ordinary stage
warp. -/
theorem HalfwayGeometry.exists_stage_of_mem_vertexSet_limitWarp
    (hL : HalfwayGeometry L) {x : V}
    (hx : x ∈ Gamma.vertexSet L.limitWarp) :
    ∃ a : Ladder.Stage kappa, x ∈ Gamma.vertexSet (L.warpAt a) := by
  have hlimit : Order.IsSuccLimit kappa.ord :=
    Cardinal.isSuccLimit_ord hL.regular.aleph0_le
  obtain ⟨C, hstage, hfinal⟩ :=
    hL.limitStages (Ladder.finalStage kappa) hlimit
  have hxC : x ∈ Gamma.vertexSet (C.limitPaths Gamma) := by
    rw [← hfinal]
    exact hx
  rw [C.vertexSet_limitPaths Gamma] at hxC
  obtain ⟨a, hxa⟩ := Set.mem_iUnion.1 hxC
  refine ⟨⟨a.1, a.2⟩, ?_⟩
  have hstageA : C.stage a = L.warpAt ⟨a.1, a.2⟩ := by
    rw [hstage a]
    rfl
  rwa [← hstageA]

/-- Two fixed vertices of the limiting carrier occur together in one full
ordinary stage warp. -/
theorem HalfwayGeometry.exists_stage_of_pair_mem_vertexSet_limitWarp
    (hL : HalfwayGeometry L) {x y : V}
    (hx : x ∈ Gamma.vertexSet L.limitWarp)
    (hy : y ∈ Gamma.vertexSet L.limitWarp) :
    ∃ a : Ladder.Stage kappa,
      x ∈ Gamma.vertexSet (L.warpAt a) ∧
      y ∈ Gamma.vertexSet (L.warpAt a) := by
  have hlimit : Order.IsSuccLimit kappa.ord :=
    Cardinal.isSuccLimit_ord hL.regular.aleph0_le
  obtain ⟨C, hstage, hfinal⟩ :=
    hL.limitStages (Ladder.finalStage kappa) hlimit
  have hxC : x ∈ Gamma.vertexSet (C.limitPaths Gamma) := by
    rw [← hfinal]
    exact hx
  have hyC : y ∈ Gamma.vertexSet (C.limitPaths Gamma) := by
    rw [← hfinal]
    exact hy
  rw [C.vertexSet_limitPaths Gamma] at hxC hyC
  obtain ⟨ax, hxax⟩ := Set.mem_iUnion.1 hxC
  obtain ⟨ay, hyay⟩ := Set.mem_iUnion.1 hyC
  let a : Set.Iio kappa.ord := max ax ay
  have hxStage : x ∈ Gamma.vertexSet (C.stage a) :=
    C.vertexSet_mono Gamma (le_max_left ax ay) hxax
  have hyStage : y ∈ Gamma.vertexSet (C.stage a) :=
    C.vertexSet_mono Gamma (le_max_right ax ay) hyay
  refine ⟨⟨a.1, a.2⟩, ?_, ?_⟩
  · have hstageA : C.stage a = L.warpAt ⟨a.1, a.2⟩ := by
      rw [hstage a]
      rfl
    rwa [← hstageA]
  · have hstageA : C.stage a = L.warpAt ⟨a.1, a.2⟩ := by
      rw [hstage a]
      rfl
    rwa [← hstageA]

/-- For every alternating path, one full stage sees every exposed endpoint
which lies on the limiting reference.  At most two vertices are involved,
and the common stage is supplied by the preceding direct-limit theorem. -/
theorem HalfwayGeometry.exists_stage_exposedEndpointIncidence
    (hL : HalfwayGeometry L) (Q : AltPath Gamma.graph) :
    ∃ a : Ladder.Stage kappa,
      (hL.stageReferenceEmbedding a).ExposedEndpointIncidence Q := by
  classical
  by_cases hinitial : Q.initial ∈ Gamma.vertexSet L.limitWarp
  · cases hterminal : Q.terminal? with
    | none =>
        obtain ⟨a, ha⟩ := hL.exists_stage_of_mem_vertexSet_limitWarp hinitial
        refine ⟨a, ?_, ?_⟩
        · exact fun _ _ ↦ ha
        · intro t ht
          rw [hterminal] at ht
          simp at ht
    | some t =>
        by_cases htglobal : t ∈ Gamma.vertexSet L.limitWarp
        · obtain ⟨a, haInitial, haTerminal⟩ :=
            hL.exists_stage_of_pair_mem_vertexSet_limitWarp hinitial htglobal
          refine ⟨a, ?_, ?_⟩
          · exact fun _ _ ↦ haInitial
          · intro s hs _ _
            rw [hterminal] at hs
            have hst : s = t := (Option.some.inj hs).symm
            simpa only [hst] using haTerminal
        · obtain ⟨a, ha⟩ := hL.exists_stage_of_mem_vertexSet_limitWarp hinitial
          refine ⟨a, ?_, ?_⟩
          · exact fun _ _ ↦ ha
          · intro s hs _ hsglobal
            rw [hterminal] at hs
            have hst : s = t := (Option.some.inj hs).symm
            exact (htglobal (hst ▸ hsglobal)).elim
  · cases hterminal : Q.terminal? with
    | none =>
        let zero : Ladder.Stage kappa := ⟨0, hL.regular.ord_pos⟩
        refine ⟨zero, ?_, ?_⟩
        · intro _ hglobal
          exact (hinitial hglobal).elim
        · intro t ht
          rw [hterminal] at ht
          simp at ht
    | some t =>
        by_cases htglobal : t ∈ Gamma.vertexSet L.limitWarp
        · obtain ⟨a, ha⟩ := hL.exists_stage_of_mem_vertexSet_limitWarp htglobal
          refine ⟨a, ?_, ?_⟩
          · intro _ hglobal
            exact (hinitial hglobal).elim
          · intro s hs _ _
            rw [hterminal] at hs
            have hst : s = t := (Option.some.inj hs).symm
            simpa only [hst] using ha
        · let zero : Ladder.Stage kappa := ⟨0, hL.regular.ord_pos⟩
          refine ⟨zero, ?_, ?_⟩
          · intro _ hglobal
            exact (hinitial hglobal).elim
          · intro s hs _ hsglobal
            rw [hterminal] at hs
            have hst : s = t := (Option.some.inj hs).symm
            exact (htglobal (hst ▸ hsglobal)).elim

#print axioms HalfwayGeometry.stageReferenceEmbedding
#print axioms HalfwayGeometry.exists_stage_of_mem_vertexSet_limitWarp
#print axioms HalfwayGeometry.exists_stage_of_pair_mem_vertexSet_limitWarp
#print axioms HalfwayGeometry.exists_stage_exposedEndpointIncidence

end DWeb.KappaLadder.Deferred

#print axioms Blueprint.ReferenceSubpathEmbedding.isSafe_of_exposedEndpointIncidence

end Erdos599
