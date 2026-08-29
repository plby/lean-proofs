/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGlobalSafePathAttainment

/-!
# Eventual transport of stage and limiting hammocks

For fixed endpoints, one sufficiently late stage reflects every globally
covered endpoint.  Internal safeness already transports through the
injective reference-owner embedding.  Thus all later stage hammocks with
these endpoints are limiting hammocks, uniformly in their members and size.

In the reverse direction, each fixed globally safe path becomes stage-safe
eventually.  Regularity makes this uniform over a small family, but not over
the whole collection of paths.  No transfer of maximality is asserted.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

open DirectedPath Alternating Ladder Blueprint

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder.Deferred

variable {L : Gamma.KappaLadder kappa}

/-- Full stage carriers increase, even though the literal path families
need not be nested before their members have finished growing. -/
theorem HalfwayGeometry.vertexSet_warpAt_monotone
    (hL : HalfwayGeometry L) :
    Monotone (fun a : Ladder.Stage kappa ↦ Gamma.vertexSet (L.warpAt a)) := by
  intro a b hab
  have hlimit : Order.IsSuccLimit kappa.ord :=
    Cardinal.isSuccLimit_ord hL.regular.aleph0_le
  obtain ⟨C, hstage, _hfinal⟩ :=
    hL.limitStages (Ladder.finalStage kappa) hlimit
  have hmono := C.vertexSet_mono Gamma hab
  have ha : C.stage a = L.warpAt a := by
    rw [hstage a]
    rfl
  have hb : C.stage b = L.warpAt b := by
    rw [hstage b]
    rfl
  change Gamma.vertexSet (C.stage a) ⊆ Gamma.vertexSet (C.stage b) at hmono
  rwa [ha, hb] at hmono

/-- Every fixed vertex has its limiting-reference incidence reflected at
all sufficiently late full stages. -/
theorem HalfwayGeometry.exists_eventually_vertexSet_incidence
    (hL : HalfwayGeometry L) (x : V) :
    ∃ a : Ladder.Stage kappa, ∀ b, a ≤ b →
      x ∈ Gamma.vertexSet L.limitWarp → x ∈ Gamma.vertexSet (L.warpAt b) := by
  by_cases hx : x ∈ Gamma.vertexSet L.limitWarp
  · obtain ⟨a, ha⟩ := hL.exists_stage_of_mem_vertexSet_limitWarp hx
    exact ⟨a, fun b hab _ ↦ hL.vertexSet_warpAt_monotone hab ha⟩
  · exact ⟨⟨0, hL.regular.ord_pos⟩, fun _ _ h ↦ (hx h).elim⟩

/-- At most two endpoint incidences must be captured.  The resulting stage
works for every alternating path with the prescribed endpoints. -/
theorem HalfwayGeometry.exists_eventually_hammock_endpoint_incidence
    (hL : HalfwayGeometry L) (x : V) (e : AltEnd V) :
    ∃ a : Ladder.Stage kappa, ∀ b, a ≤ b →
      ∀ Q : AltPath Gamma.graph, Q.initial = x → HasEnd Q e →
        (hL.stageReferenceEmbedding b).ExposedEndpointIncidence Q := by
  obtain ⟨a, ha⟩ := hL.exists_eventually_vertexSet_incidence x
  cases e with
  | infinity =>
      refine ⟨a, ?_⟩
      intro b hab Q hstart hend
      refine ⟨?_, ?_⟩
      · intro _ hglobal
        rw [hstart] at hglobal ⊢
        exact ha b hab hglobal
      · intro t ht _ _
        have hnone : Q.terminal? = none :=
          (AltPath.isInfinite_iff_terminal?_eq_none Q).mp hend
        rw [hnone] at ht
        cases ht
  | vertex y =>
      obtain ⟨c, hc⟩ := hL.exists_eventually_vertexSet_incidence y
      refine ⟨max a c, ?_⟩
      intro b hab Q hstart hend
      refine ⟨?_, ?_⟩
      · intro _ hglobal
        rw [hstart] at hglobal ⊢
        exact ha b ((le_max_left a c).trans hab) hglobal
      · intro t ht _ hglobal
        have hty : t = y := Option.some.inj (ht.symm.trans hend)
        rw [hty] at hglobal ⊢
        exact hc b ((le_max_right a c).trans hab) hglobal

/-- Uniform local-to-global safeness for paths with fixed endpoints. -/
theorem HalfwayGeometry.exists_eventually_isSafe_limitWarp_of_endpoints
    (hL : HalfwayGeometry L) (x : V) (e : AltEnd V) :
    ∃ a : Ladder.Stage kappa, ∀ b, a ≤ b →
      ∀ Q : AltPath Gamma.graph, Q.initial = x → HasEnd Q e →
        IsSafe (L.warpAt b) Q → IsSafe L.limitWarp Q := by
  obtain ⟨a, ha⟩ := hL.exists_eventually_hammock_endpoint_incidence x e
  exact ⟨a, fun b hab Q hstart hend hsafe ↦
    (hL.stageReferenceEmbedding b).isSafe_of_exposedEndpointIncidence
      hsafe (ha b hab Q hstart hend)⟩

/-- All sufficiently late stage hammocks with fixed endpoints are global
hammocks.  Their members and cardinalities are unchanged. -/
theorem HalfwayGeometry.exists_eventually_hammock_limitWarp
    (hL : HalfwayGeometry L) (x : V) (e : AltEnd V) :
    ∃ a : Ladder.Stage kappa, ∀ b, a ≤ b →
      ∀ H : Set (AltPath Gamma.graph),
        Hammock Gamma (L.warpAt b) x e H →
        Hammock Gamma L.limitWarp x e H := by
  obtain ⟨a, ha⟩ := hL.exists_eventually_isSafe_limitWarp_of_endpoints x e
  refine ⟨a, ?_⟩
  intro b hab H hH
  refine ⟨?_, hH.2⟩
  intro Q hQ
  obtain ⟨hsafe, hstart, hend⟩ := hH.1 Q hQ
  exact ⟨ha b hab Q hstart hend hsafe, hstart, hend⟩

/-- Regularity makes eventual stage safeness simultaneous for a small
family of fixed globally safe paths. -/
theorem HalfwayGeometry.exists_eventually_isSafe_warpAt_family
    (hL : HalfwayGeometry L) (H : Set (AltPath Gamma.graph))
    (hsmall : #H < kappa) (hsafe : ∀ Q ∈ H, IsSafe L.limitWarp Q) :
    ∃ a : Ladder.Stage kappa, ∀ b, a ≤ b →
      ∀ Q ∈ H, IsSafe (L.warpAt b) Q := by
  have hexists (Q : H) : ∃ a : Ladder.Stage kappa,
      ∀ b, a ≤ b → IsSafe (L.warpAt b) Q.1 :=
    hL.exists_eventually_isSafe_warpAt Q.1 (hsafe Q.1 Q.2)
  let birth : H → Ladder.Stage kappa :=
    fun Q ↦ Classical.choose (hexists Q)
  let bound : Ordinal.{u} := ⨆ Q : H, (birth Q).1
  have hbound : bound < kappa.ord :=
    Stationary.iSup_lt_ord_of_lt hL.regular hsmall (fun Q ↦ (birth Q).2)
  let a : Ladder.Stage kappa := ⟨bound, hbound⟩
  refine ⟨a, ?_⟩
  intro b hab Q hQ
  let Qs : H := ⟨Q, hQ⟩
  have hbirth : birth Qs ≤ a :=
    Ordinal.le_iSup (fun R : H ↦ (birth R).1) Qs
  exact Classical.choose_spec (hexists Qs) b (hbirth.trans hab)

/-- A small global hammock is a hammock of every sufficiently late full
stage reference.  This is not a uniform bound on all global hammocks. -/
theorem HalfwayGeometry.exists_eventually_hammock_warpAt
    (hL : HalfwayGeometry L) {x : V} {e : AltEnd V}
    {H : Set (AltPath Gamma.graph)}
    (hH : Hammock Gamma L.limitWarp x e H) (hsmall : #H < kappa) :
    ∃ a : Ladder.Stage kappa, ∀ b, a ≤ b →
      Hammock Gamma (L.warpAt b) x e H := by
  obtain ⟨a, ha⟩ := hL.exists_eventually_isSafe_warpAt_family
    H hsmall (fun Q hQ ↦ (hH.1 Q hQ).1)
  exact ⟨a, fun b hab ↦ ⟨fun Q hQ ↦
    ⟨ha b hab Q hQ, (hH.1 Q hQ).2⟩, hH.2⟩⟩

#print axioms HalfwayGeometry.exists_eventually_hammock_endpoint_incidence
#print axioms HalfwayGeometry.exists_eventually_hammock_limitWarp
#print axioms HalfwayGeometry.exists_eventually_isSafe_warpAt_family
#print axioms HalfwayGeometry.exists_eventually_hammock_warpAt

end DWeb.KappaLadder.Deferred
end Erdos599
