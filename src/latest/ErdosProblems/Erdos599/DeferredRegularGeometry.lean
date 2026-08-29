/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredHalfwayGeometry

/-!
# Regular ladder geometry with deferred bookkeeping

The deferred choice rule changes only the path recorded at a stage.  This
module records the two geometric facts needed to replace the legacy/split
bookkeeping in the regular-cardinal argument:

* the deferred geometry package supplies the exact construction interface
  used by Lemma 7.6; and
* the witness produced by Lemma 7.6 was already present in the current
  accumulated warp, so it cannot start at the marker born at that stage.

Consequently a hindered rung is an obstruction for the deferred
bookkeeping, not merely for the larger successor-normalized bookkeeping.
The successor and cardinal estimates accept the one-sided half-way geometry;
no marker-exhaustion assertion is used in them.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

universe u

variable {V : Type u} {G : DWeb V} {kappa : Cardinal.{u}}

/-- Deferred legality contains all geometric construction laws used by
source Lemma 7.6. -/
theorem IsDeferredLegal.lemma76Data {L : G.KappaLadder kappa}
    (hL : IsDeferredLegal L) : L.Lemma76Data where
  waveRungs := hL.waveRungs
  exactSuccessorArrows := hL.exactSuccessorArrows
  roofsSourceAtStages := hL.roofsSourceAtStages
  recordedPathsPersist := hL.recordedPathsPersist

/-- The ordinary successor of a deferred ladder stage is still below the
regular uncountable cardinal. -/
def successorStage (L : G.KappaLadder kappa)
    (hlegal : HalfwayGeometry L) (a : Ladder.Stage kappa) :
    Ladder.Stage kappa :=
  ⟨a.1 + 1, by
    have hone : #(PUnit) < kappa := by
      simpa only [mk_punit] using
        (lt_trans Cardinal.one_lt_aleph0 hlegal.uncountable)
    have hbound := Stationary.iSup_add_one_lt_ord_of_lt
      hlegal.regular (f := fun _ : PUnit ↦ a.1) hone (fun _ ↦ a.2)
    exact lt_of_le_of_lt
      (Ordinal.le_iSup (fun _ : PUnit ↦ a.1 + 1) PUnit.unit) hbound⟩

@[simp]
theorem successorStage_val (L : G.KappaLadder kappa)
    (hlegal : HalfwayGeometry L) (a : Ladder.Stage kappa) :
    (successorStage L hlegal a).1 = a.1 + 1 :=
  rfl

theorem successorStage_le_iff_lt (L : G.KappaLadder kappa)
    (hlegal : HalfwayGeometry L) {a b : Ladder.Stage kappa} :
    successorStage L hlegal a ≤ b ↔ a < b := by
  change a.1 + 1 ≤ b.1 ↔ a.1 < b.1
  exact Order.add_one_le_iff

/-- Marker freshness and essential-frontier geometry place a marker born at
`a` outside the roof of the frontier at `a`.  No bookkeeping field is used. -/
theorem marker_not_mem_roof_frontier
    (L : G.KappaLadder kappa) (hlegal : HalfwayGeometry L)
    {a : Ladder.Stage kappa} {y : V} (hy : L.marker a = some y) :
    y ∉ G.roof (L.frontier a) := hlegal.markerOutsideRoof a y hy

/-- If the current marker is outside the current accumulated family, the
old-component witness from Lemma 7.6 is selectable by deferred
bookkeeping. -/
theorem IsDeferredLegal.phiHindrance_subset_phi_of_markerOutside
    {L : G.KappaLadder kappa} (hL : IsDeferredLegal L)
    (hG : G.IsNormalized)
    (hmarkerOutside : ∀ (a : Ladder.Stage kappa) (y : V),
      L.marker a = some y → y ∉ G.vertexSet (L.warpAt a)) :
    L.phiHindrance ⊆ phi L := by
  intro a ha
  obtain ⟨p, hpCurrent, hpNext, hpNotRecorded⟩ :=
    L.exists_warpAt_available_of_mem_phiHindrance
      hG hL.lemma76Data ha
  have havoid : L.marker a ≠ some p.initial := by
    intro hmarker
    exact hmarkerOutside a p.initial hmarker
      ⟨p, hpCurrent, p.initial_mem_support⟩
  refine ⟨p, ⟨hpNext, havoid⟩, ?_⟩
  simpa only [bookkeeping, KappaLadder.bookkeeping,
    Ladder.Bookkeeping.recordedBefore] using hpNotRecorded

/-- The marker geometry of the deferred canonical ladder is exactly the
marker geometry of the canonical core: a marker born at `a` is outside the
current accumulated family `Y_a`. -/
theorem canonicalDeferredLadder_marker_not_mem_currentVertexSet
    (preferred : Ladder.Stage kappa → Option V)
    (hNoEnter : G.NoEdgeEnters G.source)
    (a : Ladder.Stage kappa) (y : V)
    (hy : (canonicalDeferredLadder G kappa preferred).marker a = some y) :
    y ∉ G.vertexSet
      ((canonicalDeferredLadder G kappa preferred).warpAt a) := by
  change
    y ∉ G.vertexSet ((canonicalLadder G kappa preferred).warpAt a)
  exact canonicalLadder_marker_not_mem_currentVertexSet
    preferred hNoEnter a y hy

/-- Deferred Lemma 7.6 for the actual canonical regular ladder. -/
theorem canonicalDeferredLadder_phiHindrance_subset_phi
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : ℵ₀ < kappa)
    (hG : G.IsNormalized) (hNoEnter : G.NoEdgeEnters G.source) :
    let L := canonicalDeferredLadder G kappa preferred
    L.phiHindrance ⊆ phi L := by
  dsimp only
  let L := canonicalDeferredLadder G kappa preferred
  have hlegal : IsDeferredLegal L :=
    canonicalDeferredLadder_isDeferredLegal
      preferred hkappa huncountable hNoEnter
  apply hlegal.phiHindrance_subset_phi_of_markerOutside hG
  intro a y hy
  exact canonicalDeferredLadder_marker_not_mem_currentVertexSet
    preferred hNoEnter a y hy

/-- Outside the deferred obstruction set, every successor-inessential
component except possibly the single component starting at the current
marker was recorded earlier.  Hence there are fewer than `kappa` such
components. -/
theorem mk_inessentialSuccessor_lt_of_not_mem_phi
    {L : G.KappaLadder kappa} (hL : HalfwayGeometry L)
    (a : Ladder.Stage kappa) (ha : a ∉ phi L) :
    #(G.inessentialPaths (L.successorWarp a)) < kappa := by
  classical
  let R := (bookkeeping L).recordedBefore a
  have hrecordedCard : #R < kappa := by
    let stageWitness : ∀ p : R, ∃ b : Ladder.Stage kappa,
        b < a ∧ L.chosen b = some p.1 := fun p ↦ p.2
    let recordStage : R → Ladder.Stage kappa :=
      fun p ↦ Classical.choose (stageWitness p)
    have hrecordStage : Function.Injective recordStage := by
      intro p q hpq
      apply Subtype.ext
      have hp := (Classical.choose_spec (stageWitness p)).2
      have hq := (Classical.choose_spec (stageWitness q)).2
      rw [show Classical.choose (stageWitness p) =
        Classical.choose (stageWitness q) by exact hpq] at hp
      exact Option.some.inj (hp.symm.trans hq)
    exact RegularCardinal.mk_lt_of_injective_bounded_stage
      a recordStage hrecordStage
        (fun p ↦ (Classical.choose_spec (stageWitness p)).1)
  let code : G.inessentialPaths (L.successorWarp a) → R ⊕ PUnit :=
    fun p ↦ if havoid : L.marker a ≠ some p.1.initial then
      Sum.inl ⟨p.1, by
        by_contra hpNotRecorded
        exact ha ⟨p.1, ⟨p.2, havoid⟩, hpNotRecorded⟩⟩
    else Sum.inr PUnit.unit
  have hcode : Function.Injective code := by
    intro p q hpq
    by_cases hpavoid : L.marker a ≠ some p.1.initial
    · by_cases hqavoid : L.marker a ≠ some q.1.initial
      · have hpqValue : p.1 = q.1 := by
          have := hpq
          simp only [code, dif_pos hpavoid, dif_pos hqavoid,
            Sum.inl.injEq, Subtype.mk.injEq] at this
          exact this
        exact Subtype.ext hpqValue
      · have := hpq
        simp only [code, dif_pos hpavoid, dif_neg hqavoid] at this
        exact (Sum.inl_ne_inr this).elim
    · by_cases hqavoid : L.marker a ≠ some q.1.initial
      · have := hpq
        simp only [code, dif_neg hpavoid, dif_pos hqavoid] at this
        exact (Sum.inr_ne_inl this).elim
      · apply Subtype.ext
        apply DWeb.IsWarp.eq_of_initial_eq G
          (hL.warpStages (Ladder.Stage.succExtended a)) p.2.1 q.2.1
        have hpMarker : L.marker a = some p.1.initial :=
          not_ne_iff.mp hpavoid
        have hqMarker : L.marker a = some q.1.initial :=
          not_ne_iff.mp hqavoid
        exact Option.some.inj (hpMarker.symm.trans hqMarker)
  have hcodeCard : #(R ⊕ PUnit) < kappa := by
    rw [Cardinal.mk_sum]
    simp only [Cardinal.lift_id, Cardinal.mk_punit]
    exact Cardinal.add_lt_of_lt hL.regular.aleph0_le hrecordedCard
      (Cardinal.one_lt_aleph0.trans hL.uncountable)
  exact (Cardinal.mk_le_of_injective hcode).trans_lt hcodeCard

/-- Current-stage form of the deferred inessential-path estimate. -/
theorem mk_inessentialWarpAt_lt_of_not_mem_phi
    {L : G.KappaLadder kappa} (hL : HalfwayGeometry L)
    (a : Ladder.Stage kappa) (ha : a ∉ phi L) :
    #(G.inessentialPaths (L.warpAt a)) < kappa :=
  (Cardinal.mk_subtype_mono (hL.currentInessentialPersists a)).trans_lt
    (mk_inessentialSuccessor_lt_of_not_mem_phi hL a ha)

#print axioms marker_not_mem_roof_frontier
#print axioms mk_inessentialSuccessor_lt_of_not_mem_phi
#print axioms mk_inessentialWarpAt_lt_of_not_mem_phi

end Deferred
end KappaLadder
end DWeb
end Erdos599
