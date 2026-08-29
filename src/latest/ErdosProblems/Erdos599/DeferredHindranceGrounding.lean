/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LadderDeferredBookkeeping

/-!
# Grounded stages for deferred ladder bookkeeping

The successor-normalized ladder may first see the singleton at the marker
inserted at the current stage.  `Deferred.bookkeeping` removes that path
from the current selectable family.  Consequently every hanging deferred
record has a strictly earlier marker origin, and the original pressing-down
argument applies without a same-stage remainder.

This file deliberately keeps the deferred obstruction sets separate from
the legacy projections on `KappaLadder`: the two availability predicates
need not agree.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

universe u

variable {V : Type u} {G : DWeb V} {kappa : Cardinal.{u}}

/-- The obstruction stages for current-marker-deferred bookkeeping. -/
def phi (L : G.KappaLadder kappa) : Set (Ladder.Stage kappa) :=
  (bookkeeping L).phi

/-- Deferred stages at which an available ray is preferred. -/
def phiInfinite (L : G.KappaLadder kappa) : Set (Ladder.Stage kappa) :=
  (bookkeeping L).phiInfinite

/-- Deferred stages at which every available path is finite. -/
def phiFinite (L : G.KappaLadder kappa) : Set (Ladder.Stage kappa) :=
  (bookkeeping L).phiFinite

/-- Deferred obstruction stages whose chosen record starts in the source. -/
def phiGround (L : G.KappaLadder kappa) : Set (Ladder.Stage kappa) :=
  L.phiGround

/-- The hanging part of the deferred obstruction set. -/
def phiHanging (L : G.KappaLadder kappa) : Set (Ladder.Stage kappa) :=
  phi L \ phiGround L

/-- A stationary obstruction for the repaired, current-marker-deferred
ladder construction. -/
structure IsKappaHindrance (L : G.KappaLadder kappa) : Prop where
  legal : IsDeferredLegal L
  stationary : Stationary.IsStationaryBelow kappa (phi L)

/-- The grounded predicate itself is independent of which availability
family is used: it only inspects the chosen path. -/
@[simp]
theorem phiGround_eq_legacy (L : G.KappaLadder kappa) :
    phiGround L = L.phiGround := by
  rfl

/-- Every deferred obstruction stage is also a legacy obstruction stage.
The converse is intentionally not asserted. -/
theorem phi_subset_legacy (L : G.KappaLadder kappa)
    (hvalid : HasValidBookkeeping L) :
    phi L ⊆ L.phi := by
  intro a ha
  obtain ⟨p, hp⟩ :=
    ((bookkeeping L).mem_phi_iff_exists_chosen hvalid).1 ha
  have hpAvailable := (bookkeeping L).chosen_mem_available hvalid hp
  refine ⟨p, hpAvailable.1.1, ?_⟩
  simpa only [bookkeeping, KappaLadder.bookkeeping,
    Ladder.Bookkeeping.recordedBefore] using hpAvailable.2

/-- A deferred hanging stage has a chosen path, hence is a legacy hanging
stage as well.  This is the bridge to the already-proved strict marker
provenance of the deferred canonical construction. -/
theorem phiHanging_subset_legacy (L : G.KappaLadder kappa)
    (hvalid : HasValidBookkeeping L) :
    phiHanging L ⊆ L.phiHanging := by
  rintro a ⟨ha, hground⟩
  exact ⟨phi_subset_legacy L hvalid ha, by
    simpa only [phiGround_eq_legacy] using hground⟩

/-- The path selected by valid deferred bookkeeping at an obstruction
stage. -/
noncomputable def selectedPath (L : G.KappaLadder kappa)
    (hvalid : HasValidBookkeeping L) (a : phi L) : G.DPath :=
  Classical.choose
    (((bookkeeping L).mem_phi_iff_exists_chosen hvalid).1 a.2)

@[simp]
theorem chosen_selectedPath (L : G.KappaLadder kappa)
    (hvalid : HasValidBookkeeping L) (a : phi L) :
    L.chosen a.1 = some (selectedPath L hvalid a) :=
  Classical.choose_spec
    (((bookkeeping L).mem_phi_iff_exists_chosen hvalid).1 a.2)

/-- The strictly earlier marker stage supporting a hanging deferred record. -/
noncomputable def hangingOrigin (L : G.KappaLadder kappa)
    (hlegal : IsDeferredLegal L) (a : Ladder.Stage kappa) :
    Ladder.Stage kappa := by
  classical
  exact if ha : a ∈ phiHanging L then
    Classical.choose (hlegal.hangingProvenance a
      (phiHanging_subset_legacy L hlegal.validBookkeeping ha)
      (selectedPath L hlegal.validBookkeeping ⟨a, ha.1⟩)
      (chosen_selectedPath L hlegal.validBookkeeping ⟨a, ha.1⟩))
  else a

theorem hangingOrigin_spec (L : G.KappaLadder kappa)
    (hlegal : IsDeferredLegal L) {a : Ladder.Stage kappa}
    (ha : a ∈ phiHanging L) :
    hangingOrigin L hlegal a < a ∧
      L.marker (hangingOrigin L hlegal a) =
        some (selectedPath L hlegal.validBookkeeping ⟨a, ha.1⟩).initial := by
  rw [hangingOrigin, dif_pos ha]
  exact Classical.choose_spec (hlegal.hangingProvenance a
    (phiHanging_subset_legacy L hlegal.validBookkeeping ha)
    (selectedPath L hlegal.validBookkeeping ⟨a, ha.1⟩)
    (chosen_selectedPath L hlegal.validBookkeeping ⟨a, ha.1⟩))

theorem hangingOrigin_regressive (L : G.KappaLadder kappa)
    (hlegal : IsDeferredLegal L) :
    Stationary.IsRegressiveOn (phiHanging L) (hangingOrigin L hlegal) :=
  fun _ ha ↦ (hangingOrigin_spec L hlegal ha).1

/-- Persistence and disjointness make the deferred marker-origin map
injective, exactly as in source Lemma 7.15. -/
theorem hangingOrigin_injOn (L : G.KappaLadder kappa)
    (hlegal : IsDeferredLegal L) :
    Set.InjOn (hangingOrigin L hlegal) (phiHanging L) := by
  intro a ha b hb hab
  let pa : G.DPath := selectedPath L hlegal.validBookkeeping ⟨a, ha.1⟩
  let pb : G.DPath := selectedPath L hlegal.validBookkeeping ⟨b, hb.1⟩
  have hpa : L.chosen a = some pa :=
    chosen_selectedPath L hlegal.validBookkeeping ⟨a, ha.1⟩
  have hpb : L.chosen b = some pb :=
    chosen_selectedPath L hlegal.validBookkeeping ⟨b, hb.1⟩
  have hinitial : pa.initial = pb.initial := by
    have hma := (hangingOrigin_spec L hlegal ha).2
    have hmb := (hangingOrigin_spec L hlegal hb).2
    rw [hab] at hma
    exact Option.some.inj (hma.symm.trans hmb)
  rcases lt_trichotomy a b with hablt | rfl | hbalt
  · have hpaIE : pa ∈ G.inessentialPaths (L.successorWarp b) := by
      apply hlegal.recordedPathsPersist a pa hpa
        (Ladder.Stage.succExtended b)
      change a.1 + 1 ≤ b.1 + 1
      rw [← Order.succ_eq_add_one, ← Order.succ_eq_add_one]
      exact Order.succ_le_succ hablt.le
    have hpbWarp : pb ∈ L.successorWarp b :=
      (chosen_spec hlegal.validBookkeeping hpb).1.1
    by_cases hp : pa = pb
    · exact (bookkeeping L).chosen_stage_unique
        hlegal.validBookkeeping hpa (hp ▸ hpb)
    · exact False.elim <| Set.disjoint_left.1
        (hlegal.warpStages (Ladder.Stage.succExtended b)
          hpaIE.1 hpbWarp hp)
        pa.initial_mem_support (hinitial ▸ pb.initial_mem_support)
  · rfl
  · have hpbIE : pb ∈ G.inessentialPaths (L.successorWarp a) := by
      apply hlegal.recordedPathsPersist b pb hpb
        (Ladder.Stage.succExtended a)
      change b.1 + 1 ≤ a.1 + 1
      rw [← Order.succ_eq_add_one, ← Order.succ_eq_add_one]
      exact Order.succ_le_succ hbalt.le
    have hpaWarp : pa ∈ L.successorWarp a :=
      (chosen_spec hlegal.validBookkeeping hpa).1.1
    by_cases hp : pa = pb
    · exact (bookkeeping L).chosen_stage_unique
        hlegal.validBookkeeping hpa (hp ▸ hpb)
    · exact False.elim <| Set.disjoint_left.1
        (hlegal.warpStages (Ladder.Stage.succExtended a)
          hpaWarp hpbIE.1 hp)
        pa.initial_mem_support (hinitial ▸ pb.initial_mem_support)

theorem phiHanging_not_stationary (L : G.KappaLadder kappa)
    (hlegal : IsDeferredLegal L) :
    ¬ Stationary.IsStationaryBelow kappa (phiHanging L) :=
  Stationary.not_isStationaryBelow_of_injOn_regressive
    hlegal.uncountable hlegal.regular
    (hangingOrigin_regressive L hlegal)
    (hangingOrigin_injOn L hlegal)

/-- Deferred source Lemma 7.22: the grounded records of a stationary
deferred obstruction are stationary. -/
theorem IsKappaHindrance.phiGround_isStationary
    (L : G.KappaLadder kappa) (hL : IsKappaHindrance L) :
    Stationary.IsStationaryBelow kappa (phiGround L) :=
  Ladder.phiGround_isStationary
    hL.legal.regular hL.legal.uncountable
    (bookkeeping L) hL.legal.validBookkeeping
    (fun p : G.DPath ↦ p.initial) G.source
    hL.stationary (phiHanging_not_stationary L hL.legal)

end Deferred
end KappaLadder
end DWeb
end Erdos599
