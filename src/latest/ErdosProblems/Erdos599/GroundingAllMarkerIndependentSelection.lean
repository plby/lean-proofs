/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerFootprintClosure
import ErdosProblems.Erdos599.GroundingAssembly

/-!
# Independent selection from the actual shortened stationary fans

Requests are embedded below kappa. Well-founded recursion chooses from
each shortened fan a route avoiding all earlier countable footprints.
The nonstationary ideal is kappa-complete, and earlier footprints miss
the current request. Closure then gives pairwise disjoint full footprints.
The older assembly is used only for its generic predecessor-cardinality
lemma; none of its auxiliary graphs or controls is substituted here.
-/

noncomputable section

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set Cardinal DirectedPath Alternating GroundingAllMarkerPorts Stationary

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I) {kappa : Cardinal.{u}}
  {U : Popular.KappaIndexed L.web kappa}
  (S : Popular.PopularSeparator U)
  (hInitial : ∀ i, (L.record i).initial ∉ L.markers)

def independentRequestRank : L.Request S.cut ↪ Below kappa :=
  Classical.choice (by
    apply Cardinal.lift_mk_le'.mp
    rw [Stationary.mk_below]
    simpa only [Cardinal.lift_lift] using Cardinal.lift_le.mpr (L.requests_card_le S))

abbrev ShortenedChoice (r : L.Request S.cut) := (L.shortenedRecordFan S r hInitial).paths

theorem rank_predecessors_small (rank : L.Request S.cut ↪ Below kappa) (r : L.Request S.cut) :
    #(ULift.{u + 1} {s : L.Request S.cut // rank s < rank r}) < Cardinal.lift.{u + 1} kappa := by
  let f : ULift.{u + 1} {s : L.Request S.cut // rank s < rank r} → Set.Iio (rank r) :=
    fun s ↦ ⟨rank s.down.1, s.down.2⟩
  have hf : Function.Injective f := by
    intro s t h
    apply ULift.ext
    apply Subtype.ext
    exact rank.injective (congrArg Subtype.val h)
  exact (Cardinal.mk_le_of_injective hf).trans_lt
    (GroundingAssembly.mk_Iio_below_lt_lift (rank r))

/-- The recursion step has a candidate for every possible earlier
selection of legitimate fan members. No global independence is assumed. -/
theorem exists_fresh_shortened_choice (rank : L.Request S.cut ↪ Below kappa)
    (r : L.Request S.cut)
    (previous : ∀ s : L.Request S.cut, rank s < rank r → L.ShortenedChoice S hInitial s) :
    ∃ p : L.ShortenedChoice S hInitial r, ∀ s (hsr : rank s < rank r),
      Disjoint p.1.support (L.routeFootprint S.cut (previous s hsr).1) := by
  classical
  let F := L.shortenedRecordFan S r hInitial
  let Earlier := ULift.{u + 1} {s : L.Request S.cut // rank s < rank r}
  let collision (s : Earlier) := PopularSwitching.restrictPaths F
    {p | (p.support ∩ L.routeFootprint S.cut (previous s.down.1 s.down.2).1).Nonempty}
  let bad (s : Earlier) := Popular.initialIndicesOf U
    (collision s).paths (collision s).starts_in_source
  have hbad : ∀ s, ¬ IsStationaryBelow kappa (bad s) := by
    intro s
    apply PopularAuxiliary.Input.joinedFamily_initialIndices_nonstationary_of_meets_countable
      U (collision s) (L.routeFootprint_countable S.cut (previous s.down.1 s.down.2).1)
    · apply Set.disjoint_left.mpr
      intro a ha har
      have har' : a = r.1 := har
      subst a
      have hsne : s.down.1 ≠ r := by
        intro h
        exact (ne_of_lt s.down.2) (congrArg rank h)
      exact L.shortenedRecordFan_other_request_not_footprint S s.down.1 r hsne
        hInitial (previous s.down.1 s.down.2).2 ha
    · intro p hp
      obtain ⟨x, hxp, hxFoot⟩ := hp.2
      exact ⟨x, hxFoot, hxp⟩
  have hbadUnion : ¬ IsStationaryBelow kappa (⋃ s, bad s) :=
    not_isStationaryBelow_iUnion_of_lt U.regular U.uncountable
      (L.rank_predecessors_small S rank r) hbad
  have hfresh := PopularSwitching.stationary_diff_of_stationary_of_nonstationary
    U.regular U.uncountable (L.shortenedRecordFan_stationary S r hInitial) hbadUnion
  obtain ⟨a, haFan, haBad⟩ := hfresh.nonempty
  obtain ⟨p, hp, hpa⟩ := haFan
  refine ⟨⟨p, hp⟩, ?_⟩
  intro s hsr
  by_contra hnot
  obtain ⟨x, hxp, hxFoot⟩ := Set.not_disjoint_iff.mp hnot
  have haOne : a ∈ bad ⟨⟨s, hsr⟩⟩ := ⟨p, ⟨hp, ⟨x, hxp, hxFoot⟩⟩, hpa⟩
  exact haBad (Set.mem_iUnion.mpr ⟨⟨⟨s, hsr⟩⟩, haOne⟩)

def chooseIndependentAt (rank : L.Request S.cut ↪ Below kappa) (r : L.Request S.cut)
    (previous : ∀ s : L.Request S.cut, rank s < rank r → L.ShortenedChoice S hInitial s) :
    L.ShortenedChoice S hInitial r :=
  Classical.choose (L.exists_fresh_shortened_choice S hInitial rank r previous)

theorem chooseIndependentAt_avoids (rank : L.Request S.cut ↪ Below kappa)
    (r : L.Request S.cut)
    (previous : ∀ s : L.Request S.cut, rank s < rank r → L.ShortenedChoice S hInitial s)
    (s : L.Request S.cut) (hsr : rank s < rank r) :
    Disjoint (L.chooseIndependentAt S hInitial rank r previous).1.support
      (L.routeFootprint S.cut (previous s hsr).1) :=
  Classical.choose_spec (L.exists_fresh_shortened_choice S hInitial rank r previous) s hsr

def independentChoice (rank : L.Request S.cut ↪ Below kappa) (r : L.Request S.cut) :
    L.ShortenedChoice S hInitial r :=
  WellFounded.fix (InvImage.wf rank wellFounded_lt)
    (fun r previous ↦ L.chooseIndependentAt S hInitial rank r previous) r

theorem independentChoice_eq (rank : L.Request S.cut ↪ Below kappa) (r : L.Request S.cut) :
    L.independentChoice S hInitial rank r = L.chooseIndependentAt S hInitial rank r
      (fun s _ ↦ L.independentChoice S hInitial rank s) :=
  WellFounded.fix_eq (InvImage.wf rank wellFounded_lt)
    (fun r previous ↦ L.chooseIndependentAt S hInitial rank r previous) r

theorem independentChoice_avoids_earlier (rank : L.Request S.cut ↪ Below kappa)
    (r s : L.Request S.cut) (hsr : rank s < rank r) :
    Disjoint (L.independentChoice S hInitial rank r).1.support
      (L.routeFootprint S.cut (L.independentChoice S hInitial rank s).1) := by
  rw [L.independentChoice_eq S hInitial rank r]
  exact L.chooseIndependentAt_avoids S hInitial rank r
    (fun s _ ↦ L.independentChoice S hInitial rank s) s hsr

def independentSelectedPath (r : L.Request S.cut) : FinitePath L.web.graph :=
  (L.independentChoice S hInitial (L.independentRequestRank S) r).1

theorem independentSelectedPath_mem (r : L.Request S.cut) :
    L.independentSelectedPath S hInitial r ∈ (L.shortenedRecordFan S r hInitial).paths :=
  (L.independentChoice S hInitial (L.independentRequestRank S) r).2

theorem independentSelectedPath_footprints_disjoint : Pairwise (fun r s : L.Request S.cut ↦
    Disjoint (L.routeFootprint S.cut (L.independentSelectedPath S hInitial r))
      (L.routeFootprint S.cut (L.independentSelectedPath S hInitial s))) := by
  intro r s hrs
  have hranks : L.independentRequestRank S r ≠ L.independentRequestRank S s :=
    fun h ↦ hrs ((L.independentRequestRank S).injective h)
  rcases lt_or_gt_of_ne hranks with hlt | hgt
  · exact (L.routeFootprint_disjoint_of_support_disjoint S.cut _ _
      (L.independentChoice_avoids_earlier S hInitial (L.independentRequestRank S) s r hlt)).symm
  · exact L.routeFootprint_disjoint_of_support_disjoint S.cut _ _
      (L.independentChoice_avoids_earlier S hInitial (L.independentRequestRank S) r s hgt)

theorem independentSelectedPath_supports_disjoint : Pairwise (fun r s : L.Request S.cut ↦
    Disjoint (L.independentSelectedPath S hInitial r).support
      (L.independentSelectedPath S hInitial s).support) := by
  intro r s hrs
  exact (L.independentSelectedPath_footprints_disjoint S hInitial hrs).mono
    (L.support_subset_routeFootprint S.cut _) (L.support_subset_routeFootprint S.cut _)

#print axioms exists_fresh_shortened_choice
#print axioms independentSelectedPath
#print axioms independentSelectedPath_footprints_disjoint
#print axioms independentSelectedPath_supports_disjoint

end Erdos599.GroundingAllMarkerAuxiliary.Input
