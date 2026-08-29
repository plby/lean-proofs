/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeLinkClosureFinal
import ErdosProblems.Erdos599.SafeLinkQuotientMeeting

/-!
# Closing invariants for the dependent Section 6 construction

This file converts concrete path witnesses in a dependent Section 6 stage
into the boundary and tree clauses inserted by the next carrier.  It also
handles commitment vertices represented by isolated essential paths: such
a vertex is inserted by the next quotient transport and hence occurs on a
genuine path of the successor stage.
-/

noncomputable section

namespace Erdos599

open Set DirectedPath

universe u

namespace DWeb

variable {V : Type u} (G : DWeb V)

/-- Essentiality for a larger set descends to a smaller set containing the
point. -/
theorem essential_of_mem_of_subset_of_essential
    {S R : Set V} (hSR : S ⊆ R) {x : V}
    (hxS : x ∈ S) (hxR : x ∈ G.essential R) :
    x ∈ G.essential S := by
  refine ⟨hxS, ?_⟩
  intro hxRoof
  apply hxR.2
  apply G.roof_mono ?_ hxRoof
  intro z hz
  exact ⟨hSR hz.1, hz.2⟩

/-- If `X ⊆ Y`, a point essential for `Y` in the ambient web is still
essential for `Y` after quotienting by `X`. -/
theorem quotient_essential_of_essential_larger
    (hNoEnter : G.NoEdgeEnters G.source)
    {X Y : Set V} (hXY : X ⊆ Y) {x : V}
    (hx : x ∈ G.essential Y) :
    x ∈ (G.quotient X).essential Y := by
  let H := G.quotient X
  have heq : H.quotient Y = G.quotient Y := by
    calc
      H.quotient Y = G.quotient (X ∪ Y) :=
        G.quotient_quotient_eq_union X Y hNoEnter
      _ = G.quotient Y := by rw [Set.union_eq_right.mpr hXY]
  have hxSource : x ∈ (G.quotient Y).source := by
    rw [G.quotient_source_eq_union_sdiff_strictRoof_of_noEdgeEnters_general
      hNoEnter]
    exact ⟨Or.inr hx.1, fun hstrict ↦ hstrict.2 hx⟩
  have hxSourceH : x ∈ (H.quotient Y).source := by
    rw [heq]
    exact hxSource
  have hxNotStrict : x ∉ H.strictRoof Y := by
    rw [H.quotient_source_eq_union_sdiff_strictRoof_of_noEdgeEnters_general
      hNoEnter.quotient] at hxSourceH
    exact hxSourceH.2
  rw [← H.sdiff_strictRoof_self Y]
  exact ⟨hx.1, hxNotStrict⟩

/-- Every point essential for the new carrier occurs in the wave obtained
by transporting an old quotient wave to that carrier. -/
theorem essential_subset_vertexSet_waveToLargerQuotient
    (hNoEnter : G.NoEdgeEnters G.source)
    {X Y : Set V} (hXY : X ⊆ Y)
    (W : (G.quotient X).Wave) :
    (G.quotient X).essential Y ⊆
      (G.quotient Y).vertexSet
        (G.waveToLargerQuotient hNoEnter hXY W).1 := by
  let H := G.quotient X
  let Z : (H.quotient Y).Wave :=
    ⟨H.generalWaveQuotient Y W.1,
      H.isWave_generalWaveQuotient hNoEnter.quotient W.2⟩
  have heq : H.quotient Y = G.quotient Y := by
    calc
      H.quotient Y = G.quotient (X ∪ Y) :=
        G.quotient_quotient_eq_union X Y hNoEnter
      _ = G.quotient Y := by rw [Set.union_eq_right.mpr hXY]
  have htransport : G.waveToLargerQuotient hNoEnter hXY W = heq ▸ Z := by
    apply Subtype.ext
    rfl
  intro x hx
  rw [htransport, DWeb.vertexSet_castWebWave heq Z]
  change x ∈ (H.quotient Y).vertexSet (H.generalWaveQuotient Y W.1)
  rw [generalWaveQuotient, H.vertexSet_admissibleWarpQuotient]
  exact Or.inr hx

/-- A commitment point essential for the final union occurs on a genuine
successor-stage path meeting the successor carrier. -/
theorem exists_sectionSixAccumStage_path_meeting_of_mem_closure_essential
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) {z : V}
    (hzX : z ∈ G.sectionSixAccumClosure hNoEnter F K Y Q T y)
    (hzEss : z ∈ G.essential
      (G.sectionSixAccumClosure hNoEnter F K Y Q T y)) :
    ∃ n, ∃ p ∈
      (G.sectionSixAccumStage hNoEnter F K Y Q T y n).wave.1,
        (p.support ∩
          (G.sectionSixAccumStage hNoEnter F K Y Q T y n).carrier).Nonempty ∧
        z ∈ p.support := by
  let X := G.sectionSixAccumClosure hNoEnter F K Y Q T y
  obtain ⟨k, hzk⟩ := Set.mem_iUnion.mp hzX
  let s := G.sectionSixAccumStage hNoEnter F K Y Q T y k
  let Xnext := G.sectionSixAccumNextCarrier F K Y Q T s
  let old := G.sectionSixAccumOldInNext hNoEnter F K Y Q T s
  let next := G.sectionSixAccumNext hNoEnter F K Y Q T s
  have hzCarrier : z ∈ s.carrier := hzk
  have hzNext : z ∈ Xnext :=
    G.sectionSixAccumStage_carrier_subset_next F K Y Q T s hzCarrier
  have hNextX : Xnext ⊆ X := by
    intro v hv
    apply Set.mem_iUnion_of_mem (k + 1)
    change v ∈ Xnext
    exact hv
  have hzEssNext : z ∈ G.essential Xnext :=
    G.essential_of_mem_of_subset_of_essential hNextX hzNext hzEss
  have hzEssQ : z ∈ (G.quotient s.carrier).essential Xnext :=
    G.quotient_essential_of_essential_larger hNoEnter
      (G.sectionSixAccumStage_carrier_subset_next F K Y Q T s)
      hzEssNext
  have hzOldVertex : z ∈ (G.quotient Xnext).vertexSet old.1 := by
    exact G.essential_subset_vertexSet_waveToLargerQuotient hNoEnter
      (G.sectionSixAccumStage_carrier_subset_next F K Y Q T s)
      s.wave hzEssQ
  obtain ⟨p, hpOld, hzp⟩ := hzOldVertex
  obtain ⟨q, hqNext, hpq⟩ :=
    (G.sectionSixAccumOldInNext_le_next hNoEnter F K Y Q T s).1 p hpOld
  have hzq : z ∈ q.support :=
    (G.quotient Xnext).support_mono_of_extends hpq hzp
  refine ⟨k + 1, q, ?_, ?_, hzq⟩
  · change q ∈ next.wave.1
    exact hqNext
  · change (q.support ∩ Xnext).Nonempty
    exact ⟨z, hzq, hzNext⟩

/-- A genuine stage path meeting its carrier closes the boundary datum at
every boundary vertex on that path. -/
theorem sectionSixAccum_F_subset_closure_of_stage_path
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y z : V)
    (hzY : z ∈ Y)
    (hstage : ∃ n, ∃ p ∈
      (G.sectionSixAccumStage hNoEnter F K Y Q T y n).wave.1,
        (p.support ∩
          (G.sectionSixAccumStage hNoEnter F K Y Q T y n).carrier).Nonempty ∧
        z ∈ p.support) :
    F z ⊆ G.sectionSixAccumClosure hNoEnter F K Y Q T y := by
  obtain ⟨n, p, hp, hpMeet, hzp⟩ := hstage
  let s := G.sectionSixAccumStage hNoEnter F K Y Q T y n
  let p' : G.DPath := G.liftQuotientPath s.carrier p
  have hp' : p' ∈ G.sectionSixAccumStageLift s := ⟨p, hp, rfl⟩
  have hp'Meet : (p'.support ∩ s.carrier).Nonempty := by
    simpa only [p', G.support_liftQuotientPath] using hpMeet
  have hzp' : z ∈ p'.support := by
    simpa only [p', G.support_liftQuotientPath] using hzp
  apply G.sectionSixAccum_F_subset_closure hNoEnter F K Y Q T y n
  refine ⟨hzY, ?_⟩
  exact Set.mem_iUnion_of_mem p'
    (Set.mem_iUnion_of_mem ⟨hp', hp'Meet⟩ hzp')

/-- A tree vertex on a genuine stage path meeting its carrier is inserted
in the dependent closure. -/
theorem sectionSixAccum_mem_closure_of_stage_path
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y z : V)
    (hzT : z ∈ T)
    (hstage : ∃ n, ∃ p ∈
      (G.sectionSixAccumStage hNoEnter F K Y Q T y n).wave.1,
        (p.support ∩
          (G.sectionSixAccumStage hNoEnter F K Y Q T y n).carrier).Nonempty ∧
        z ∈ p.support) :
    z ∈ G.sectionSixAccumClosure hNoEnter F K Y Q T y := by
  obtain ⟨n, p, hp, hpMeet, hzp⟩ := hstage
  let s := G.sectionSixAccumStage hNoEnter F K Y Q T y n
  let p' : G.DPath := G.liftQuotientPath s.carrier p
  have hp' : p' ∈ G.sectionSixAccumStageLift s := ⟨p, hp, rfl⟩
  have hp'Meet : (p'.support ∩ s.carrier).Nonempty := by
    simpa only [p', G.support_liftQuotientPath] using hpMeet
  have hzp' : z ∈ p'.support := by
    simpa only [p', G.support_liftQuotientPath] using hzp
  apply G.sectionSixAccum_meetingTree_subset_closure
    hNoEnter F K Y Q T y n
  refine ⟨?_, hzT⟩
  exact Set.mem_iUnion_of_mem p'
    (Set.mem_iUnion_of_mem ⟨hp', hp'Meet⟩ hzp')

/-- A boundary point which is both committed and essential for the final
commitment set has its obstruction inserted by the dependent recurrence. -/
theorem sectionSixAccum_F_subset_closure_of_mem_essential
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y z : V)
    (hzY : z ∈ Y)
    (hzX : z ∈ G.sectionSixAccumClosure hNoEnter F K Y Q T y)
    (hzEss : z ∈ G.essential
      (G.sectionSixAccumClosure hNoEnter F K Y Q T y)) :
    F z ⊆ G.sectionSixAccumClosure hNoEnter F K Y Q T y := by
  apply G.sectionSixAccum_F_subset_closure_of_stage_path
    hNoEnter F K Y Q T y z hzY
  exact G.exists_sectionSixAccumStage_path_meeting_of_mem_closure_essential
    hNoEnter F K Y Q T y hzX hzEss

/-- A commitment-set vertex occurring on a quotient wave is essential for
the commitment set.  Quotient paths can contain such a vertex only at their
initial point, and the initial point lies in the quotient source. -/
theorem essential_closure_of_mem_wave_support_mem_closure
    (hNoEnter : G.NoEdgeEnters G.source) {X : Set V}
    {W : Set (G.quotient X).DPath}
    (hW : (G.quotient X).IsWave W)
    {p : (G.quotient X).DPath} (hpW : p ∈ W)
    {x : V} (hxp : x ∈ p.support) (hxX : x ∈ X) :
    x ∈ G.essential X := by
  have hxInitial : x = p.initial :=
    G.eq_initial_of_mem_support_of_mem_quotient X p hxp hxX
  have hpSource : p.initial ∈ (G.quotient X).source :=
    hW.2.1 ⟨p, hpW, rfl⟩
  rw [G.quotient_source_eq_union_sdiff_strictRoof_of_noEdgeEnters_general
    hNoEnter] at hpSource
  rw [← G.sdiff_strictRoof_self X]
  exact ⟨hxX, fun hxStrict ↦ hpSource.2 (hxInitial ▸ hxStrict)⟩

end DWeb

end Erdos599
