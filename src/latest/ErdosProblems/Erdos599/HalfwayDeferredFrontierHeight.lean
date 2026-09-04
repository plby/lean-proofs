/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayClause
import ErdosProblems.Erdos599.DeferredHalfwayGeometry
import ErdosProblems.Erdos599.CountableAssignment
import ErdosProblems.Erdos599.GroundingHangingLadderRank
import ErdosProblems.Erdos599.GroundingDescentBridge
import ErdosProblems.Erdos599.RoofQuotient
import ErdosProblems.Erdos599.RegularCardinal

/-!
# The altitude of a deferred-legal ladder frontier

An accumulated legal-ladder family need not be a wave: besides the
components starting in the original source it can contain components which
start at earlier marker vertices.  At a stage below `kappa^+`, however, the
supports of all these hanging components have cardinality at most `kappa`.
Deleting those supports leaves the grounded components as a wave in the
deleted web.  Lemma 3.27 then turns that deleted wave into a wave in the
quotient and shows that it roofs the essential accumulated frontier.

This is the final altitude estimate in the half-way construction.  It does
not assert that the accumulated family itself is a wave.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace CardinalInduction

open DirectedPath

universe u

variable {V : Type u}

namespace DeferredHalfwayFrontierHeight

variable {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- The source-starting part of the accumulated family at a ladder stage. -/
abbrev groundedAt (L : Gamma.KappaLadder (succ kappa))
    (a : Ladder.Stage (succ kappa)) : Set Gamma.DPath :=
  PopularAuxiliary.groundedPaths Gamma (L.warpAt a)

/-- The marker-starting part of the accumulated family at a ladder stage. -/
abbrev hangingAt (L : Gamma.KappaLadder (succ kappa))
    (a : Ladder.Stage (succ kappa)) : Set Gamma.DPath :=
  PopularAuxiliary.hangingPaths Gamma (L.warpAt a)

/-- The deletion set used in the height witness: all vertices of all
marker-starting components accumulated before the selected stage. -/
def hangingVerticesAt (L : Gamma.KappaLadder (succ kappa))
    (a : Ladder.Stage (succ kappa)) : Set V :=
  Gamma.vertexSet (hangingAt L a)

/-- Distinct grounded and hanging components of the same warp have disjoint
vertex sets. -/
theorem disjoint_groundedAt_hangingAt
    {L : Gamma.KappaLadder (succ kappa)}
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L) (a : Ladder.Stage (succ kappa)) :
    Disjoint (Gamma.vertexSet (groundedAt L a))
      (Gamma.vertexSet (hangingAt L a)) := by
  apply Set.disjoint_left.2
  rintro x ⟨p, hp, hxp⟩ ⟨q, hq, hxq⟩
  by_cases hpq : p = q
  · subst q
    exact hq.2 hp.2
  · exact Set.disjoint_left.1
      (hL.warpStages (Ladder.Stage.toExtended a) hp.1 hq.1 hpq) hxp hxq

/-- In a normalized web the hanging deletion set contains no original
source vertex. -/
theorem hangingVerticesAt_subset_source_compl
    {L : Gamma.KappaLadder (succ kappa)}
    (hGamma : Gamma.IsNormalized) (a : Ladder.Stage (succ kappa)) :
    hangingVerticesAt L a ⊆ Gamma.sourceᶜ := by
  rintro x ⟨p, hp, hxp⟩ hxsource
  have hxinitial : x = p.initial :=
    Alternating.path_eq_initial_of_mem_support_of_mem_source
      hGamma p hxp hxsource
  exact hp.2 (hxinitial ▸ hxsource)

/-- Choose the marker stage which owns a hanging accumulated component. -/
noncomputable def ownerStage
    {L : Gamma.KappaLadder (succ kappa)} (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (a : Ladder.Stage (succ kappa)) (p : hangingAt L a) :
    Ladder.Stage (succ kappa) :=
  Classical.choose (show ∃ b : Ladder.Stage (succ kappa),
      Ladder.Stage.succExtended b ≤ Ladder.Stage.toExtended a ∧
        L.marker b = some p.1.initial by
    rcases hL.accumulatedInitialProvenance
        (Ladder.Stage.toExtended a) p.1 p.2.1 with
      hpSource | ⟨b, hb, hmarker⟩
    · exact False.elim (p.2.2 hpSource)
    · exact ⟨b, hb, hmarker⟩)

theorem ownerStage_spec
    {L : Gamma.KappaLadder (succ kappa)} (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (a : Ladder.Stage (succ kappa)) (p : hangingAt L a) :
    Ladder.Stage.succExtended (ownerStage hL a p) ≤
        Ladder.Stage.toExtended a ∧
      L.marker (ownerStage hL a p) = some p.1.initial :=
  Classical.choose_spec (show ∃ b : Ladder.Stage (succ kappa),
      Ladder.Stage.succExtended b ≤ Ladder.Stage.toExtended a ∧
        L.marker b = some p.1.initial by
    rcases hL.accumulatedInitialProvenance
        (Ladder.Stage.toExtended a) p.1 p.2.1 with
      hpSource | ⟨b, hb, hmarker⟩
    · exact False.elim (p.2.2 hpSource)
    · exact ⟨b, hb, hmarker⟩)

theorem ownerStage_lt
    {L : Gamma.KappaLadder (succ kappa)} (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (a : Ladder.Stage (succ kappa)) (p : hangingAt L a) :
    ownerStage hL a p < a := by
  have h := (ownerStage_spec hL a p).1
  change (ownerStage hL a p).1 + 1 ≤ a.1 at h
  have hord : (ownerStage hL a p).1 < a.1 :=
    Order.add_one_le_iff.mp h
  exact hord

theorem ownerStage_injective
    {L : Gamma.KappaLadder (succ kappa)} (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (a : Ladder.Stage (succ kappa)) :
    Function.Injective (ownerStage hL a) := by
  intro p q hpq
  apply Subtype.ext
  by_contra hne
  have hpmarker := (ownerStage_spec hL a p).2
  have hqmarker := (ownerStage_spec hL a q).2
  rw [hpq] at hpmarker
  have hinitial : p.1.initial = q.1.initial :=
    Option.some.inj (hpmarker.symm.trans hqmarker)
  have hdisjoint := hL.warpStages (Ladder.Stage.toExtended a)
    p.2.1 q.2.1 hne
  exact Set.disjoint_left.1 hdisjoint p.1.initial_mem_support
    (hinitial ▸ q.1.initial_mem_support)

/-- There are at most `kappa` hanging components at a stage below
`(succ kappa).ord`. -/
theorem mk_hangingAt_le
    {L : Gamma.KappaLadder (succ kappa)} (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (a : Ladder.Stage (succ kappa)) :
    #(hangingAt L a) ≤ kappa := by
  have hlt : #(hangingAt L a) < succ kappa :=
    RegularCardinal.mk_lt_of_injective_bounded_stage a
      (ownerStage hL a) (ownerStage_injective hL a)
      (ownerStage_lt hL a)
  exact lt_succ_iff.mp hlt

/-- A family of at most `kappa` directed paths uses at most `kappa`
vertices when `kappa` is infinite. -/
theorem mk_vertexSet_le_of_mk_family_le
    (hkappa : aleph0 ≤ kappa) (W : Set Gamma.DPath)
    (hW : #W ≤ kappa) :
    #(Gamma.vertexSet W) ≤ kappa := by
  by_cases hnonempty : W.Nonempty
  · let : Nonempty W := hnonempty.to_subtype
    have heq : Gamma.vertexSet W = ⋃ p : W, p.1.support := by
      ext x
      simp only [DWeb.vertexSet, Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨p, hp, hxp⟩
        exact ⟨⟨p, hp⟩, hxp⟩
      · rintro ⟨p, hxp⟩
        exact ⟨p.1, p.2, hxp⟩
    rw [heq]
    refine (Cardinal.mk_iUnion_le (fun p : W ↦ p.1.support)).trans ?_
    apply Cardinal.mul_le_of_le hkappa hW
    apply ciSup_le
    intro p
    exact p.1.support_countable.le_aleph0.trans hkappa
  · have hempty : W = ∅ := Set.not_nonempty_iff_eq_empty.mp hnonempty
    have hvertices : Gamma.vertexSet W = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨p, hp, _⟩
      rw [hempty] at hp
      exact hp
    rw [hvertices]
    simp

theorem mk_hangingVerticesAt_le
    {L : Gamma.KappaLadder (succ kappa)} (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (hkappa : aleph0 ≤ kappa) (a : Ladder.Stage (succ kappa)) :
    #(hangingVerticesAt L a) ≤ kappa :=
  mk_vertexSet_le_of_mk_family_le hkappa (hangingAt L a)
    (mk_hangingAt_le hL a)

/-- Restrict the grounded accumulated components to the web obtained by
deleting all hanging-component vertices. -/
noncomputable def groundedDeleteFamily
    {L : Gamma.KappaLadder (succ kappa)} (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (a : Ladder.Stage (succ kappa)) :
    Set (Gamma.delete (hangingVerticesAt L a)).DPath :=
  Gamma.restrictDeleteFamily (hangingVerticesAt L a) (groundedAt L a)
    (by
      rw [Set.disjoint_left]
      intro x hxGrounded hxHanging
      exact Set.disjoint_left.1 (disjoint_groundedAt_hangingAt hL a)
        hxGrounded hxHanging)

/-- After the hanging components are deleted, the grounded accumulated
components are a wave.  The separator proof uses the legal ladder's roofing
invariant; a terminal belonging to a hanging component cannot be met by a
path in the deleted web. -/
theorem groundedDeleteFamily_isWave
    {L : Gamma.KappaLadder (succ kappa)}
    (hGamma : Gamma.IsNormalized) (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (a : Ladder.Stage (succ kappa)) :
    (Gamma.delete (hangingVerticesAt L a)).IsWave
      (groundedDeleteFamily hL a) := by
  let X := hangingVerticesAt L a
  let W := L.warpAt a
  let Gd := groundedAt L a
  have havoid : Disjoint (Gamma.vertexSet Gd) X :=
    disjoint_groundedAt_hangingAt hL a
  have hGdWarp : Gamma.IsWarp Gd := by
    intro p hp q hq hpq
    exact hL.warpStages (Ladder.Stage.toExtended a)
      hp.1 hq.1 hpq
  refine ⟨DWeb.IsWarp.restrictDeleteFamily Gamma hGdWarp havoid, ?_, ?_⟩
  · change (Gamma.delete X).initialSet
      (Gamma.restrictDeleteFamily X Gd havoid) ⊆
        (Gamma.delete X).source
    rw [Gamma.initialSet_restrictDeleteFamily]
    rintro x ⟨p, hp, rfl⟩
    exact ⟨hp.2, fun hpX ↦
      (hangingVerticesAt_subset_source_compl hGamma a hpX) hp.2⟩
  · intro x hx p hp
    let q : FinitePath Gamma.graph :=
      p.lift (fun {_ _} e ↦ Gamma.delete_adj_imp e)
    have hq : Gamma.IsTargetPathFrom x q := by
      refine ⟨?_, ?_⟩
      · change p.start = x
        exact hp.1
      · change p.finish ∈ Gamma.target
        exact hp.2.1
    obtain ⟨z, hzq, hzW⟩ :=
      hL.roofsSourceAtStages (Ladder.Stage.toExtended a) hx.1 q hq
    have hzp : z ∈ p.support := by
      simpa [q] using hzq
    refine ⟨z, hzp, ?_⟩
    change z ∈ (Gamma.delete X).terminalFrontier
      (Gamma.restrictDeleteFamily X Gd havoid)
    rw [Gamma.terminalFrontier_restrictDeleteFamily]
    obtain ⟨r, hrW, hrz⟩ := hzW
    by_cases hrground : r.initial ∈ Gamma.source
    · exact ⟨r, ⟨hrW, hrground⟩, hrz⟩
    · exfalso
      have hzX : z ∈ X :=
        ⟨r, ⟨hrW, hrground⟩, Gamma.terminal_mem_support hrz⟩
      have hqAvoid : Disjoint q.support X := by
        have hpstart : p.start ∉ X := by simpa [hp.1] using hx.2
        have hav := Gamma.liftDeletePath_avoids X
          (Sum.inl p : (Gamma.delete X).DPath) hpstart
        have hsupport : q.support = p.support := by
          exact FinitePath.support_lift _ p
        rw [hsupport]
        change Disjoint p.support X
        change Disjoint
          (Gamma.liftDeletePath X
            (Sum.inl p : (Gamma.delete X).DPath)).support X at hav
        rw [Gamma.support_liftDeletePath] at hav
        exact hav
      exact Set.disjoint_left.1 hqAvoid hzq hzX

/-- Every frontier selected before the end of a `kappa^+`-ladder has height
at most `kappa`.  The witness is completely explicit: delete the vertices
of the hanging components and take the canonical quotient of the remaining
grounded wave. -/
theorem frontier_heightAtMost
    {L : Gamma.KappaLadder (succ kappa)}
    (hGamma : Gamma.IsNormalized) (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (hkappa : aleph0 ≤ kappa) (a : Ladder.Stage (succ kappa)) :
    HeightAtMost Gamma (L.frontier a) kappa := by
  let X := hangingVerticesAt L a
  let U := groundedDeleteFamily hL a
  have hXsource : X ⊆ Gamma.sourceᶜ :=
    hangingVerticesAt_subset_source_compl hGamma a
  have hSourceX : Disjoint Gamma.source X := by
    exact Set.disjoint_left.2 (fun x hxsource hxX ↦ hXsource hxX hxsource)
  have hU : (Gamma.delete X).IsWave U :=
    groundedDeleteFamily_isWave hGamma hL a
  let Q : Set (Gamma.quotient X).DPath :=
    Gamma.waveQuotient X U hU
  have hNoEnter : Gamma.NoEdgeEnters Gamma.source := by
    intro u v huv hv
    exact (hGamma huv).1 hv
  have hQData :=
    Gamma.isWave_waveQuotient_and_roof hNoEnter hSourceX hU
  have hEss : Gamma.essential X ⊆
      Gamma.roof ((Gamma.quotient X).terminalFrontier Q) :=
    Gamma.essential_subset_original_roof_of_quotient_wave
      hNoEnter hSourceX hQData.1
  have hRoofX : Gamma.roof X ⊆
      Gamma.roof ((Gamma.quotient X).terminalFrontier Q) := by
    rw [← Gamma.roof_essential X]
    exact Gamma.roof_cut hEss
  have hConvert := Gamma.quotient_roof_subset_original_roof_of_essential
    X ((Gamma.quotient X).terminalFrontier Q) hEss
  have hTerminalRoof : Gamma.terminalFrontier (L.warpAt a) ⊆
      Gamma.roof ((Gamma.quotient X).terminalFrontier Q) := by
    rintro z ⟨r, hrW, hrz⟩
    by_cases hrground : r.initial ∈ Gamma.source
    · have hzGrounded : z ∈ Gamma.terminalFrontier (groundedAt L a) :=
        ⟨r, ⟨hrW, hrground⟩, hrz⟩
      have hzU0 : z ∈
          (Gamma.delete (hangingVerticesAt L a)).terminalFrontier
            (groundedDeleteFamily hL a) := by
        unfold groundedDeleteFamily
        rw [Gamma.terminalFrontier_restrictDeleteFamily]
        exact hzGrounded
      have hzU : z ∈ (Gamma.delete X).terminalFrontier U := by
        simpa only [X, U] using hzU0
      have hzNotX : z ∉ X := by
        intro hzX
        exact Set.disjoint_left.1
          (disjoint_groundedAt_hangingAt hL a)
          ⟨r, ⟨hrW, hrground⟩, Gamma.terminal_mem_support hrz⟩ hzX
      by_cases hzStrict : z ∈ Gamma.strictRoof X
      · exact hRoofX hzStrict.1
      · apply hConvert
        refine ⟨hQData.2 ?_, hzStrict⟩
        exact ⟨⟨(Gamma.delete X).subset_roof _ hzU, hzNotX⟩, hzStrict⟩
    · have hzX : z ∈ X :=
        ⟨r, ⟨hrW, hrground⟩, Gamma.terminal_mem_support hrz⟩
      exact hRoofX (Gamma.subset_roof X hzX)
  refine ⟨X, ⟨hXsource, Q, hQData.1, ?_⟩, ?_⟩
  · intro x hx
    apply hTerminalRoof
    rw [L.frontier_eq_essential_terminalFrontier
      hL.roofsSourceAtStages a] at hx
    exact hx.1
  · exact mk_hangingVerticesAt_le hL hkappa a

end DeferredHalfwayFrontierHeight
end CardinalInduction
end Erdos599
