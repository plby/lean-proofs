/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularFiniteRepairProfileProgress

/-!
# Localizing the roof defect of a finite carrier exchange

Replacing a target linkage changes the deleted web.  A wave behind the old
linkage need not remain a wave behind the replacement: a target path may use
a vertex of the old carrier which the replacement has freed.  This file
records the exact positive transport statement.  Every new residual target
path which avoids the freed part of the old carrier is still caught by the
old wave frontier.  Thus every failure of roof transport is localized in the
freed carrier.

For a finite-support linkage update that exceptional carrier is finite.  The
result is the precise handoff to a subsequent finite/lower-cardinal repair;
it does not incorrectly assert continuity of waves under carrier exchange.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularFiniteCarrierRoofLocalization

open DWeb
open SingularMarkedResidualTouchedPaths

universe u

variable {V : Type u}

/-- A wave behind `X` still roofs every target path behind `X'` which avoids
the vertices freed by the change from `X` to `X'`. -/
theorem deleteWave_meets_of_avoids_freedCarrier
    (G : DWeb V) (X X' : Set V)
    {U : Set ((G.delete X).DPath)}
    (hU : (G.delete X).IsWave U)
    {a : V} (ha : a ∈ (G.delete X').source)
    (p : DirectedPath.FinitePath (G.delete X').graph)
    (hp : (G.delete X').IsTargetPathFrom a p)
    (havoidFreed : Disjoint p.support (X \ X')) :
    ∃ x ∈ p.support, x ∈ (G.delete X).terminalFrontier U := by
  let q : DirectedPath.FinitePath G.graph := p.lift G.delete_adj_imp
  have haNotX' : a ∉ X' := ha.2
  have hqAvoidX' : Disjoint q.support X' := by
    change Disjoint (G.liftDeletePath X' (.inl p)).support X'
    apply G.liftDeletePath_avoids X' (.inl p)
    change p.start ∉ X'
    rw [hp.1]
    exact haNotX'
  have hqAvoidFreed : Disjoint q.support (X \ X') := by
    simpa only [q, DirectedPath.FinitePath.support_lift] using havoidFreed
  have hqAvoidX : Disjoint q.support X := by
    apply Set.disjoint_left.2
    intro x hxq hxX
    by_cases hxX' : x ∈ X'
    · exact Set.disjoint_left.1 hqAvoidX' hxq hxX'
    · exact Set.disjoint_left.1 hqAvoidFreed hxq ⟨hxX, hxX'⟩
  have haNotX : a ∉ X := by
    intro haX
    have haq : a ∈ q.support := by
      have hap : a ∈ p.support := hp.1 ▸ p.start_mem_support
      simpa only [q, DirectedPath.FinitePath.support_lift] using hap
    exact Set.disjoint_left.1 hqAvoidX haq haX
  have hqAvoidXWalk : SafeLink.Walk.Avoids q.walk X := by
    intro x hxq hxX
    exact Set.disjoint_left.1 hqAvoidX hxq hxX
  let r : DirectedPath.FinitePath (G.delete X).graph :=
    SafeLink.FinitePath.toDelete G X q hqAvoidXWalk
  have hrTarget : (G.delete X).IsTargetPathFrom a r := by
    refine ⟨?_, hp.2.1, ?_⟩
    · change p.start = a
      exact hp.1
    · intro hfinishX
      have hfinishQ : p.finish ∈ q.support := by
        simpa only [q, DirectedPath.FinitePath.support_lift] using
          p.finish_mem_support
      exact Set.disjoint_left.1 hqAvoidX hfinishQ hfinishX
  obtain ⟨x, hxr, hxU⟩ := hU.2.2 ⟨ha.1, haNotX⟩ r hrTarget
  refine ⟨x, ?_, hxU⟩
  have hxr' : x ∈ q.support := by
    simpa only [r, SafeLink.FinitePath.support_toDelete] using hxr
  simpa only [q, DirectedPath.FinitePath.support_lift] using hxr'

/-- Separator form of the localization theorem.  Restoring vertices while
changing the deleted carrier can enlarge the required separator only by the
freed part of the old carrier. -/
theorem source_subset_roof_frontier_union_freedCarrier
    (G : DWeb V) (X X' : Set V)
    {U : Set ((G.delete X).DPath)}
    (hU : (G.delete X).IsWave U) :
    (G.delete X').source ⊆ (G.delete X').roof
      ((G.delete X).terminalFrontier U ∪ (X \ X')) := by
  intro a ha p hp
  by_cases hcontact : (p.support ∩ (X \ X')).Nonempty
  · obtain ⟨x, hxp, hxFreed⟩ := hcontact
    exact ⟨x, hxp, Or.inr hxFreed⟩
  · have hdisjoint : Disjoint p.support (X \ X') := by
      rw [Set.disjoint_left]
      intro x hxp hxFreed
      exact hcontact ⟨x, hxp, hxFreed⟩
    obtain ⟨x, hxp, hxU⟩ :=
      deleteWave_meets_of_avoids_freedCarrier
        G X X' hU ha p hp hdisjoint
    exact ⟨x, hxp, Or.inl hxU⟩

/-- Once the finite freed carrier is itself roofed by a proposed new
frontier, the old separator transports completely to the new deletion. -/
theorem source_subset_roof_of_freedCarrier_roofed
    (G : DWeb V) (X X' S : Set V)
    {U : Set ((G.delete X).DPath)}
    (hU : (G.delete X).IsWave U)
    (hfrontier : (G.delete X).terminalFrontier U ⊆ S)
    (hfreed : X \ X' ⊆ (G.delete X').roof S) :
    (G.delete X').source ⊆ (G.delete X').roof S := by
  have hlocalized :=
    source_subset_roof_frontier_union_freedCarrier G X X' hU
  apply hlocalized.trans
  apply (G.delete X').roof_cut
  intro x hx
  rcases hx with hxU | hxFreed
  · exact (G.delete X').subset_roof S (hfrontier hxU)
  · exact hfreed hxFreed

/-- Wave constructor for a rerouted residual warp.  The only extra
obligation beyond endpoint transport is that its frontier roofs the finite
carrier freed by the target-linkage update. -/
theorem isWave_of_freedCarrier_roofed
    (G : DWeb V) (X X' : Set V)
    {U : Set ((G.delete X).DPath)}
    (hU : (G.delete X).IsWave U)
    {R : Set ((G.delete X').DPath)}
    (hRwarp : (G.delete X').IsWarp R)
    (hRinitial : (G.delete X').initialSet R ⊆ (G.delete X').source)
    (hfrontier : (G.delete X).terminalFrontier U ⊆
      (G.delete X').terminalFrontier R)
    (hfreed : X \ X' ⊆ (G.delete X').roof
      ((G.delete X').terminalFrontier R)) :
    (G.delete X').IsWave R := by
  refine ⟨hRwarp, hRinitial, ?_⟩
  exact source_subset_roof_of_freedCarrier_roofed G X X'
    ((G.delete X').terminalFrontier R) hU hfrontier hfreed

/-- Roof formulation of `deleteWave_meets_of_avoids_freedCarrier`.  A
failure of the old frontier to roof a new residual source supplies a target
path meeting the freed carrier. -/
theorem exists_freedCarrier_contact_of_not_mem_roof
    (G : DWeb V) (X X' : Set V)
    {U : Set ((G.delete X).DPath)}
    (hU : (G.delete X).IsWave U)
    {a : V} (ha : a ∈ (G.delete X').source)
    (haNotRoof : a ∉ (G.delete X').roof
      ((G.delete X).terminalFrontier U)) :
    ∃ p : DirectedPath.FinitePath (G.delete X').graph,
      (G.delete X').IsTargetPathFrom a p ∧
        (p.support ∩ (X \ X')).Nonempty := by
  obtain ⟨p, hp, hpAvoid⟩ :=
    ((G.delete X').not_mem_roof_iff
      ((G.delete X).terminalFrontier U) a).1 haNotRoof
  refine ⟨p, hp, ?_⟩
  by_contra hempty
  have hdisjoint : Disjoint p.support (X \ X') := by
    rw [Set.disjoint_left]
    intro x hxp hxFreed
    exact hempty ⟨x, hxp, hxFreed⟩
  obtain ⟨x, hxp, hxU⟩ :=
    deleteWave_meets_of_avoids_freedCarrier G X X' hU ha p hp hdisjoint
  exact Set.disjoint_left.1 hpAvoid hxp hxU

/-- The carrier freed by replacing `R ∪ T` with `R ∪ Q` is contained in
the finite local exchange carrier `T ∪ Q`. -/
theorem freedCarrier_subset_localExchange
    (G : DWeb V) (R T Q : Set G.DPath) :
    G.vertexSet (R ∪ T) \ G.vertexSet (R ∪ Q) ⊆
      G.vertexSet (T ∪ Q) := by
  rintro x ⟨hxOld, _hxNew⟩
  rw [G.vertexSet_union] at hxOld ⊢
  rcases hxOld with hxR | hxT
  · exact False.elim (_hxNew (by
      rw [G.vertexSet_union]
      exact Or.inl hxR))
  · exact Or.inl hxT

/-- In a finite-support target-linkage update, the entire freed part of the
old carrier is finite. -/
theorem freedCarrier_finite_of_localExchange
    (G : DWeb V) {R T Q : Set G.DPath}
    (hlocal : (G.vertexSet (T ∪ Q)).Finite) :
    (G.vertexSet (R ∪ T) \ G.vertexSet (R ∪ Q)).Finite :=
  hlocal.subset (freedCarrier_subset_localExchange G R T Q)

#print axioms deleteWave_meets_of_avoids_freedCarrier
#print axioms source_subset_roof_frontier_union_freedCarrier
#print axioms source_subset_roof_of_freedCarrier_roofed
#print axioms isWave_of_freedCarrier_roofed
#print axioms exists_freedCarrier_contact_of_not_mem_roof
#print axioms freedCarrier_subset_localExchange
#print axioms freedCarrier_finite_of_localExchange

end SingularFiniteCarrierRoofLocalization
end CardinalInduction
end Erdos599
