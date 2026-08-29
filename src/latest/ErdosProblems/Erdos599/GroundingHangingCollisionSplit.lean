/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingHangingLadderRank
import ErdosProblems.Erdos599.GroundingSuccessorRoofTransport

/-!
# Weak chronology and the strict/equal split for Assertion 8.19

With successor-normalized ladder bookkeeping, a hanging component met by a
Lambda path has owner stage at most the source stage.  Equality is a genuine
diagonal case, so the regressive argument of Assertion 8.19 must be applied
only to the strict part.  This file proves the component-side roof propagation
and records the exact strict/equal partition.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open _root_.Erdos599.DWeb.DirectedPath Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace Walk

/-- If membership in `R` propagates backwards along every edge of a finite
walk, then meeting `R` anywhere forces the initial vertex into `R`. -/
theorem start_mem_of_meets_of_backwardClosed
    {D : Digraph V} {R : Set V}
    {a b : V} (w : DirectedPath.Walk D a b)
    (hback : ∀ {x y}, (x, y) ∈ w.edgeSet → y ∈ R → x ∈ R)
    (hmeets : w.Meets R) :
    a ∈ R := by
  induction w with
  | @nil x =>
      obtain ⟨z, hz, hzR⟩ := hmeets
      have hzx : z = x := by simpa using hz
      exact hzx ▸ hzR
  | @cons x y z hxy w ih =>
      obtain ⟨t, ht, htR⟩ := hmeets
      simp only [DirectedPath.Walk.support_cons, List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact htR
      · apply hback (x := x) (y := y)
          (by simp [DirectedPath.Walk.edgeSet_cons])
        apply ih
        · intro u v huv
          apply hback
          rw [DirectedPath.Walk.edgeSet_cons]
          exact Set.mem_union_right _ huv
        · exact ⟨t, ht, htR⟩

end Walk

/-- Along a limiting ladder component, roof membership of any support point
propagates backwards to the component's initial vertex.  A later family edge
whose head is already in an earlier roof occurred at that earlier stage;
self-roofing of the stage then puts its tail in the strict roof. -/
theorem IsLegal.limitComponent_initial_mem_roof_of_support_mem
    {L : Gamma.KappaLadder kappa} (hlegal : L.IsLegal)
    (c : Stage kappa) {p : Gamma.DPath} (hp : p ∈ L.limitWarp)
    {v : V} (hvp : v ∈ p.support)
    (hvRoof : v ∈ Gamma.roof (L.frontier c)) :
    p.initial ∈ Gamma.roof (L.frontier c) := by
  have hback : ∀ {x y : V}, (x, y) ∈ p.edgeSet →
      y ∈ Gamma.roof (L.frontier c) →
      x ∈ Gamma.roof (L.frontier c) := by
    intro x y hxy hyRoof
    have hxyLimit : (x, y) ∈
        Gamma.pathFamilyEdgeSet L.limitWarp := ⟨p, hp, hxy⟩
    have hxyStage : (x, y) ∈
        Gamma.pathFamilyEdgeSet (L.warpAt c) :=
      hlegal.pathFamilyEdgeSet_of_head_mem_roof_frontier c
        kappa.ord le_rfl c.2.le hxyLimit hyRoof
    have hxRaw := hlegal.edge_tail_mem_strictRoof_of_mem_warpAt c hxyStage
    rw [L.frontier_eq_essential_terminalFrontier
      hlegal.roofsSourceAtStages, Gamma.roof_essential]
    exact hxRaw.1
  rcases p with p | r
  · apply Walk.start_mem_of_meets_of_backwardClosed
      (w := p.walk) (R := Gamma.roof (L.frontier c))
    · intro x y hxy hy
      exact hback hxy hy
    · exact ⟨v, hvp, hvRoof⟩
  · obtain ⟨n, hn⟩ := hvp
    subst v
    change r.initial ∈ Gamma.roof (L.frontier c)
    change r 0 ∈ Gamma.roof (L.frontier c)
    have hprefix : ∀ n : ℕ,
        r n ∈ Gamma.roof (L.frontier c) →
          r 0 ∈ Gamma.roof (L.frontier c) := by
      intro n
      induction n with
      | zero => exact fun h ↦ h
      | succ n ih =>
          intro hnRoof
          apply ih
          apply hback
          · exact ⟨n, rfl⟩
          · exact hnRoof
    exact hprefix n hvRoof

/-- If a point of a hanging limiting component owned at `b` is roofed by the
successor frontier of `a`, then `b ≤ a`.  The strict inequality `a < b`
would move that roof membership to `T_b`, contradicting freshness of the
marker which is the component's initial vertex. -/
theorem IsLegal.hangingComponentStage_le_of_support_mem_roof_successor
    {L : Gamma.KappaLadder kappa} (hlegal : L.IsLegal)
    (a : Stage kappa) {p : Gamma.DPath} (hp : p ∈ L.limitWarp)
    (hhang : PopularAuxiliary.IsHangingPath Gamma p)
    {v : V} (hvp : v ∈ p.support)
    (hvRoof : v ∈ Gamma.roof
      (L.frontier (L.successorStage hlegal a))) :
    L.hangingComponentStage hlegal p hp hhang ≤ a := by
  let b := L.hangingComponentStage hlegal p hp hhang
  have hbMarker : L.marker b = some p.initial :=
    L.marker_hangingComponentStage hlegal p hp hhang
  have hInitialRoof : p.initial ∈ Gamma.roof
      (L.frontier (L.successorStage hlegal a)) :=
    hlegal.limitComponent_initial_mem_roof_of_support_mem
      (L.successorStage hlegal a) hp hvp hvRoof
  by_contra hnot
  have hab : a < b := lt_of_not_ge hnot
  have hsuccle : L.successorStage hlegal a ≤ b :=
    (L.successorStage_le_iff_lt hlegal).2 hab
  have hInitialRoofB : p.initial ∈ Gamma.roof (L.frontier b) := by
    rcases hsuccle.lt_or_eq with hlt | heq
    · exact Gamma.roof_cut (hlegal.frontierChronology hlt) hInitialRoof
    · rwa [heq] at hInitialRoof
  exact L.marker_not_mem_roof_frontier hlegal hbMarker hInitialRoofB

/-- Strict collision indices: the chosen hanging owner really is earlier
than the source index. -/
def strictHangingCollisionIndices
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut) :
    Set (Stationary.Below kappa) :=
  {a | ∃ d : L.Assertion819CollisionOwner hL S r a,
    L.hangingComponentStage hL.legal d.component
      d.component_mem d.component_hanging < a}

/-- Equal collision indices: the chosen hanging owner is born at exactly the
source index.  These are the diagonal cases which cannot be fed to Fodor's
regressive-map argument. -/
def equalHangingCollisionIndices
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut) :
    Set (Stationary.Below kappa) :=
  {a | ∃ d : L.Assertion819CollisionOwner hL S r a,
    L.hangingComponentStage hL.legal d.component
      d.component_mem d.component_hanging = a}

end KappaLadder
end DWeb
end Erdos599
