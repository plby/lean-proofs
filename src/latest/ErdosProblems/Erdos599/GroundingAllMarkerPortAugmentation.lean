/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerMatchingDecode

/-!
# Actual finite augmenting port paths for every selected request

The origin is a good record and the departure is a real vertex of that
record. Finite and ray origins both produce a simple finite path in the
stopped, origin-truncated matching graph. The two matching ports are free;
all forward sending vertices avoid the exact blocking separator.

This is the input to a matching toggle, not yet a projected original-graph
path family. No simplicity of the original-vertex projection is asserted.
-/

noncomputable section

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set Cardinal DirectedPath Alternating GroundingAllMarkerPorts

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I)

structure PortAugmentation (C : Set L.Vertex) (q : FinitePath L.web.graph)
    (r : L.Request C) where
  origin : I
  origin_start : q.start = .source origin
  origin_good : origin ∉ L.badRecords C
  departure : V
  departure_mem : departure ∈ (L.record origin).support
  departure_not_blocking : departure ∉ L.blockingSet C
  path : FinitePath (L.matchingRouteGraph q.support r.1 departure
    (L.originStoppedMatching C origin departure))
  path_start : path.start = .inl departure
  path_finish : path.finish = .inr (L.requestVertex r)

theorem PortAugmentation.source_unmatched {C : Set L.Vertex}
    {q : FinitePath L.web.graph} {r : L.Request C} (D : L.PortAugmentation C q r) (y : V) :
    ¬ L.originStoppedMatching C D.origin D.departure D.departure y :=
  L.originStoppedMatching_source_unmatched C D.origin D.departure_mem y

theorem PortAugmentation.request_unmatched {C : Set L.Vertex}
    {q : FinitePath L.web.graph} {r : L.Request C} (D : L.PortAugmentation C q r) (x : V) :
    ¬ L.originStoppedMatching C D.origin D.departure x (L.requestVertex r) :=
  L.originStoppedMatching_request_unmatched C D.origin D.departure r x

variable {kappa : Cardinal.{u}} {U : Popular.KappaIndexed L.web kappa}
  (S : Popular.PopularSeparator U) (hInitial : ∀ i, (L.record i).initial ∉ L.markers)

/-- All decoder premises are proved for an actual shortened fan member. -/
theorem exists_shortenedRecordFan_portAugmentation (r : L.Request S.cut)
    {q : FinitePath L.web.graph} (hq : q ∈ (L.shortenedRecordFan S r hInitial).paths) :
    Nonempty (L.PortAugmentation S.cut q r) := by
  obtain ⟨i, hqi, hiGood⟩ := L.shortenedRecordFan_start_good_record S r hInitial hq
  have hfinish : q.finish = r.1 := (L.shortenedRecordFan S r hInitial).ends_in_join hq
  have hreceive : L.receiving q.finish = some (L.requestVertex r) :=
    hfinish.symm ▸ L.request_receiving r
  have hne : q.start ≠ q.finish := by
    intro heq
    exact r.2.2 ⟨i, (hqi.symm.trans heq).trans hfinish⟩
  have hsub : ∀ d {x y}, L.originStoppedMatching S.cut i d x y →
      referenceMatching L.reference.paths x y :=
    fun _ {_ _} h ↦ L.residualMatching_subset_reference S.cut
      (L.stoppedMatching_subset_residual S.cut h.1)
  obtain ⟨x, hx, ⟨w⟩⟩ : ∃ x ∈ (L.record i).support,
      Nonempty (Walk (L.matchingRouteGraph q.support r.1 x
        (L.originStoppedMatching S.cut i x)) (.inl x) (.inr (L.requestVertex r))) := by
    cases hi : L.record i with
    | inl f =>
        have hsend : L.sending q.start = some f.finish := by
          simp only [hqi, sending, hi, Path.terminal?]
        have hInternal : ∀ a ∈ q.support, a ≠ q.finish → ∀ x y,
            L.sending a = some x → L.receiving a = some y →
              L.originStoppedMatching S.cut i f.finish x y := by
          intro a ha har x y hs hr
          exact L.shortenedRecordFan_internal_originMatching_finite S hInitial r hq i f hi
            ha (by simpa only [hfinish] using har) hs hr
        have hwalk := L.walk_decode_matching_from_sending q.support
          (L.originStoppedMatching S.cut i f.finish) (hsub f.finish) q.walk q.isPath
          (fun _ hz ↦ hz) hInternal hne hsend hreceive
        refine ⟨f.finish, ?_, ?_⟩
        · simpa only [hi, Path.support] using f.finish_mem_support
        · simpa only [hfinish] using hwalk
    | inr ray =>
        have hInternal : ∀ d, ∀ a ∈ q.support, a ≠ q.finish → ∀ x y,
            L.sending a = some x → L.receiving a = some y →
              L.originStoppedMatching S.cut i d x y := by
          intro d a ha har x y hs hr
          exact L.shortenedRecordFan_internal_originMatching_ray S hInitial r hq i ray hi hqi
            d ha (by simpa only [hfinish] using har) hs hr
        have hFree : ∀ x ∈ ray.support, ∀ y,
            ¬ L.originStoppedMatching S.cut i x x y := by
          intro x hx y
          exact L.originStoppedMatching_source_unmatched S.cut i
            (by simpa only [hi, Path.support] using hx) y
        obtain ⟨x, hx, hwalk⟩ := L.walk_decode_matching_from_ray q.support
          (L.originStoppedMatching S.cut i) hsub i ray hi q.walk q.isPath
          (fun _ hz ↦ hz) hqi hInternal hFree hreceive
        refine ⟨x, ?_, ?_⟩
        · simpa only [hi, Path.support] using hx
        · simpa only [hfinish] using hwalk
  obtain ⟨p, _hp⟩ := RelationalRoof.exists_pathTo_support_subset
    (R := (L.matchingRouteGraph q.support r.1 x (L.originStoppedMatching S.cut i x)).Adj) w
  exact ⟨{
    origin := i
    origin_start := hqi
    origin_good := hiGood
    departure := x
    departure_mem := hx
    departure_not_blocking := Set.disjoint_left.mp
      (L.goodRecordVertices_disjoint_blockingSet S.cut S.separates) ⟨i, hiGood, hx⟩
    path := ⟨_, _, p.1, p.2⟩
    path_start := rfl
    path_finish := rfl }⟩

/-- The provenance restriction excludes every new forward edge leaving
the blocking set; receiving vertices may still lie in that set. -/
theorem PortAugmentation.forward_tail_not_blockingSet (r : L.Request S.cut)
    {q : FinitePath L.web.graph} (hq : q ∈ (L.shortenedRecordFan S r hInitial).paths)
    (D : L.PortAugmentation S.cut q r) {x y : V}
    (he : (.inl x, .inr y) ∈ D.path.edgeSet) : x ∉ L.blockingSet S.cut := by
  have hport := (D.path.edgeSet_subset_adj he).2.1
  rcases hport with hx | ⟨a, ha, har, hsend⟩
  · exact hx ▸ D.departure_not_blocking
  · exact L.shortenedRecordFan_sending_not_blockingSet S hInitial r hq ha har hsend

def independentPortAugmentation (r : L.Request S.cut) :
    L.PortAugmentation S.cut (L.independentSelectedPath S hInitial r) r :=
  Classical.choice (L.exists_shortenedRecordFan_portAugmentation S hInitial r
    (L.independentSelectedPath_mem S hInitial r))

theorem independentPortAugmentation_forward_tail_not_blockingSet (r : L.Request S.cut)
    {x y : V} (he : (.inl x, .inr y) ∈
      (L.independentPortAugmentation S hInitial r).path.edgeSet) : x ∉ L.blockingSet S.cut :=
  PortAugmentation.forward_tail_not_blockingSet L S hInitial r
    (L.independentSelectedPath_mem S hInitial r) (L.independentPortAugmentation S hInitial r) he

#print axioms exists_shortenedRecordFan_portAugmentation
#print axioms PortAugmentation.forward_tail_not_blockingSet
#print axioms independentPortAugmentation

end Erdos599.GroundingAllMarkerAuxiliary.Input
