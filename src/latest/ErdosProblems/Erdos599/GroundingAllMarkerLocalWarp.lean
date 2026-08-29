/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerLocalSinks
import ErdosProblems.Erdos599.GroundingRootedReachabilityWarp

/-!
# A finite-path warp covering every required local blocking point

The actual local switched relation roots all required blockers. They are
sinks, hence a reachability antichain. The existing rooted-reachability
compiler gives pairwise disjoint finite paths, including singleton source
blockers and companion components. Every path meets the full blocking set
only at its finish; no component containing a required blocker is lost.
-/

noncomputable section

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set Cardinal DirectedPath Alternating GroundingRootedReachabilityWarp

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I)
  {kappa : Cardinal.{u}} {U : Popular.KappaIndexed L.web kappa}
  (S : Popular.PopularSeparator U) (hInitial : ∀ i, (L.record i).initial ∉ L.markers)
  (hInitials : G.initialSet L.reference.paths ⊆ G.source ∪ L.markers)

namespace PortAugmentation

variable (r : L.Request S.cut) {q : FinitePath L.web.graph}
  (hq : q ∈ (L.shortenedRecordFan S r hInitial).paths) (D : L.PortAugmentation S.cut q r)
  (hOrigin : (L.record D.origin).initial ∈ G.source)

theorem localBlockingSet_antichain :
    IsReachabilityAntichain (D.localSwitchedEdges L S hInitial r hq)
      (D.localBlockingSet L) := by
  intro b hb c _hc hbc
  rcases hbc.cases_head with h | ⟨x, hbx, _hxc⟩
  · exact h
  · exact (D.localSwitchedEdges_no_outgoing_blockingSet L S hInitial r hq hb.1
      ⟨x, hbx⟩).elim

include hInitials hOrigin in
theorem exists_localGroundingWarp :
    ∃ P : Popular.XSWarp G (D.localBlockingSet L),
      (∀ b ∈ D.localBlockingSet L, ∃ p ∈ P.paths, p.finish = b) ∧
      ∀ p ∈ P.paths, p.edgeSet ⊆ D.localSwitchedEdges L S hInitial r hq := by
  obtain ⟨P, hcover, hpaths⟩ := exists_rootedReachabilityWarp
    (Gamma := G) (A := G.source) (B := D.localBlockingSet L)
    (fun _ he ↦ D.switchedEdges_subset_adj L
      (D.localSwitchedEdges_subset_switchedEdges L S hInitial r hq he))
    (D.localSwitchedEdges_biUnique L S hInitial r hq) Set.Subset.rfl
    (D.localBlockingSet_antichain L S hInitial r hq)
    (fun _ hb ↦ D.localBlockingSet_rooted L S hInitial r hq hInitials hOrigin hb)
  exact ⟨P, hcover, fun p hp ↦ (hpaths p hp).1⟩

def localGroundingWarp : Popular.XSWarp G (D.localBlockingSet L) :=
  Classical.choose (D.exists_localGroundingWarp L S hInitial hInitials r hq hOrigin)

theorem localGroundingWarp_covers :
    ∀ b ∈ D.localBlockingSet L, ∃ p ∈
      (D.localGroundingWarp L S hInitial hInitials r hq hOrigin).paths, p.finish = b :=
  (Classical.choose_spec
    (D.exists_localGroundingWarp L S hInitial hInitials r hq hOrigin)).1

theorem localGroundingWarp_edges {p : FinitePath G.graph}
    (hp : p ∈ (D.localGroundingWarp L S hInitial hInitials r hq hOrigin).paths) :
    p.edgeSet ⊆ D.localSwitchedEdges L S hInitial r hq :=
  (Classical.choose_spec
    (D.exists_localGroundingWarp L S hInitial hInitials r hq hOrigin)).2 p hp

theorem localGroundingWarp_one_hit {p : FinitePath G.graph}
    (hp : p ∈ (D.localGroundingWarp L S hInitial hInitials r hq hOrigin).paths) :
    p.support ∩ L.blockingSet S.cut = {p.finish} := by
  ext x
  constructor
  · rintro ⟨hxp, hxK⟩
    apply Set.mem_singleton_iff.mpr
    by_contra hne
    obtain ⟨y, hy⟩ := FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish p hxp hne
    exact D.localSwitchedEdges_no_outgoing_blockingSet L S hInitial r hq hxK
      ⟨y, D.localGroundingWarp_edges L S hInitial hInitials r hq hOrigin hp hy⟩
  · rintro rfl
    exact ⟨p.finish_mem_support,
      ((D.localGroundingWarp L S hInitial hInitials r hq hOrigin).ends_in_target hp).1⟩

theorem localGroundingWarp_paths_finite :
    (D.localGroundingWarp L S hInitial hInitials r hq hOrigin).paths.Finite := by
  let P := D.localGroundingWarp L S hInitial hInitials r hq hOrigin
  have hinj : Set.InjOn FinitePath.finish P.paths := by
    intro p hp t ht hfinish
    by_contra hne
    exact Set.disjoint_left.mp (P.disjoint hp ht hne) p.finish_mem_support
      (hfinish.symm ▸ t.finish_mem_support)
  exact (D.localBlockingSet_finite L).of_injOn
    (fun _ hp ↦ P.ends_in_target hp) hinj

#print axioms exists_localGroundingWarp
#print axioms localGroundingWarp_one_hit
#print axioms localGroundingWarp_paths_finite

end PortAugmentation
end Erdos599.GroundingAllMarkerAuxiliary.Input
