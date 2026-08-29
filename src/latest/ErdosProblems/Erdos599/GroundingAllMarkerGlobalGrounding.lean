/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerLeftoverPaths

/-!
# Global grounding of the entire all-marker blocking set

The union of the local transactions and all uncovered grounded prefixes
is an actual vertex-disjoint source--blocking-set warp. Every blocker is
covered, every path meets the blocker set once, and every untouched good
record is omitted. This closes the global path-family assembly without
assuming any realization, orthogonalization, or coverage conclusion.
-/

noncomputable section

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set Cardinal DirectedPath Alternating GroundingAllMarkerPorts

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I) {kappa : Cardinal.{u}}
  {U : Popular.KappaIndexed L.web kappa} (S : Popular.PopularSeparator U)
  (hInitial : ∀ i, (L.record i).initial ∉ L.markers)
  (hInitials : G.initialSet L.reference.paths ⊆ G.source ∪ L.markers)
  (hRecords : ∀ i, (L.record i).initial ∈ G.source)

def independentGroundingWarp (r : L.Request S.cut) :
    Popular.XSWarp G ((L.independentPortAugmentation S hInitial r).localBlockingSet L) :=
  (L.independentPortAugmentation S hInitial r).localGroundingWarp L S hInitial hInitials r
    (L.independentSelectedPath_mem S hInitial r) (hRecords _)

def globalGroundingPaths : Set (FinitePath G.graph) :=
  (⋃ r : L.Request S.cut, (L.independentGroundingWarp S hInitial hInitials hRecords r).paths) ∪
    Set.range (L.leftoverPath S hInitial hInitials)

theorem independentGroundingWarp_support {r : L.Request S.cut} {p : FinitePath G.graph}
    (hp : p ∈ (L.independentGroundingWarp S hInitial hInitials hRecords r).paths) :
    p.support ⊆ (L.independentPortAugmentation S hInitial r).localRegion L :=
  (L.independentPortAugmentation S hInitial r).localGroundingWarp_support_subset L S hInitial r
    (L.independentSelectedPath_mem S hInitial r) hInitials (hRecords _) hp

variable (hNoEnter : G.NoEdgeEnters G.source) (hMarkers : Disjoint G.source L.markers)

include hNoEnter hMarkers in
theorem globalGroundingPaths_disjoint :
    (L.globalGroundingPaths S hInitial hInitials hRecords).PairwiseDisjoint FinitePath.support := by
  rintro p (hp | ⟨b, rfl⟩) q (hq | ⟨c, rfl⟩) hpq
  · obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hp
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hq
    by_cases hrs : r = s
    · subst s
      exact (L.independentGroundingWarp S hInitial hInitials hRecords r).disjoint hr hs hpq
    · exact (L.independentLocalRegions_disjoint S hInitial hInitials hNoEnter hMarkers
        r s hrs).mono (L.independentGroundingWarp_support S hInitial hInitials hRecords hr)
          (L.independentGroundingWarp_support S hInitial hInitials hRecords hs)
  · obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hp
    exact (L.leftoverPath_disjoint_localRegion S hInitial hInitials c r).symm.mono_left
      (L.independentGroundingWarp_support S hInitial hInitials hRecords hr)
  · obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hq
    exact (L.leftoverPath_disjoint_localRegion S hInitial hInitials b r).mono_right
      (L.independentGroundingWarp_support S hInitial hInitials hRecords hr)
  · exact L.leftoverPaths_disjoint S hInitial hInitials b c
      (fun h ↦ hpq (congrArg (L.leftoverPath S hInitial hInitials) h))

def globalGroundingWarp : Popular.XSWarp G (L.blockingSet S.cut) where
  paths := L.globalGroundingPaths S hInitial hInitials hRecords
  disjoint := L.globalGroundingPaths_disjoint S hInitial hInitials hRecords hNoEnter hMarkers
  starts_in_source := by
    rintro p (hp | ⟨b, rfl⟩)
    · obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hp
      exact (L.independentGroundingWarp S hInitial hInitials hRecords r).starts_in_source hr
    · exact (L.leftoverPath_spec S hInitial hInitials b).1
  ends_in_target := by
    rintro p (hp | ⟨b, rfl⟩)
    · obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hp
      exact ((L.independentGroundingWarp S hInitial hInitials hRecords r).ends_in_target hr).1
    · exact (L.leftoverPath_spec S hInitial hInitials b).2.1.symm ▸ b.2.1

theorem globalGroundingWarp_covers : ∀ b ∈ L.blockingSet S.cut,
    ∃ p ∈ (L.globalGroundingWarp S hInitial hInitials hRecords hNoEnter hMarkers).paths,
      p.finish = b := by
  intro b hb
  by_cases hlocal : b ∈ L.locallyCoveredBlockers S hInitial
  · obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hlocal
    obtain ⟨p, hp, hpb⟩ :=
      (L.independentPortAugmentation S hInitial r).localGroundingWarp_covers L S hInitial
        hInitials r (L.independentSelectedPath_mem S hInitial r) (hRecords _) b hr
    exact ⟨p, Or.inl (Set.mem_iUnion.mpr ⟨r, hp⟩), hpb⟩
  · let c : L.UncoveredBlocker S hInitial := ⟨b, hb, hlocal⟩
    exact ⟨L.leftoverPath S hInitial hInitials c, Or.inr ⟨c, rfl⟩,
      (L.leftoverPath_spec S hInitial hInitials c).2.1⟩

theorem globalGroundingWarp_one_hit {p : FinitePath G.graph}
    (hp : p ∈ (L.globalGroundingWarp S hInitial hInitials hRecords hNoEnter hMarkers).paths) :
    p.support ∩ L.blockingSet S.cut = {p.finish} := by
  rcases hp with hp | ⟨b, rfl⟩
  · obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hp
    exact (L.independentPortAugmentation S hInitial r).localGroundingWarp_one_hit L S hInitial
      hInitials r (L.independentSelectedPath_mem S hInitial r) (hRecords _) hr
  · rw [L.leftoverPath_one_hit S hInitial hInitials b,
      (L.leftoverPath_spec S hInitial hInitials b).2.1]

theorem globalGroundingWarp_avoids_untouched (i : I) (hi : L.UntouchedRecord S hInitial i)
    {p : FinitePath G.graph}
    (hp : p ∈ (L.globalGroundingWarp S hInitial hInitials hRecords hNoEnter hMarkers).paths) :
    Disjoint p.support (L.record i).support := by
  rcases hp with hp | ⟨b, rfl⟩
  · obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hp
    exact (L.untouchedRecord_disjoint_localRegion S hInitial i hi r).symm.mono_left
      (L.independentGroundingWarp_support S hInitial hInitials hRecords hr)
  · exact L.leftoverPath_disjoint_good_record S hInitial hInitials b i hi.1

#print axioms globalGroundingPaths_disjoint
#print axioms globalGroundingWarp_covers
#print axioms globalGroundingWarp_one_hit
#print axioms globalGroundingWarp_avoids_untouched

end Erdos599.GroundingAllMarkerAuxiliary.Input
