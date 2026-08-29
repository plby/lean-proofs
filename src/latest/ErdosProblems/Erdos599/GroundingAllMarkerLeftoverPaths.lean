/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerUncoveredBlockers

/-!
# The disjoint grounded prefixes for all uncovered blockers

Each uncovered blocker chooses its actual grounded fragment and finite
blocking prefix. Distinct endpoints give disjoint prefixes by fragment
uniqueness and the one-blocker property. Every such path avoids every
local transaction region and every good reference record.
-/

noncomputable section

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set Cardinal DirectedPath Alternating GroundingAllMarkerPorts

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I) {kappa : Cardinal.{u}}
  {U : Popular.KappaIndexed L.web kappa} (S : Popular.PopularSeparator U)
  (hInitial : ∀ i, (L.record i).initial ∉ L.markers)

abbrev UncoveredBlocker :=
  {b : V // b ∈ L.blockingSet S.cut ∧ b ∉ L.locallyCoveredBlockers S hInitial}

variable (hInitials : G.initialSet L.reference.paths ⊆ G.source ∪ L.markers)

def uncoveredFragment (b : L.UncoveredBlocker S hInitial) : L.CutFragment :=
  Classical.choose (L.uncovered_blocker_fragment S hInitial hInitials b.2.1 b.2.2)

theorem uncoveredFragment_spec (b : L.UncoveredBlocker S hInitial) :
    L.uncoveredFragment S hInitial hInitials b ∈ L.blockedFragments S.cut ∧
      L.CutFragmentGrounded (L.uncoveredFragment S hInitial hInitials b) ∧
      L.fragmentBlockingPoint S.cut (L.uncoveredFragment S hInitial hInitials b) = b.1 ∧
      ∀ r : L.Request S.cut,
        Disjoint (L.uncoveredFragment S hInitial hInitials b).path.support
          ((L.independentPortAugmentation S hInitial r).localRegion L) :=
  Classical.choose_spec (L.uncovered_blocker_fragment S hInitial hInitials b.2.1 b.2.2)

def leftoverPath (b : L.UncoveredBlocker S hInitial) : FinitePath G.graph :=
  L.blockingPrefix S.cut (L.uncoveredFragment_spec S hInitial hInitials b).1

theorem leftoverPath_spec (b : L.UncoveredBlocker S hInitial) :
    (L.leftoverPath S hInitial hInitials b).start ∈ G.source ∧
      (L.leftoverPath S hInitial hInitials b).finish = b.1 ∧
      (L.leftoverPath S hInitial hInitials b).support ⊆
        (L.uncoveredFragment S hInitial hInitials b).path.support := by
  have hspec := L.uncoveredFragment_spec S hInitial hInitials b
  have hprefix := L.blockingPrefix_spec S.cut hspec.1
  exact ⟨hprefix.1.symm ▸ hspec.2.1, hprefix.2.1.trans hspec.2.2.1, hprefix.2.2.1⟩

theorem leftoverPath_one_hit (b : L.UncoveredBlocker S hInitial) :
    (L.leftoverPath S hInitial hInitials b).support ∩ L.blockingSet S.cut = {b.1} := by
  have hspec := L.uncoveredFragment_spec S hInitial hInitials b
  have hprefix := L.leftoverPath_spec S hInitial hInitials b
  ext x
  constructor
  · rintro ⟨hx, hxK⟩
    exact (L.fragmentBlockingPoint_eq_of_mem S.cut hspec.1.1 (hprefix.2.2 hx) hxK).symm.trans
      hspec.2.2.1
  · rintro rfl
    exact ⟨hprefix.2.1 ▸ (L.leftoverPath S hInitial hInitials b).finish_mem_support, b.2.1⟩

theorem leftoverPaths_disjoint (b c : L.UncoveredBlocker S hInitial) (hbc : b ≠ c) :
    Disjoint (L.leftoverPath S hInitial hInitials b).support
      (L.leftoverPath S hInitial hInitials c).support := by
  apply Set.disjoint_left.mpr
  intro x hxb hxc
  have hb := L.uncoveredFragment_spec S hInitial hInitials b
  have hc := L.uncoveredFragment_spec S hInitial hInitials c
  have heq := (L.cutFragment_parent_and_support_eq_of_common S.cut hb.1.1 hc.1.1
    ((L.leftoverPath_spec S hInitial hInitials b).2.2 hxb)
    ((L.leftoverPath_spec S hInitial hInitials c).2.2 hxc)).2
  have hbmem := L.fragmentBlockingPoint_mem S.cut hb.1
  have hbQ := heq ▸ hbmem.1
  have hpoint := L.fragmentBlockingPoint_eq_of_mem S.cut hc.1.1 hbQ hbmem.2
  exact hbc (Subtype.ext (hb.2.2.1.symm.trans (hpoint.symm.trans hc.2.2.1)))

theorem leftoverPath_disjoint_localRegion (b : L.UncoveredBlocker S hInitial)
    (r : L.Request S.cut) :
    Disjoint (L.leftoverPath S hInitial hInitials b).support
      ((L.independentPortAugmentation S hInitial r).localRegion L) :=
  ((L.uncoveredFragment_spec S hInitial hInitials b).2.2.2 r).mono_left
    (L.leftoverPath_spec S hInitial hInitials b).2.2

theorem leftoverPath_disjoint_good_record (b : L.UncoveredBlocker S hInitial) (i : I)
    (hi : i ∉ L.badRecords S.cut) :
    Disjoint (L.leftoverPath S hInitial hInitials b).support (L.record i).support := by
  apply Set.disjoint_left.mpr
  intro x hxp hxi
  have hb := L.uncoveredFragment_spec S hInitial hInitials b
  have hxP := (L.leftoverPath_spec S hInitial hInitials b).2.2 hxp
  have heq := DWeb.IsWarp.eq_of_mem_support L.reference.disjoint
    (L.uncoveredFragment S hInitial hInitials b).parent_mem (L.record_mem i)
    ((L.uncoveredFragment S hInitial hInitials b).support_subset hxP) hxi
  exact L.blockedFragment_parent_ne_goodRecord S.cut S.separates hb.1 hi heq

#print axioms leftoverPath_spec
#print axioms leftoverPath_one_hit
#print axioms leftoverPaths_disjoint
#print axioms leftoverPath_disjoint_localRegion
#print axioms leftoverPath_disjoint_good_record

end Erdos599.GroundingAllMarkerAuxiliary.Input
