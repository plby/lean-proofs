/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SliceCandidate

/-!
# First-hit prefixes as a segment realization

This packages the canonical first hit of each member of a linkage at a
separating set into the generic `SliceSegmentCore.SegmentRealization` API.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SliceCandidate

open DirectedPath

universe u

variable {V : Type u}

/-- The source-indexed first-hit prefixes of a linkage, retaining their
original linkage members as carriers. -/
noncomputable def firstHitSegmentRealization
    {Q : DWeb V} {A C D : Set V} {W : Set Q.DPath}
    (hW : IsLinkageBetween Q A C W)
    (hsep : RelationalRoof.Separates Q.graph.Adj A C D) :
    SliceSegmentCore.SegmentRealization Q W A D A where
  source_subset := Set.Subset.rfl
  carrier := fun x => (linkageMemberAt hW x).1
  carrier_mem := fun x => (linkageMemberAt hW x).2
  carrier_injective := by
    intro x y hxy
    exact linkageMemberAt_injective hW (Subtype.ext hxy)
  segment := linkageFirstHitAt hW hsep
  segment_start := linkageFirstHitAt_start hW hsep
  segment_finish_mem := linkageFirstHitAt_finish_mem hW hsep
  segment_subpath := by
    intro x
    unfold linkageFirstHitAt
    simpa only [← linkageMemberAt_eq_finite hW x] using
      (linkageFiniteAt hW x).firstHit_isSubpathOf D
        (linkageFiniteAt_meets hW hsep x)
  segment_source := by
    intro x
    obtain ⟨q, hq, _hends, hsource⟩ :=
      hW.endpointPure (linkageMemberAt hW x).1
        (linkageMemberAt hW x).2
    have hqeq : q = linkageFiniteAt hW x := by
      apply Sum.inl.inj
      exact hq.symm.trans (linkageMemberAt_eq_finite hW x)
    subst q
    apply Set.Subset.antisymm
    · rintro y ⟨hy, hyA⟩
      have hyOld : y ∈ (linkageFiniteAt hW x).support ∩ A :=
        ⟨linkageFirstHitAt_support_subset hW hsep x hy, hyA⟩
      rw [hsource] at hyOld
      exact Set.mem_singleton_iff.mpr
        ((Set.mem_singleton_iff.mp hyOld).trans
          ((linkageFiniteAt_start hW x).trans
            (linkageFirstHitAt_start hW hsep x).symm))
    · intro y hy
      subst y
      exact ⟨(linkageFirstHitAt hW hsep x).start_mem_support,
        linkageFirstHitAt_start hW hsep x ▸ x.2⟩
  segment_endpoints := by
    intro x
    rw [Set.inter_union_distrib_left,
      linkageFirstHitAt_targetPure hW hsep x]
    rw [show (linkageFirstHitAt hW hsep x).support ∩ A =
        {(linkageFirstHitAt hW hsep x).start} from by
      obtain ⟨q, hq, _hends, hsource⟩ :=
        hW.endpointPure (linkageMemberAt hW x).1
          (linkageMemberAt hW x).2
      have hqeq : q = linkageFiniteAt hW x := by
        apply Sum.inl.inj
        exact hq.symm.trans (linkageMemberAt_eq_finite hW x)
      subst q
      apply Set.Subset.antisymm
      · rintro y ⟨hy, hyA⟩
        have hyOld : y ∈ (linkageFiniteAt hW x).support ∩ A :=
          ⟨linkageFirstHitAt_support_subset hW hsep x hy, hyA⟩
        rw [hsource] at hyOld
        exact Set.mem_singleton_iff.mpr
          ((Set.mem_singleton_iff.mp hyOld).trans
            ((linkageFiniteAt_start hW x).trans
              (linkageFirstHitAt_start hW hsep x).symm))
      · intro y hy
        subst y
        exact ⟨(linkageFirstHitAt hW hsep x).start_mem_support,
          linkageFirstHitAt_start hW hsep x ▸ x.2⟩]
    rfl

end SliceCandidate
end CardinalInduction
end Erdos599
