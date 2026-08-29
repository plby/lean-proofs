/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingMinimalSeparatingBoundary

/-!
# Removing one point from a finite-path separator

For the finite-path separator predicate used in grounding, one point is
either redundant or has a private original-source--target witness meeting
the old separator exactly there.  This is the precise ambient alternative
needed at the finite-parent priority deletion; no reachability relation is
confused with ambient separation.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingSeparatorPointRemoval

open DirectedPath GroundingMinimalSeparatingBoundary

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- Exact point-removal dichotomy for an ambient separator. -/
theorem separator_diff_singleton_or_privatePath
    (B : Set V) (hB : Popular.IsSeparator Gamma B)
    {t : V} (ht : t ∈ B) :
    Popular.IsSeparator Gamma (B \ {t}) ∨
      ∃ a ∈ Gamma.source, ∃ p : FinitePath Gamma.graph,
        Gamma.IsTargetPathFrom a p ∧ p.support ∩ B = {t} := by
  by_cases hdiff : Popular.IsSeparator Gamma (B \ {t})
  · exact Or.inl hdiff
  · right
    have hnotRoof : ¬ Gamma.source ⊆ Gamma.roof (B \ {t}) := by
      intro hroof
      exact hdiff ((isSeparator_iff_source_subset_roof (B \ {t})).2 hroof)
    obtain ⟨a, haSource, haNotRoof⟩ := Set.not_subset.mp hnotRoof
    obtain ⟨p, hpTarget, hpAvoid⟩ :=
      (Gamma.not_mem_roof_iff (B \ {t}) a).1 haNotRoof
    obtain ⟨x, hxp, hxB⟩ := hB p
      (by simpa only [hpTarget.1] using haSource) hpTarget.2
    have hxt : x = t := by
      by_contra hne
      exact Set.disjoint_left.1 hpAvoid hxp ⟨hxB, hne⟩
    subst x
    refine ⟨a, haSource, p, hpTarget, Set.Subset.antisymm ?_ ?_⟩
    · rintro x ⟨hxp, hxB⟩
      have hxt : x = t := by
        by_contra hne
        exact Set.disjoint_left.1 hpAvoid hxp ⟨hxB, hne⟩
      simpa only [Set.mem_singleton_iff] using hxt
    · intro x hx
      have hxt : x = t := Set.mem_singleton_iff.1 hx
      subst x
      exact ⟨hxp, ht⟩

end GroundingSeparatorPointRemoval
end Erdos599

#print axioms
  Erdos599.GroundingSeparatorPointRemoval.separator_diff_singleton_or_privatePath
