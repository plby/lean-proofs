/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.PopularIndexedDichotomy

/-!
# Strong target popularity excludes a popular separator

A source--target warp may be truncated at its first hit on any source--target
separator.  Truncation preserves pairwise disjointness and every source
index.  Consequently, if the target is strongly popular, every separator is
strongly popular.  This makes the two branches of the indexed popularity
dichotomy genuinely exclusive and rules out reapplying Theorem 8.4 inside
the stationary equal-index branch.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Popular

open DirectedPath Stationary

universe u

variable {V : Type u}

namespace XSWarp

/-- A target-warp member truncated at its first hit on a separator. -/
def firstSeparatorPath {Gamma : DWeb V} {C : Set V}
    (hC : IsSeparator Gamma C) (P : XSWarp Gamma Gamma.target)
    (p : P.paths) : FinitePath Gamma.graph :=
  p.1.firstHit C
    (hC p.1 (P.starts_in_source p.2) (P.ends_in_target p.2))

/-- Truncate every member of a target warp at its first separator hit. -/
def firstSeparatorWarp {Gamma : DWeb V} {C : Set V}
    (hC : IsSeparator Gamma C) (P : XSWarp Gamma Gamma.target) :
    XSWarp Gamma C where
  paths := Set.range (P.firstSeparatorPath hC)
  disjoint := by
    rintro q ⟨p, rfl⟩ r ⟨p', rfl⟩ hqr
    have hpp' : p.1 ≠ p'.1 := by
      intro hpp'
      apply hqr
      exact congrArg (P.firstSeparatorPath hC) (Subtype.ext hpp')
    exact (P.disjoint p.2 p'.2 hpp').mono
      (p.1.firstHit_support_subset C
        (hC p.1 (P.starts_in_source p.2) (P.ends_in_target p.2)))
      (p'.1.firstHit_support_subset C
        (hC p'.1 (P.starts_in_source p'.2) (P.ends_in_target p'.2)))
  starts_in_source := by
    rintro q ⟨p, rfl⟩
    change p.1.start ∈ Gamma.source
    exact P.starts_in_source p.2
  ends_in_target := by
    rintro q ⟨p, rfl⟩
    exact p.1.firstHit_finish_mem C
      (hC p.1 (P.starts_in_source p.2) (P.ends_in_target p.2))

/-- Separator truncation preserves every initial ordinal index. -/
theorem initialIndices_subset_firstSeparatorWarp
    {Gamma : DWeb V} {kappa : Cardinal.{u}} (U : KappaIndexed Gamma kappa)
    {C : Set V} (hC : IsSeparator Gamma C)
    (P : XSWarp Gamma Gamma.target) :
    initialIndicesOf U P.paths P.starts_in_source ⊆
      initialIndicesOf U (P.firstSeparatorWarp hC).paths
        (P.firstSeparatorWarp hC).starts_in_source := by
  rintro a ⟨p, hp, hpa⟩
  let ps : P.paths := ⟨p, hp⟩
  let q := P.firstSeparatorPath hC ps
  have hq : q ∈ (P.firstSeparatorWarp hC).paths := ⟨ps, rfl⟩
  refine ⟨q, hq, ?_⟩
  have hsource :
      (⟨q.start, (P.firstSeparatorWarp hC).starts_in_source hq⟩ :
          Gamma.source) =
        ⟨p.start, P.starts_in_source hp⟩ := Subtype.ext rfl
  exact (congrArg U.f hsource).trans hpa

end XSWarp

/-- A strongly popular target makes every source--target separator strongly
popular by first-hit truncation. -/
theorem IsStronglyPopular.separator
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {U : KappaIndexed Gamma kappa}
    (hstrong : IsStronglyPopular U Gamma.target)
    {C : Set V} (hC : IsSeparator Gamma C) :
    IsStronglyPopular U C := by
  obtain ⟨P, hP⟩ := hstrong
  refine ⟨P.firstSeparatorWarp hC, ?_⟩
  exact hP.mono
    (XSWarp.initialIndices_subset_firstSeparatorWarp U hC P)

/-- In particular, the strongly popular target branch contains no object of
the `PopularSeparator` structure. -/
theorem not_nonempty_popularSeparator_of_stronglyPopular_target
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {U : KappaIndexed Gamma kappa}
    (hstrong : IsStronglyPopular U Gamma.target) :
    ¬ Nonempty (PopularSeparator U) := by
  rintro ⟨S⟩
  exact S.not_strongly_popular (hstrong.separator S.separates)

end Popular
end Erdos599

#print axioms Erdos599.Popular.IsStronglyPopular.separator
#print axioms Erdos599.Popular.not_nonempty_popularSeparator_of_stronglyPopular_target
