/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularJointFullRow

/-!
# Full rows supported on a bounded request

A bounded target linkage can be completed to a full-source warp with
trivial paths at every unrequested source.  Besides the usual structural
row fields, this gives an exact support certificate: every member whose
initial vertex is outside the request is literally trivial.

This certificate has a useful closure consequence.  In a normalized web,
competitors of `S` inside a family supported on `R` have initials in
`S ∪ R`.  Indeed, a competitor rooted outside `R` is trivial, and any path
meeting that trivial path at its source must start there as well.  Thus a
triangular family whose requests all lie in one source layer cannot enlarge
that layer through internal row competitors.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularBoundedSupportRows

open SingularExtension SingularJointFullRow

universe u

variable {V : Type u}

/-- A full-source row whose only nontrivial components are rooted in the
designated request. -/
structure BoundedSupportRow (G : DWeb V) (B : Set V) where
  paths : Set G.DPath
  isWarp : G.IsWarp paths
  finiteCharacter : G.HasFiniteCharacter paths
  initialSet : G.initialSet paths = G.source
  links : LinksToTarget G paths B
  trivial_outside : ∀ p ∈ paths, p.initial ∉ B →
    p = G.trivialPath p.initial

/-- Filling a target linkage with trivial paths produces a row supported on
the linkage's initial set. -/
noncomputable def BoundedSupportRow.ofLinkage
    {G : DWeb V} (hNorm : G.IsNormalized)
    {B : Set V} (hB : B ⊆ G.source) {P : Set G.DPath}
    (hP : IsLinkageBetween G B G.target P) :
    BoundedSupportRow G B where
  paths := fillTargetLinkage G B P
  isWarp := (fillTargetLinkage_spec hNorm hB hP).1
  finiteCharacter := (fillTargetLinkage_spec hNorm hB hP).2.1
  initialSet := (fillTargetLinkage_spec hNorm hB hP).2.2.1
  links := (fillTargetLinkage_spec hNorm hB hP).2.2.2
  trivial_outside := by
    intro p hp hpOutside
    rcases hp with hpP | hpTrivial
    · have hpInitial : p.initial ∈ B := by
        rw [← hP.initialSet_eq]
        exact ⟨p, hpP, rfl⟩
      exact (hpOutside hpInitial).elim
    · obtain ⟨x, _hx, rfl⟩ := hpTrivial
      rw [G.initial_trivialPath]

@[simp] theorem BoundedSupportRow.ofLinkage_paths
    {G : DWeb V} (hNorm : G.IsNormalized)
    {B : Set V} (hB : B ⊆ G.source) {P : Set G.DPath}
    (hP : IsLinkageBetween G B G.target P) :
    (BoundedSupportRow.ofLinkage hNorm hB hP).paths =
      fillTargetLinkage G B P :=
  rfl

/-- Lower induction supplies a bounded-support row for every request of
cardinality strictly below the current cardinal. -/
theorem exists_boundedSupportRow_of_lower
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    {G : DWeb V} (hG : G.IsUnhindered) (hNorm : G.IsNormalized)
    {B : Set V} (hB : B ⊆ G.source) (hBcard : #B < kappa) :
    Nonempty (BoundedSupportRow G B) := by
  obtain ⟨P, hP⟩ :=
    exists_smallSourceLinkage_of_lower hlower G hG hNorm hB hBcard
  exact ⟨BoundedSupportRow.ofLinkage hNorm hB hP⟩

namespace BoundedSupportRow

variable {G : DWeb V} {B : Set V}

/-- Every member starts in the ambient source. -/
theorem initial_mem_source (R : BoundedSupportRow G B)
    {p : G.DPath} (hp : p ∈ R.paths) : p.initial ∈ G.source := by
  rw [← R.initialSet]
  exact ⟨p, hp, rfl⟩

/-- A nontrivial member must start in the bounded request. -/
theorem initial_mem_of_ne_trivial (R : BoundedSupportRow G B)
    {p : G.DPath} (hp : p ∈ R.paths)
    (hne : p ≠ G.trivialPath p.initial) : p.initial ∈ B := by
  by_contra hpOutside
  exact hne (R.trivial_outside p hp hpOutside)

end BoundedSupportRow

/-! ## Competitor closure of support-controlled families -/

/-- If all nontrivial paths in a family are rooted in `R`, then normalized
source geometry confines every competitor of `S` to `S ∪ R`. -/
theorem competitorClosure_subset_union_of_trivial_outside
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {R S : Set V}
    (hinitial : G.initialSet W ⊆ G.source)
    (htrivial : ∀ p ∈ W, p.initial ∉ R →
      p = G.trivialPath p.initial) :
    G.competitorClosure W S ⊆ S ∪ R := by
  rintro b ⟨a, haS, p, hpW, hpa, q, hqW, hqb, hpq⟩
  by_cases hbR : b ∈ R
  · exact Or.inr hbR
  have hqTrivial : q = G.trivialPath q.initial :=
    htrivial q hqW (hqb ▸ hbR)
  have hbq : b ∈ q.support := by
    rw [hqTrivial, G.support_trivialPath, hqb]
    exact Set.mem_singleton b
  have hmeet : (p.support ∩ q.support).Nonempty :=
    Set.not_disjoint_iff.mp hpq
  obtain ⟨x, hxp, hxq⟩ := hmeet
  have hxb : x = b := by
    rw [hqTrivial, G.support_trivialPath, hqb] at hxq
    exact Set.mem_singleton_iff.mp hxq
  have hbSource : b ∈ G.source := by
    apply hinitial
    exact ⟨q, hqW, hqb⟩
  have hbInitial : b = p.initial :=
    hNorm.eq_initial_of_mem_path p (hxb ▸ hxp) hbSource
  exact Or.inl (hbInitial ▸ hpa ▸ haS)

/-- The union of bounded-support rows is supported on the union of their
requests. -/
theorem trivial_outside_iUnion
    {G : DWeb V} {I : Type*} {B : I → Set V}
    (R : ∀ i, BoundedSupportRow G (B i))
    {p : G.DPath} (hp : p ∈ ⋃ i, (R i).paths)
    (hpOutside : p.initial ∉ ⋃ i, B i) :
    p = G.trivialPath p.initial := by
  obtain ⟨i, hpi⟩ := Set.mem_iUnion.1 hp
  apply (R i).trivial_outside p hpi
  intro hpBi
  exact hpOutside (Set.mem_iUnion.2 ⟨i, hpBi⟩)

/-- Consequently, competitors inside any simultaneous family of
bounded-support rows are confined to the old set together with the union of
the registered requests. -/
theorem competitorClosure_iUnion_subset
    {G : DWeb V} (hNorm : G.IsNormalized)
    {I : Type*} {B : I → Set V}
    (R : ∀ i, BoundedSupportRow G (B i)) (S : Set V) :
    G.competitorClosure (⋃ i, (R i).paths) S ⊆
      S ∪ ⋃ i, B i := by
  apply competitorClosure_subset_union_of_trivial_outside hNorm
  · rintro x ⟨p, hp, rfl⟩
    obtain ⟨i, hpi⟩ := Set.mem_iUnion.1 hp
    exact (R i).initial_mem_source hpi
  · exact fun p hp hpOutside ↦
      trivial_outside_iUnion R hp hpOutside

/-- If every registered request is already contained in `S`, the entire
simultaneous row family creates no competitors outside `S`. -/
theorem competitorClosure_iUnion_subset_of_requests_subset
    {G : DWeb V} (hNorm : G.IsNormalized)
    {I : Type*} {B : I → Set V}
    (R : ∀ i, BoundedSupportRow G (B i)) {S : Set V}
    (hBS : ∀ i, B i ⊆ S) :
    G.competitorClosure (⋃ i, (R i).paths) S ⊆ S := by
  apply (competitorClosure_iUnion_subset hNorm R S).trans
  rintro x (hxS | hxB)
  · exact hxS
  · obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hxB
    exact hBS i hxi

#print axioms exists_boundedSupportRow_of_lower
#print axioms competitorClosure_iUnion_subset
#print axioms competitorClosure_iUnion_subset_of_requests_subset

end SingularBoundedSupportRows
end CardinalInduction
end Erdos599
