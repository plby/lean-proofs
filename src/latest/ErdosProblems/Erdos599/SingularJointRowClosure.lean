/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularJointFullRow

/-!
# Competitor closure of one filled joint row

A target linkage on `D`, filled by trivial paths at the remaining ambient
sources, creates no new competitors outside `D` when it is combined with a
fixed family which also starts in `D`.  Indeed, a trivial path based outside
`D` cannot meet a normalized path based in `D`: a source vertex on such a
path must be its initial vertex.

For the singular construction, take
`D = (G.source \ A₀) ∪ B`.  The retargeted lower-induction construction
gives a linkage on `D`, so its filled full-source row is already closed
under itself and the fixed complementary linkage.  Only interactions with
other columns (or other historical choices) can enlarge its source set.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularJointRowClosure

open SingularExtension SingularRetargetedRow SingularJointFullRow

universe u

variable {V : Type u}

/-- Generic closure lemma for a family filled by trivial paths outside its
designated initial set.  Neither `F` nor `L` must be disjoint from the other;
only their initial vertices must lie in `D`. -/
theorem competitorClosure_fixed_union_fill_subset
    {G : DWeb V} (hNorm : G.IsNormalized)
    {D : Set V} {F L : Set G.DPath}
    (hFinit : G.initialSet F ⊆ D)
    (hLinit : G.initialSet L ⊆ D) :
    G.competitorClosure
        (F ∪ fillTargetLinkage G D L) D ⊆ D := by
  rintro b ⟨a, ha, p, hp, hpa, q, hq, hqb, hpq⟩
  rw [← hqb]
  rcases hq with hqF | hqFill
  · exact hFinit ⟨q, hqF, rfl⟩
  · rcases hqFill with hqL | hqTrivial
    · exact hLinit ⟨q, hqL, rfl⟩
    · obtain ⟨x, hx, rfl⟩ := hqTrivial
      rw [G.initial_trivialPath]
      obtain ⟨z, hzp, hztrivial⟩ := Set.not_disjoint_iff.1 hpq
      rw [G.support_trivialPath] at hztrivial
      have hzx : z = x := Set.mem_singleton_iff.1 hztrivial
      subst z
      have hxInitial : x = p.initial :=
        hNorm.eq_initial_of_mem_path p hzp hx.1
      rw [hxInitial, hpa]
      exact ha

/-- Specialization to two target linkages: the fixed linkage starts in a
subset of `D`, while the filled linkage starts exactly in `D`. -/
theorem competitorClosure_linkages_fill_subset
    {G : DWeb V} (hNorm : G.IsNormalized)
    {C D : Set V} (hCD : C ⊆ D)
    {F L : Set G.DPath}
    (hF : IsLinkageBetween G C G.target F)
    (hL : IsLinkageBetween G D G.target L) :
    G.competitorClosure
        (F ∪ fillTargetLinkage G D L) D ⊆ D := by
  apply competitorClosure_fixed_union_fill_subset hNorm
  · rw [hF.initialSet_eq]
    exact hCD
  · rw [hL.initialSet_eq]

/-- Every bounded request has a joint full-source row which is already
closed under its own paths together with the fixed complementary linkage. -/
theorem exists_jointFullRow_selfClosed
    {kappa rho : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hrho : rho < kappa)
    {G : DWeb V} (hG : G.IsUnhindered) (hNorm : G.IsNormalized)
    {A₀ B : Set V} (hA₀ : A₀ ⊆ G.source) (hB : B ⊆ A₀)
    (hBcard : #B = rho)
    {fixed : Set G.DPath}
    (hfixed : IsLinkageBetween G (G.source \ A₀) G.target fixed) :
    ∃ R : JointFullRow G A₀ B,
      G.competitorClosure (fixed ∪ R.paths)
          ((G.source \ A₀) ∪ B) ⊆
        (G.source \ A₀) ∪ B := by
  obtain ⟨L, hL⟩ := exists_jointBoundedTargetLinkage
    hlower hrho hG hNorm hA₀ hB hBcard hfixed
  let D : Set V := (G.source \ A₀) ∪ B
  have hD : D ⊆ G.source := by
    rintro x (hx | hx)
    · exact hx.1
    · exact hA₀ (hB hx)
  obtain ⟨hwarp, hfinite, hinitial, hlinks⟩ :=
    fillTargetLinkage_spec hNorm hD hL
  let R : JointFullRow G A₀ B :=
    { paths := fillTargetLinkage G D L
      isWarp := hwarp
      finiteCharacter := hfinite
      initialSet := hinitial
      linksJoint := hlinks }
  refine ⟨R, ?_⟩
  change G.competitorClosure
      (fixed ∪ fillTargetLinkage G D L) D ⊆ D
  apply competitorClosure_linkages_fill_subset hNorm
      (C := G.source \ A₀) (D := D)
  · exact Set.subset_union_left
  · exact hfixed
  · exact hL

/-- Strict-cardinality form of the self-closed joint-row construction. -/
theorem exists_jointFullRow_selfClosed_of_mk_lt
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    {G : DWeb V} (hG : G.IsUnhindered) (hNorm : G.IsNormalized)
    {A₀ B : Set V} (hA₀ : A₀ ⊆ G.source) (hB : B ⊆ A₀)
    (hBcard : #B < kappa)
    {fixed : Set G.DPath}
    (hfixed : IsLinkageBetween G (G.source \ A₀) G.target fixed) :
    ∃ R : JointFullRow G A₀ B,
      G.competitorClosure (fixed ∪ R.paths)
          ((G.source \ A₀) ∪ B) ⊆
        (G.source \ A₀) ∪ B := by
  exact exists_jointFullRow_selfClosed hlower hBcard hG hNorm
    hA₀ hB rfl hfixed

#print axioms competitorClosure_fixed_union_fill_subset
#print axioms competitorClosure_linkages_fill_subset
#print axioms exists_jointFullRow_selfClosed

end SingularJointRowClosure
end CardinalInduction
end Erdos599

