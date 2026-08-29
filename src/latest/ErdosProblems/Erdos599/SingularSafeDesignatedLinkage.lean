/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularSafeCompletion
import ErdosProblems.Erdos599.SingularSafeBatch

/-!
# Safely completing a designated source set

The singular row can be made future-proof if its newly completed source
coordinates are joined to the target by a linkage whose whole carrier may be
deleted without creating a hindrance.  This file records that exact selector
and constructs it for every finite designated set by repeated applications
of Aharoni--Berger Theorem 6.1.

The finite construction is genuinely ambient: safety is asserted in the
original web, not merely in the source subweb on the designated set.  It is
therefore the sound base case for a future transfinite batching theorem.  At
an infinite limit, the missing assertion is precisely that deletion of the
union of the previously selected carriers remains unhindered; no such limit
claim is made here.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularSafeDesignatedLinkage

open RegularSafeCompletion SingularSafeBatch

universe u

variable {V : Type u}

/-- An ambiently safe target linkage on exactly the designated source set. -/
structure SafeDesignatedLinkage (G : DWeb V) (A : Set V) where
  paths : Set G.DPath
  linkage : IsLinkageBetween G A G.target paths
  residual_unhindered : (G.delete (G.vertexSet paths)).IsUnhindered

namespace SafeDesignatedLinkage

variable {G : DWeb V} {A : Set V}

theorem isWarp (S : SafeDesignatedLinkage G A) : G.IsWarp S.paths :=
  S.linkage.isWarp

theorem finiteCharacter (S : SafeDesignatedLinkage G A) :
    G.HasFiniteCharacter S.paths :=
  S.linkage.finiteCharacter

@[simp] theorem initialSet (S : SafeDesignatedLinkage G A) :
    G.initialSet S.paths = A :=
  S.linkage.initialSet_eq

end SafeDesignatedLinkage

/-- In a normalized web, two carrier-disjoint target linkages combine to a
target linkage on the union of their initial sets. -/
theorem linkage_union_of_disjoint
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A B : Set V} {P R : Set G.DPath}
    (hA : A ⊆ G.source) (hB : B ⊆ G.source)
    (hP : IsLinkageBetween G A G.target P)
    (hR : IsLinkageBetween G B G.target R)
    (hPR : Disjoint (G.vertexSet P) (G.vertexSet R)) :
    IsLinkageBetween G (A ∪ B) G.target (P ∪ R) := by
  have hwarp : G.IsWarp (P ∪ R) := by
    intro p hp q hq hpq
    rcases hp with hpP | hpR
    · rcases hq with hqP | hqR
      · exact hP.isWarp hpP hqP hpq
      · apply Set.disjoint_left.2
        intro x hxp hxq
        exact Set.disjoint_left.1 hPR ⟨p, hpP, hxp⟩ ⟨q, hqR, hxq⟩
    · rcases hq with hqP | hqR
      · apply Set.disjoint_left.2
        intro x hxp hxq
        exact Set.disjoint_left.1 hPR ⟨q, hqP, hxq⟩ ⟨p, hpR, hxp⟩
      · exact hR.isWarp hpR hqR hpq
  have hfinite : G.HasFiniteCharacter (P ∪ R) := by
    intro p hp
    exact hp.elim hP.finiteCharacter hR.finiteCharacter
  have hinitial : G.initialSet (P ∪ R) = A ∪ B := by
    rw [G.initialSet_union, hP.initialSet_eq, hR.initialSet_eq]
  have hterminal : G.terminalFrontier (P ∪ R) ⊆ G.target := by
    rw [G.terminalFrontier_union]
    exact Set.union_subset hP.terminalFrontier_subset
      hR.terminalFrontier_subset
  refine ⟨hwarp, hfinite, hinitial, hterminal, ?_⟩
  intro p hp
  obtain ⟨q, rfl⟩ := hfinite hp
  have hsource : q.support ∩ (A ∪ B) = {q.start} := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxq, hxA | hxB⟩
      · exact Set.mem_singleton_iff.2
          (hNorm.eq_start_of_mem_walk q.walk hxq (hA hxA))
      · exact Set.mem_singleton_iff.2
          (hNorm.eq_start_of_mem_walk q.walk hxq (hB hxB))
    · intro x hx
      have hxStart : x = q.start := Set.mem_singleton_iff.1 hx
      subst x
      have hqInitial : q.start ∈ G.initialSet (P ∪ R) :=
        ⟨.inl q, hp, rfl⟩
      exact ⟨q.start_mem_support, hinitial ▸ hqInitial⟩
  have htarget : q.support ∩ G.target = {q.finish} := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxq, hxTarget⟩
      exact Set.mem_singleton_iff.2
        (hNorm.eq_finish_of_mem_walk q.walk hxq hxTarget)
    · intro x hx
      have hxFinish : x = q.finish := Set.mem_singleton_iff.1 hx
      subst x
      have hqTerminal : q.finish ∈ G.terminalFrontier (P ∪ R) :=
        ⟨.inl q, hp, rfl⟩
      exact ⟨q.finish_mem_support, hterminal hqTerminal⟩
  refine ⟨q, rfl, ?_, hsource⟩
  rw [Set.inter_union_distrib_left, hsource, htarget]
  ext x
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]

/-- The empty designated set is safely completed without deleting a vertex. -/
def empty (G : DWeb V) (hG : G.IsUnhindered) :
    SafeDesignatedLinkage G ∅ where
  paths := ∅
  linkage := empty_linkage G
  residual_unhindered := by
    have hempty : G.vertexSet (∅ : Set G.DPath) = ∅ := by
      ext x
      constructor
      · rintro ⟨p, hp, _hxp⟩
        exact hp.elim
      · intro hx
        exact hx.elim
    rw [hempty]
    simpa using hG

/-- Theorem 6.1 supplies the exact singleton safe selector. -/
theorem exists_singleton
    (G : DWeb V) (hG : G.IsUnhindered) {a : V}
    (ha : a ∈ G.source) :
    Nonempty (SafeDesignatedLinkage G {a}) := by
  obtain ⟨c⟩ := exists_safeCompletionChoice G ∅ (by simpa using hG)
    ha (by simp)
  refine ⟨⟨c.family, c.family_isLinkageBetween, ?_⟩⟩
  rw [c.vertexSet_family]
  simpa using c.next_unhindered

/-- A source outside the initial set of a normalized linkage is outside its
entire carrier. -/
theorem source_not_mem_vertexSet_of_not_mem_initialSet
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A : Set V} {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    {a : V} (haSource : a ∈ G.source) (haA : a ∉ A) :
    a ∉ G.vertexSet P := by
  rintro ⟨p, hpP, hap⟩
  have haInitial : a = p.initial :=
    hNorm.eq_initial_of_mem_path p hap haSource
  apply haA
  rw [← hP.initialSet_eq]
  exact ⟨p, hpP, haInitial.symm⟩

/-- Every finite set of sources has a jointly safely deletable target
linkage.  The proof iterates Theorem 6.1 in the current ambient residual;
because there are only finitely many steps, no limit-deletion assertion is
needed. -/
theorem exists_finite
    (G : DWeb V) (hNorm : G.IsNormalized) (hG : G.IsUnhindered)
    {A : Set V} (hAfinite : A.Finite) (hA : A ⊆ G.source) :
    Nonempty (SafeDesignatedLinkage G A) := by
  induction A, hAfinite using Set.Finite.induction_on with
  | empty => exact ⟨empty G hG⟩
  | @insert a S haS hSfinite ih =>
      have hSsource : S ⊆ G.source :=
        fun x hx ↦ hA (Set.mem_insert_iff.2 (Or.inr hx))
      obtain ⟨P⟩ := ih hSsource
      have haSource : a ∈ G.source := hA (Set.mem_insert a S)
      have haFresh : a ∉ G.vertexSet P.paths :=
        source_not_mem_vertexSet_of_not_mem_initialSet
          hNorm P.linkage haSource haS
      obtain ⟨c⟩ := exists_safeCompletionChoice G
        (G.vertexSet P.paths) P.residual_unhindered haSource haFresh
      have hcross : Disjoint (G.vertexSet P.paths)
          (G.vertexSet c.family) := by
        rw [c.vertexSet_family]
        exact c.avoids.symm
      let L := P.paths ∪ c.family
      have hlink : IsLinkageBetween G (S ∪ {a}) G.target L :=
        linkage_union_of_disjoint hNorm hSsource
          (Set.singleton_subset_iff.2 haSource)
          P.linkage c.family_isLinkageBetween hcross
      refine ⟨⟨L, ?_, ?_⟩⟩
      · rw [Set.union_comm] at hlink
        exact hlink
      · dsimp only [L]
        rw [G.vertexSet_union, c.vertexSet_family]
        exact c.next_unhindered

/-! ## Completing the entire residual source

When the lower induction hypothesis already links the whole residual source,
that full linkage is automatically a safe covering batch: deleting its
carrier deletes every source vertex, and a web with empty source is
unhindered.  This gives the second unconditional branch used by a singular
safe-row machine.
-/

/-- A full source--target linkage is safely deletable because no source
survives its carrier deletion. -/
def ofFullLinkage
    {G : DWeb V} {P : Set G.DPath}
    (hP : IsLinkageBetween G G.source G.target P) :
    SafeDesignatedLinkage G G.source where
  paths := P
  linkage := hP
  residual_unhindered := by
    apply isUnhindered_of_source_eq_empty
    ext a
    constructor
    · intro ha
      exfalso
      apply ha.2
      have haInitial : a ∈ G.initialSet P :=
        hP.initialSet_eq.symm ▸ ha.1
      obtain ⟨p, hpP, hpa⟩ := haInitial
      exact ⟨p, hpP, hpa ▸ p.initial_mem_support⟩
    · intro ha
      exact ha.elim

/-- If the entire residual source has cardinal below the current induction
cardinal, the lower extension clause supplies a safely deletable full-source
batch. -/
theorem exists_full_of_source_below
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    {G : DWeb V} (hG : G.IsUnhindered)
    (hsource : #G.source < kappa) :
    Nonempty (SafeDesignatedLinkage G G.source) := by
  have hext : ExtensionClauseAt G #G.source :=
    (hlower #G.source hsource G hG).extension
  obtain ⟨P, hP⟩ := linkable_of_extension_at_source_card G hext
  exact ⟨ofFullLinkage hP⟩

end SingularSafeDesignatedLinkage
end CardinalInduction
end Erdos599
