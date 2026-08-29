/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Blueprint
import ErdosProblems.Erdos599.FamilyTools

/-!
# Representation-independent hammock closure

Only a good-route predicate, carrier map, and pairwise disjoint interiors
are used in maximality and cardinal avoidance. This isolates the genuine
closing argument for native occurrences without coercing them to `AltPath`
or asserting that all common-endpoint routes may be switched together.
-/

noncomputable section

namespace Erdos599.Blueprint.CarrierHammock

open Cardinal Set Order

universe u

variable {Route V : Type u}

def Admissible (good : Set Route) (carrier : Route → Set V)
    (ends : Set V) (H : Set Route) : Prop :=
  H ⊆ good ∧ H.PairwiseDisjoint (fun q ↦ carrier q \ ends)

variable {good : Set Route} {carrier : Route → Set V} {ends : Set V}

theorem empty_admissible : Admissible good carrier ends ∅ := by
  constructor <;> simp

theorem Admissible.subset {H K : Set Route}
    (hH : Admissible good carrier ends H) (hKH : K ⊆ H) :
    Admissible good carrier ends K :=
  ⟨hKH.trans hH.1, hH.2.subset hKH⟩

theorem Admissible.insert {H : Set Route} {q : Route}
    (hH : Admissible good carrier ends H) (hq : q ∈ good)
    (hdisj : ∀ r ∈ H, Disjoint (carrier q \ ends) (carrier r \ ends)) :
    Admissible good carrier ends (insert q H) := by
  constructor
  · rintro r (rfl | hr)
    · exact hq
    · exact hH.1 hr
  · intro a ha b hb hab
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact False.elim (hab rfl)
    · exact hdisj b hb
    · exact (hdisj a ha).symm
    · exact hH.2 ha hb hab

theorem admissible_sUnion_of_chain {c : Set (Set Route)}
    (hgood : ∀ H ∈ c, Admissible good carrier ends H)
    (hc : IsChain (· ⊆ ·) c) : Admissible good carrier ends (⋃₀ c) := by
  constructor
  · rintro q ⟨H, hHc, hqH⟩
    exact (hgood H hHc).1 hqH
  · intro q hq r hr hqr
    obtain ⟨H, hHc, hqH⟩ := hq
    obtain ⟨K, hKc, hrK⟩ := hr
    by_cases hHK : H = K
    · subst K
      exact (hgood H hHc).2 hqH hrK hqr
    · rcases hc hHc hKc hHK with hHK | hKH
      · exact (hgood K hKc).2 (hHK hqH) hrK hqr
      · exact (hgood H hHc).2 hqH (hKH hrK) hqr

theorem exists_maximal_superset {K : Set Route}
    (hK : Admissible good carrier ends K) :
    ∃ H : Set Route, K ⊆ H ∧ Maximal (Admissible good carrier ends) H := by
  apply zorn_subset_nonempty {H | Admissible good carrier ends H}
  · intro c hcsub hc _
    exact ⟨⋃₀ c, admissible_sUnion_of_chain (fun H hH ↦ hcsub hH) hc,
      fun H hH ↦ Set.subset_sUnion_of_mem hH⟩
  · exact hK

/-- Cardinal truncation is performed on actual subfamilies of a witness. -/
theorem exists_maximalUpTo (rho : Cardinal.{u}) :
    ∃ H : Set Route,
      MaximalUpTo {K | Admissible good carrier ends K} rho H := by
  by_cases hlarge : ∃ K : Set Route, Admissible good carrier ends K ∧ succ rho ≤ #K
  · obtain ⟨K, hK, hcard⟩ := hlarge
    obtain ⟨a, ha⟩ := Cardinal.le_mk_iff_exists_set.mp ((le_succ rho).trans hcard)
    obtain ⟨b, hb⟩ := Cardinal.le_mk_iff_exists_set.mp hcard
    have haK : Subtype.val '' a ⊆ K := by
      rintro q ⟨r, _, rfl⟩
      exact r.property
    have hbK : Subtype.val '' b ⊆ K := by
      rintro q ⟨r, _, rfl⟩
      exact r.property
    refine ⟨Subtype.val '' a, maximalUpTo_of_large (hK.subset haK) ?_
      (hK.subset hbK) ?_⟩
    · exact (Cardinal.mk_image_eq_of_injOn Subtype.val a Set.injOn_subtype_val).trans ha
    · exact (Cardinal.mk_image_eq_of_injOn Subtype.val b Set.injOn_subtype_val).trans hb
  · obtain ⟨H, _, hH⟩ := exists_maximal_superset
      (empty_admissible (good := good) (carrier := carrier) (ends := ends))
    have hcard : #H ≤ rho := by
      by_contra hn
      exact hlarge ⟨H, hH.1, succ_le_of_lt (lt_of_not_ge hn)⟩
    exact ⟨H, maximalUpTo_of_maximal hH.1 hH hcard⟩

/-- An external admissible route forces the genuinely large branch of a
small-carrier maximal-up-to family. -/
theorem exists_large_of_external {rho : Cardinal.{u}} {H : Set Route} {X : Set V}
    (hH : MaximalUpTo {K | Admissible good carrier ends K} rho H)
    (hHX : ∀ q ∈ H, carrier q ⊆ X)
    {q : Route} (hq : q ∈ good)
    (hcap : carrier q ∩ X ⊆ ends) (hout : ¬carrier q ⊆ X) :
    ∃ K : Set Route, Admissible good carrier ends K ∧ #K = succ rho := by
  have hdisj : ∀ r ∈ H, Disjoint (carrier q \ ends) (carrier r \ ends) := by
    intro r hr
    rw [Set.disjoint_left]
    intro x hxq hxr
    exact hxq.2 (hcap ⟨hxq.1, hHX r hr hxr.1⟩)
  have hinsert := (MaximalUpTo.mem hH).insert hq hdisj
  rcases hH with hsmall | hlarge
  · have heq : H = insert q H :=
      hsmall.2.1.eq_of_subset hinsert (Set.subset_insert q H)
    have hqH : q ∈ H := heq.symm.subset (Set.mem_insert q H)
    exact False.elim (hout (hHX q hqH))
  · exact hlarge.2.2

/-- Large pairwise-disjoint interiors contain a member avoiding any small
set. This selects one route, not a simultaneous union of all switches. -/
theorem exists_mem_disjoint {rho : Cardinal.{u}} {H : Set Route} {X : Set V}
    (hH : Admissible good carrier ends H) (hcard : #H = succ rho)
    (hX : #X ≤ rho) :
    ∃ q ∈ H, Disjoint (carrier q \ ends) X := by
  by_contra hnone
  push Not at hnone
  have hmeet : ∀ q ∈ H, ∃ x ∈ X, x ∈ carrier q \ ends := by
    intro q hq
    obtain ⟨x, hxq, hxX⟩ := Set.not_disjoint_iff.mp (hnone q hq)
    exact ⟨x, hxX, hxq⟩
  have hle : #H ≤ #X := FamilyTools.mk_le_of_pairwiseDisjoint_of_meets hH.2 hmeet
  have hbad : succ rho ≤ rho := hcard.symm ▸ hle.trans hX
  exact (not_le_of_gt (Order.lt_succ rho)) hbad

/-- A small family of countable carriers stays small. Indexing by the
actual subtype avoids charging all routes in the ambient route type. -/
theorem mk_carrierUnion_le {rho : Cardinal.{u}} {H : Set Route}
    (hrho : aleph0 ≤ rho) (hH : #H ≤ rho)
    (hcount : ∀ q ∈ H, (carrier q).Countable) :
    #(⋃ q : H, carrier q.1) ≤ rho := by
  refine (Cardinal.mk_iUnion_le (fun q : H ↦ carrier q.1)).trans ?_
  exact Cardinal.mul_le_of_le hrho hH
    (ciSup_le' fun q : H ↦ (hcount q.1 q.2).le_aleph0.trans hrho)

/-- An inclusion-maximal small family of countable carriers bounds every
admissible family. Count only routes outside the maximal family, so routes
with empty interiors cause no exception to the injection argument. -/
theorem mk_le_of_maximal_of_countable
    {rho : Cardinal.{u}} (hrho : aleph0 ≤ rho) {M H : Set Route}
    (hM : Maximal (Admissible good carrier ends) M)
    (hMcard : #M ≤ rho) (hcount : ∀ q ∈ M, (carrier q).Countable)
    (hH : Admissible good carrier ends H) : #H ≤ rho := by
  classical
  let X : Set V := ⋃ q : M, carrier q.1
  have hXcard : #X ≤ rho := mk_carrierUnion_le hrho hMcard hcount
  have hmeet : ∀ q ∈ H \ M, ∃ x ∈ X, x ∈ carrier q \ ends := by
    intro q hq
    by_contra hnone
    have hdisjX : Disjoint (carrier q \ ends) X := by
      rw [Set.disjoint_left]
      intro x hxq hxX
      exact hnone ⟨x, hxX, hxq⟩
    have hdisj : ∀ r ∈ M,
        Disjoint (carrier q \ ends) (carrier r \ ends) := by
      intro r hr
      apply hdisjX.mono_right
      intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨r, hr⟩, hx.1⟩
    have hinsert := hM.1.insert (hH.1 hq.1) hdisj
    have heq : M = insert q M :=
      hM.eq_of_subset hinsert (Set.subset_insert q M)
    exact hq.2 (heq.symm.subset (Set.mem_insert q M))
  have hdiff : #(H \ M : Set Route) ≤ rho :=
    (FamilyTools.mk_le_of_pairwiseDisjoint_of_meets
      (hH.2.subset Set.sdiff_subset) hmeet).trans hXcard
  exact (Cardinal.le_mk_sdiff_add_mk H M).trans
    (Cardinal.add_le_of_le hrho hdiff hMcard)

#print axioms exists_maximalUpTo
#print axioms exists_large_of_external
#print axioms exists_mem_disjoint
#print axioms mk_carrierUnion_le
#print axioms mk_le_of_maximal_of_countable

end Erdos599.Blueprint.CarrierHammock
