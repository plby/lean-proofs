/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Blueprint931
import ErdosProblems.Erdos599.SeededHammock

/-!
# Maximal nondegenerate hammocks and their closure consequence

Ordinary hammock closure does not turn nondegeneracy of a particular
outside path into a strong imaginary edge. Here we construct the stronger
filtered maximal families by Zorn and cardinal thinning, and prove their
exact insertion consequence. Incorporating these families in the actual
causal closing set is a separate obligation.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {u₀ : V} {e : AltEnd V}

theorem NondegenerateHammock.subset
    {H K : Set (AltPath Gamma.graph)}
    (hH : NondegenerateHammock Gamma Y u₀ e H) (hKH : K ⊆ H) :
    NondegenerateHammock Gamma Y u₀ e K :=
  ⟨hH.1.subset hKH, fun Q hQ ↦ hH.2 Q (hKH hQ)⟩

theorem NondegenerateHammock.insert
    {H : Set (AltPath Gamma.graph)} {Q : AltPath Gamma.graph}
    (hH : NondegenerateHammock Gamma Y u₀ e H)
    (hsafe : IsSafe Y Q) (hstart : Q.initial = u₀)
    (hend : HasEnd Q e) (hnondeg : ¬IsDegenerate Y Q e)
    (hdisj : ∀ R ∈ H,
      Disjoint (hammockInterior u₀ e Q) (hammockInterior u₀ e R)) :
    NondegenerateHammock Gamma Y u₀ e (insert Q H) := by
  refine ⟨hH.1.insert hsafe hstart hend hdisj, ?_⟩
  intro R hR
  rcases hR with rfl | hR
  · exact hnondeg
  · exact hH.2 R hR

theorem nondegenerateHammock_sUnion_of_chain
    {c : Set (Set (AltPath Gamma.graph))}
    (hcsub : ∀ H ∈ c, NondegenerateHammock Gamma Y u₀ e H)
    (hc : IsChain (· ⊆ ·) c) :
    NondegenerateHammock Gamma Y u₀ e (⋃₀ c) := by
  refine ⟨hammock_sUnion_of_chain (fun H hH ↦ (hcsub H hH).1) hc, ?_⟩
  intro Q hQ
  obtain ⟨H, hHc, hQH⟩ := Set.mem_sUnion.1 hQ
  exact (hcsub H hHc).2 Q hQH

theorem exists_maximal_nondegenerateHammock_superset
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (u₀ : V) (e : AltEnd V)
    {K : Set (AltPath Gamma.graph)}
    (hK : NondegenerateHammock Gamma Y u₀ e K) :
    ∃ H : Set (AltPath Gamma.graph), K ⊆ H ∧
      Maximal (fun L ↦ NondegenerateHammock Gamma Y u₀ e L) H := by
  apply zorn_subset_nonempty
    {L : Set (AltPath Gamma.graph) | NondegenerateHammock Gamma Y u₀ e L}
  · intro c hcsub hc _hcne
    exact ⟨⋃₀ c,
      nondegenerateHammock_sUnion_of_chain (fun H hH ↦ hcsub hH) hc,
      fun L hL ↦ Set.subset_sUnion_of_mem hL⟩
  · exact hK

def NondegenerateHammockMaximalUpTo
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (u₀ : V) (e : AltEnd V)
    (rho : Cardinal.{u}) (H : Set (AltPath Gamma.graph)) : Prop :=
  MaximalUpTo {L | NondegenerateHammock Gamma Y u₀ e L} rho H

theorem NondegenerateHammockMaximalUpTo.isNondegenerateHammock
    {rho : Cardinal.{u}} {H : Set (AltPath Gamma.graph)}
    (hH : NondegenerateHammockMaximalUpTo Gamma Y u₀ e rho H) :
    NondegenerateHammock Gamma Y u₀ e H :=
  MaximalUpTo.mem hH

theorem NondegenerateHammockMaximalUpTo.card_le
    {rho : Cardinal.{u}} {H : Set (AltPath Gamma.graph)}
    (hH : NondegenerateHammockMaximalUpTo Gamma Y u₀ e rho H) :
    #H ≤ rho := MaximalUpTo.card_le hH

/-- The cardinal truncation is constructive in the proof-theoretic sense:
both subfamilies in the large branch are chosen from an actual witness. -/
theorem exists_nondegenerateHammockMaximalUpTo
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (u₀ : V) (e : AltEnd V)
    (rho : Cardinal.{u}) :
    ∃ H : Set (AltPath Gamma.graph),
      NondegenerateHammockMaximalUpTo Gamma Y u₀ e rho H := by
  by_cases hlarge : ∃ K : Set (AltPath Gamma.graph),
      NondegenerateHammock Gamma Y u₀ e K ∧ succ rho ≤ #K
  · obtain ⟨K, hK, hKcard⟩ := hlarge
    obtain ⟨s, hs⟩ := Cardinal.le_mk_iff_exists_set.mp
      ((le_succ rho).trans hKcard)
    obtain ⟨t, ht⟩ := Cardinal.le_mk_iff_exists_set.mp hKcard
    have hsK : Subtype.val '' s ⊆ K := by
      rintro x ⟨y, _, rfl⟩
      exact y.2
    have htK : Subtype.val '' t ⊆ K := by
      rintro x ⟨y, _, rfl⟩
      exact y.2
    refine ⟨Subtype.val '' s,
      maximalUpTo_of_large (hK.subset hsK) ?_ (hK.subset htK) ?_⟩
    · exact (Cardinal.mk_image_eq_of_injOn Subtype.val s
        Set.injOn_subtype_val).trans hs
    · exact (Cardinal.mk_image_eq_of_injOn Subtype.val t
        Set.injOn_subtype_val).trans ht
  · have hempty : NondegenerateHammock Gamma Y u₀ e ∅ :=
      ⟨hammock_empty Gamma Y u₀ e, by simp⟩
    obtain ⟨H, _, hH⟩ :=
      exists_maximal_nondegenerateHammock_superset Gamma Y u₀ e hempty
    have hcard : #H ≤ rho := by
      by_contra hnot
      exact hlarge ⟨H, hH.1, succ_le_of_lt (lt_of_not_ge hnot)⟩
    exact ⟨H, maximalUpTo_of_maximal hH.1 hH hcard⟩

def NondegenerateHammockClosedUpTo
    (Gamma : DWeb V) (Y : Set Gamma.DPath)
    (X before innerRoof outerRoof : Set V) (rho : Cardinal.{u}) : Prop :=
  ∀ u₀ e, HammockEligible before innerRoof outerRoof u₀ e →
    ∃ H : Set (AltPath Gamma.graph),
      NondegenerateHammockMaximalUpTo Gamma Y u₀ e rho H ∧
        HammockContained H X

/-- Insertion into the filtered family supplies the actual strong witness;
no bound on degenerate members of an unrelated hammock is assumed. -/
theorem hasNondegenerateHammockCard_of_nondegenerateClosed
    {X before innerRoof outerRoof : Set V} {rho : Cardinal.{u}}
    {Q : AltPath Gamma.graph}
    (hclosed : NondegenerateHammockClosedUpTo Gamma Y X before
      innerRoof outerRoof rho)
    (heligible : HammockEligible before innerRoof outerRoof u₀ e)
    (hsafe : IsSafe Y Q) (hstart : Q.initial = u₀)
    (hend : HasEnd Q e) (hnondeg : ¬IsDegenerate Y Q e)
    (hdisj : Disjoint (hammockInterior u₀ e Q) X)
    (houtside : ¬Q.vertexSet ⊆ X) :
    HasNondegenerateHammockCard Gamma Y u₀ e (succ rho) := by
  obtain ⟨H, hH, hHX⟩ := hclosed u₀ e heligible
  have hinsert := hH.isNondegenerateHammock.insert hsafe hstart hend
    hnondeg (disjoint_hammockInterior_of_contained hHX hdisj)
  rcases hH with hsmall | hlarge
  · have heq : H = insert Q H :=
      hsmall.2.1.eq_of_subset hinsert (Set.subset_insert Q H)
    have hQH : Q ∈ H := heq.symm.subset (Set.mem_insert Q H)
    exact (houtside fun x hx ↦
      hHX (Set.mem_iUnion.2 ⟨Q, Set.mem_iUnion.2 ⟨hQH, hx⟩⟩)).elim
  · exact hlarge.2.2

theorem isDegenerate_of_not_strong_of_nondegenerateClosed
    {X before innerRoof outerRoof : Set V} {rho : Cardinal.{u}}
    {v : V} {Q : AltPath Gamma.graph}
    (hclosed : NondegenerateHammockClosedUpTo Gamma Y X before
      innerRoof outerRoof rho)
    (heligible : HammockEligible before innerRoof outerRoof u₀ (.vertex v))
    (hsafe : IsSafe Y Q) (hstart : Q.initial = u₀)
    (hend : HasEnd Q (.vertex v))
    (hdisj : Disjoint (hammockInterior u₀ (.vertex v) Q) X)
    (houtside : ¬Q.vertexSet ⊆ X)
    (hweak : ¬IsStrongImaginaryEdge Gamma Y rho u₀ v) :
    IsDegenerate Y Q (.vertex v) := by
  by_contra hnondeg
  exact hweak (hasNondegenerateHammockCard_of_nondegenerateClosed
    hclosed heligible hsafe hstart hend hnondeg hdisj houtside)

#print axioms exists_nondegenerateHammockMaximalUpTo
#print axioms hasNondegenerateHammockCard_of_nondegenerateClosed
#print axioms isDegenerate_of_not_strong_of_nondegenerateClosed

end Erdos599.Blueprint
