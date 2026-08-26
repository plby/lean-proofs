import Mathlib
import ErdosProblems.Erdos550.SkeletonLowBad
import ErdosProblems.Erdos550.HPTrimmedThreshold

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Matching edges good for a low-bad head vertex

A vertex in a low-bad head core may fail the usual degree estimate toward a
small number of matching endpoints.  We delete every matching edge containing
one such endpoint.  Since all matching endpoints are distinct, charging each
deleted edge to one bad endpoint is injective; hence the number of deleted
whole edges is at most the vertex's `badCount`.
-/

open Finset SimpleGraph

namespace Erdos550

open Classical

noncomputable def hpEndpointBad
    {V ι : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : ι → Finset V) (dcap : ι → ℝ) (ε : ℝ)
    (anchor : V) (i : ι) : Prop :=
  (((C i).filter fun x => G.Adj anchor x).card : ℝ) <
    (dcap i - ε) * ((C i).card : ℝ)

noncomputable def hpGoodMatchingEdges
    {V ι κ : Type*} [Fintype V] [DecidableEq V]
    [Fintype κ] [DecidableEq κ]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : ι → Finset V) (dcap : ι → ℝ) (ε : ℝ)
    (cL cR : κ → ι) (anchor : V) : Finset κ :=
  Finset.univ.filter fun k =>
    ¬hpEndpointBad G C dcap ε anchor (cL k) ∧
      ¬hpEndpointBad G C dcap ε anchor (cR k)

noncomputable def hpAllocatedGoodMatchingEdges
    {V ι κ : Type*} [Fintype V] [DecidableEq V]
    [Fintype κ] [DecidableEq κ]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : ι → Finset V) (dcap : ι → ℝ) (ε : ℝ)
    (K : Finset κ) (cL cR : κ → ι) (anchor : V) : Finset κ :=
  K ∩ hpGoodMatchingEdges G C dcap ε cL cR anchor

lemma hpAllocatedGoodMatchingEdges_subset
    {V ι κ : Type*} [Fintype V] [DecidableEq V]
    [Fintype κ] [DecidableEq κ]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : ι → Finset V) (dcap : ι → ℝ) (ε : ℝ)
    (K : Finset κ) (cL cR : κ → ι) (anchor : V) :
    hpAllocatedGoodMatchingEdges G C dcap ε K cL cR anchor ⊆ K :=
  Finset.inter_subset_left

lemma mem_hpAllocatedGoodMatchingEdges
    {V ι κ : Type*} [Fintype V] [DecidableEq V]
    [Fintype κ] [DecidableEq κ]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : ι → Finset V) (dcap : ι → ℝ) (ε : ℝ)
    (K : Finset κ) (cL cR : κ → ι) (anchor : V) {k : κ}
    (hk : k ∈ hpAllocatedGoodMatchingEdges
      G C dcap ε K cL cR anchor) :
    k ∈ K ∧
      ¬hpEndpointBad G C dcap ε anchor (cL k) ∧
      ¬hpEndpointBad G C dcap ε anchor (cR k) := by
  have hk' := Finset.mem_inter.mp hk
  have hgood := Finset.mem_filter.mp hk'.2
  exact ⟨hk'.1, hgood.2.1, hgood.2.2⟩

lemma hpAllocatedGood_left_degree
    {V ι κ : Type*} [Fintype V] [DecidableEq V]
    [Fintype κ] [DecidableEq κ]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : ι → Finset V) (dcap : ι → ℝ) (ε : ℝ)
    (K : Finset κ) (cL cR : κ → ι) (anchor : V) {k : κ}
    (hk : k ∈ hpAllocatedGoodMatchingEdges
      G C dcap ε K cL cR anchor) :
    (dcap (cL k) - ε) * ((C (cL k)).card : ℝ) ≤
      (((C (cL k)).filter fun v => G.Adj anchor v).card : ℝ) := by
  exact le_of_not_gt
    (mem_hpAllocatedGoodMatchingEdges
      G C dcap ε K cL cR anchor hk).2.1

lemma hpAllocatedGood_right_degree
    {V ι κ : Type*} [Fintype V] [DecidableEq V]
    [Fintype κ] [DecidableEq κ]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : ι → Finset V) (dcap : ι → ℝ) (ε : ℝ)
    (K : Finset κ) (cL cR : κ → ι) (anchor : V) {k : κ}
    (hk : k ∈ hpAllocatedGoodMatchingEdges
      G C dcap ε K cL cR anchor) :
    (dcap (cR k) - ε) * ((C (cR k)).card : ℝ) ≤
      (((C (cR k)).filter fun v => G.Adj anchor v).card : ℝ) := by
  exact le_of_not_gt
    (mem_hpAllocatedGoodMatchingEdges
      G C dcap ε K cL cR anchor hk).2.2

/-- A good matching endpoint supplies the twice-trimmed packedness threshold
used by the stateful embedding. -/
lemma hpAllocatedGood_left_trimmed_degree
    {V ι κ : Type*} [Fintype V] [DecidableEq V]
    [Fintype κ] [DecidableEq κ]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : ι → Finset V) (dcap : ι → ℝ) (ε : ℝ)
    (K : Finset κ) (cL cR : κ → ι) (anchor : V) {k : κ}
    (hε0 : 0 ≤ ε)
    (hk : k ∈ hpAllocatedGoodMatchingEdges
      G C dcap ε K cL cR anchor) :
    hpTrimmedThreshold
        (dcap (cL k) * ((C (cL k)).card : ℝ))
        ε ((C (cL k)).card : ℝ) ≤
      (((C (cL k)).filter fun v => G.Adj anchor v).card : ℝ) := by
  apply hpTrimmedThreshold_typical_degree
  · exact hε0
  · positivity
  · positivity
  · convert! hpAllocatedGood_left_degree
      G C dcap ε K cL cR anchor hk using 1 <;> ring

lemma hpAllocatedGood_right_trimmed_degree
    {V ι κ : Type*} [Fintype V] [DecidableEq V]
    [Fintype κ] [DecidableEq κ]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : ι → Finset V) (dcap : ι → ℝ) (ε : ℝ)
    (K : Finset κ) (cL cR : κ → ι) (anchor : V) {k : κ}
    (hε0 : 0 ≤ ε)
    (hk : k ∈ hpAllocatedGoodMatchingEdges
      G C dcap ε K cL cR anchor) :
    hpTrimmedThreshold
        (dcap (cR k) * ((C (cR k)).card : ℝ))
        ε ((C (cR k)).card : ℝ) ≤
      (((C (cR k)).filter fun v => G.Adj anchor v).card : ℝ) := by
  apply hpTrimmedThreshold_typical_degree
  · exact hε0
  · positivity
  · positivity
  · convert! hpAllocatedGood_right_degree
      G C dcap ε K cL cR anchor hk using 1 <;> ring

noncomputable def hpChosenBadEndpoint
    {V ι κ : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : ι → Finset V) (dcap : ι → ℝ) (ε : ℝ)
    (cL cR : κ → ι) (anchor : V) (k : κ) : ι :=
  if hpEndpointBad G C dcap ε anchor (cL k) then cL k else cR k

lemma hpChosenBadEndpoint_injective
    {V ι κ : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : ι → Finset V) (dcap : ι → ℝ) (ε : ℝ)
    (cL cR : κ → ι) (anchor : V)
    (hinj : Function.Injective (Sum.elim cL cR)) :
    Function.Injective
      (hpChosenBadEndpoint G C dcap ε cL cR anchor) := by
  intro k j hkj
  by_cases hk : hpEndpointBad G C dcap ε anchor (cL k)
  · by_cases hj : hpEndpointBad G C dcap ε anchor (cL j)
    · have hleft : cL k = cL j := by
        simpa [hpChosenBadEndpoint, hk, hj] using! hkj
      exact Sum.inl.inj (hinj hleft)
    · have hcross : cL k = cR j := by
        simpa [hpChosenBadEndpoint, hk, hj] using! hkj
      have himpossible :
          (Sum.inl k : Sum κ κ) = Sum.inr j :=
        hinj hcross
      cases himpossible
  · by_cases hj : hpEndpointBad G C dcap ε anchor (cL j)
    · have hcross : cR k = cL j := by
        simpa [hpChosenBadEndpoint, hk, hj] using! hkj
      have himpossible :
          (Sum.inr k : Sum κ κ) = Sum.inl j :=
        hinj hcross
      cases himpossible
    · have hright : cR k = cR j := by
        simpa [hpChosenBadEndpoint, hk, hj] using! hkj
      exact Sum.inr.inj (hinj hright)

lemma hpChosenBadEndpoint_mem_bad
    {V ι κ : Type*} [Fintype V] [DecidableEq V]
    [Fintype κ] [DecidableEq κ]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : ι → Finset V) (dcap : ι → ℝ) (ε : ℝ)
    (Tset : Finset ι) (cL cR : κ → ι) (anchor : V)
    (hleft : ∀ k, cL k ∈ Tset)
    (hright : ∀ k, cR k ∈ Tset)
    {k : κ}
    (hk : k ∈
      Finset.univ \ hpGoodMatchingEdges G C dcap ε cL cR anchor) :
    hpChosenBadEndpoint G C dcap ε cL cR anchor k ∈
      Tset.filter fun i => hpEndpointBad G C dcap ε anchor i := by
  have hkNot :=
    (Finset.mem_sdiff.mp hk).2
  have hbad :
      hpEndpointBad G C dcap ε anchor (cL k) ∨
        hpEndpointBad G C dcap ε anchor (cR k) := by
    by_cases hL : hpEndpointBad G C dcap ε anchor (cL k)
    · exact Or.inl hL
    · apply Or.inr
      by_contra hR
      apply hkNot
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hL, hR⟩
  by_cases hL : hpEndpointBad G C dcap ε anchor (cL k)
  · rw [hpChosenBadEndpoint, if_pos hL]
    exact Finset.mem_filter.mpr ⟨hleft k, hL⟩
  · have hR := hbad.resolve_left hL
    rw [hpChosenBadEndpoint, if_neg hL]
    exact Finset.mem_filter.mpr ⟨hright k, hR⟩

/-- Whole bad matching edges inject into the endpoint set counted by
`badCount`. -/
lemma bad_matching_edges_card_le_badCount
    {V ι κ : Type*} [Fintype V] [DecidableEq V]
    [Fintype κ] [DecidableEq κ] [DecidableEq ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : ι → Finset V) (dcap : ι → ℝ) (ε : ℝ)
    (Tset : Finset ι) (cL cR : κ → ι) (anchor : V)
    (hinj : Function.Injective (Sum.elim cL cR))
    (hleft : ∀ k, cL k ∈ Tset)
    (hright : ∀ k, cR k ∈ Tset) :
    (Finset.univ \
        hpGoodMatchingEdges G C dcap ε cL cR anchor).card ≤
      badCount G C dcap ε Tset anchor := by
  let Bad :=
    Finset.univ \ hpGoodMatchingEdges G C dcap ε cL cR anchor
  let choose :=
    hpChosenBadEndpoint G C dcap ε cL cR anchor
  have hsub :
      Bad.image choose ⊆
        Tset.filter fun i => hpEndpointBad G C dcap ε anchor i := by
    intro i hi
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
    exact hpChosenBadEndpoint_mem_bad G C dcap ε Tset cL cR anchor
      hleft hright hk
  have hcardImage : (Bad.image choose).card = Bad.card :=
    Finset.card_image_of_injective Bad
      (hpChosenBadEndpoint_injective G C dcap ε cL cR anchor hinj)
  have hbadEq :
      (Tset.filter fun i => hpEndpointBad G C dcap ε anchor i).card =
        badCount G C dcap ε Tset anchor := by
    rfl
  rw [← hcardImage, ← hbadEq]
  exact Finset.card_le_card hsub

lemma hpGoodMatchingEdges_nonempty
    {V ι κ : Type*} [Fintype V] [DecidableEq V]
    [Fintype κ] [DecidableEq κ] [DecidableEq ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : ι → Finset V) (dcap : ι → ℝ) (ε : ℝ)
    (Tset : Finset ι) (cL cR : κ → ι) (anchor : V)
    (hinj : Function.Injective (Sum.elim cL cR))
    (hleft : ∀ k, cL k ∈ Tset)
    (hright : ∀ k, cR k ∈ Tset)
    (hbad :
      badCount G C dcap ε Tset anchor < Fintype.card κ) :
    (hpGoodMatchingEdges G C dcap ε cL cR anchor).Nonempty := by
  have hdeleted :=
    bad_matching_edges_card_le_badCount
      G C dcap ε Tset cL cR anchor hinj hleft hright
  have hdelLt :
      (Finset.univ \
        hpGoodMatchingEdges G C dcap ε cL cR anchor).card <
          Fintype.card κ :=
    hdeleted.trans_lt hbad
  apply Finset.nonempty_iff_ne_empty.mpr
  intro hempty
  have hbadAll :
      Finset.univ \
          hpGoodMatchingEdges G C dcap ε cL cR anchor =
        (Finset.univ : Finset κ) := by
    rw [hempty]
    simp
  rw [hbadAll, Finset.card_univ] at hdelLt
  exact (Nat.lt_irrefl _ hdelLt)

lemma allocated_bad_matching_edges_card_le_badCount
    {V ι κ : Type*} [Fintype V] [DecidableEq V]
    [Fintype κ] [DecidableEq κ] [DecidableEq ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : ι → Finset V) (dcap : ι → ℝ) (ε : ℝ)
    (Tset : Finset ι) (K : Finset κ)
    (cL cR : κ → ι) (anchor : V)
    (hinj : Function.Injective (Sum.elim cL cR))
    (hleft : ∀ k, cL k ∈ Tset)
    (hright : ∀ k, cR k ∈ Tset) :
    (K \ hpAllocatedGoodMatchingEdges
        G C dcap ε K cL cR anchor).card ≤
      badCount G C dcap ε Tset anchor := by
  have hsub :
      K \ hpAllocatedGoodMatchingEdges G C dcap ε K cL cR anchor ⊆
        Finset.univ \
          hpGoodMatchingEdges G C dcap ε cL cR anchor := by
    intro k hk
    have hk' := Finset.mem_sdiff.mp hk
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hgood
    exact hk'.2 (Finset.mem_inter.mpr ⟨hk'.1, hgood⟩)
  exact (Finset.card_le_card hsub).trans
    (bad_matching_edges_card_le_badCount
      G C dcap ε Tset cL cR anchor hinj hleft hright)

lemma hpAllocatedGoodMatchingEdges_nonempty
    {V ι κ : Type*} [Fintype V] [DecidableEq V]
    [Fintype κ] [DecidableEq κ] [DecidableEq ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : ι → Finset V) (dcap : ι → ℝ) (ε : ℝ)
    (Tset : Finset ι) (K : Finset κ)
    (cL cR : κ → ι) (anchor : V)
    (hinj : Function.Injective (Sum.elim cL cR))
    (hleft : ∀ k, cL k ∈ Tset)
    (hright : ∀ k, cR k ∈ Tset)
    (hbad : badCount G C dcap ε Tset anchor < K.card) :
    (hpAllocatedGoodMatchingEdges
      G C dcap ε K cL cR anchor).Nonempty := by
  have hdeleted :=
    allocated_bad_matching_edges_card_le_badCount
      G C dcap ε Tset K cL cR anchor hinj hleft hright
  have hdelLt :
      (K \ hpAllocatedGoodMatchingEdges
          G C dcap ε K cL cR anchor).card < K.card :=
    hdeleted.trans_lt hbad
  apply Finset.nonempty_iff_ne_empty.mpr
  intro hempty
  have hbadAll :
      K \ hpAllocatedGoodMatchingEdges G C dcap ε K cL cR anchor = K := by
    rw [hempty]
    simp
  rw [hbadAll] at hdelLt
  exact Nat.lt_irrefl _ hdelLt

/-- Deleting at most `bad` whole edges from an allocated family loses at most
`bad * cap` of any nonnegative edge weight bounded by `cap`. -/
lemma sum_allocated_good_lower
    {κ : Type*} [DecidableEq κ]
    (K Good : Finset κ) (weight : κ → ℝ)
    (cap bad : ℝ)
    (hGood : Good ⊆ K)
    (hweight0 : ∀ k ∈ K, 0 ≤ weight k)
    (hweightCap : ∀ k ∈ K, weight k ≤ cap)
    (hdeleted : ((K \ Good).card : ℝ) ≤ bad)
    (hcap0 : 0 ≤ cap) :
    (∑ k ∈ K, weight k) - bad * cap ≤
      ∑ k ∈ Good, weight k := by
  have hout :
      ∑ k ∈ K \ Good, weight k ≤ bad * cap := by
    calc
      _ ≤ ∑ _k ∈ K \ Good, cap := by
        apply Finset.sum_le_sum
        intro k hk
        exact hweightCap k (Finset.mem_sdiff.mp hk).1
      _ = ((K \ Good).card : ℝ) * cap := by simp
      _ ≤ bad * cap :=
        mul_le_mul_of_nonneg_right hdeleted hcap0
  rw [← Finset.sum_sdiff hGood]
  linarith

end Erdos550
