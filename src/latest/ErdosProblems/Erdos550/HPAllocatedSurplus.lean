import Mathlib
import ErdosProblems.Erdos550.HPGoodMatchingEdges

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Robust allocated surplus after deleting bad whole edges

The whole-edge split is performed once, before the stateful embedding.  A
particular seed image may then delete a small number of its allocated edges as
atypical.  This lemma shows that an allocation containing the source demand,
one reserve per allocated edge, and one bounded loss per deleted edge still
supplies the exact aggregate surplus required by the local matching selector.
-/

open Finset

namespace Erdos550

open Classical

lemma allocated_surplus_after_bad_deletion
    {κ : Type*} [DecidableEq κ]
    (K Good : Finset κ)
    (load supply : κ → ℝ)
    (demand reserve edgeCap bad : ℝ)
    (hGood : Good ⊆ K)
    (hload0 : ∀ k ∈ Good, 0 ≤ load k)
    (hsupply0 : ∀ k ∈ K, 0 ≤ supply k)
    (hsupplyCap : ∀ k ∈ K, supply k ≤ edgeCap)
    (hedgeCap0 : 0 ≤ edgeCap)
    (hreserve0 : 0 ≤ reserve)
    (hdeleted : ((K \ Good).card : ℝ) ≤ bad)
    (hload : (∑ k ∈ Good, load k) ≤ demand)
    (hallocated :
      demand + bad * edgeCap + (K.card : ℝ) * reserve ≤
        ∑ k ∈ K, supply k) :
    (∑ k ∈ Good, load k) + (Good.card : ℝ) * reserve ≤
      ∑ k ∈ Good, supply k := by
  have hsupply :=
    sum_allocated_good_lower K Good supply edgeCap bad hGood
      hsupply0 hsupplyCap hdeleted hedgeCap0
  have hcard : (Good.card : ℝ) ≤ (K.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hGood
  have hreserve :
      (Good.card : ℝ) * reserve ≤ (K.card : ℝ) * reserve :=
    mul_le_mul_of_nonneg_right hcard hreserve0
  linarith

/-- The concrete `Good` family used by the off--Turán embedding is nonempty
and has the exact stateful surplus once the anchor's bad-count is bounded.
This packages the injective whole-edge deletion argument with
`allocated_surplus_after_bad_deletion`. -/
lemma allocated_good_nonempty_and_surplus
    {V ι κ : Type*} [Fintype V] [DecidableEq V]
    [Fintype κ] [DecidableEq κ] [DecidableEq ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : ι → Finset V) (dcap : ι → ℝ) (ε : ℝ)
    (Tset : Finset ι) (K : Finset κ)
    (cL cR : κ → ι) (anchor : V)
    (hinj : Function.Injective (Sum.elim cL cR))
    (hleft : ∀ k, cL k ∈ Tset)
    (hright : ∀ k, cR k ∈ Tset)
    (load supply : κ → ℝ)
    (demand reserve edgeCap bad : ℝ)
    (hbadCard :
      badCount G C dcap ε Tset anchor < K.card)
    (hbadReal :
      (badCount G C dcap ε Tset anchor : ℝ) ≤ bad)
    (hload0 : ∀ k ∈
      hpAllocatedGoodMatchingEdges G C dcap ε K cL cR anchor,
        0 ≤ load k)
    (hsupply0 : ∀ k ∈ K, 0 ≤ supply k)
    (hsupplyCap : ∀ k ∈ K, supply k ≤ edgeCap)
    (hedgeCap0 : 0 ≤ edgeCap)
    (hreserve0 : 0 ≤ reserve)
    (hload :
      (∑ k ∈ hpAllocatedGoodMatchingEdges
          G C dcap ε K cL cR anchor, load k) ≤ demand)
    (hallocated :
      demand + bad * edgeCap + (K.card : ℝ) * reserve ≤
        ∑ k ∈ K, supply k) :
    let Good :=
      hpAllocatedGoodMatchingEdges G C dcap ε K cL cR anchor
    Good.Nonempty ∧
      (∑ k ∈ Good, load k) + (Good.card : ℝ) * reserve ≤
        ∑ k ∈ Good, supply k := by
  let Good :=
    hpAllocatedGoodMatchingEdges G C dcap ε K cL cR anchor
  have hGood : Good ⊆ K :=
    hpAllocatedGoodMatchingEdges_subset
      G C dcap ε K cL cR anchor
  have hnonempty : Good.Nonempty :=
    hpAllocatedGoodMatchingEdges_nonempty
      G C dcap ε Tset K cL cR anchor hinj hleft hright hbadCard
  have hdeletedNat :=
    allocated_bad_matching_edges_card_le_badCount
      G C dcap ε Tset K cL cR anchor hinj hleft hright
  have hdeleted :
      ((K \ Good).card : ℝ) ≤ bad := by
    have hcast :
        ((K \ Good).card : ℝ) ≤
          (badCount G C dcap ε Tset anchor : ℝ) := by
      exact_mod_cast hdeletedNat
    exact hcast.trans hbadReal
  refine ⟨hnonempty, ?_⟩
  exact allocated_surplus_after_bad_deletion
    K Good load supply demand reserve edgeCap bad hGood
    hload0 hsupply0 hsupplyCap hedgeCap0 hreserve0 hdeleted
    hload hallocated

/-- Static version used before the embedding state exists: the allocated
family contains the full route demand, a deletion charge, and one reserve per
allocated edge.  After deleting the anchor's bad edges, the full route demand
and one reserve per surviving edge remain. -/
lemma allocated_good_nonempty_and_static_surplus
    {V ι κ : Type*} [Fintype V] [DecidableEq V]
    [Fintype κ] [DecidableEq κ] [DecidableEq ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : ι → Finset V) (dcap : ι → ℝ) (ε : ℝ)
    (Tset : Finset ι) (K : Finset κ)
    (cL cR : κ → ι) (anchor : V)
    (hinj : Function.Injective (Sum.elim cL cR))
    (hleft : ∀ k, cL k ∈ Tset)
    (hright : ∀ k, cR k ∈ Tset)
    (supply : κ → ℝ)
    (demand reserve edgeCap bad : ℝ)
    (hbadCard :
      badCount G C dcap ε Tset anchor < K.card)
    (hbadReal :
      (badCount G C dcap ε Tset anchor : ℝ) ≤ bad)
    (hsupply0 : ∀ k ∈ K, 0 ≤ supply k)
    (hsupplyCap : ∀ k ∈ K, supply k ≤ edgeCap)
    (hedgeCap0 : 0 ≤ edgeCap)
    (hreserve0 : 0 ≤ reserve)
    (hallocated :
      demand + bad * edgeCap + (K.card : ℝ) * reserve ≤
        ∑ k ∈ K, supply k) :
    let Good :=
      hpAllocatedGoodMatchingEdges G C dcap ε K cL cR anchor
    Good.Nonempty ∧
      demand + (Good.card : ℝ) * reserve ≤
        ∑ k ∈ Good, supply k := by
  let Good :=
    hpAllocatedGoodMatchingEdges G C dcap ε K cL cR anchor
  have hGood : Good ⊆ K :=
    hpAllocatedGoodMatchingEdges_subset
      G C dcap ε K cL cR anchor
  have hnonempty : Good.Nonempty :=
    hpAllocatedGoodMatchingEdges_nonempty
      G C dcap ε Tset K cL cR anchor hinj hleft hright hbadCard
  have hdeletedNat :=
    allocated_bad_matching_edges_card_le_badCount
      G C dcap ε Tset K cL cR anchor hinj hleft hright
  have hdeleted :
      ((K \ Good).card : ℝ) ≤ bad := by
    have hcast :
        ((K \ Good).card : ℝ) ≤
          (badCount G C dcap ε Tset anchor : ℝ) := by
      exact_mod_cast hdeletedNat
    exact hcast.trans hbadReal
  have hsupply :=
    sum_allocated_good_lower K Good supply edgeCap bad hGood
      hsupply0 hsupplyCap hdeleted hedgeCap0
  have hcard : (Good.card : ℝ) ≤ (K.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hGood
  have hreserve :
      (Good.card : ℝ) * reserve ≤ (K.card : ℝ) * reserve :=
    mul_le_mul_of_nonneg_right hcard hreserve0
  refine ⟨hnonempty, ?_⟩
  linarith

end Erdos550
