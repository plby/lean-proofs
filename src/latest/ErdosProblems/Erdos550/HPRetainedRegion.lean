import Mathlib
import ErdosProblems.Erdos550.HPLoadAccounting

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Retained-contact regions over whole matching-edge families

For each head colour, the off--Turán allocation assigns complete matching
edges.  The global retained region is the union of the two retained endpoint
sets over those edges.  Membership therefore carries both matching support and
the fixed degree back into the corresponding head core.
-/

open Finset SimpleGraph

namespace Erdos550

open Classical

noncomputable def hpRetainedRegion
    {κ V : Type*} [DecidableEq κ] [DecidableEq V]
    (K : Finset κ) (retainedL retainedR : κ → Finset V) : Finset V :=
  K.biUnion fun k => retainedL k ∪ retainedR k

lemma retainedL_subset_hpRetainedRegion
    {κ V : Type*} [DecidableEq κ] [DecidableEq V]
    (K : Finset κ) (retainedL retainedR : κ → Finset V)
    {k : κ} (hk : k ∈ K) :
    retainedL k ⊆ hpRetainedRegion K retainedL retainedR := by
  intro v hv
  exact Finset.mem_biUnion.mpr
    ⟨k, hk, Finset.mem_union_left _ hv⟩

lemma retainedR_subset_hpRetainedRegion
    {κ V : Type*} [DecidableEq κ] [DecidableEq V]
    (K : Finset κ) (retainedL retainedR : κ → Finset V)
    {k : κ} (hk : k ∈ K) :
    retainedR k ⊆ hpRetainedRegion K retainedL retainedR := by
  intro v hv
  exact Finset.mem_biUnion.mpr
    ⟨k, hk, Finset.mem_union_right _ hv⟩

lemma hpRetainedRegion_subset_matchingRegion
    {κ V : Type*} [DecidableEq κ] [DecidableEq V]
    (K : Finset κ)
    (left right retainedL retainedR : κ → Finset V)
    (hL : ∀ k ∈ K, retainedL k ⊆ left k)
    (hR : ∀ k ∈ K, retainedR k ⊆ right k) :
    hpRetainedRegion K retainedL retainedR ⊆
      hpMatchingRegion K left right := by
  intro v hv
  obtain ⟨k, hk, hvSide⟩ := Finset.mem_biUnion.mp hv
  rcases Finset.mem_union.mp hvSide with hvL | hvR
  · exact Finset.mem_biUnion.mpr
      ⟨k, hk, Finset.mem_union_left _ (hL k hk hvL)⟩
  · exact Finset.mem_biUnion.mpr
      ⟨k, hk, Finset.mem_union_right _ (hR k hk hvR)⟩

lemma hpRetainedRegion_degree
    {κ V : Type*} [DecidableEq κ] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Finset κ) (retainedL retainedR : κ → Finset V)
    (headCore : Finset V) (need : ℝ)
    (hL : ∀ k ∈ K, ∀ u ∈ retainedL k,
      need <
        ((headCore.filter fun v => G.Adj v u).card : ℝ))
    (hR : ∀ k ∈ K, ∀ u ∈ retainedR k,
      need <
        ((headCore.filter fun v => G.Adj v u).card : ℝ)) :
    ∀ u ∈ hpRetainedRegion K retainedL retainedR,
      need <
        ((headCore.filter fun v => G.Adj v u).card : ℝ) := by
  intro u hu
  obtain ⟨k, hk, huSide⟩ := Finset.mem_biUnion.mp hu
  rcases Finset.mem_union.mp huSide with huL | huR
  · exact hL k hk u huL
  · exact hR k hk u huR

end Erdos550
