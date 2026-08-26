import Mathlib
import ErdosProblems.Erdos550.HPTrimmedThreshold
import ErdosProblems.Erdos550.OffTuranMatchingSupply
import ErdosProblems.Erdos550.RegularClusterCardinality

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Matching-endpoint cardinality and trimmed supply

Matching endpoints are distinct parts of a partition, so their total order is
at most the host order.  Consequently replacing raw head weights by the two
endpoint-wise trimmed thresholds costs at most `2 ε N` on either allocated
edge family.
-/

open Finset SimpleGraph Finpartition

namespace Erdos550

open Classical

lemma partition_subfamily_card_sum_le_univ
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Finpartition (Finset.univ : Finset V))
    (S : Finset {C // C ∈ P.parts}) :
    ∑ i ∈ S, i.1.card ≤ Fintype.card V := by
  have hdisj :
      ∀ i j : {C // C ∈ P.parts}, i ≠ j →
        Disjoint i.1 j.1 := by
    intro i j hij
    exact P.disjoint i.2 j.2 (fun h => hij (Subtype.ext h))
  have hcard :=
    card_biUnion_clusters
      (fun i : {C // C ∈ P.parts} => i.1) hdisj S
  have hle :
      (S.biUnion fun i : {C // C ∈ P.parts} => i.1).card ≤
        Fintype.card V := by
    change
      (S.biUnion fun i : {C // C ∈ P.parts} => i.1).card ≤
        (Finset.univ : Finset V).card
    exact Finset.card_le_univ _
  rw [hcard] at hle
  exact hle

lemma matching_endpoint_card_sum_le_univ
    {V κ : Type*} [Fintype V] [DecidableEq V]
    [Fintype κ] [DecidableEq κ]
    (P : Finpartition (Finset.univ : Finset V))
    (cL cR : κ → {C // C ∈ P.parts})
    (hinj : Function.Injective (Sum.elim cL cR))
    (K : Finset κ) :
    (∑ k ∈ K,
      (((cL k).1.card : ℝ) + ((cR k).1.card : ℝ))) ≤
        Fintype.card V := by
  let S :=
    K.image cL ∪ K.image cR
  have hL : Function.Injective cL := by
    intro k j h
    exact Sum.inl.inj (hinj h)
  have hR : Function.Injective cR := by
    intro k j h
    exact Sum.inr.inj (hinj h)
  have hdisj : Disjoint (K.image cL) (K.image cR) := by
    rw [Finset.disjoint_left]
    intro i hiL hiR
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hiL
    obtain ⟨j, hj, hcross⟩ := Finset.mem_image.mp hiR
    have himpossible : (Sum.inl k : Sum κ κ) = Sum.inr j :=
      hinj hcross.symm
    cases himpossible
  have hsum :
      (∑ i ∈ S, (i.1.card : ℝ)) =
        ∑ k ∈ K,
          (((cL k).1.card : ℝ) + ((cR k).1.card : ℝ)) := by
    dsimp [S]
    rw [Finset.sum_union hdisj]
    rw [Finset.sum_image (fun k _ j _ h => hL h)]
    rw [Finset.sum_image (fun k _ j _ h => hR h)]
    simp only [Finset.sum_add_distrib]
  rw [← hsum]
  exact_mod_cast partition_subfamily_card_sum_le_univ P S

/-- Endpoint-wise trimming loses at most `2εN` on any allocated family. -/
lemma allocated_matching_trimmed_supply
    {V ι κ : Type*} [Fintype V] [DecidableEq V]
    [Fintype κ] [DecidableEq κ]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (C : ι → Finset V) (head : ι)
    (cL cR : κ → ι) (K : Finset κ)
    (ε N need : ℝ) (hε0 : 0 ≤ ε)
    (hsize :
      (∑ k ∈ K,
        (((C (cL k)).card : ℝ) + ((C (cR k)).card : ℝ))) ≤ N)
    (hraw :
      need + 2 * ε * N ≤
        ∑ k ∈ K, hpHeadMatchingWeight G R C head cL cR k) :
    need ≤
      ∑ k ∈ K,
        (hpTrimmedThreshold
            (hpHeadEndpointWeight G R C head (cL k))
            ε ((C (cL k)).card : ℝ) +
          hpTrimmedThreshold
            (hpHeadEndpointWeight G R C head (cR k))
            ε ((C (cR k)).card : ℝ)) := by
  have htrim :
      (∑ k ∈ K, hpHeadMatchingWeight G R C head cL cR k) -
          2 * ε *
            (∑ k ∈ K,
              (((C (cL k)).card : ℝ) +
                ((C (cR k)).card : ℝ))) ≤
        ∑ k ∈ K,
          (hpTrimmedThreshold
              (hpHeadEndpointWeight G R C head (cL k))
              ε ((C (cL k)).card : ℝ) +
            hpTrimmedThreshold
              (hpHeadEndpointWeight G R C head (cR k))
              ε ((C (cR k)).card : ℝ)) := by
    change
      Finset.sum K
          (fun k => hpHeadMatchingWeight G R C head cL cR k) -
            2 * ε *
              Finset.sum K (fun k =>
                ((C (cL k)).card : ℝ) + ((C (cR k)).card : ℝ)) ≤
        Finset.sum K (fun k =>
          hpTrimmedThreshold
              (hpHeadEndpointWeight G R C head (cL k))
              ε ((C (cL k)).card : ℝ) +
            hpTrimmedThreshold
              (hpHeadEndpointWeight G R C head (cR k))
              ε ((C (cR k)).card : ℝ))
    calc
      _ = Finset.sum K (fun k =>
          hpHeadMatchingWeight G R C head cL cR k -
            2 * ε *
              (((C (cL k)).card : ℝ) + ((C (cR k)).card : ℝ))) := by
            rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = Finset.sum K (fun k =>
          ((hpHeadEndpointWeight G R C head (cL k) -
              2 * ε * ((C (cL k)).card : ℝ)) +
            (hpHeadEndpointWeight G R C head (cR k) -
              2 * ε * ((C (cR k)).card : ℝ)))) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [hpHeadMatchingWeight]
            ring
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k hk
        exact add_le_add
          (hpTrimmedThreshold_lower
            (hpHeadEndpointWeight G R C head (cL k))
            ε ((C (cL k)).card : ℝ))
          (hpTrimmedThreshold_lower
            (hpHeadEndpointWeight G R C head (cR k))
            ε ((C (cR k)).card : ℝ))
  have hloss :
      2 * ε *
          (∑ k ∈ K,
            (((C (cL k)).card : ℝ) +
              ((C (cR k)).card : ℝ))) ≤
        2 * ε * N := by
    exact mul_le_mul_of_nonneg_left hsize (mul_nonneg (by norm_num) hε0)
  linarith

end Erdos550
