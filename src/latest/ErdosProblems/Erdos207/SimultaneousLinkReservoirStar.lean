/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.JointInclusionCardTail
import ErdosProblems.Erdos207.MasterLinkStarConditioning
import ErdosProblems.Erdos207.SimultaneousLinkReservoirSampling

/-!
# Vertex-star caps for the simultaneous link reservoir

The global link reservoir is an injective image of independent Bernoulli
coordinates.  Its established C4 estimate therefore gives a binomial
union bound for every vertex star.  These caps are imposed on the *raw*
reservoir, before the sequential robust-matching sweep; consequently every
intermediate selected link family inherits them.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- Failure of a vertex-star cap in the raw simultaneous link reservoir is
bounded by the sum of the corresponding binomial tails. -/
theorem independentBits_probability_not_simultaneousLinkReservoir_starCaps_le
    {O V : Type*} [Fintype O] [DecidableEq O]
    [Fintype V] [DecidableEq V]
    (U : Finset V) (center : O ↪ V) (K : O → BipartiteLink V)
    (hcenter : ∀ o, (K o).center = center o)
    (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U)
    (hright : ∀ o, (K o).right ⊆ U)
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1) (caps : V → ℕ) :
    (FiniteLaw.independentBits
      (fun _ : SimultaneousLinkPair O V K ↦ sigma)
      (fun _ ↦ hsigma)).probability (fun omega ↦
        ¬ LinkStarCapsGood caps
          (simultaneousLinkReservoir U center K hcenter hout hleft hright
            omega)) ≤
      ∑ v : V, ((ambientTriplesThrough v).powersetCard (caps v)).card *
        sigma ^ caps v := by
  let L := FiniteLaw.independentBits
    (fun _ : SimultaneousLinkPair O V K ↦ sigma) (fun _ ↦ hsigma)
  let selected := fun omega ↦
    simultaneousLinkReservoir U center K hcenter hout hleft hright omega
  calc
    L.probability (fun omega ↦ ¬ LinkStarCapsGood caps (selected omega)) ≤
        L.probability (fun omega ↦ Exists fun v : V ↦
          caps v ≤ (ambientTriplesThrough v ∩ selected omega).card) := by
      apply L.probability_mono
      intro omega hbad
      unfold LinkStarCapsGood at hbad
      push Not at hbad
      exact hbad
    _ ≤ ∑ v : V, L.probability (fun omega ↦
        caps v ≤ (ambientTriplesThrough v ∩ selected omega).card) := by
      simpa using L.probability_exists_le (univ : Finset V)
        (fun v omega ↦
          caps v ≤ (ambientTriplesThrough v ∩ selected omega).card)
    _ ≤ ∑ v : V,
        ((ambientTriplesThrough v).powersetCard (caps v)).card *
          sigma ^ caps v := by
      apply sum_le_sum
      intro v _hv
      exact L.probability_card_inter_selected_ge_le_of_card_jointInclusion
        selected (ambientTriplesThrough v) sigma (caps v) (fun Q ↦ by
          simpa only [L, selected] using
            simultaneousLinkReservoir_probability_subset_le U center K
              hcenter hout hleft hright sigma hsigma Q)

/-- If an intermediate packing is contained in the fixed preliminary
family, a reserve family, and a star-capped raw link reservoir, then its
degree beyond the preliminary family is bounded by twice the reserve and
reservoir star budgets. -/
theorem coveredGraph_sdiff_historical_degree_le_of_reservoir_starCap
    {V : Type*} [Fintype V] [DecidableEq V]
    {Pbase R reservoir P' : TripleSystemOn V}
    (hPsub : P' ⊆ Pbase ∪ (R ∪ reservoir))
    (hPpacking : IsPackingOn P') (caps : V → ℕ)
    (hcap : LinkStarCapsGood caps reservoir) (v : V) :
    (coveredGraph (P' \ Pbase)).degree v ≤
      2 * ((triplesThrough R v).card + caps v) := by
  have hnewPacking : IsPackingOn (P' \ Pbase) :=
    hPpacking.mono sdiff_subset
  have hthroughSub : triplesThrough (P' \ Pbase) v ⊆
      triplesThrough (R ∪ reservoir) v := by
    intro T hT
    rw [triplesThrough, mem_filter] at hT ⊢
    refine ⟨?_, hT.2⟩
    have hTin := hPsub (mem_sdiff.mp hT.1).1
    rcases mem_union.mp hTin with hTbase | hTrest
    · exact ((mem_sdiff.mp hT.1).2 hTbase).elim
    · exact hTrest
  have hthroughUnion : triplesThrough (R ∪ reservoir) v =
      triplesThrough R v ∪ triplesThrough reservoir v := by
    ext T
    simp only [triplesThrough, mem_filter, mem_union]
    tauto
  calc
    (coveredGraph (P' \ Pbase)).degree v =
        2 * (triplesThrough (P' \ Pbase) v).card :=
      hnewPacking.coveredGraph_degree_eq_two_mul_triplesThrough v
    _ ≤ 2 * (triplesThrough (R ∪ reservoir) v).card :=
      Nat.mul_le_mul_left 2 (card_le_card hthroughSub)
    _ ≤ 2 * ((triplesThrough R v).card +
        (triplesThrough reservoir v).card) := by
      rw [hthroughUnion]
      exact Nat.mul_le_mul_left 2 (card_union_le _ _)
    _ ≤ 2 * ((triplesThrough R v).card + caps v) := by
      apply Nat.mul_le_mul_left
      exact Nat.add_le_add_left (Nat.le_of_lt (by
        simpa only [ambientTriplesThrough_inter] using hcap v)) _

end

end Erdos207
