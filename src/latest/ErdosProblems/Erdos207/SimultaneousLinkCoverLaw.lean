/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SimultaneousLinkReservoirSampling

/-!
# A C4 law for simultaneous crossing-link covers

This file isolates the exact probabilistic endpoint of the KSSS link stage.
Once a positive-probability event guarantees a valid simultaneous cover
inside the exposed global reservoir, classical finite choice selects one
cover on every good outcome.  Conditioning and pushing forward gives an
actual law supported on valid covers, and the preceding global encoding
supplies C4.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Structural output required from the complete simultaneous crossing-link
stage. -/
def IsSimultaneousLinkCover
    {O V : Type*} [DecidableEq V]
    (F : ForbiddenFamilyOn V) (available P : TripleSystemOn V)
    (K : O → BipartiteLink V) (M : TripleSystemOn V) : Prop :=
  M ⊆ available ∧ Disjoint P M ∧
    IsPackingOn (P ∪ M) ∧ AvoidsForbidden (P ∪ M) F ∧
    ∀ o, CoversBipartiteLink (K o) M

/-- The law-level simultaneous link-stage theorem.  The only input still
specific to robust matching is the pointwise assertion on the global good
event. -/
theorem exists_simultaneousLinkCoverLaw_of_good_reservoir
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (U : Finset V) (center : O ↪ V) (K : O → BipartiteLink V)
    (hcenter : ∀ o, (K o).center = center o)
    (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U)
    (hright : ∀ o, (K o).right ⊆ U)
    (F : ForbiddenFamilyOn V) (available P : TripleSystemOn V)
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1)
    (Good : (SimultaneousLinkPair O V K → Bool) → Prop)
    (hGood : 0 < (FiniteLaw.independentBits
      (fun _ : SimultaneousLinkPair O V K ↦ sigma)
      (fun _ ↦ hsigma)).probability Good)
    (hcover : ∀ ω, Good ω → ∃ M : TripleSystemOn V,
      M ⊆ simultaneousLinkReservoir U center K hcenter hout hleft hright ω ∧
      IsSimultaneousLinkCover F available P K M) :
    ∃ L : FiniteLaw (TripleSystemOn V),
      L.SupportedOn (IsSimultaneousLinkCover F available P K) ∧
      ∀ Q : TripleSystemOn V,
        L.probability (fun M ↦ Q ⊆ M) ≤
          sigma ^ Q.card /
            (FiniteLaw.independentBits
              (fun _ : SimultaneousLinkPair O V K ↦ sigma)
              (fun _ ↦ hsigma)).probability Good := by
  exact exists_conditioned_encodedSelectionLaw sigma hsigma
    (simultaneousLinkPairEmbedding U center K hcenter hout hleft hright)
      Good hGood (IsSimultaneousLinkCover F available P K) hcover

/-- Per-triangle-base form of the simultaneous cover law, convenient for
the strong-distribution powerset update. -/
theorem exists_simultaneousLinkCoverLaw_of_good_reservoir_pow
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (U : Finset V) (center : O ↪ V) (K : O → BipartiteLink V)
    (hcenter : ∀ o, (K o).center = center o)
    (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U)
    (hright : ∀ o, (K o).right ⊆ U)
    (F : ForbiddenFamilyOn V) (available P : TripleSystemOn V)
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1)
    (Good : (SimultaneousLinkPair O V K → Bool) → Prop)
    (hGood : 0 < (FiniteLaw.independentBits
      (fun _ : SimultaneousLinkPair O V K ↦ sigma)
      (fun _ ↦ hsigma)).probability Good)
    (hcover : ∀ ω, Good ω → ∃ M : TripleSystemOn V,
      M ⊆ simultaneousLinkReservoir U center K hcenter hout hleft hright ω ∧
      IsSimultaneousLinkCover F available P K M) :
    ∃ L : FiniteLaw (TripleSystemOn V),
      L.SupportedOn (IsSimultaneousLinkCover F available P K) ∧
      ∀ Q : TripleSystemOn V,
        L.probability (fun M ↦ Q ⊆ M) ≤
          (sigma /
            (FiniteLaw.independentBits
              (fun _ : SimultaneousLinkPair O V K ↦ sigma)
              (fun _ ↦ hsigma)).probability Good) ^ Q.card := by
  exact exists_conditioned_encodedSelectionLaw_pow sigma hsigma
    (simultaneousLinkPairEmbedding U center K hcenter hout hleft hright)
      Good hGood (IsSimultaneousLinkCover F available P K) hcover

/-- A failure-probability estimate strictly below one supplies the positive
success probability required by the conditioned law. -/
theorem exists_simultaneousLinkCoverLaw_of_failure_lt_one
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (U : Finset V) (center : O ↪ V) (K : O → BipartiteLink V)
    (hcenter : ∀ o, (K o).center = center o)
    (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U)
    (hright : ∀ o, (K o).right ⊆ U)
    (F : ForbiddenFamilyOn V) (available P : TripleSystemOn V)
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1)
    (Good : (SimultaneousLinkPair O V K → Bool) → Prop)
    (hbad : (FiniteLaw.independentBits
      (fun _ : SimultaneousLinkPair O V K ↦ sigma)
      (fun _ ↦ hsigma)).probability (fun ω ↦ ¬ Good ω) < 1)
    (hcover : ∀ ω, Good ω → ∃ M : TripleSystemOn V,
      M ⊆ simultaneousLinkReservoir U center K hcenter hout hleft hright ω ∧
      IsSimultaneousLinkCover F available P K M) :
    ∃ L : FiniteLaw (TripleSystemOn V),
      L.SupportedOn (IsSimultaneousLinkCover F available P K) ∧
      ∀ Q : TripleSystemOn V,
        L.probability (fun M ↦ Q ⊆ M) ≤
          sigma ^ Q.card /
            (FiniteLaw.independentBits
              (fun _ : SimultaneousLinkPair O V K ↦ sigma)
              (fun _ ↦ hsigma)).probability Good := by
  let R := FiniteLaw.independentBits
    (fun _ : SimultaneousLinkPair O V K ↦ sigma) (fun _ ↦ hsigma)
  have hGood : 0 < R.probability Good := by
    by_contra hnot
    have hzero : R.probability Good = 0 :=
      le_antisymm (not_lt.mp hnot) zero_le
    have hfailure : R.probability (fun ω ↦ ¬ Good ω) = 1 := by
      rw [R.probability_not Good, hzero]
      simp
    rw [hfailure] at hbad
    exact (lt_irrefl 1 hbad)
  exact exists_simultaneousLinkCoverLaw_of_good_reservoir
    U center K hcenter hout hleft hright F available P sigma hsigma
      Good hGood hcover

end

end Erdos207
