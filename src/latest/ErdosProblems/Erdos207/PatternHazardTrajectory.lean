/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PatternExcludedOverlaps
import ErdosProblems.Erdos207.RestrictedUnionVariableTargets

/-! # An explicit trajectory error for one proper extension vertex's hazard -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem patternExtensionKillers_card_trajectory_error
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q : ℕ}
    (hS : GreedyInvariant F S) (hpack : ∀ E ∈ F, IsPackingOn E)
    (hcard : ∀ E ∈ F, 2 ≤ E.card → E.card + 2 ≤ q)
    (Q : SimpleGraph V) (U : Finset V) (u : V) (hu : u ∉ graphSupportFinset Q)
    (huY : u ∈ properPatternExtensions S.available Q U)
    (K : ℕ) (hK : 1 ≤ K)
    (hpair : ∀ T : TripleOn V, ∀ P : PairOn V,
      selectedCount (fun w : PairTwoAwayThreatWitness V F T P ↦ pairTwoAwayThreatRemainder w) S.chosen ≤ K)
    (hcommon : ∀ T T' : TripleOn V,
      selectedCount (fun w : CommonThreatWitness F F T T' ↦ w.remainder) S.chosen ≤ K)
    (x z ex ez : ℝ)
    (hpairTrajectory : ∀ v ∈ graphSupportFinset Q,
      |((availableTrianglesContainingPair S {u, v}).card : ℝ) - x| ≤ ex)
    (hterminalTrajectory : ∀ e : graphEdges Q,
      |(∑ j ∈ Icc 4 q, ((greedyConfigurationClass (forbiddenFamilyOfOrder F j)
          S (patternExtensionTriangle Q e u hu) (j - 4)).card : ℝ)) - z| ≤ ez) :
    let h := (graphSupportFinset Q).card
    let m := (graphEdges Q).card
    |((patternExtensionKillers F Q U S u).card : ℝ) - (h * x + m * z)| ≤
      h * ex + m * (ez + K) + ((h + m) * (m * K) + (h + m).choose 2 * K : ℕ) := by
  classical
  dsimp only
  have halive := ((mem_properPatternExtensions_iff_triangles S.available Q U u hu).mp huY).2
  let target : PatternThreatIndex Q → ℝ := Sum.elim (fun _ ↦ x) (fun _ ↦ z)
  let err : PatternThreatIndex Q → ℝ := Sum.elim (fun _ ↦ ex) (fun _ ↦ ez + K)
  have htrajectory : ∀ i : PatternThreatIndex Q,
      |((patternThreatFamily F Q S u hu i).card : ℝ) - target i| ≤ err i := by
    intro i
    cases i with
    | inl v => exact hpairTrajectory v.1 v.2
    | inr e =>
      have hcount := abs_twoAway_card_sub_terminal_sum_le hS (halive e) hcard
      have hK' : (selectedCount (fun w : CommonThreatWitness F F
          (patternExtensionTriangle Q e u hu) (patternExtensionTriangle Q e u hu) ↦ w.remainder)
          S.chosen : ℝ) ≤ K := by exact_mod_cast hcommon _ _
      have hbound := hcount.trans hK'
      have hterm := hterminalTrajectory e
      calc
        _ ≤ |((availableTwoAwayForbiddenTriangles F S (patternExtensionTriangle Q e u hu)).card : ℝ) -
            ∑ j ∈ Icc 4 q, ((greedyConfigurationClass (forbiddenFamilyOfOrder F j)
              S (patternExtensionTriangle Q e u hu) (j - 4)).card : ℝ)| +
            |(∑ j ∈ Icc 4 q, ((greedyConfigurationClass (forbiddenFamilyOfOrder F j)
              S (patternExtensionTriangle Q e u hu) (j - 4)).card : ℝ)) - z| := abs_sub_le _ _ _
        _ ≤ (K : ℝ) + ez := add_le_add hbound hterm
        _ = err (.inr e) := add_comm _ _
  have h := abs_card_restricted_biUnion_sub_sum_targets
    (univ : Finset (PatternThreatIndex Q)) (patternThreatFamily F Q S u hu)
    (patternBasePairStars Q S) ((graphEdges Q).card * K) K target err
    (fun i _ ↦ patternThreatFamily_inter_base_le F S hpack Q u hu K hK hpair i)
    (fun i _ j _ hij ↦ patternThreatFamily_pairwise_inter_le hS hpack Q u hu halive K hK hpair hcommon i j hij)
    (fun i _ ↦ htrajectory i)
  rw [← patternExtensionKillers_eq_restricted_family hS Q U u hu huY] at h
  simpa only [target, err, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul, card_patternThreatIndex] using h

end

end Erdos207
