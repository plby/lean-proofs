/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.StoppedGreedyRootedThreat
import ErdosProblems.Erdos207.StoppedGreedyVertexDegree
import ErdosProblems.Erdos207.CoverDownProbability

/-!
# A simultaneous positive-mass stopped-greedy outcome

The two moment estimates needed for the first constrained-greedy stage must
hold on the same trajectory.  This file takes one union bound over all
vertices and all ordered distinct pairs.  The extracted state has positive
mass, so the stopped-process support theorem transfers the full absorber
greedy invariant to it.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The Markov upper-tail envelope for one selected vertex star. -/
def stoppedVertexStarTailEnvelope
    (V : Type*) [Fintype V] (s : ℕ) (a : ℝ≥0) : ℝ≥0 :=
  ((s.factorial : ℝ≥0) *
      (((2 : ℝ≥0) ^ s * (Fintype.card V + 2 : ℕ)) ^ s)) /
    a ^ s

/-- The Markov upper-tail envelope for one rooted absorber threat count. -/
def stoppedRootedThreatTailEnvelope
    {V : Type*} [Fintype V] [DecidableEq V]
    (q M s : ℕ) (H : SimpleGraph V) (X : Finset V)
    (B : TripleSystemOn V) (a : ℝ≥0) : ℝ≥0 :=
  ((rootedMomentJointConstant q s : ℝ≥0) *
      (((2 : ℝ≥0) ^ rootedMomentUnionCutoff q s *
        ((Fintype.card V *
          rootedThreatExtensionCoefficient q M H X B : ℕ) : ℝ≥0)) ^ s)) /
    a ^ s

/-- If the sum of the vertex-star and rooted-threat tail envelopes is below
one, a single positive-mass stopped trajectory satisfies both families of
bounds and the full absorber greedy invariant. -/
theorem exists_stoppedAbsorberGreedy_invariant_star_root_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M D fuel s : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B A : TripleSystemOn V} (aStar aRoot : ℝ≥0)
    (hA2 : HasAbsorberLocalization q M H X B)
    (hD : 0 < D) (haStar : 0 < aStar) (haRoot : 0 < aRoot)
    (hratio : (fuel : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤
      (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (hsmall :
      (Fintype.card V : ℝ≥0) *
          stoppedVertexStarTailEnvelope V s aStar +
        (Fintype.card (DistinctPair V) : ℝ≥0) *
          stoppedRootedThreatTailEnvelope q M s H X B aRoot < 1) :
    ∃ S : GreedyStateOn V,
      AbsorberGreedyInvariant
          (absorberErdosForbiddenConfigurationsOn q B) A S ∧
        (∀ v : V,
          ((triplesThrough S.chosen v).card : ℝ≥0) < aStar) ∧
        ∀ e : DistinctPair V,
          ((rootedActiveForbiddenConfigurations
            (absorberErdosForbiddenConfigurationsOn q B)
            S.chosen e.1.1 e.1.2).card : ℝ≥0) < aRoot := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S₀ := absorberGreedyInitialState F A
  let L := stoppedGreedyProcessLaw F D fuel S₀
  let starBad : GreedyStateOn V → Prop := fun S ↦
    ∃ v : V, aStar ≤ (triplesThrough S.chosen v).card
  let rootBad : GreedyStateOn V → Prop := fun S ↦
    ∃ e : DistinctPair V,
      aRoot ≤ (rootedActiveForbiddenConfigurations F S.chosen
        e.1.1 e.1.2).card
  have hstarOne : ∀ v : V,
      L.probability (fun S ↦
        aStar ≤ (triplesThrough S.chosen v).card) ≤
        stoppedVertexStarTailEnvelope V s aStar := by
    intro v
    simpa [L, F, S₀, stoppedVertexStarTailEnvelope] using
      (stoppedGreedy_probability_triplesThrough_ge_le
        (F := F) (S₀ := S₀) (s := s) v aStar hD haStar
        (by simp [S₀, absorberGreedyInitialState]) hratio)
  have hrootOne : ∀ e : DistinctPair V,
      L.probability (fun S ↦
        aRoot ≤ (rootedActiveForbiddenConfigurations F S.chosen
          e.1.1 e.1.2).card) ≤
        stoppedRootedThreatTailEnvelope q M s H X B aRoot := by
    intro e
    simpa [L, F, S₀, stoppedRootedThreatTailEnvelope] using
      (stoppedAbsorberGreedy_probability_rootedActive_ge_le
        (A := A) (s := s) e aRoot hA2 hD haRoot hratio)
  have hstar : L.probability starBad ≤
      (Fintype.card V : ℝ≥0) *
        stoppedVertexStarTailEnvelope V s aStar := by
    calc
      L.probability starBad ≤
          ∑ v ∈ (univ : Finset V),
            L.probability (fun S ↦
              aStar ≤ (triplesThrough S.chosen v).card) := by
        simpa [starBad] using L.probability_exists_le
          (univ : Finset V) (fun v S ↦
            aStar ≤ (triplesThrough S.chosen v).card)
      _ ≤ ∑ _v ∈ (univ : Finset V),
          stoppedVertexStarTailEnvelope V s aStar := by
        apply sum_le_sum
        intro v _hv
        exact hstarOne v
      _ = (Fintype.card V : ℝ≥0) *
          stoppedVertexStarTailEnvelope V s aStar := by simp
  have hroot : L.probability rootBad ≤
      (Fintype.card (DistinctPair V) : ℝ≥0) *
        stoppedRootedThreatTailEnvelope q M s H X B aRoot := by
    calc
      L.probability rootBad ≤
          ∑ e ∈ (univ : Finset (DistinctPair V)),
            L.probability (fun S ↦
              aRoot ≤ (rootedActiveForbiddenConfigurations F S.chosen
                e.1.1 e.1.2).card) := by
        simpa [rootBad] using L.probability_exists_le
          (univ : Finset (DistinctPair V)) (fun e S ↦
            aRoot ≤ (rootedActiveForbiddenConfigurations F S.chosen
              e.1.1 e.1.2).card)
      _ ≤ ∑ _e ∈ (univ : Finset (DistinctPair V)),
          stoppedRootedThreatTailEnvelope q M s H X B aRoot := by
        apply sum_le_sum
        intro e _he
        exact hrootOne e
      _ = (Fintype.card (DistinctPair V) : ℝ≥0) *
          stoppedRootedThreatTailEnvelope q M s H X B aRoot := by simp
  have hbad : L.probability (fun S ↦ starBad S ∨ rootBad S) < 1 :=
    (L.probability_or_le starBad rootBad).trans_lt
      ((add_le_add hstar hroot).trans_lt hsmall)
  have hgood : 0 < L.probability
      (fun S ↦ ¬ (starBad S ∨ rootBad S)) := by
    rw [L.probability_not]
    exact tsub_pos_iff_lt.mpr hbad
  obtain ⟨S, hSgood, hSmass⟩ :=
    L.exists_of_probability_pos_with_mass hgood
  have hInv : AbsorberGreedyInvariant F A S := by
    exact stoppedAbsorberGreedyInitialProcessLaw_supported
      q D fuel B A S hSmass
  refine ⟨S, hInv, ?_, ?_⟩
  · intro v
    exact lt_of_not_ge fun hv ↦ hSgood (Or.inl ⟨v, hv⟩)
  · intro e
    exact lt_of_not_ge fun he ↦ hSgood (Or.inr ⟨e, he⟩)

end

end Erdos207
