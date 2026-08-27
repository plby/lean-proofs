/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.EnvelopeStoppedGreedy
import ErdosProblems.Erdos207.TwoAwayAbsorberBound
import ErdosProblems.Erdos207.CoverDownProbability

/-!
# Two-away cutoff for an envelope-stopped absorber process

The weighted A2 extension bound and the inhomogeneous joint-inclusion bound
give a high moment for the two-away deletion count of every fixed triangle.
A finite union bound then produces a positive-mass terminal state on which
the cutoff still holds.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

def twoAwayMomentUnionCutoff (q s : ℕ) : ℕ := s * (q - 2)

def twoAwayMomentJointConstant (q s : ℕ) : ℕ :=
  (twoAwayMomentUnionCutoff q s).factorial

/-- Moment bound for one fixed triangle at one envelope-stopped time. -/
theorem envelopeStoppedAbsorberGreedy_twoAwayMomentBound
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M K fuel s : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B A : TripleSystemOn V} {D : ℕ → ℕ} (U : TripleOn V)
    (hA2 : HasAbsorberLocalization q M H X B)
    (hD : ∀ i, 0 < D i)
    (hratio : (∑ i ∈ range fuel, (D i : ℝ≥0)⁻¹) ≤
      (Fintype.card V + 1 : ℝ≥0)⁻¹) :
    (envelopeStoppedGreedyProcessLaw
        (absorberErdosForbiddenConfigurationsOn q B) K D fuel
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B) A)).expectation
      (fun S ↦ ((twoAwayForbiddenTriangles
        (absorberErdosForbiddenConfigurationsOn q B)
        S.chosen U).card : ℝ≥0) ^ s) ≤
      (twoAwayMomentJointConstant q s : ℝ≥0) *
        (((2 : ℝ≥0) ^ twoAwayMomentUnionCutoff q s *
          (twoAwayThreatExtensionCoefficient q M H X B : ℕ)) ^ s) := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S₀ := absorberGreedyInitialState F A
  let L := envelopeStoppedGreedyProcessLaw F K D fuel S₀
  apply twoAwayForbiddenMomentBound L (fun S ↦ S.chosen) F U
    (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹))
    (twoAwayMomentJointConstant q s : ℝ≥0)
    (twoAwayThreatExtensionCoefficient q M H X B : ℕ)
  · intro C hCF
    exact card_le_cutoff_of_mem_absorberErdosForbidden hCF
  · exact absorberTwoAwayThreatRemainder_hasExtensionBound hA2
  · intro T hTcard
    apply envelopeStoppedGreedyProcess_probability_subset_chosen_le_weight
      F K D hD fuel (twoAwayMomentUnionCutoff q s)
      ((Fintype.card V + 1 : ℝ≥0)⁻¹) hratio S₀ T
    · simp [S₀, absorberGreedyInitialState]
    · exact hTcard

def envelopeTwoAwayTail
    {V : Type*} [Fintype V] [DecidableEq V]
    (q M s : ℕ) (H : SimpleGraph V) (X : Finset V)
    (B : TripleSystemOn V) (K : ℕ) : ℝ≥0 :=
  ((twoAwayMomentJointConstant q s : ℝ≥0) *
      (((2 : ℝ≥0) ^ twoAwayMomentUnionCutoff q s *
        (twoAwayThreatExtensionCoefficient q M H X B : ℕ)) ^ s)) /
    ((K + 1 : ℕ) : ℝ≥0) ^ s

/-- Markov upper tail for one fixed triangle. -/
theorem envelopeStoppedAbsorberGreedy_probability_twoAway_gt_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M K fuel s : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B A : TripleSystemOn V} {D : ℕ → ℕ} (U : TripleOn V)
    (hA2 : HasAbsorberLocalization q M H X B)
    (hD : ∀ i, 0 < D i)
    (hratio : (∑ i ∈ range fuel, (D i : ℝ≥0)⁻¹) ≤
      (Fintype.card V + 1 : ℝ≥0)⁻¹) :
    (envelopeStoppedGreedyProcessLaw
        (absorberErdosForbiddenConfigurationsOn q B) K D fuel
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B) A)).probability
      (fun S ↦ K < (twoAwayForbiddenTriangles
        (absorberErdosForbiddenConfigurationsOn q B)
        S.chosen U).card) ≤
      envelopeTwoAwayTail q M s H X B K := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S₀ := absorberGreedyInitialState F A
  let L := envelopeStoppedGreedyProcessLaw F K D fuel S₀
  let Y : GreedyStateOn V → ℝ≥0 := fun S ↦
    ((twoAwayForbiddenTriangles F S.chosen U).card : ℝ≥0) ^ s
  have hthreshold : (0 : ℝ≥0) < (((K + 1 : ℕ) : ℝ≥0) ^ s) := by
    positivity
  have hmono : L.probability
      (fun S ↦ K < (twoAwayForbiddenTriangles F S.chosen U).card) ≤
      L.probability (fun S ↦ (((K + 1 : ℕ) : ℝ≥0) ^ s) ≤ Y S) := by
    apply L.probability_mono
    intro S hS
    apply pow_le_pow_left'
    exact_mod_cast (show K + 1 ≤
      (twoAwayForbiddenTriangles F S.chosen U).card by omega)
  refine hmono.trans ?_
  have hmarkov := L.probability_le_expectation_div Y hthreshold
  refine hmarkov.trans ?_
  apply (div_le_div_iff_of_pos_right hthreshold).2
  simpa [L, F, S₀, envelopeTwoAwayTail] using
    (envelopeStoppedAbsorberGreedy_twoAwayMomentBound
      (K := K) (s := s) U hA2 hD hratio)

/-- Failure of the cutoff is bounded by the union of the fixed-triangle
tails. -/
theorem envelopeStoppedAbsorberGreedy_probability_not_twoAwayCutoff_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M K fuel s : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B A : TripleSystemOn V} {D : ℕ → ℕ}
    (hA2 : HasAbsorberLocalization q M H X B)
    (hD : ∀ i, 0 < D i)
    (hratio : (∑ i ∈ range fuel, (D i : ℝ≥0)⁻¹) ≤
      (Fintype.card V + 1 : ℝ≥0)⁻¹) :
    (envelopeStoppedGreedyProcessLaw
        (absorberErdosForbiddenConfigurationsOn q B) K D fuel
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B) A)).probability
      (fun S ↦ ¬ HasTwoAwayCutoff
        (absorberErdosForbiddenConfigurationsOn q B) K S) ≤
      (Fintype.card (TripleOn V) : ℝ≥0) *
        envelopeTwoAwayTail q M s H X B K := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S₀ := absorberGreedyInitialState F A
  let L := envelopeStoppedGreedyProcessLaw F K D fuel S₀
  let badAt : TripleOn V → GreedyStateOn V → Prop := fun U S ↦
    K < (twoAwayForbiddenTriangles F S.chosen U).card
  calc
    L.probability (fun S ↦ ¬ HasTwoAwayCutoff F K S) ≤
        L.probability (fun S ↦ ∃ U : TripleOn V, badAt U S) := by
      apply L.probability_mono
      intro S hS
      rw [HasTwoAwayCutoff] at hS
      push_neg at hS
      obtain ⟨U, hUavailable, hU⟩ := hS
      exact ⟨U, by simpa [badAt] using hU⟩
    _ ≤ ∑ U ∈ (univ : Finset (TripleOn V)),
        L.probability (badAt U) := by
      simpa using L.probability_exists_le
        (univ : Finset (TripleOn V)) badAt
    _ ≤ ∑ _U ∈ (univ : Finset (TripleOn V)),
        envelopeTwoAwayTail q M s H X B K := by
      apply sum_le_sum
      intro U _hU
      simpa [L, F, S₀, badAt] using
        (envelopeStoppedAbsorberGreedy_probability_twoAway_gt_le
          (K := K) (s := s) U hA2 hD hratio)
    _ = (Fintype.card (TripleOn V) : ℝ≥0) *
        envelopeTwoAwayTail q M s H X B K := by simp

/-- A strict union-bound inequality yields a positive-mass terminal state
where the cutoff survives. -/
theorem exists_envelopeStoppedAbsorberGreedy_cutoff
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M K fuel s : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B A : TripleSystemOn V} {D : ℕ → ℕ}
    (hA2 : HasAbsorberLocalization q M H X B)
    (hD : ∀ i, 0 < D i)
    (hratio : (∑ i ∈ range fuel, (D i : ℝ≥0)⁻¹) ≤
      (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (hsmall : (Fintype.card (TripleOn V) : ℝ≥0) *
      envelopeTwoAwayTail q M s H X B K < 1) :
    ∃ S : GreedyStateOn V,
      HasTwoAwayCutoff (absorberErdosForbiddenConfigurationsOn q B) K S ∧
      0 < (envelopeStoppedGreedyProcessLaw
        (absorberErdosForbiddenConfigurationsOn q B) K D fuel
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B) A)).mass S := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S₀ := absorberGreedyInitialState F A
  let L := envelopeStoppedGreedyProcessLaw F K D fuel S₀
  have hbad : L.probability (fun S ↦ ¬ HasTwoAwayCutoff F K S) < 1 :=
    (envelopeStoppedAbsorberGreedy_probability_not_twoAwayCutoff_le
      hA2 hD hratio).trans_lt hsmall
  have hgood : 0 < L.probability (HasTwoAwayCutoff F K) := by
    rw [show L.probability (HasTwoAwayCutoff F K) =
      L.probability (fun S ↦ ¬ ¬ HasTwoAwayCutoff F K S) by
        congr 1; funext S; simp]
    rw [L.probability_not]
    exact tsub_pos_iff_lt.mpr hbad
  exact L.exists_of_probability_pos_with_mass hgood

/-- Combining positive mass with the process support invariant yields a
genuine `fuel`-step absorber-constrained packing that retains the cutoff and
the scheduled availability floor. -/
theorem exists_envelopeStoppedAbsorberGreedy_phase
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M K fuel s : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B A : TripleSystemOn V} {D : ℕ → ℕ}
    (hA2 : HasAbsorberLocalization q M H X B)
    (hD : ∀ i, 0 < D i)
    (hfloor : D 0 ≤ (absorberGreedyInitialState
      (absorberErdosForbiddenConfigurationsOn q B) A).available.card)
    (hdecrease : ∀ i,
      D (i + 1) + (3 * Fintype.card V + K) ≤ D i)
    (hratio : (∑ i ∈ range fuel, (D i : ℝ≥0)⁻¹) ≤
      (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (hsmall : (Fintype.card (TripleOn V) : ℝ≥0) *
      envelopeTwoAwayTail q M s H X B K < 1) :
    ∃ S : GreedyStateOn V,
      AbsorberGreedyInvariant
          (absorberErdosForbiddenConfigurationsOn q B) A S ∧
        HasTwoAwayCutoff
          (absorberErdosForbiddenConfigurationsOn q B) K S ∧
        D fuel ≤ S.available.card ∧ S.chosen.card = fuel := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S₀ := absorberGreedyInitialState F A
  let L := envelopeStoppedGreedyProcessLaw F K D fuel S₀
  obtain ⟨S, hcut, hmass⟩ :=
    exists_envelopeStoppedAbsorberGreedy_cutoff
      (A := A) (D := D) hA2 hD hratio hsmall
  have hInv₀ : AbsorberGreedyInvariant F A S₀ :=
    absorberGreedyInitialState_invariant F A fun C hC ↦
      absorberErdosForbidden_nonempty hC
  have hs := envelopeStoppedAbsorberGreedyProcessLaw_supported_progress
    hInv₀ hfloor hD hdecrease fuel S hmass
  have hcard : S.chosen.card = fuel := by
    rcases hs.2.2 with hbad | hcard
    · exact (hbad hcut).elim
    · simpa [S₀, absorberGreedyInitialState] using hcard
  exact ⟨S, hs.1, hcut, hs.2.1, hcard⟩

end

end Erdos207
