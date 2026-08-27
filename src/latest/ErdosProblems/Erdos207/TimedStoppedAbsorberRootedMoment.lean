/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TimedStoppedSharpJointInclusion
import ErdosProblems.Erdos207.AbsorberRootedMoment

/-! # First crude-statistic moment and tail for an actual stopped greedy law -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def absorberRootedMomentUpper
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j c s : ℕ) (B : TripleSystemOn V) (w : ℝ≥0) : ℝ≥0 :=
  w ^ (s * c) * (((2 : ℝ≥0) ^ (s * c) *
    ((2 : ℝ≥0) ^ (j - 2) * pairExactBankExtensionCoefficient q B *
      (Fintype.card V + 1 : ℝ≥0) ^ (j - c - 5))) ^ s)

theorem timedStoppedAbsorber_rootedMomentBound
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop)
    (D : ℕ) (S₀ : GreedyStateOn V) (B R : TripleSystemOn V)
    (q j c s : ℕ) (w : ℝ≥0)
    (hInv₀ : GreedyInvariant F S₀) (hchosen₀ : S₀.chosen = ∅)
    (hR : R.card = 2) (hc : c + 5 ≤ j) (hD : 0 < D) (hw : 1 ≤ w)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ w * (Fintype.card V + 1 : ℝ≥0)⁻¹) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).expectation
      (fun z ↦ ((greedyRootedConfigurationClass
        (absorberInducedConfigurationsOn q j B) z.2 R c).card : ℝ≥0) ^ s) ≤
      absorberRootedMomentUpper q j c s B w := by
  let L := FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀
  have hInv : L.SupportedOn (fun z ↦ GreedyInvariant F z.2) :=
    FiniteLaw.timedStoppedProcessLaw_supported n (fun _ ↦ greedyKernel F) active S₀
      hInv₀ (fun _ _ _ hS ↦ greedyKernel_supported hS)
  apply absorberInduced_rootedConfiguration_moment_le L (fun z ↦ z.2) F B R
    q j c s (w ^ (s * c)) hInv hR hc
  intro T hT
  exact timedStoppedGreedyProcess_probability_subset_le_scaled_weight n F active D (s * c)
    (Fintype.card V + 1 : ℝ≥0)⁻¹ w hD hw hfloor hratio S₀ T
    (by simp [hchosen₀]) hT

theorem timedStoppedAbsorber_rootedTailBound
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop)
    (D : ℕ) (S₀ : GreedyStateOn V) (B R : TripleSystemOn V)
    (q j c s K : ℕ) (w : ℝ≥0)
    (hInv₀ : GreedyInvariant F S₀) (hchosen₀ : S₀.chosen = ∅)
    (hR : R.card = 2) (hc : c + 5 ≤ j) (hD : 0 < D) (hw : 1 ≤ w)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ w * (Fintype.card V + 1 : ℝ≥0)⁻¹) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ K < (greedyRootedConfigurationClass
        (absorberInducedConfigurationsOn q j B) z.2 R c).card) ≤
      absorberRootedMomentUpper q j c s B w / ((K + 1 : ℕ) : ℝ≥0) ^ s := by
  let L := FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀
  let X : FiniteLaw.TimedState (GreedyStateOn V) n → ℝ≥0 := fun z ↦
    ((greedyRootedConfigurationClass (absorberInducedConfigurationsOn q j B) z.2 R c).card : ℝ≥0) ^ s
  have hpos : (0 : ℝ≥0) < ((K + 1 : ℕ) : ℝ≥0) ^ s := by positivity
  have hmono : L.probability (fun z ↦ K < (greedyRootedConfigurationClass
        (absorberInducedConfigurationsOn q j B) z.2 R c).card) ≤
      L.probability (fun z ↦ ((K + 1 : ℕ) : ℝ≥0) ^ s ≤ X z) := by
    apply L.probability_mono
    intro z hz
    apply pow_le_pow_left'
    exact_mod_cast (show K + 1 ≤ (greedyRootedConfigurationClass
      (absorberInducedConfigurationsOn q j B) z.2 R c).card by omega)
  refine hmono.trans ((L.probability_le_expectation_div X hpos).trans ?_)
  apply (div_le_div_iff_of_pos_right hpos).mpr
  exact timedStoppedAbsorber_rootedMomentBound n F active D S₀ B R q j c s w
    hInv₀ hchosen₀ hR hc hD hw hfloor hratio

end

end Erdos207
