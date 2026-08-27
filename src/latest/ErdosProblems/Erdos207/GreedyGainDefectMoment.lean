/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AbsorberGainDefectFamily
import ErdosProblems.Erdos207.GreedyGainDefectPairs
import ErdosProblems.Erdos207.TimedStoppedSharpJointInclusion

/-! # The actual fourth crude-statistic moment and stopped-process tail -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def absorberGainDefectMomentUpper
    {V : Type*} [Fintype V] [DecidableEq V]
    (q r c s : ℕ) (B : TripleSystemOn V) (C : ℝ≥0) : ℝ≥0 :=
  C * ((2 : ℝ≥0) ^ (s * (2 * q)) *
    (absorberGainDefectWeightBound q B * (Fintype.card V + 1 : ℝ≥0) ^ (r - c - 4))) ^ s

theorem greedyActiveGainDefectCount_absorber_moment_le
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (S : Ω → GreedyStateOn V) (F : ForbiddenFamilyOn V)
    (q r c s : ℕ) (B : TripleSystemOn V) (T : TripleOn V) (C : ℝ≥0)
    (hS : L.SupportedOn (fun ω ↦ GreedyInvariant F (S ω)))
    (hc : c + 4 ≤ r) (hr : r ≤ q)
    (hjoint : ∀ U : TripleSystemOn V, U.card ≤ s * (2 * q) →
      L.probability (fun ω ↦ U ⊆ (S ω).chosen) ≤
        C * ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^ U.card) :
    L.expectation (fun ω ↦ (greedyActiveGainDefectCount
      (absorberInducedConfigurationsOn q r B) (absorberNontrivialInducedFamily q B)
      (S ω) T c : ℝ≥0) ^ s) ≤ absorberGainDefectMomentUpper q r c s B C := by
  let J := absorberInducedConfigurationsOn q r B
  let G := absorberNontrivialInducedFamily q B
  let rem := fun w : GainDefectWitness J G T (r - 2 - c - 1) ↦ w.remainder
  have hcard : ∀ w, (rem w).card ≤ 2 * q :=
    absorberGainDefect_remainder_card_le q r (r - 2 - c - 1) B T hr
  have hk : HasExtensionBound rem (fun _ ↦ (Fintype.card V + 1 : ℝ≥0)⁻¹)
      (absorberGainDefectWeightBound q B * (Fintype.card V + 1 : ℝ≥0) ^ (r - c - 4)) := by
    have he : r - 2 - c - 1 - 1 = r - c - 4 := by omega
    simpa only [he] using absorberGainDefect_hasExtensionBound q r (r - 2 - c - 1) B T
      (by omega) hr (by omega)
  have hdom : L.expectation (fun ω ↦ (greedyActiveGainDefectCount J G (S ω) T c : ℝ≥0) ^ s) ≤
      L.expectation (fun ω ↦ (selectedCount rem (S ω).chosen) ^ s) := by
    unfold FiniteLaw.expectation
    apply sum_le_sum
    intro ω _
    by_cases hmass : 0 < L.mass ω
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left'
        (greedyActiveGainDefectCount_le_selectedCount J G (S ω) T c (r - 2)
          (hS ω hmass) absorberInducedConfigurationsOn_fixed_card) s) zero_le
    · have hzero : L.mass ω = 0 := le_antisymm (le_of_not_gt hmass) zero_le
      simp [hzero]
  refine hdom.trans (configurationMomentBound L rem (fun ω ↦ (S ω).chosen)
    (fun _ ↦ (Fintype.card V + 1 : ℝ≥0)⁻¹) C _ hcard hk ?_)
  intro U hU
  simpa only [setWeight, prod_const] using hjoint U hU

theorem timedStoppedAbsorber_gainDefectMomentBound
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop)
    (D : ℕ) (S₀ : GreedyStateOn V) (B : TripleSystemOn V)
    (q r c s : ℕ) (T : TripleOn V) (w : ℝ≥0)
    (hInv₀ : GreedyInvariant F S₀) (hchosen₀ : S₀.chosen = ∅)
    (hc : c + 4 ≤ r) (hr : r ≤ q) (hD : 0 < D) (hw : 1 ≤ w)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ w * (Fintype.card V + 1 : ℝ≥0)⁻¹) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).expectation
      (fun z ↦ (greedyActiveGainDefectCount
        (absorberInducedConfigurationsOn q r B) (absorberNontrivialInducedFamily q B)
        z.2 T c : ℝ≥0) ^ s) ≤
      absorberGainDefectMomentUpper q r c s B (w ^ (s * (2 * q))) := by
  let L := FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀
  have hInv : L.SupportedOn (fun z ↦ GreedyInvariant F z.2) :=
    FiniteLaw.timedStoppedProcessLaw_supported n (fun _ ↦ greedyKernel F) active S₀
      hInv₀ (fun _ _ _ hS ↦ greedyKernel_supported hS)
  refine greedyActiveGainDefectCount_absorber_moment_le L
    (fun z : FiniteLaw.TimedState (GreedyStateOn V) n ↦ z.2) F q r c s B T
    (w ^ (s * (2 * q))) hInv hc hr ?_
  intro U hU
  exact timedStoppedGreedyProcess_probability_subset_le_scaled_weight n F active D (s * (2 * q))
    (Fintype.card V + 1 : ℝ≥0)⁻¹ w hD hw hfloor hratio S₀ U (by simp [hchosen₀]) hU

theorem timedStoppedAbsorber_gainDefectTailBound
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop)
    (D : ℕ) (S₀ : GreedyStateOn V) (B : TripleSystemOn V)
    (q r c s K : ℕ) (T : TripleOn V) (w : ℝ≥0)
    (hInv₀ : GreedyInvariant F S₀) (hchosen₀ : S₀.chosen = ∅)
    (hc : c + 4 ≤ r) (hr : r ≤ q) (hD : 0 < D) (hw : 1 ≤ w)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ w * (Fintype.card V + 1 : ℝ≥0)⁻¹) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ K < greedyActiveGainDefectCount
        (absorberInducedConfigurationsOn q r B) (absorberNontrivialInducedFamily q B) z.2 T c) ≤
      absorberGainDefectMomentUpper q r c s B (w ^ (s * (2 * q))) /
        ((K + 1 : ℕ) : ℝ≥0) ^ s := by
  let L := FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀
  let J := absorberInducedConfigurationsOn q r B
  let G := absorberNontrivialInducedFamily q B
  let X : FiniteLaw.TimedState (GreedyStateOn V) n → ℝ≥0 := fun z ↦
    (greedyActiveGainDefectCount J G z.2 T c : ℝ≥0) ^ s
  have hpos : (0 : ℝ≥0) < ((K + 1 : ℕ) : ℝ≥0) ^ s := by positivity
  have hmono : L.probability (fun z ↦ K < greedyActiveGainDefectCount J G z.2 T c) ≤
      L.probability (fun z ↦ ((K + 1 : ℕ) : ℝ≥0) ^ s ≤ X z) := by
    apply L.probability_mono
    intro z hz
    apply pow_le_pow_left'
    exact_mod_cast (show K + 1 ≤ greedyActiveGainDefectCount J G z.2 T c by omega)
  refine hmono.trans ((L.probability_le_expectation_div X hpos).trans ?_)
  apply (div_le_div_iff_of_pos_right hpos).mpr
  exact timedStoppedAbsorber_gainDefectMomentBound n F active D S₀ B q r c s T w
    hInv₀ hchosen₀ hc hr hD hw hfloor hratio

end

end Erdos207
