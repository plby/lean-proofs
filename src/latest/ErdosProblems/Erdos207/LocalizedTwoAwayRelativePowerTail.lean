/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LocalizedTwoAwayGeometricTail

/-! # Localized tails at a cutoff proportional to the tracked vertex-set size -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem localizedTwoAwayWeightBound_le_relative_scale
    {V : Type*} [Fintype V] [DecidableEq V]
    (q k : ℕ) (B : TripleSystemOn V) (U : Finset V) (t : ℝ≥0) (ht : 0 < t)
    (hsize : (45 * (q + 1) + 28 : ℕ) * t ^ k ≤ (U.card : ℝ≥0))
    (hbank : pairExactBankExtensionCoefficient q B * t ^ k ≤ (Fintype.card V + 1 : ℝ≥0)) :
    localizedTwoAwayWeightBound q B U ≤
      (2 * (q + 1 : ℕ) : ℝ≥0) * ((U.card : ℝ≥0) / t ^ k) := by
  have hpow : 0 < t ^ k := pow_pos ht k
  have hN : (0 : ℝ≥0) < Fintype.card V + 1 := by positivity
  have hroot : (45 * (q + 1) + 28 : ℕ) ≤ (U.card : ℝ≥0) / t ^ k :=
    (le_div_iff₀ hpow).mpr hsize
  have hbankRatio : pairExactBankExtensionCoefficient q B / (Fintype.card V + 1 : ℝ≥0) ≤ 1 / t ^ k := by
    apply (div_le_div_iff₀ hN hpow).mpr
    simpa only [one_mul] using hbank
  have hbankTerm : (U.card : ℝ≥0) * pairExactBankExtensionCoefficient q B /
      (Fintype.card V + 1 : ℝ≥0) ≤ (U.card : ℝ≥0) / t ^ k := by
    calc
      _ = (U.card : ℝ≥0) * (pairExactBankExtensionCoefficient q B / (Fintype.card V + 1 : ℝ≥0)) := by ring
      _ ≤ (U.card : ℝ≥0) * (1 / t ^ k) := mul_le_mul_of_nonneg_left hbankRatio (bot_le : 0 ≤ (U.card : ℝ≥0))
      _ = _ := by ring
  calc
    _ ≤ (q + 1 : ℕ) * ((U.card : ℝ≥0) / t ^ k + (U.card : ℝ≥0) / t ^ k) :=
      mul_le_mul_of_nonneg_left (add_le_add hroot hbankTerm) (by positivity)
    _ = _ := by ring

theorem timedStoppedAbsorber_localizedTwoAway_relative_power_tail
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop)
    (D : ℕ) (S₀ : GreedyStateOn V) (q t r v : ℕ)
    (H : SimpleGraph V) (B : TripleSystemOn V) (X U : Finset V)
    (T : TripleOn V) {a b : V} (hab : a ≠ b) (w : ℝ≥0)
    (hF : F ⊆ absorberErdosForbiddenConfigurationsOn q B)
    (hsep : AbsorberSeparatedLevel H X B U)
    (hrootLocal : HasPaddedAbsorberRootLocalization q X B)
    (hInv₀ : GreedyInvariant F S₀) (hchosen₀ : S₀.chosen = ∅)
    (hD : 0 < D) (hw : 1 ≤ w) (ht : 1 ≤ t) (hU : U.Nonempty)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ w * (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (hwscale : w ≤ (t : ℝ≥0) ^ v)
    (hsize : (45 * (q + 1) + 28 : ℕ) * (t : ℝ≥0) ^ (r + q * (v + 1) + 1) ≤ (U.card : ℝ≥0))
    (hbank : pairExactBankExtensionCoefficient q B * (t : ℝ≥0) ^ (r + q * (v + 1) + 1) ≤
      (Fintype.card V + 1 : ℝ≥0))
    (hconst : (4 * (q + 1) ^ (q + 2) : ℕ) ≤ t) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ (U.card : ℝ≥0) / (t : ℝ≥0) ^ r ≤ selectedCount
        (fun u : LocalizedTwoAwayWitness V F T a b U ↦ localizedTwoAwayRemainder u) z.2.chosen) ≤
      (1 / 2 : ℝ≥0) ^ t := by
  let k := r + q * (v + 1) + 1
  let Z := (U.card : ℝ≥0) / (t : ℝ≥0) ^ k
  have htpos : (0 : ℝ≥0) < t := by exact_mod_cast (show 0 < t by omega)
  have hUpos : (0 : ℝ≥0) < U.card := by exact_mod_cast card_pos.mpr hU
  have hZ : 0 < Z := div_pos hUpos (pow_pos htpos _)
  have hκ := localizedTwoAwayWeightBound_le_relative_scale q k B U t htpos hsize hbank
  have hc : 2 * (((q + 1) ^ (q + 1) : ℕ) : ℝ≥0) * (2 * (q + 1 : ℕ) : ℝ≥0) ≤ t := by
    have hid : 2 * ((q + 1) ^ (q + 1)) * (2 * (q + 1)) = 4 * (q + 1) ^ (q + 2) := by
      rw [show q + 2 = (q + 1) + 1 by omega, pow_succ]
      ring
    exact_mod_cast (hid ▸ hconst)
  have h := timedStoppedGreedy_dominatedConfigurationTail_power n F active D S₀
    (fun u : LocalizedTwoAwayWitness V F T a b U ↦ localizedTwoAwayRemainder u)
    (fun S ↦ selectedCount
      (fun u : LocalizedTwoAwayWitness V F T a b U ↦ localizedTwoAwayRemainder u) S.chosen)
    q t 0 v (Fintype.card V + 1 : ℝ≥0)⁻¹ t w (localizedTwoAwayWeightBound q B U)
    (2 * (q + 1 : ℕ) : ℝ≥0) Z hInv₀ hchosen₀ hD hw ht le_rfl hZ hfloor hratio
    (fun _ _ ↦ le_rfl) (localizedTwoAway_absorber_remainder_card_le hF)
    (localizedTwoAway_absorber_hasExtensionBound F hF T hab hsep hrootLocal) hwscale
    (by simpa only [pow_zero, mul_one] using hκ) hc
  have hcut : Z * (t : ℝ≥0) ^ (0 + q * (v + 1) + 1) = (U.card : ℝ≥0) / (t : ℝ≥0) ^ r := by
    dsimp only [Z, k]
    rw [show r + q * (v + 1) + 1 = r + (q * (v + 1) + 1) by omega, pow_add]
    simp only [zero_add]
    field_simp
  simpa only [hcut] using h

end

end Erdos207
