/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RegularizationInputPowerScalars
import ErdosProblems.Erdos207.RegularizationInputFailurePower
import ErdosProblems.Erdos207.SourceRegularizationOrderData

/-! # Every order-input numerical condition follows from fixed power gaps -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem eventually_sourceRegularizationOrderInput
    (j K Y D A v w L R : ℕ) (C : ℝ≥0) (hj : 4 ≤ j) (hC : 0 < C)
    (hD : K + 1 ≤ D) (hA : D + 1 ≤ A) (hv : K + 1 ≤ v)
    (hLmass : w + 2 ≤ L) (hLdensity : w * (j - 3) + 1 ≤ L)
    (hLsquare : 2 * D ≤ L) (hLy : D + Y ≤ L) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      ∀ {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Nonempty I] {ell : ℕ},
      ∀ (W : Vortex V ell) (e : I ↪ TripleOn V),
      (∀ i, (e i).1 ⊆ W.U (Fin.last ell)) →
      ∀ (localFamily : Finset (Finset I)) (F : ForbiddenFamilyOn V) (y z B sigma : ℝ≥0),
      (∀ E ∈ localFamily, E.card = j - 2) → SourceVortexWellSpread W j F y z →
      t ^ L ≤ W.terminalSize → Fintype.card V ≤ t ^ R →
      1 / (t : ℝ≥0) ^ w ≤ sigma → sigma ≤ 1 / (t : ℝ≥0) ^ v →
      B ≤ (t : ℝ≥0) ^ K → y ≤ (t : ℝ≥0) ^ Y →
      sigma * (W.terminalSize : ℝ≥0) ^ 3 / C ≤ Fintype.card I →
      (finiteHypergraphMaxDegree localFamily : ℝ≥0) ≤
        B * sigma ^ (j - 3) * (W.terminalSize : ℝ≥0) ^ (j - 3) →
      SourceRegularizationOrderInput W j localFamily F (8192 * t) t y z
        ((t : ℝ≥0) ^ A) ((t : ℝ≥0) ^ D) sigma C B := by
  let densityCoefficient : ℝ≥0 := 324 * 2 ^ (j - 2) * (2 * C) ^ (j - 3) * (j - 3).factorial
  let hazardCoefficient : ℝ≥0 := 2 ^ (j - 1) * (2 * C) ^ (j - 3) * (j - 3).factorial
  obtain ⟨TC, hTC⟩ := exists_nat_gt (C : ℝ)
  obtain ⟨TD, hTD⟩ := exists_nat_gt (densityCoefficient : ℝ)
  obtain ⟨TH, hTH⟩ := exists_nat_gt (hazardCoefficient : ℝ)
  obtain ⟨TF, _hTF1, hTF⟩ := eventually_regularizationInput_failure_power_lt j R
  let T := 9 + TC + TD + TH + TF + 16 * 2 ^ (j - 3) * (j - 3)
  refine ⟨T, by dsimp [T]; omega, ?_⟩
  intro t ht V I _ _ _ _ _ ell W e hsupport localFamily F y z B sigma huniform hspread hn hN
    hsigmaLo hsigmaHi hB hy hmass hdegree
  have ht9 : 9 ≤ t := by dsimp [T] at ht; omega
  have ht1 : 1 ≤ t := by omega
  have htNN : (1 : ℝ≥0) ≤ t := by exact_mod_cast ht1
  have ht0 : (0 : ℝ≥0) < t := zero_lt_one.trans_le htNN
  have htNN9 : (9 : ℝ≥0) ≤ t := by exact_mod_cast ht9
  have htNN4 : (4 : ℝ≥0) ≤ t := by exact_mod_cast (show 4 ≤ t by omega)
  have hnNN : (t : ℝ≥0) ^ L ≤ W.terminalSize := by exact_mod_cast hn
  have hn1 : (1 : ℝ≥0) ≤ W.terminalSize := by exact_mod_cast hspread.terminal_nonempty
  have hCt : C ≤ t := by
    have hTCt : TC ≤ t := by dsimp [T] at ht; omega
    exact_mod_cast hTC.le.trans (show (TC : ℝ) ≤ t by exact_mod_cast hTCt)
  have hDt : densityCoefficient ≤ t := by
    have hTDt : TD ≤ t := by dsimp [T] at ht; omega
    exact_mod_cast hTD.le.trans (show (TD : ℝ) ≤ t by exact_mod_cast hTDt)
  have hHt : hazardCoefficient ≤ t := by
    have hTHt : TH ≤ t := by dsimp [T] at ht; omega
    exact_mod_cast hTH.le.trans (show (TH : ℝ) ≤ t by exact_mod_cast hTHt)
  have hdeltaSquare : ((t : ℝ≥0) ^ D) ^ 2 ≤ W.terminalSize := by
    rw [← pow_mul, Nat.mul_comm D 2]
    exact (pow_le_pow_right₀ htNN hLsquare).trans hnNN
  have hdeltaY : (t : ℝ≥0) ^ D * y ≤ W.terminalSize := by
    calc
      _ ≤ (t : ℝ≥0) ^ D * (t : ℝ≥0) ^ Y := mul_le_mul_of_nonneg_left hy zero_le
      _ = (t : ℝ≥0) ^ (D + Y) := (pow_add _ _ _).symm
      _ ≤ (t : ℝ≥0) ^ L := pow_le_pow_right₀ htNN hLy
      _ ≤ _ := hnNN
  have hparameters : SourceRandomConfigurationParameters W j ((t : ℝ≥0) ^ D) ((t : ℝ≥0) ^ A) t := by
    refine ⟨hj, hspread.terminal_nonempty, one_le_pow₀ htNN, hdeltaSquare,
      power_amplitude_four t D A htNN4 hA, ?_⟩
    have hh := power_amplitude_four (t : ℝ≥0) 1 A htNN4 (by omega)
    simpa only [pow_one, Nat.cast_mul, Nat.cast_ofNat] using hh
  have hsigma : 0 < sigma := (one_div_pos.mpr (pow_pos ht0 w)).trans_le hsigmaLo
  have hsizeLower : (t : ℝ≥0) ≤ Fintype.card I := by
    apply regularization_auxiliary_size_from_power_mass t W.terminalSize (Fintype.card I) sigma C
      htNN hn1 hC hCt _ hmass
    have hh := inversePower_density_ge_power t sigma W.terminalSize w 1 2 L htNN hsigmaLo
      (by simpa only [Nat.mul_one] using hLmass) hnNN
    simpa only [pow_one] using hh
  have hsize : 16 * 2 ^ (j - 3) * (j - 3) ≤ Fintype.card I := by
    have htSize : 16 * 2 ^ (j - 3) * (j - 3) ≤ t := by dsimp [T] at ht; omega
    have hmNat : t ≤ Fintype.card I := by exact_mod_cast hsizeLower
    exact htSize.trans hmNat
  have hsmallCoefficient := regularization_degree_coefficient_power_small t B sigma K v (j - 3)
    htNN9 hv (by omega) hB hsigmaHi
  have hmaxPower : 9 * finiteHypergraphMaxDegree localFamily ≤ W.terminalSize ^ (j - 3) := by
    have hbound : (9 : ℝ≥0) * finiteHypergraphMaxDegree localFamily ≤ (W.terminalSize : ℝ≥0) ^ (j - 3) := by
      calc
        _ ≤ 9 * (B * sigma ^ (j - 3) * (W.terminalSize : ℝ≥0) ^ (j - 3)) :=
          mul_le_mul_of_nonneg_left hdegree zero_le
        _ = (9 * B * sigma ^ (j - 3)) * (W.terminalSize : ℝ≥0) ^ (j - 3) := by ring
        _ ≤ 1 * (W.terminalSize : ℝ≥0) ^ (j - 3) := mul_le_mul_of_nonneg_right hsmallCoefficient zero_le
        _ = _ := one_mul _
    exact_mod_cast hbound
  have hdensity : densityCoefficient ≤ sigma ^ (j - 3) * W.terminalSize :=
    hDt.trans (by simpa only [pow_one] using
      inversePower_density_ge_power t sigma W.terminalSize w (j - 3) 1 L htNN hsigmaLo hLdensity hnNN)
  have hcoefficient : hazardCoefficient * B ≤ (t : ℝ≥0) ^ D :=
    power_coefficient_absorption t hazardCoefficient B K D htNN hHt hB hD
  refine ⟨hparameters, huniform, hspread, hdeltaY, hsize, hmaxPower, hsigma, hC, hmass,
    hdegree, hdensity, hcoefficient, ?_⟩
  have hmax : finiteHypergraphMaxDegree localFamily ≤ W.terminalSize ^ (j - 3) := by omega
  have hfailure := regularizationInput_failure_power_bound t W.terminalSize (Fintype.card V) (Fintype.card I)
    (finiteHypergraphMaxDegree localFamily) (sourceRandomFailureCoefficient W j) j R ht1 hj
    (card_le_univ _) hN (card_auxiliary_triangles_le e (W.U (Fin.last ell)) hsupport) hmax
    (sourceRandomFailureCoefficient_le_polynomial W j hj)
  exact hfailure.trans_lt (hTF t (by dsimp [T] at ht; omega))

end

end Erdos207
