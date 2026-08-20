/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.GallagherNormalizedMean

/-!
# Raw Gallagher log-free density inequality

This module inserts the rough-modulus amplifier into the common variable
zero-selection construction.  It deliberately leaves the elementary cutoff
size hypotheses explicit; later asymptotic modules discharge them with a
single parameter choice.
-/

open scoped BigOperators

noncomputable section

namespace Erdos48

open Complex
open BoundedGaps.Maynard

/-- One detector order on the explicit right hand side of Gallagher's
amplified density inequality. -/
noncomputable def gallagherRawDensityTerm
    (Q T N J j : ℕ) (W eta R : ℝ) : ℝ :=
  (variableDetectorNormalization eta J j ^ 2 *
      (2 * |gallagherWeight eta (j - 1) N| ^ 2)) *
        gallagherAmplifiedCutoffBandBound W
          (variableDetectorLowerCutoff 0 eta j) N +
    (2 * eta ^ 3 *
      normalizedGallagherDerivativeGammaCoefficient eta J (j - 1)) *
      gallagherAmplifiedCutoffEnergyBound W
        (variableDetectorLowerCutoff 0 eta j) N

/-- The same term, with the detector lower-cutoff parameter displayed. -/
noncomputable def gallagherRawDensityTermAt
    (Q T E N J j : ℕ) (W eta R : ℝ) : ℝ :=
  (variableDetectorNormalization eta J j ^ 2 *
      (2 * |gallagherWeight eta (j - 1) N| ^ 2)) *
        gallagherAmplifiedCutoffBandBound W
          (variableDetectorLowerCutoff E eta j) N +
    (2 * eta ^ 3 *
      normalizedGallagherDerivativeGammaCoefficient eta J (j - 1)) *
      gallagherAmplifiedCutoffEnergyBound W
        (variableDetectorLowerCutoff E eta j) N

/-- Complete raw Gallagher density estimate.  The hypotheses are precisely
the finite inequalities needed by the amplified cutoff mean for every
detector order selected by the zero-detection argument. -/
theorem exists_gallagher_rawDensity_parameters :
    ∃ κ D A : ℕ, 1 ≤ κ ∧ 1 ≤ D ∧ 37 ≤ A ∧
      ∀ (Q T Amp : ℕ), 2 ≤ Q →
        ∀ (eta W : ℝ), 0 < eta → eta ≤ 1 / 8 → 0 ≤ W →
          let E := D + κ
          let B := (Q : ℝ) * ((T : ℝ) + 2)
          let H₀ := Nat.ceil (1 + eta * Real.log B)
          let H := variableDetectorHeightDilation E * H₀
          let J := (D + κ) * H
          let delta := variableDetectorPropagationRadius J
          let R := variableZeroDetectorTailRadius J
          let N := zeroDetectorCutoff R eta
          let L := D * H + 1
          let Klocal := 32 * (Real.log 4 + 4) +
            (256 * (A : ℝ) / 3) * (eta * Real.log B)
          (∀ q ∈ Finset.Ioc 0 Q,
            W ≤ roughAmplifierCoefficient q Amp) →
          (∀ j ∈ Finset.Icc L J,
            2 ≤ variableDetectorLowerCutoff E eta j ∧
            variableDetectorLowerCutoff E eta j ≤ N ∧
            4 * ((T + 1) + 1) ≤ variableDetectorLowerCutoff E eta j ∧
            Q * Amp ≤ variableDetectorLowerCutoff E eta j ∧
            2 * (((T + 1) + 1) * (Q * Amp) ^ 2) ≤
              variableDetectorLowerCutoff E eta j ∧
            2 * (((T + 1) + 1) * Q ^ 2) ≤
              variableDetectorLowerCutoff E eta j) →
          W * ((primitiveHighZeroMass Q eta T : ℝ) *
                (delta * eta) * (1 / 16 : ℝ) ^ 2) ≤
            Klocal *
              ∑ j ∈ Finset.Icc L J,
                gallagherRawDensityTermAt Q (T + 1) E N J j W eta R := by
  obtain ⟨κ, D, A, hκ, hD, hA, hselection⟩ :=
    exists_variable_unweightedIntegral_parameters
  refine ⟨κ, D, A, hκ, hD, hA, ?_⟩
  intro Q T Amp hQ eta W heta heta8 hW
  dsimp only
  let E := D + κ
  let B : ℝ := (Q : ℝ) * ((T : ℝ) + 2)
  let H₀ : ℕ := Nat.ceil (1 + eta * Real.log B)
  let H : ℕ := variableDetectorHeightDilation E * H₀
  let J : ℕ := (D + κ) * H
  let delta : ℝ := variableDetectorPropagationRadius J
  let R : ℝ := variableZeroDetectorTailRadius J
  let N : ℕ := zeroDetectorCutoff R eta
  let L : ℕ := D * H + 1
  let Klocal : ℝ := 32 * (Real.log 4 + 4) +
    (256 * (A : ℝ) / 3) * (eta * Real.log B)
  intro hcoeff hcutoffs
  have hselected := hselection Q T hQ eta heta heta8
  have hB : (1 : ℝ) ≤ B := by
    dsimp [B]
    have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    have hT0 : (0 : ℝ) ≤ T := by positivity
    nlinarith
  have hH₀pos : 1 ≤ H₀ := by
    have harg : (1 : ℝ) ≤ 1 + eta * Real.log B := by
      have hlog : 0 ≤ Real.log B := Real.log_nonneg hB
      nlinarith [mul_nonneg heta.le hlog]
    have hcast : (1 : ℝ) ≤ (H₀ : ℕ) := by
      exact harg.trans (by
        simpa only [H₀] using Nat.le_ceil (1 + eta * Real.log B))
    exact_mod_cast hcast
  have hHpos : 1 ≤ H := by
    dsimp [H]
    exact Nat.mul_pos (variableDetectorHeightDilation_pos E) (by omega)
  have hKlocal : 0 ≤ Klocal := by
    dsimp [Klocal]
    have hlog : 0 ≤ Real.log B := Real.log_nonneg hB
    positivity
  have hterms :
      W * (∑ j ∈ Finset.Icc L J,
        ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
          unweightedPrimitiveNegativeDirichletMass Q
            (Finset.Ioc (variableDetectorLowerCutoff E eta j) N)
            (variableNormalizedDetectorCoefficient eta J j) u) ≤
        ∑ j ∈ Finset.Icc L J,
          gallagherRawDensityTermAt Q (T + 1) E N J j W eta R := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjLower : D * H + 1 ≤ j := by
      simpa only [L] using (Finset.mem_Icc.mp hj).1
    have hDH : 1 ≤ D * H := Nat.mul_pos (by omega) (by omega)
    have hj2 : 2 ≤ j := by omega
    obtain ⟨hY2, hYN, hheight, hrough, hroughConductor, hconductor⟩ :=
      hcutoffs j hj
    simpa only [gallagherRawDensityTermAt] using
      mul_intervalIntegral_unweightedPrimitiveNegativeDirichletMass_normalized_le_band
        Q Amp (variableDetectorLowerCutoff E eta j) N (T + 1) J j W
          heta hj2 hY2 hYN hW hcoeff hheight hrough
          hroughConductor hconductor
  calc
    W * ((primitiveHighZeroMass Q eta T : ℝ) *
          (delta * eta) * (1 / 16 : ℝ) ^ 2) ≤
      W * (Klocal *
        ∑ j ∈ Finset.Icc L J,
          ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
            unweightedPrimitiveNegativeDirichletMass Q
              (Finset.Ioc (variableDetectorLowerCutoff E eta j) N)
              (variableNormalizedDetectorCoefficient eta J j) u) :=
        mul_le_mul_of_nonneg_left hselected hW
    _ = Klocal * (W *
        ∑ j ∈ Finset.Icc L J,
          ∫ u in (0 : ℝ)..((T + 1 : ℕ) : ℝ),
            unweightedPrimitiveNegativeDirichletMass Q
              (Finset.Ioc (variableDetectorLowerCutoff E eta j) N)
              (variableNormalizedDetectorCoefficient eta J j) u) := by ring
    _ ≤ Klocal *
        ∑ j ∈ Finset.Icc L J,
          gallagherRawDensityTermAt Q (T + 1) E N J j W eta R :=
      mul_le_mul_of_nonneg_left hterms hKlocal
    _ = _ := by rfl

/-- At the natural amplifier endpoint `Q * (T + 2)`, the fourth-power
detector cutoff dominates every height, rough-support, and conductor square
required by the Gallagher mean. -/
theorem gallagher_globalProduct_cutoffs
    (Q T E j : ℕ) {eta : ℝ} (hQ : 2 ≤ Q) (heta : 0 < eta) :
    let B := (Q : ℝ) * ((T : ℝ) + 2)
    let H₀ := Nat.ceil (1 + eta * Real.log B)
    let H := variableDetectorHeightDilation E * H₀
    let D := 1
    let J := (E + 1) * H
    D * H + 1 ≤ j → j ≤ J →
      2 ≤ variableDetectorLowerCutoff E eta j ∧
      variableDetectorLowerCutoff E eta j ≤
        zeroDetectorCutoff (variableZeroDetectorTailRadius J) eta ∧
      4 * ((T + 1) + 1) ≤ variableDetectorLowerCutoff E eta j ∧
      Q * (Q * (T + 2)) ≤ variableDetectorLowerCutoff E eta j ∧
      2 * (((T + 1) + 1) * (Q * (Q * (T + 2))) ^ 2) ≤
        variableDetectorLowerCutoff E eta j ∧
      2 * (((T + 1) + 1) * Q ^ 2) ≤
        variableDetectorLowerCutoff E eta j := by
  dsimp only
  intro hjLower hjJ
  let b : ℕ := Q * (T + 2)
  let B : ℝ := (Q : ℝ) * ((T : ℝ) + 2)
  let H₀ : ℕ := Nat.ceil (1 + eta * Real.log B)
  let H : ℕ := variableDetectorHeightDilation E * H₀
  let J : ℕ := (E + 1) * H
  have hb2 : 2 ≤ b := by dsimp [b]; nlinarith
  have hB : (1 : ℝ) ≤ B := by
    dsimp [B]
    have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    have hT0 : (0 : ℝ) ≤ T := by positivity
    nlinarith
  have hYcompare : zeroDetectorLowerCutoff B ≤
      variableDetectorLowerCutoff E eta j := by
    apply zeroDetectorLowerCutoff_le_variableDetectorLowerCutoff
      (D := 1) (H₀ := H₀) (H := H)
    · omega
    · exact hB
    · exact heta
    · exact le_rfl
    · exact le_rfl
    · simpa only [H] using hjLower
  have hcast : (b : ℝ) = B := by
    dsimp [b, B]
    push_cast
    ring
  have hpow : b ^ 4 ≤ zeroDetectorLowerCutoff B := by
    rw [← hcast]
    exact pow_four_le_zeroDetectorLowerCutoff b hb2
  have hbig : b ^ 4 ≤ variableDetectorLowerCutoff E eta j :=
    hpow.trans hYcompare
  have hmain :
      2 * (((T + 1) + 1) * (Q * (Q * (T + 2))) ^ 2) ≤ b ^ 4 := by
    have hU : 2 ≤ T + 2 := by omega
    have hmul := Nat.mul_le_mul_right (Q ^ 4 * (T + 2) ^ 3) hU
    calc
      2 * (((T + 1) + 1) * (Q * (Q * (T + 2))) ^ 2) =
          2 * (Q ^ 4 * (T + 2) ^ 3) := by ring
      _ ≤ (T + 2) * (Q ^ 4 * (T + 2) ^ 3) := hmul
      _ = b ^ 4 := by dsimp [b]; ring
  have hheight : 4 * ((T + 1) + 1) ≤ b ^ 4 := by
    have hx2 : 2 ≤ (Q * (Q * (T + 2))) ^ 2 := by
      have hx : 2 ≤ Q * (Q * (T + 2)) := by
        calc
          2 ≤ Q := hQ
          _ = Q * 1 := by omega
          _ ≤ Q * (Q * (T + 2)) :=
            Nat.mul_le_mul_left Q (by omega)
      exact hx.trans (Nat.le_pow (by omega : 0 < 2))
    calc
      4 * ((T + 1) + 1) ≤
          2 * (((T + 1) + 1) * (Q * (Q * (T + 2))) ^ 2) := by
        have hm := Nat.mul_le_mul_left (2 * ((T + 1) + 1)) hx2
        convert hm using 1 <;> ring
      _ ≤ b ^ 4 := hmain
  have hrough : Q * (Q * (T + 2)) ≤ b ^ 4 := by
    have hxpos : 0 < Q * (Q * (T + 2)) := by
      exact Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))
    have hxsq : Q * (Q * (T + 2)) ≤ (Q * (Q * (T + 2))) ^ 2 :=
      Nat.le_pow (by omega : 0 < 2)
    have hone : 1 ≤ 2 * ((T + 1) + 1) := by omega
    calc
      Q * (Q * (T + 2)) ≤
          (Q * (Q * (T + 2))) ^ 2 := hxsq
      _ ≤ 2 * (((T + 1) + 1) * (Q * (Q * (T + 2))) ^ 2) := by
        have hm := Nat.mul_le_mul_right ((Q * (Q * (T + 2))) ^ 2) hone
        convert hm using 1 <;> ring
      _ ≤ b ^ 4 := hmain
  have hconductor : 2 * (((T + 1) + 1) * Q ^ 2) ≤ b ^ 4 := by
    calc
      2 * (((T + 1) + 1) * Q ^ 2) ≤
          2 * (((T + 1) + 1) * (Q * (Q * (T + 2))) ^ 2) := by
        have hfac : Q ≤ Q * (Q * (T + 2)) := by
          calc
            Q = Q * 1 := by omega
            _ ≤ Q * (Q * (T + 2)) := Nat.mul_le_mul_left Q (by omega)
        simpa only [mul_assoc] using
          Nat.mul_le_mul_left (2 * ((T + 1) + 1))
            (Nat.pow_le_pow_left hfac 2)
      _ ≤ b ^ 4 := hmain
  refine ⟨?_, ?_, hheight.trans hbig, hrough.trans hbig,
    hmain.trans hbig, hconductor.trans hbig⟩
  · exact hb2.trans (Nat.le_pow (by omega : 0 < 4) |>.trans hbig)
  · exact variableDetectorLowerCutoff_le_zeroDetectorCutoff hjJ heta

/-- The raw density theorem with the canonical integral amplifier
`Amp = Q * (T + 2)` and its half-logarithmic coefficient. -/
theorem exists_gallagher_rawDensity_globalProduct_parameters :
    ∃ κ D A : ℕ, ∃ K C : ℝ,
      1 ≤ κ ∧ 1 ≤ D ∧ 37 ≤ A ∧ 0 < K ∧
      ∀ (Q T : ℕ), 2 ≤ Q →
        ∀ eta : ℝ, 0 < eta → eta ≤ 1 / 8 →
          let E := D + κ
          let B := (Q : ℝ) * ((T : ℝ) + 2)
          let Amp := Q * (T + 2)
          let W := Real.log Amp / 2
          let H₀ := Nat.ceil (1 + eta * Real.log B)
          let H := variableDetectorHeightDilation E * H₀
          let J := (D + κ) * H
          let delta := variableDetectorPropagationRadius J
          let R := variableZeroDetectorTailRadius J
          let N := zeroDetectorCutoff R eta
          let L := D * H + 1
          let Klocal := 32 * (Real.log 4 + 4) +
            (256 * (A : ℝ) / 3) * (eta * Real.log B)
          2 ≤ Real.log Amp →
          20 * (K + (Real.log (Real.log Amp) + C + 2) + Real.log 2) ≤
            Real.log Amp →
          W * ((primitiveHighZeroMass Q eta T : ℝ) *
                (delta * eta) * (1 / 16 : ℝ) ^ 2) ≤
            Klocal *
              ∑ j ∈ Finset.Icc L J,
                gallagherRawDensityTermAt Q (T + 1) E N J j W eta R := by
  obtain ⟨κ, D, A, hκ, hD, hA, hraw⟩ :=
    exists_gallagher_rawDensity_parameters
  obtain ⟨K, C, hK, hcoeffUniform⟩ :=
    exists_uniform_roughAmplifierCoefficient_half_log_lower_up_to
  refine ⟨κ, D, A, K, C, hκ, hD, hA, hK, ?_⟩
  intro Q T hQ eta heta heta8
  dsimp only
  intro hlogAmp hdom
  let E := D + κ
  let B : ℝ := (Q : ℝ) * ((T : ℝ) + 2)
  let Amp : ℕ := Q * (T + 2)
  let W : ℝ := Real.log Amp / 2
  let H₀ : ℕ := Nat.ceil (1 + eta * Real.log B)
  let H : ℕ := variableDetectorHeightDilation E * H₀
  let J : ℕ := (D + κ) * H
  let R : ℝ := variableZeroDetectorTailRadius J
  let N : ℕ := zeroDetectorCutoff R eta
  let L : ℕ := D * H + 1
  have hW : 0 ≤ W := by dsimp [W]; linarith
  have hQAmp : Q < Amp := by
    dsimp [Amp]
    have hQpos : 0 < Q := by omega
    nlinarith
  have hcoeff : ∀ q ∈ Finset.Ioc 0 Q,
      W ≤ roughAmplifierCoefficient q Amp := by
    simpa only [W] using hcoeffUniform hQAmp hlogAmp hdom
  have hB : (1 : ℝ) ≤ B := by
    dsimp [B]
    have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    have hT0 : (0 : ℝ) ≤ T := by positivity
    nlinarith
  have hH₀pos : 1 ≤ H₀ := by
    have harg : (1 : ℝ) ≤ 1 + eta * Real.log B := by
      have hlog : 0 ≤ Real.log B := Real.log_nonneg hB
      nlinarith [mul_nonneg heta.le hlog]
    have hcast : (1 : ℝ) ≤ (H₀ : ℕ) := by
      exact harg.trans (by
        simpa only [H₀] using Nat.le_ceil (1 + eta * Real.log B))
    exact_mod_cast hcast
  have hHpos : 1 ≤ H := by
    dsimp [H]
    exact Nat.mul_pos (variableDetectorHeightDilation_pos E) (by omega)
  apply hraw Q T Amp hQ eta W heta heta8 hW hcoeff
  intro j hj
  have hjLower : D * H + 1 ≤ j := by
    simpa only [L] using (Finset.mem_Icc.mp hj).1
  have hjJ : j ≤ J := (Finset.mem_Icc.mp hj).2
  let b : ℕ := Q * (T + 2)
  have hb2 : 2 ≤ b := by dsimp [b]; nlinarith
  have hYcompare : zeroDetectorLowerCutoff B ≤
      variableDetectorLowerCutoff E eta j := by
    exact zeroDetectorLowerCutoff_le_variableDetectorLowerCutoff
      hD hB heta (by exact le_rfl) (by exact le_rfl) hjLower
  have hcast : (b : ℝ) = B := by
    dsimp [b, B]
    push_cast
    ring
  have hpow : b ^ 4 ≤ zeroDetectorLowerCutoff B := by
    rw [← hcast]
    exact pow_four_le_zeroDetectorLowerCutoff b hb2
  have hbig : b ^ 4 ≤ variableDetectorLowerCutoff E eta j :=
    hpow.trans hYcompare
  have hmain :
      2 * (((T + 1) + 1) * (Q * Amp) ^ 2) ≤ b ^ 4 := by
    have hU : 2 ≤ T + 2 := by omega
    have hmul := Nat.mul_le_mul_right (Q ^ 4 * (T + 2) ^ 3) hU
    calc
      2 * (((T + 1) + 1) * (Q * Amp) ^ 2) =
          2 * (Q ^ 4 * (T + 2) ^ 3) := by dsimp [Amp]; ring
      _ ≤ (T + 2) * (Q ^ 4 * (T + 2) ^ 3) := hmul
      _ = b ^ 4 := by dsimp [b]; ring
  have hheight : 4 * ((T + 1) + 1) ≤ b ^ 4 := by
    have hx2 : 2 ≤ (Q * Amp) ^ 2 := by
      have hAmpPos : 0 < Amp := by dsimp [Amp]; positivity
      have hx : 2 ≤ Q * Amp := by
        calc
          2 ≤ Q := hQ
          _ = Q * 1 := by omega
          _ ≤ Q * Amp := Nat.mul_le_mul_left Q hAmpPos
      exact hx.trans (Nat.le_pow (by omega : 0 < 2))
    calc
      4 * ((T + 1) + 1) ≤
          2 * (((T + 1) + 1) * (Q * Amp) ^ 2) := by
        have hm := Nat.mul_le_mul_left (2 * ((T + 1) + 1)) hx2
        convert hm using 1 <;> ring
      _ ≤ b ^ 4 := hmain
  have hrough : Q * Amp ≤ b ^ 4 := by
    have hxpos : 0 < Q * Amp := by
      exact Nat.mul_pos (by omega) (by dsimp [Amp]; positivity)
    have hxsq : Q * Amp ≤ (Q * Amp) ^ 2 :=
      Nat.le_pow (by omega : 0 < 2)
    have hone : 1 ≤ 2 * ((T + 1) + 1) := by omega
    calc
      Q * Amp ≤ (Q * Amp) ^ 2 := hxsq
      _ ≤ 2 * (((T + 1) + 1) * (Q * Amp) ^ 2) := by
        have hm := Nat.mul_le_mul_right ((Q * Amp) ^ 2) hone
        convert hm using 1 <;> ring
      _ ≤ b ^ 4 := hmain
  have hconductor : 2 * (((T + 1) + 1) * Q ^ 2) ≤ b ^ 4 := by
    calc
      2 * (((T + 1) + 1) * Q ^ 2) ≤
          2 * (((T + 1) + 1) * (Q * Amp) ^ 2) := by
        have hfac : Q ≤ Q * Amp := by
          calc
            Q = Q * 1 := by omega
            _ ≤ Q * Amp := Nat.mul_le_mul_left Q (by
              dsimp [Amp]
              exact Nat.mul_pos (by omega) (by omega))
        simpa only [mul_assoc] using
          Nat.mul_le_mul_left (2 * ((T + 1) + 1))
            (Nat.pow_le_pow_left hfac 2)
      _ ≤ b ^ 4 := hmain
  refine ⟨?_, variableDetectorLowerCutoff_le_zeroDetectorCutoff hjJ heta,
    hheight.trans hbig, hrough.trans hbig, hmain.trans hbig,
    hconductor.trans hbig⟩
  exact hb2.trans (Nat.le_pow (by omega : 0 < 4) |>.trans hbig)

end Erdos48

end
