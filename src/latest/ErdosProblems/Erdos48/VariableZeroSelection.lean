/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.VariableBandLimitedDetector
import ErdosProblems.Erdos48.DetectorLowerCutoffGrowth
import ErdosProblems.Erdos48.ZeroMultiplicityCover

/-!
# Global selection for the variable-order detector

The local logarithmic height is dilated before applying the pointwise
detector.  This makes every order-dependent lower endpoint dominate the
fixed fourth-power cutoff used by the optimized hybrid large sieve.
-/

namespace Erdos48

open Complex Metric Set
open BoundedGaps.Maynard

noncomputable section

/-- Fixed dilation which converts the order-dependent cutoff into a large
power of the global conductor-height parameter. -/
def variableDetectorHeightDilation (E : ℕ) : ℕ :=
  16 * variableDetectorDilution E

theorem variableDetectorHeightDilation_pos (E : ℕ) :
    0 < variableDetectorHeightDilation E := by
  unfold variableDetectorHeightDilation
  exact Nat.mul_pos (by norm_num) (variableDetectorDilution_pos E)

theorem highZero_dist_variable_detector_center_le
    {rho : ℂ} {t eta : ℝ}
    (hrelo : 1 - eta ≤ rho.re) (hrehi : rho.re ≤ 1)
    (hrhoim : rho.im = t) (heta : 0 < eta) :
    dist rho (((1 + eta : ℝ) : ℂ) + t * I) ≤ 2 * eta := by
  rw [Complex.dist_eq]
  have heq :
      rho - (((1 + eta : ℝ) : ℂ) + t * I) =
        ((rho.re - (1 + eta) : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simp [hrhoim]
  rw [heq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (by linarith)]
  linarith

/-- At the dilated height, every detected order has a lower endpoint at
least as large as the fixed cutoff `2^floor(8 log B)`. -/
theorem zeroDetectorLowerCutoff_le_variableDetectorLowerCutoff
    {D E H₀ H j : ℕ} {B eta : ℝ}
    (hD : 1 ≤ D) (hB : 1 ≤ B) (heta : 0 < eta)
    (hH₀ : Nat.ceil (1 + eta * Real.log B) ≤ H₀)
    (hH : variableDetectorHeightDilation E * H₀ ≤ H)
    (hj : D * H + 1 ≤ j) :
    zeroDetectorLowerCutoff B ≤ variableDetectorLowerCutoff E eta j := by
  let A : ℕ := variableDetectorDilution E
  have hA : 0 < A := by simpa only [A] using variableDetectorDilution_pos E
  have hlog : 0 ≤ Real.log B := Real.log_nonneg hB
  have hceil : 1 + eta * Real.log B ≤
      (Nat.ceil (1 + eta * Real.log B) : ℕ) := Nat.le_ceil _
  have hH₀real : eta * Real.log B ≤ (H₀ : ℝ) := by
    have hceilCast :
        (Nat.ceil (1 + eta * Real.log B) : ℝ) ≤ (H₀ : ℝ) := by
      exact_mod_cast hH₀
    linarith [hceil.trans hceilCast]
  have hHj : variableDetectorHeightDilation E * H₀ ≤ j := by
    calc
      variableDetectorHeightDilation E * H₀ ≤ H := hH
      _ ≤ D * H := by
        simpa only [one_mul] using Nat.mul_le_mul_right H hD
      _ ≤ j := by omega
  have hquot : 8 * Real.log B ≤
      (j : ℝ) / ((A : ℝ) * eta) := by
    rw [le_div_iff₀ (mul_pos (by exact_mod_cast hA) heta)]
    calc
      8 * Real.log B * ((A : ℝ) * eta) ≤
          16 * ((A : ℝ) * (eta * Real.log B)) := by
        have hnonneg : 0 ≤ (A : ℝ) * (eta * Real.log B) := by positivity
        nlinarith
      _ ≤ 16 * ((A : ℝ) * (H₀ : ℝ)) := by gcongr
      _ = (variableDetectorHeightDilation E * H₀ : ℕ) := by
        dsimp [variableDetectorHeightDilation, A]
        push_cast
        ring
      _ ≤ (j : ℝ) := by exact_mod_cast hHj
  have hfloor : zeroDetectorLowerLog B ≤
      variableDetectorLowerLog E eta j := by
    unfold zeroDetectorLowerLog variableDetectorLowerLog
    exact Nat.floor_mono hquot
  unfold zeroDetectorLowerCutoff variableDetectorLowerCutoff
  exact Nat.pow_le_pow_right (by omega) hfloor

/-- A maximal separated selection in a global rectangle, carrying the
variable order, its two cutoff comparisons, and a uniform unscaled lower
bound. -/
theorem exists_variable_detected_zero_selection :
    ∃ κ D : ℕ, 1 ≤ κ ∧ 1 ≤ D ∧
      ∀ (Q T : ℕ), 2 ≤ Q →
        ∀ eta : ℝ, 0 < eta → eta ≤ 1 / 8 →
          let E := D + κ
          let B := (Q : ℝ) * ((T : ℝ) + 2)
          let H₀ := Nat.ceil (1 + eta * Real.log B)
          let H := variableDetectorHeightDilation E * H₀
          let J := (D + κ) * H
          let delta := variableDetectorPropagationRadius J
          let R := variableZeroDetectorTailRadius J
          let N := zeroDetectorCutoff R eta
          ∀ (q : ℕ) [NeZero q], ∀ (hq : 1 < q), q ≤ Q →
            ∀ (chi : DirichletCharacter ℂ q), ∀ (hchi : chi.IsPrimitive),
              ∃ S : Finset ℝ, ∃ order : ℝ → ℕ,
                S ⊆ highZeroOrdinates hq chi hchi eta T ∧
                (∀ x ∈ S, ∀ y ∈ S, x ≠ y →
                  2 * delta * eta < dist x y) ∧
                (∀ x ∈ highZeroOrdinates hq chi hchi eta T,
                  ∃ y ∈ S, dist x y ≤ 2 * delta * eta) ∧
                (∀ t ∈ S,
                  D * H + 1 ≤ order t ∧ order t ≤ J ∧
                  zeroDetectorLowerCutoff B ≤
                    variableDetectorLowerCutoff E eta (order t) ∧
                  variableDetectorLowerCutoff E eta (order t) ≤ N ∧
                  ∀ u : ℝ, |u - t| ≤ delta * eta →
                    ((order t - 1).factorial : ℝ) / 16 <
                        ((578 : ℝ) ^ J / 2) * (2 * eta) ^ (order t) *
                          ‖variableBandZeroDetectorPolynomial chi E eta
                            (order t) N u‖ ∧
                    1 / (8 * (578 : ℝ) ^ J) <
                        ‖variableBandZeroDetectorPolynomial chi E eta
                          (order t) N u‖) := by
  obtain ⟨κ, D, hκ, hD, hdetector⟩ :=
    exists_variable_propagated_band_series_detector
  refine ⟨κ, D, hκ, hD, ?_⟩
  intro Q T hQ eta heta heta8
  dsimp only
  let E := D + κ
  let B : ℝ := (Q : ℝ) * ((T : ℝ) + 2)
  let H₀ : ℕ := Nat.ceil (1 + eta * Real.log B)
  let H : ℕ := variableDetectorHeightDilation E * H₀
  let J : ℕ := (D + κ) * H
  let delta : ℝ := variableDetectorPropagationRadius J
  let R : ℝ := variableZeroDetectorTailRadius J
  let N : ℕ := zeroDetectorCutoff R eta
  intro q _ hq hqQ chi hchi
  have hB : (1 : ℝ) ≤ B := by
    dsimp [B]
    have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    have hTnonneg : (0 : ℝ) ≤ T := by positivity
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
  have hJpos : 1 ≤ J := by
    dsimp [J]
    exact Nat.mul_pos (by omega) (by omega)
  have hdelta : 0 < delta := by
    simpa only [delta] using variableDetectorPropagationRadius_pos hJpos
  have hdelta1 : delta ≤ 1 := by
    simpa only [delta] using variableDetectorPropagationRadius_le_one hJpos
  obtain ⟨S, hSsub, hsep, hcover⟩ :=
    exists_separated_highZeroOrdinates hq chi hchi eta T
      (2 * delta * eta) (by positivity)
  have hdata : ∀ t ∈ S, ∃ j : ℕ,
      D * H + 1 ≤ j ∧ j ≤ J ∧
      zeroDetectorLowerCutoff B ≤ variableDetectorLowerCutoff E eta j ∧
      variableDetectorLowerCutoff E eta j ≤ N ∧
      ∀ u : ℝ, |u - t| ≤ delta * eta →
        ((j - 1).factorial : ℝ) / 16 <
            ((578 : ℝ) ^ J / 2) * (2 * eta) ^ j *
              ‖variableBandZeroDetectorPolynomial chi E eta j N u‖ ∧
        1 / (8 * (578 : ℝ) ^ J) <
            ‖variableBandZeroDetectorPolynomial chi E eta j N u‖ := by
    intro t ht
    have htOrd := hSsub ht
    have hT0 : (0 : ℝ) ≤ T := by positivity
    have heta1 : eta ≤ 1 := by linarith
    obtain ⟨rho, hzero, hrelo, hrehi, hrhoim, ht0, htT⟩ :=
      (mem_highZeroOrdinates_iff hq chi hchi heta1 hT0 t).mp htOrd
    have hqcast : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
    have hinside : (0 : ℝ) < (q : ℝ) * (|t| + 2) := by positivity
    have hprod : (q : ℝ) * (|t| + 2) ≤ B := by
      rw [abs_of_nonneg ht0]
      dsimp [B]
      exact mul_le_mul hqcast (by exact_mod_cast (show t + 2 ≤ T + 2 by linarith))
        (by positivity) (by positivity)
    have hlog : Real.log ((q : ℝ) * (|t| + 2)) ≤ Real.log B :=
      Real.log_le_log hinside hprod
    have hheight₀ : variableDetectorHeight q t eta ≤ H₀ := by
      unfold variableDetectorHeight
      dsimp [H₀]
      apply Nat.ceil_mono
      simpa only [add_comm] using
        add_le_add_left (mul_le_mul_of_nonneg_left hlog heta.le) 1
    have hheight : variableDetectorHeight q t eta ≤ H := by
      exact hheight₀.trans <| by
        dsimp [H]
        calc
          H₀ = 1 * H₀ := by omega
          _ ≤ variableDetectorHeightDilation E * H₀ :=
            Nat.mul_le_mul_right H₀
              (variableDetectorHeightDilation_pos E).nat_succ_le
    have hrho : dist rho (((1 + eta : ℝ) : ℂ) + t * I) ≤ 2 * eta :=
      highZero_dist_variable_detector_center_le hrelo hrehi hrhoim heta
    obtain ⟨j, hj, hKH, hjJ, hcut, hlarge⟩ :=
      hdetector q hq chi hchi t eta heta heta8 rho hzero hrho
        H J hheight (by exact le_rfl)
    let Z := smallDiskZeroFinsupp hq chi hchi t eta
    let K := Z.support.card
    let M := D * H
    have hjLocal : j ∈ Finset.Icc (M + 1) (M + K) := by
      simpa only [Z, K, M] using hj
    have hK : 1 ≤ K := by
      have hMK : M + 1 ≤ M + K :=
        (Finset.mem_Icc.mp hjLocal).1.trans (Finset.mem_Icc.mp hjLocal).2
      exact Nat.add_le_add_iff_left.mp hMK
    have hjTwo : 2 ≤ j := by
      have hMpos : 1 ≤ M := by
        dsimp [M]
        exact Nat.mul_pos (by omega) (by omega)
      exact (Nat.succ_le_succ hMpos).trans
        (Finset.mem_Icc.mp hjLocal).1
    have hKJ : K ≤ J := by
      calc
        K ≤ κ * H := by simpa only [Z, K] using hKH
        _ ≤ (D + κ) * H := by gcongr <;> omega
        _ = J := by rfl
    have hMJ : M ≤ J := by
      dsimp [M, J]
      gcongr <;> omega
    have hloss := turanSecondLoss_le_orderEnvelope hK hKJ hMJ
    have hpow : (2 * eta) ^ j ≤ (1 : ℝ) :=
      pow_le_one₀ (by positivity) (by linarith)
    have hscale : turanSecondLoss K M * (2 * eta) ^ j ≤
        (578 : ℝ) ^ J / 2 := by
      calc
        turanSecondLoss K M * (2 * eta) ^ j ≤
            ((578 : ℝ) ^ J / 2) * 1 := by gcongr
        _ = (578 : ℝ) ^ J / 2 := mul_one _
    have hfac : (1 : ℝ) ≤ (j - 1).factorial := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hfixedCut := zeroDetectorLowerCutoff_le_variableDetectorLowerCutoff
      (D := D) (E := E) (H₀ := H₀) (H := H) (j := j)
      (B := B) (eta := eta) hD hB heta le_rfl le_rfl
        (Finset.mem_Icc.mp hjLocal).1
    refine ⟨j, (Finset.mem_Icc.mp hjLocal).1, hjJ, hfixedCut, hcut, ?_⟩
    intro u hu
    have hlargeU := hlarge u (by simpa only [delta] using hu)
    have hscaledLoss :
        turanSecondLoss K M * (2 * eta) ^ j *
            ‖variableBandZeroDetectorPolynomial chi E eta j N u‖ ≤
          ((578 : ℝ) ^ J / 2) * (2 * eta) ^ j *
            ‖variableBandZeroDetectorPolynomial chi E eta j N u‖ := by
      gcongr
    have hscaledUpper := mul_le_mul_of_nonneg_right hscale
      (norm_nonneg (variableBandZeroDetectorPolynomial chi E eta j N u))
    have hfacDiv : (1 / 16 : ℝ) ≤
        ((j - 1).factorial : ℝ) / 16 := by nlinarith
    have hmid : (1 / 16 : ℝ) <
        ((578 : ℝ) ^ J / 2) *
          ‖variableBandZeroDetectorPolynomial chi E eta j N u‖ :=
      hfacDiv.trans_lt (hlargeU.trans_le hscaledUpper)
    have hp578 : 0 < (578 : ℝ) ^ J := by positivity
    refine ⟨hlargeU.trans_le hscaledLoss, ?_⟩
    rw [div_lt_iff₀ (mul_pos (by norm_num) hp578)]
    nlinarith
  let order : ℝ → ℕ := fun t ↦
    if ht : t ∈ S then Classical.choose (hdata t ht) else 2
  have horder : ∀ t ∈ S,
      D * H + 1 ≤ order t ∧ order t ≤ J ∧
      zeroDetectorLowerCutoff B ≤
        variableDetectorLowerCutoff E eta (order t) ∧
      variableDetectorLowerCutoff E eta (order t) ≤ N ∧
      ∀ u : ℝ, |u - t| ≤ delta * eta →
        ((order t - 1).factorial : ℝ) / 16 <
            ((578 : ℝ) ^ J / 2) * (2 * eta) ^ (order t) *
              ‖variableBandZeroDetectorPolynomial chi E eta (order t) N u‖ ∧
        1 / (8 * (578 : ℝ) ^ J) <
            ‖variableBandZeroDetectorPolynomial chi E eta (order t) N u‖ := by
    intro t ht
    rw [show order t = Classical.choose (hdata t ht) by simp [order, ht]]
    exact Classical.choose_spec (hdata t ht)
  exact ⟨S, order, hSsub, hsep, hcover, horder⟩

end

end Erdos48
