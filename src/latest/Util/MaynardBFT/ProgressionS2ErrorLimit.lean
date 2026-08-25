import Util.MaynardBFT.ProgressionS2
import Util.MaynardBFT.ProgressionErrorBound
import Util.MaynardBFT.ProgressionCutoff
import ErdosProblems.Erdos6.GenericS2ErrorLimit

/-! # Vanishing distribution error for a fixed progression modulus -/

namespace MaynardBFT

open Filter Erdos6.Maynard BoundedGaps.Maynard
open scoped BigOperators

theorem exists_progressionS2Error_envelope {q : ℕ} (hq : 0 < q)
    (H : Finset ℕ) (hH : H.Nonempty) (v : ℕ → ℕ)
    (F : (H → ℝ) → ℝ) (B : ℝ) (hB : 0 ≤ B) (hF : ∀ x, |F x| ≤ B)
    (hv : ∀ᶠ N : ℕ in atTop, ∀ h ∈ H, Nat.Coprime (v N + h) (progressionModulus q N))
    {theta delta A : ℝ} (htheta : 0 ≤ theta) (hthetaHalf : theta < 1 / 2)
    (hdelta : 0 < delta) (hlevel : hasPrimeLevel theta) (hA : 0 < A) :
    ∃ C : ℝ, ∃ X₀ : ℕ, PrimeLevelWitness theta A C X₀ ∧
      ∀ᶠ N : ℕ in atTop,
        |progressionS2Error H q (theta / 2 - delta) v F N| ≤
          tupleMaynardS2TauErrorEnvelope H (theta / 2 - delta) B A C N := by
  obtain ⟨C, X₀, hw⟩ := hasPrimeLevel_exists_witness hlevel hA
  refine ⟨C, X₀, hw, ?_⟩
  filter_upwards [eventually_progression_coverage H q,
    eventually_tupleMaynardS2_endpoint_thresholds H X₀,
    eventually_progression_endpoint_cutoff q htheta hdelta, hv,
    eventually_ge_atTop 1] with N hcoverage hthresholds hcutoffs hvN hN
  let alpha := theta / 2 - delta
  let R := maynardRadius alpha N
  let W := maynardModulus N
  let D := progressionSupport H q alpha N
  let lambda := progressionCoefficient H q alpha F N
  let L := tupleMaynardSharpCoefficientEnvelope H alpha B N
  have hW : Squarefree W := BoundedGaps.Maynard.squarefree_primorial _
  have hD : ∀ d ∈ D, IsMaynardDivisorTuple H R (q * W) d :=
    progressionSupport_valid H q alpha N
  have hL : 0 ≤ L := by dsimp [L, tupleMaynardSharpCoefficientEnvelope]; positivity
  have hbound : ∀ d ∈ D, |lambda d| ≤ L := by
    intro d hd
    exact abs_maynardCoefficient_le_sharp_log H R (q * W) F d B hB hF hH hd
  have hcutLower (h : H) : q * (W * R * R) ≤ modulusCutoff theta (N + h.1 - 1) :=
    hcutoffs h.1
  have hcutUpper (h : H) : q * (W * R * R) ≤ modulusCutoff theta (2 * N + h.1 - 1) := by
    simpa only [show N + (N + h.1) - 1 = 2 * N + h.1 - 1 by omega] using
      hcutoffs (N + h.1)
  have hsizeLower (h : H) : q * (W * R * R) ≤ (N + h.1 - 1) + 1 := by
    have hx := (hthresholds h).1
    have hx₀ := hw.2.1
    exact (hcutLower h).trans
      ((modulusCutoff_le_self (by omega) (by linarith : theta ≤ 1)).trans (Nat.le_succ _))
  have hsizeUpper (h : H) : q * (W * R * R) ≤ (2 * N + h.1 - 1) + 1 := by
    have hx := (hthresholds h).2
    have hx₀ := hw.2.1
    exact (hcutUpper h).trans
      ((modulusCutoff_le_self (by omega) (by linarith : theta ≤ 1)).trans (Nat.le_succ _))
  have herr := progressionRestrictedErrorBound hw hq hH hW hD hcoverage hvN
    lambda L (by omega) hL hbound
    (fun h => (hthresholds h).2) (fun h => (hthresholds h).1)
    hcutUpper hcutLower hsizeUpper hsizeLower
  simpa only [progressionS2Error, tupleMaynardS2TauErrorEnvelope,
    D, R, W, lambda, L, alpha, progressionModulus] using herr

theorem tendsto_normalized_progressionS2Error_zero {q : ℕ} (hq : 0 < q)
    (H : Finset ℕ) (hH : H.Nonempty) (v : ℕ → ℕ)
    (F : (H → ℝ) → ℝ) (B : ℝ) (hB : 0 ≤ B) (hF : ∀ x, |F x| ≤ B)
    (hv : ∀ᶠ N : ℕ in atTop, ∀ h ∈ H, Nat.Coprime (v N + h) (progressionModulus q N))
    {theta delta : ℝ} (htheta : 0 < theta) (hthetaHalf : theta < 1 / 2)
    (hdelta : 0 < delta) (hdeltaTheta : delta < theta / 2)
    (hlevel : hasPrimeLevel theta) :
    Tendsto (fun N : ℕ =>
      progressionS2Error H q (theta / 2 - delta) v F N /
        tupleMaynardScale H (theta / 2 - delta) N) atTop (nhds 0) := by
  let A : ℝ := ((((3 * Fintype.card H) ^ 2 + 4 * (Fintype.card H) ^ 2 +
    3 * (Fintype.card H + 1) + 2) * 2 : ℕ) : ℝ)
  have hA : 0 < A := by
    dsimp [A]
    positivity
  obtain ⟨C, X₀, hw, hbound⟩ := exists_progressionS2Error_envelope hq
    H hH v F B hB hF hv htheta.le hthetaHalf hdelta hlevel hA
  have henv : Tendsto (fun N : ℕ =>
      tupleMaynardS2TauErrorEnvelope H (theta / 2 - delta) B A C N /
        tupleMaynardScale H (theta / 2 - delta) N) atTop (nhds 0) :=
    tendsto_tupleMaynardS2TauErrorEnvelope_div_scale H
      (B := B) htheta hthetaHalf hdelta hdeltaTheta hw.1
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_ henv
  filter_upwards [hbound, eventually_tupleMaynardScale_pos
    (H := H) (sub_pos.mpr hdeltaTheta)] with N hbound hscale
  rw [abs_div, abs_of_pos hscale]
  exact div_le_div_of_nonneg_right hbound hscale.le

end MaynardBFT
