import Util.MaynardTao.BFT.ProgressionSupport
import ErdosProblems.Erdos6.GenericS1

/-! # Maynard weights with an additional fixed progression modulus -/

namespace MaynardBFT

open Filter Erdos6.Maynard BoundedGaps.Maynard
open scoped BigOperators

noncomputable section

def progressionModulus (q N : ℕ) : ℕ := q * maynardModulus N

def progressionSupport (H : Finset ℕ) (q : ℕ) (alpha : ℝ) (N : ℕ) :
    Finset (H → ℕ) :=
  maynardDivisorTupleSupport H (maynardRadius alpha N) (progressionModulus q N)

def progressionCoefficient (H : Finset ℕ) (q : ℕ) (alpha : ℝ)
    (F : (H → ℝ) → ℝ) (N : ℕ) : (H → ℕ) → ℝ :=
  maynardCoefficient H (maynardRadius alpha N) (progressionModulus q N) F

def progressionWeight (H : Finset ℕ) (q : ℕ) (alpha : ℝ)
    (v : ℕ → ℕ) (F : (H → ℝ) → ℝ) (N : ℕ) : ℕ → ℝ :=
  preSievedSquareDivisorWeight H (progressionSupport H q alpha N)
    (progressionCoefficient H q alpha F N) (v N) (progressionModulus q N)

theorem progressionSupport_valid (H : Finset ℕ) (q : ℕ) (alpha : ℝ) (N : ℕ) :
    ∀ d ∈ progressionSupport H q alpha N,
      IsMaynardDivisorTuple H (maynardRadius alpha N) (progressionModulus q N) d :=
  fun _ hd => isMaynardDivisorTuple_of_mem_support hd

theorem progressionModulus_pos {q : ℕ} (hq : 0 < q) (N : ℕ) :
    0 < progressionModulus q N := mul_pos hq (primorial_pos _)

theorem eventually_progression_support_eq {q : ℕ} (hq : 0 < q)
    (H : Finset ℕ) (alpha : ℝ) :
    ∀ᶠ N : ℕ in atTop, progressionSupport H q alpha N = tupleMaynardSupport H alpha N := by
  filter_upwards [tendsto_shifted_tripleLogCutoff.eventually (eventually_ge_atTop q)]
    with N hN
  exact maynardDivisorTupleSupport_mul_primorial hq hN H _

theorem eventually_progression_coefficient_eq {q : ℕ} (hq : 0 < q)
    (H : Finset ℕ) (alpha : ℝ) (F : (H → ℝ) → ℝ) :
    ∀ᶠ N : ℕ in atTop,
      progressionCoefficient H q alpha F N = tupleMaynardCoefficient H alpha F N := by
  filter_upwards [tendsto_shifted_tripleLogCutoff.eventually (eventually_ge_atTop q)]
    with N hN
  exact maynardCoefficient_mul_primorial hq hN H _ F

theorem eventually_progression_coverage (H : Finset ℕ) (q : ℕ) :
    ∀ᶠ N : ℕ in atTop, CoversShiftDifferencePrimes H (progressionModulus q N) := by
  filter_upwards [eventually_tupleMaynard_coverage H] with N hN
  intro a b hab p hp hpd
  exact (hN hab p hp hpd).trans (Nat.dvd_mul_left _ _)

def progressionS1Main (H : Finset ℕ) (q : ℕ) (alpha : ℝ)
    (F : (H → ℝ) → ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) / progressionModulus q N *
    compatibleDivisorPairCommonDivisorTupleAuxiliaryMobiusSum H
      (progressionSupport H q alpha N) (progressionCoefficient H q alpha F N)

def progressionS1Error (H : Finset ℕ) (q : ℕ) (alpha : ℝ)
    (v : ℕ → ℕ) (F : (H → ℝ) → ℝ) (N : ℕ) : ℝ :=
  compatibleDivisorPairErrorSum H (progressionSupport H q alpha N)
    (v N) (progressionModulus q N) N (progressionCoefficient H q alpha F N)

theorem eventually_progressionS1_eq_main_add_error
    (H : Finset ℕ) (q : ℕ) (alpha : ℝ) (v : ℕ → ℕ) (F : (H → ℝ) → ℝ) :
    ∀ᶠ N : ℕ in atTop, sieveWeightSum N (progressionWeight H q alpha v F N) =
      progressionS1Main H q alpha F N + progressionS1Error H q alpha v F N := by
  filter_upwards [eventually_progression_coverage H q] with N hN
  exact sieveWeightSum_preSieved_eq_auxiliaryMobiusSum_add_error
    (progressionSupport_valid H q alpha N) hN

theorem eventually_progressionS1Main_eq {q : ℕ} (hq : 0 < q)
    (H : Finset ℕ) (alpha : ℝ) (F : (H → ℝ) → ℝ) :
    ∀ᶠ N : ℕ in atTop,
      progressionS1Main H q alpha F N = tupleMaynardS1Main H alpha F N / q := by
  filter_upwards [eventually_progression_support_eq hq H alpha,
    eventually_progression_coefficient_eq hq H alpha F] with N hsupport hcoeff
  unfold progressionS1Main tupleMaynardS1Main
  rw [hsupport, hcoeff]
  simp only [progressionModulus, Nat.cast_mul]
  ring

theorem abs_progressionS1Error_le {q : ℕ} (hq : 0 < q)
    {H : Finset ℕ} {alpha : ℝ} {v : ℕ → ℕ} {F : (H → ℝ) → ℝ}
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ x, |F x| ≤ B) (N : ℕ) :
    |progressionS1Error H q alpha v F N| ≤
      ((maynardRadius alpha N : ℝ) *
        (1 + Real.log (maynardRadius alpha N)) ^ Fintype.card H) ^ 2 *
      ((maynardRadius alpha N : ℝ) * B *
        (1 + Real.log (maynardRadius alpha N)) ^ (2 * Fintype.card H)) ^ 2 := by
  let L := (maynardRadius alpha N : ℝ) * B *
    (1 + Real.log (maynardRadius alpha N)) ^ (2 * Fintype.card H)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hcoeff : ∀ d ∈ progressionSupport H q alpha N,
      |progressionCoefficient H q alpha F N d| ≤ L := by
    intro d hd
    exact abs_maynardCoefficient_le_log_envelope H (maynardRadius alpha N)
      (progressionModulus q N) F d B hB hF hd
  have hmass := compatibleDivisorPairCoefficientMass_le_card_sq_mul hL hcoeff
  have herr := abs_compatibleDivisorPairErrorSum_le_coefficientMass
    (progressionModulus_pos hq N) (progressionSupport_valid H q alpha N)
    (v := v N) (N := N) (lambda := progressionCoefficient H q alpha F N)
  have hcard := maynardDivisorTupleSupport_card_le_log H
    (maynardRadius alpha N) (progressionModulus q N)
  exact (herr.trans hmass).trans
    (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2) (sq_nonneg L))

theorem tendsto_normalized_progressionS1Error_zero {q : ℕ} (hq : 0 < q)
    (H : Finset ℕ) {alpha : ℝ} (halpha : 0 < alpha) (halphaQuarter : alpha < 1 / 4)
    (v : ℕ → ℕ) (F : (H → ℝ) → ℝ) {B : ℝ} (hB : 0 ≤ B) (hF : ∀ x, |F x| ≤ B) :
    Tendsto (fun N : ℕ =>
      progressionS1Error H q alpha v F N / tupleMaynardScale H alpha N)
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_
    (tendsto_tupleMaynardS1ExplicitEnvelope H halpha hB halphaQuarter)
  filter_upwards [eventually_tupleMaynardScale_pos (H := H) halpha] with N hscale
  simp only [Function.comp_apply, abs_div, abs_of_pos hscale]
  exact div_le_div_of_nonneg_right (abs_progressionS1Error_le hq hB hF N) hscale.le

end

end MaynardBFT
