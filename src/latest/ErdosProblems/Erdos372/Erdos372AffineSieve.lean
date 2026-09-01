import ErdosProblems.Erdos372.Erdos372AffineFinite

/-!
# Asymptotic affine Maynard sieve

This file specializes the finite affine identities to the canonical Maynard
support, modulus, coefficient, and 105-dimensional variational candidate.
-/

namespace Erdos372.AffineMaynard

open Filter Set
open scoped BigOperators
open Erdos6.Maynard
open BoundedGaps.Maynard

noncomputable section

local instance affineSieveDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

def affineTupleMaynardWeight (H : Finset ℕ) (A : H → ℕ)
    (alpha : ℝ) (F : (H → ℝ) → ℝ) (N : ℕ) : ℕ → ℝ :=
  preSievedAffineSquareDivisorWeight A
    (tupleMaynardSupport H alpha N)
    (tupleMaynardCoefficient H alpha F N) (maynardModulus N)

def affineTupleMaynardS1Error (H : Finset ℕ) (A : H → ℕ)
    (alpha : ℝ) (F : (H → ℝ) → ℝ) (N : ℕ) : ℝ :=
  affineCompatibleDivisorPairErrorSum H A
    (tupleMaynardSupport H alpha N) (maynardModulus N) N
    (tupleMaynardCoefficient H alpha F N)

theorem eventually_affine_coverage
    {H : Finset ℕ} (A : H → ℕ) (hApos : ∀ h, 0 < A h)
    (hAinj : Function.Injective A) :
    ∀ᶠ N : ℕ in atTop,
      CoversCoefficientPrimes A (maynardModulus N) ∧
      CoversAffineDifferencePrimes A (maynardModulus N) := by
  let C := ∑ h : H, A h
  obtain ⟨M, hM⟩ := exists_tripleLogCutoff_ge C
  filter_upwards [eventually_ge_atTop (M + 1)] with N hN
  have hcut : C ≤ tripleLogCutoff (N - 1) := hM (N - 1) (by omega)
  have hle (h : H) : A h ≤ C := by
    exact Finset.single_le_sum (s := Finset.univ) (f := A)
      (fun i hi => (hApos i).le) (Finset.mem_univ h)
  constructor
  · intro h p hp
    have hpPrime := Nat.prime_of_mem_primeFactors hp
    apply Nat.mem_primeFactors.mpr
    refine ⟨hpPrime, ?_, (primorial_pos _).ne'⟩
    change p ∣ primorial (tripleLogCutoff (N - 1))
    exact hpPrime.dvd_primorial_iff.mpr
      ((Nat.le_of_dvd (hApos h) (Nat.dvd_of_mem_primeFactors hp)).trans
        ((hle h).trans hcut))
  · intro a b hab p hp hpd
    apply hp.dvd_primorial_iff.mpr
    have hdistPos : 0 < Nat.dist (A a) (A b) :=
      Nat.dist_pos_of_ne (fun heq => hab (hAinj heq))
    have hdistLe : Nat.dist (A a) (A b) ≤ C := by
      by_cases habv : A a ≤ A b
      · rw [Nat.dist_eq_sub_of_le habv]
        exact (Nat.sub_le _ _).trans (hle b)
      · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (le_of_not_ge habv)]
        exact (Nat.sub_le _ _).trans (hle a)
    exact (Nat.le_of_dvd hdistPos hpd).trans (hdistLe.trans hcut)

theorem eventually_affineTupleMaynardS1_eq_main_add_error
    {H : Finset ℕ} (A : H → ℕ) (hApos : ∀ h, 0 < A h)
    (hAinj : Function.Injective A) (alpha : ℝ)
    (F : (H → ℝ) → ℝ) :
    ∀ᶠ N : ℕ in atTop,
      sieveWeightSum N (affineTupleMaynardWeight H A alpha F N) =
        tupleMaynardS1Main H alpha F N +
          affineTupleMaynardS1Error H A alpha F N := by
  filter_upwards [eventually_affine_coverage A hApos hAinj] with N hcover
  have hD := tupleMaynardS2SupportProof H alpha N
  have hfinite := sieveWeightSum_preSievedAffine_eq_main_add_error
    (N := N) (lambda := tupleMaynardCoefficient H alpha F N)
    hcover.2 hD
  change sieveWeightSum N (affineTupleMaynardWeight H A alpha F N) = _
  rw [show tupleMaynardS1Main H alpha F N =
      compatibleDivisorPairMainSum H (tupleMaynardSupport H alpha N)
        (maynardModulus N) N (tupleMaynardCoefficient H alpha F N) by
    unfold tupleMaynardS1Main
    exact (compatibleDivisorPairMainSum_eq_auxiliaryMobiusSum hD).symm]
  simpa [affineTupleMaynardWeight, affineTupleMaynardS1Error] using hfinite

theorem abs_affineTupleMaynardS1Error_le_explicit_log_envelope
    {H : Finset ℕ} {A : H → ℕ} {alpha : ℝ}
    {F : (H → ℝ) → ℝ} {B : ℝ}
    (N : ℕ)
    (hApos : ∀ h, 0 < A h)
    (hAprimes : CoversCoefficientPrimes A (maynardModulus N))
    (hB : 0 ≤ B) (hF : ∀ x, |F x| ≤ B) :
    |affineTupleMaynardS1Error H A alpha F N| ≤
      ((maynardRadius alpha N : ℝ) *
        (1 + Real.log (maynardRadius alpha N)) ^ Fintype.card H) ^ 2 *
      ((maynardRadius alpha N : ℝ) * B *
        (1 + Real.log (maynardRadius alpha N)) ^
          (2 * Fintype.card H)) ^ 2 := by
  let D := tupleMaynardSupport H alpha N
  let lambda := tupleMaynardCoefficient H alpha F N
  let L := (maynardRadius alpha N : ℝ) * B *
    (1 + Real.log (maynardRadius alpha N)) ^ (2 * Fintype.card H)
  have hD : ∀ d ∈ D, IsMaynardDivisorTuple H
      (maynardRadius alpha N) (maynardModulus N) d := by
    intro d hd
    exact tupleMaynardS2SupportProof H alpha N d (by simpa [D] using hd)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hcoeff : ∀ d ∈ D, |lambda d| ≤ L := by
    intro d hd
    exact abs_maynardCoefficient_le_log_envelope
      H (maynardRadius alpha N) (maynardModulus N) F d B hB hF
      (by simpa [D, tupleMaynardSupport] using hd)
  have herr := abs_affineCompatibleDivisorPairErrorSum_le_coefficientMass
    (N := N) (lambda := lambda)
    hApos hAprimes (primorial_pos _) hD
  have hmass := compatibleDivisorPairCoefficientMass_le_card_sq_mul hL hcoeff
  have hcard := tupleMaynardSupport_card_le_log H alpha N
  have hcardpow := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
  change |affineCompatibleDivisorPairErrorSum H A D
    (maynardModulus N) N lambda| ≤ _
  exact herr.trans (hmass.trans
    (mul_le_mul_of_nonneg_right hcardpow (sq_nonneg L)))

theorem tendsto_normalized_affineTupleMaynardS1Error_zero
    {H : Finset ℕ} (A : H → ℕ) (hApos : ∀ h, 0 < A h)
    (hAinj : Function.Injective A) {alpha : ℝ} (halpha : 0 < alpha)
    (halphaQuarter : alpha < 1 / 4) (F : (H → ℝ) → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ x, |F x| ≤ B) :
    Tendsto (fun N : ℕ =>
      affineTupleMaynardS1Error H A alpha F N /
        tupleMaynardScale H alpha N) atTop (nhds 0) := by
  have henv := tendsto_tupleMaynardS1ExplicitEnvelope H halpha hB halphaQuarter
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_ henv
  filter_upwards [eventually_affine_coverage A hApos hAinj,
    eventually_tupleMaynardScale_pos (H := H) halpha] with N hcover hscale
  rw [abs_div, abs_of_pos hscale]
  exact div_le_div_of_nonneg_right
    (abs_affineTupleMaynardS1Error_le_explicit_log_envelope
      N hApos hcover.1 hB hF) hscale.le

theorem tendsto_normalized_largeAffineS1
    (A : largePowerTuple → ℕ) (hApos : ∀ h, 0 < A h)
    (hAinj : Function.Injective A) {alpha : ℝ}
    (halpha : 0 < alpha) (halphaQuarter : alpha < 1 / 4) :
    Tendsto (fun N : ℕ =>
      sieveWeightSum N
          (affineTupleMaynardWeight largePowerTuple A alpha
            largeTupleCandidate N) /
        tupleMaynardScale largePowerTuple alpha N) atTop
      (nhds (maynardI largeK largeCandidate)) := by
  have hmain := tendsto_normalizedLargeTupleS1Main halpha
  have herr := tendsto_normalized_affineTupleMaynardS1Error_zero
    A hApos hAinj halpha halphaQuarter largeTupleCandidate
      (B := 1) (by norm_num) largeTupleCandidate_abs_le_one
  have hsum := hmain.add herr
  simpa using hsum.congr' (by
    filter_upwards [eventually_affineTupleMaynardS1_eq_main_add_error
      A hApos hAinj alpha largeTupleCandidate] with N hN
    rw [hN]
    ring)

end

end Erdos372.AffineMaynard
