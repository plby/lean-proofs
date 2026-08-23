import ErdosProblems.Erdos248.MediumMoment
import ErdosProblems.Erdos248.MediumSharpEventMass
import ErdosProblems.Erdos248.MediumSharpEnergy
import ErdosProblems.Erdos248.MediumScaleAbsorption
import ErdosProblems.Erdos248.PrimeRangeFacts

/-!
# Erdős Problem 248: the uniform medium-prime tail

This file sums the sharp one- and two-medium-prime event estimates before
normalizing by the sieve mass.  The logarithmic finite differences give an
absolute main term; every occurrence of `96 ^ K` is attached either to an
inverse-prime remainder or to the rough cross-tail, and the scale lemmas
absorb those terms.  The accumulated interval errors are smaller than one
copy of the sieve mass.  A second-moment Markov argument then produces one
fixed natural threshold, independent of `A`, `K`, and `k`.
-/

noncomputable section

open scoped BigOperators
open BoundedGaps.Maynard

namespace Erdos248

def mediumEnergyScale (K : ℕ) : ℝ :=
  (intervalStart K : ℝ) / preSieveModulus K * productCoordinateEnergy K

def mediumSingleAnalyticCost (K : ℕ) (m : nearShifts K) (p : ℕ) : ℝ :=
  768 * (primeLogDisplacement K m p ^ 2 / (p : ℝ)) +
    (2 * (K : ℝ) ^ 2 * 96 ^ K) *
      (1 / ((p : ℝ) * (((p - 1 : ℕ) : ℝ) ^ 2))) +
    16 * roughCrossTupleTotientSquareTail (nearShifts K) (tinyCutoff K)
      (globalRadius K) * 96 ^ K * (1 / (p : ℝ))

def mediumPairAnalyticCost (K : ℕ) (m : nearShifts K) (p q : ℕ) : ℝ :=
  (6144 * (primeLogDisplacement K m p / (p : ℝ))) *
      (primeLogDisplacement K m q / (q : ℝ)) +
    (16 * (K : ℝ) ^ 2 * 96 ^ K *
      (1 / ((p : ℝ) * (((p - 1 : ℕ) : ℝ) ^ 2))) *
      (primeLogDisplacement K m q ^ 2 / (q : ℝ))) +
    (2 * (K : ℝ) ^ 2 * 96 ^ K *
      ((2 * primeLogDisplacement K m p +
          (K : ℝ) / ((p - 1 : ℕ) : ℝ)) ^ 2 / (p : ℝ)) *
      (1 / ((q : ℝ) * (((q - 1 : ℕ) : ℝ) ^ 2)))) +
    (256 * roughCrossTupleTotientSquareTail (nearShifts K) (tinyCutoff K)
      (globalRadius K) * 96 ^ K * (1 / (p : ℝ)) * (1 / (q : ℝ))
    )

def mediumSingleMajorant (K : ℕ) (m : nearShifts K) (p : ℕ) : ℝ :=
  mediumEnergyScale K * mediumSingleAnalyticCost K m p +
    16 * (radiusProduct K : ℝ) ^ 6

def mediumPairMajorant (K : ℕ) (m : nearShifts K) (p q : ℕ) : ℝ :=
  mediumEnergyScale K * mediumPairAnalyticCost K m p q +
    256 * (radiusProduct K : ℝ) ^ 6

def mediumAnalyticCostConstant : ℝ :=
  768 * normalizedPrimeLogSquareConstant + 16 +
    16 * 196608 * farPrimeReciprocalConstant +
    6144 * normalizedPrimeLogSquareConstant ^ 2 +
    128 * normalizedPrimeLogSquareConstant +
    (128 * normalizedPrimeLogSquareConstant + 256) +
    256 * 196608 * farPrimeReciprocalConstant ^ 2

def mediumPrimeSecondMomentConstant : ℝ :=
  4 * mediumAnalyticCostConstant + 1

theorem mediumAnalyticCostConstant_nonneg :
    0 ≤ mediumAnalyticCostConstant := by
  unfold mediumAnalyticCostConstant
  have hlog := normalizedPrimeLogSquareConstant_nonneg
  have hfar := farPrimeReciprocalConstant_nonneg
  positivity

theorem mediumPrimeSecondMomentConstant_pos :
    0 < mediumPrimeSecondMomentConstant := by
  unfold mediumPrimeSecondMomentConstant
  have h := mediumAnalyticCostConstant_nonneg
  linarith

private theorem mediumSingleEventMass_le_majorant
    {A : ℝ} (hA : HasUniformWirsingBound A)
    {K p : ℕ} (hreg : NormalizationRegular A K) (m : nearShifts K)
    (hpMem : p ∈ mediumPrimes K m) :
    primeProductEventMass K m {p} ≤ mediumSingleMajorant K m p := by
  obtain ⟨hp, hpCut, hpRadius⟩ := mem_mediumPrimes_facts
    (mem_nearShifts.mp m.2).1 (mem_nearShifts.mp m.2).2 hpMem
  have hraw := mediumSinglePrimeEventMass_le_actualEnergy_productCross
    hA hreg hp hpCut m
  have henergy := varyingYEnergy_mediumSingleTransformY_le_sharp
    hA hreg hp hpCut m hpRadius
  calc
    primeProductEventMass K m {p} ≤
        (intervalStart K : ℝ) / (preSieveModulus K * p) *
          (varyingYEnergy K (mediumSingleTransformY K m p) +
            16 * roughCrossTupleTotientSquareTail (nearShifts K)
              (tinyCutoff K) (globalRadius K) *
              (96 ^ K * productCoordinateEnergy K)) +
          (radiusProduct K : ℝ) ^ 6 * 16 := hraw
    _ ≤ (intervalStart K : ℝ) / (preSieveModulus K * p) *
          ((768 * primeLogDisplacement K m p ^ 2 *
                productCoordinateEnergy K +
              2 * ((K : ℝ) / (p - 1 : ℕ)) ^ 2 *
                (96 ^ K * productCoordinateEnergy K)) +
            16 * roughCrossTupleTotientSquareTail (nearShifts K)
              (tinyCutoff K) (globalRadius K) *
              (96 ^ K * productCoordinateEnergy K)) +
          (radiusProduct K : ℝ) ^ 6 * 16 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (add_le_add henergy le_rfl)
          (by positivity)) le_rfl
    _ = mediumSingleMajorant K m p := by
      simp [mediumSingleMajorant, mediumSingleAnalyticCost,
        mediumEnergyScale]
      push_cast
      field_simp
      <;> ring

private theorem mediumPairEventMass_le_majorant
    {A : ℝ} (hA : HasUniformWirsingBound A)
    {K p q : ℕ} (hreg : NormalizationRegular A K) (m : nearShifts K)
    (hpMem : p ∈ mediumPrimes K m) (hqMem : q ∈ mediumPrimes K m)
    (hpq : p ≠ q) :
    primeProductEventMass K m {p, q} ≤ mediumPairMajorant K m p q := by
  obtain ⟨hp, hpCut, hpRadius⟩ := mem_mediumPrimes_facts
    (mem_nearShifts.mp m.2).1 (mem_nearShifts.mp m.2).2 hpMem
  obtain ⟨hq, hqCut, hqRadius⟩ := mem_mediumPrimes_facts
    (mem_nearShifts.mp m.2).1 (mem_nearShifts.mp m.2).2 hqMem
  have hraw := mediumPairPrimeEventMass_le_actualEnergy_productCross
    hA hreg hp hq hpq hpCut hqCut m
  have henergy := varyingYEnergy_mediumPairTransformY_le_sharp
    hA hreg hp hq hpq hpCut hqCut m hpRadius hqRadius
  calc
    primeProductEventMass K m {p, q} ≤
        (intervalStart K : ℝ) / ((preSieveModulus K * p) * q) *
          (varyingYEnergy K (mediumPairTransformY K m p q) +
            256 * roughCrossTupleTotientSquareTail (nearShifts K)
              (tinyCutoff K) (globalRadius K) *
              (96 ^ K * productCoordinateEnergy K)) +
          (radiusProduct K : ℝ) ^ 6 * 256 := hraw
    _ ≤ (intervalStart K : ℝ) / ((preSieveModulus K * p) * q) *
          ((6144 * primeLogDisplacement K m p *
                primeLogDisplacement K m q * productCoordinateEnergy K +
              (4 * (2 * (K : ℝ) * primeLogDisplacement K m q /
                    (p - 1 : ℕ)) ^ 2 +
                2 * ((K : ℝ) *
                    (2 * primeLogDisplacement K m p +
                      (K : ℝ) / (p - 1 : ℕ)) /
                    (q - 1 : ℕ)) ^ 2) *
                  (96 ^ K * productCoordinateEnergy K)) +
            256 * roughCrossTupleTotientSquareTail (nearShifts K)
              (tinyCutoff K) (globalRadius K) *
              (96 ^ K * productCoordinateEnergy K)) +
          (radiusProduct K : ℝ) ^ 6 * 256 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (add_le_add henergy le_rfl)
          (by positivity)) le_rfl
    _ = mediumPairMajorant K m p q := by
      simp [mediumPairMajorant, mediumPairAnalyticCost,
        mediumEnergyScale]
      push_cast
      field_simp
      <;> ring

private theorem mediumPairMajorant_nonneg
    {K p q : ℕ} (m : nearShifts K)
    (hpMem : p ∈ mediumPrimes K m) (hqMem : q ∈ mediumPrimes K m) :
    0 ≤ mediumPairMajorant K m p q := by
  have hp := prime_of_mem_mediumPrimes hpMem
  have hq := prime_of_mem_mediumPrimes hqMem
  have hdp : 0 ≤ primeLogDisplacement K m p :=
    primeLogDisplacement_nonneg hp.one_le _
  have hdq : 0 ≤ primeLogDisplacement K m q :=
    primeLogDisplacement_nonneg hq.one_le _
  have htail : 0 ≤ roughCrossTupleTotientSquareTail (nearShifts K)
      (tinyCutoff K) (globalRadius K) := by
    unfold roughCrossTupleTotientSquareTail
    exact Finset.sum_nonneg fun s hs ↦ by
      unfold crossTotientSquareWeight
      positivity
  unfold mediumPairMajorant mediumPairAnalyticCost mediumEnergyScale
  have hscale : 0 ≤
      (intervalStart K : ℝ) / preSieveModulus K *
        productCoordinateEnergy K := by
    exact mul_nonneg (div_nonneg (by positivity) (by positivity))
      (productCoordinateEnergy_nonneg K)
  positivity

private theorem sum_mediumSingleAnalyticCost_le
    {K : ℕ} (hK : 0 < K) (m : nearShifts K) :
    (∑ p ∈ mediumPrimes K m, mediumSingleAnalyticCost K m p) ≤
      768 * normalizedPrimeLogSquareConstant + 16 +
        16 * 196608 * farPrimeReciprocalConstant := by
  let T : ℝ := roughCrossTupleTotientSquareTail (nearShifts K)
    (tinyCutoff K) (globalRadius K)
  calc
    (∑ p ∈ mediumPrimes K m, mediumSingleAnalyticCost K m p) =
        768 * (∑ p ∈ mediumPrimes K m,
          primeLogDisplacement K m p ^ 2 / (p : ℝ)) +
        2 * (K : ℝ) ^ 2 * 96 ^ K *
          (∑ p ∈ mediumPrimes K m,
            1 / ((p : ℝ) * (((p - 1 : ℕ) : ℝ) ^ 2))) +
        16 * T * 96 ^ K *
          (∑ p ∈ mediumPrimes K m, (1 : ℝ) / p) := by
      simp [mediumSingleAnalyticCost, T, Finset.sum_add_distrib,
        Finset.mul_sum]
    _ ≤ 768 * normalizedPrimeLogSquareConstant + 16 +
        16 * 196608 * farPrimeReciprocalConstant := by
      have hres :
          2 * (K : ℝ) ^ 2 * 96 ^ K *
              (∑ p ∈ mediumPrimes K m,
                1 / ((p : ℝ) * (((p - 1 : ℕ) : ℝ) ^ 2))) ≤ 16 := by
        calc
          _ ≤ 2 * (K : ℝ) ^ 2 * 96 ^ K *
              (8 / ((tinyCutoff K + 1 : ℕ) : ℝ)) := by
            exact mul_le_mul_of_nonneg_left
              (sum_mediumPrimes_one_div_mul_pred_sq_le K m) (by positivity)
          _ ≤ 16 := by
            convert ninetySixPow_mul_singleResidual_le_sixteen hK using 1 <;>
              ring
      have htail := crossTail_mul_ninetySixPow_mul_sum_mediumInv_le hK m
      have hmain := sum_mediumPrimes_primeLogDisplacement_sq_div_le m
      nlinarith

private theorem double_sum_mul (I : Finset ℕ) (f g : ℕ → ℝ) :
    (∑ p ∈ I, ∑ q ∈ I, f p * g q) =
      (∑ p ∈ I, f p) * (∑ q ∈ I, g q) := by
  calc
    (∑ p ∈ I, ∑ q ∈ I, f p * g q) =
        ∑ p ∈ I, f p * (∑ q ∈ I, g q) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
    _ = (∑ p ∈ I, f p) * (∑ q ∈ I, g q) := by
      rw [Finset.sum_mul]

private theorem double_sum_const_mul (I : Finset ℕ) (a : ℝ)
    (F : ℕ → ℕ → ℝ) :
    (∑ p ∈ I, ∑ q ∈ I, a * F p q) =
      a * (∑ p ∈ I, ∑ q ∈ I, F p q) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]

private theorem sum_const_mul (I : Finset ℕ) (a : ℝ) (f : ℕ → ℝ) :
    (∑ p ∈ I, a * f p) = a * (∑ p ∈ I, f p) := by
  rw [Finset.mul_sum]

private theorem sum_mediumPairAnalyticCost_le
    {K : ℕ} (hK : 0 < K) (m : nearShifts K) :
    (∑ p ∈ mediumPrimes K m,
      ∑ q ∈ mediumPrimes K m, mediumPairAnalyticCost K m p q) ≤
      6144 * normalizedPrimeLogSquareConstant ^ 2 +
        128 * normalizedPrimeLogSquareConstant +
        (128 * normalizedPrimeLogSquareConstant + 256) +
        256 * 196608 * farPrimeReciprocalConstant ^ 2 := by
  let T : ℝ := roughCrossTupleTotientSquareTail (nearShifts K)
    (tinyCutoff K) (globalRadius K)
  let Sδ : ℝ := ∑ p ∈ mediumPrimes K m,
    primeLogDisplacement K m p / (p : ℝ)
  let Sb : ℝ := ∑ p ∈ mediumPrimes K m,
    1 / ((p : ℝ) * (((p - 1 : ℕ) : ℝ) ^ 2))
  let Sδ2 : ℝ := ∑ p ∈ mediumPrimes K m,
    primeLogDisplacement K m p ^ 2 / (p : ℝ)
  let Sc : ℝ := ∑ p ∈ mediumPrimes K m,
    (2 * primeLogDisplacement K m p +
      (K : ℝ) / ((p - 1 : ℕ) : ℝ)) ^ 2 / (p : ℝ)
  let S1 : ℝ := ∑ p ∈ mediumPrimes K m, (1 : ℝ) / p
  calc
    (∑ p ∈ mediumPrimes K m,
        ∑ q ∈ mediumPrimes K m, mediumPairAnalyticCost K m p q) =
        6144 * Sδ ^ 2 +
          16 * (K : ℝ) ^ 2 * 96 ^ K * Sb * Sδ2 +
          2 * (K : ℝ) ^ 2 * 96 ^ K * Sc * Sb +
          256 * T * 96 ^ K * S1 ^ 2 := by
      simp only [mediumPairAnalyticCost, Finset.sum_add_distrib]
      repeat rw [double_sum_mul]
      simp only [← Finset.mul_sum]
      dsimp [T, Sδ, Sb, Sδ2, Sc, S1]
      ring
    _ ≤ 6144 * normalizedPrimeLogSquareConstant ^ 2 +
        128 * normalizedPrimeLogSquareConstant +
        (128 * normalizedPrimeLogSquareConstant + 256) +
        256 * 196608 * farPrimeReciprocalConstant ^ 2 := by
      have hmain := sixtyFour_mul_sq_sum_mediumDisplacement_le m
      have hmain' : 6144 * Sδ ^ 2 ≤
          6144 * normalizedPrimeLogSquareConstant ^ 2 := by
        simpa [Sδ] using (mul_le_mul_of_nonneg_left
          (sq_sum_mediumPrimes_primeLogDisplacement_div_le m) (by norm_num :
            (0 : ℝ) ≤ 6144))
      have hfirst := ninetySixPow_mul_mediumPairFirstCross_le hK m
      have hsecond := ninetySixPow_mul_mediumPairSecondCross_le hK m
      have htail := crossTail_mul_ninetySixPow_mul_sq_sum_mediumInv_le hK m
      have hfirst' : 16 * (K : ℝ) ^ 2 * 96 ^ K * Sb * Sδ2 ≤
          128 * normalizedPrimeLogSquareConstant := by
        dsimp only [Sb, Sδ2]
        convert hfirst using 1 <;> ring
      have hsecond' : 2 * (K : ℝ) ^ 2 * 96 ^ K * Sc * Sb ≤
          128 * normalizedPrimeLogSquareConstant + 256 := by
        dsimp only [Sb, Sc]
        convert hsecond using 1 <;> ring
      have htail' : T * 96 ^ K * S1 ^ 2 ≤
          196608 * farPrimeReciprocalConstant ^ 2 := by
        simpa only [T, S1] using htail
      nlinarith [hmain', hfirst', hsecond', htail']

private theorem mediumPrimes_card_le_radius {K k : ℕ} :
    (mediumPrimes K k).card ≤ shiftRadius K k := by
  have hsub : mediumPrimes K k ⊆ Finset.Icc 1 (shiftRadius K k) := by
    intro p hp
    have hp' := mem_primesBetween.mp hp
    exact Finset.mem_Icc.mpr ⟨hp'.2.2.one_le, hp'.2.1⟩
  calc
    (mediumPrimes K k).card ≤ (Finset.Icc 1 (shiftRadius K k)).card :=
      Finset.card_le_card hsub
    _ ≤ shiftRadius K k := by simp

private theorem mediumAccumulatedIntervalErrors_lt_sieveMass
    {A : ℝ} (hA : HasUniformWirsingBound A)
    {K k : ℕ} (hreg : NormalizationRegular A K)
    (hk1 : 1 ≤ k) (hkK : k ≤ K) :
    ((mediumPrimes K k).card : ℝ) *
          (16 * (radiusProduct K : ℝ) ^ 6) +
        ((mediumPrimes K k).card : ℝ) ^ 2 *
          (256 * (radiusProduct K : ℝ) ^ 6) < sieveMass K := by
  let J := (mediumPrimes K k).card
  have hJ : J ≤ shiftRadius K 1 :=
    (mediumPrimes_card_le_radius).trans (by
      unfold shiftRadius
      apply Nat.pow_le_pow_right (by norm_num)
      apply Nat.pow_le_pow_right (by norm_num)
      omega)
  have hbig := accumulatedFourthIntervalError_lt_sieveMass hA hreg hJ
  by_cases hJ0 : J = 0
  · simpa [J, hJ0] using sieveMass_pos hA hreg
  · have hJone : (1 : ℝ) ≤ J := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hJ0)
    have hJle4 : (J : ℝ) ≤ (J : ℝ) ^ 4 := by
      nlinarith [sq_nonneg ((J : ℝ) ^ 2 - 1), sq_nonneg ((J : ℝ) - 1)]
    have hJ2le4 : (J : ℝ) ^ 2 ≤ (J : ℝ) ^ 4 := by
      nlinarith [sq_nonneg ((J : ℝ) ^ 2 - 1)]
    have hcoef : 16 * (J : ℝ) + 256 * (J : ℝ) ^ 2 ≤
        16 * 257 * (J : ℝ) ^ 4 := by nlinarith
    have hR : 0 ≤ (radiusProduct K : ℝ) ^ 6 := by positivity
    calc
      ((mediumPrimes K k).card : ℝ) *
            (16 * (radiusProduct K : ℝ) ^ 6) +
          ((mediumPrimes K k).card : ℝ) ^ 2 *
            (256 * (radiusProduct K : ℝ) ^ 6) =
          (16 * (J : ℝ) + 256 * (J : ℝ) ^ 2) *
            (radiusProduct K : ℝ) ^ 6 := by simp [J]; ring
      _ ≤ (16 * 257 * (J : ℝ) ^ 4) *
            (radiusProduct K : ℝ) ^ 6 :=
        mul_le_mul_of_nonneg_right hcoef hR
      _ = 16 * (J : ℝ) ^ 4 *
            ((radiusProduct K : ℝ) ^ 6 * 257) := by ring
      _ < sieveMass K := hbig

/-- Uniform absolute second moment for the medium-prime divisor count. -/
theorem mediumWeightedSecondMoment_le_absolute
    {A : ℝ} (hA : HasUniformWirsingBound A)
    {K k : ℕ} (hreg : NormalizationRegular A K)
    (hk1 : 1 ≤ k) (hkK : k ≤ K) :
    weightedSecondMoment
        (Finset.Ico (intervalStart K) (2 * intervalStart K))
        (sieveWeight K)
        (fun n ↦ ∑ p ∈ mediumPrimes K k,
          realIndicator (p ∣ n + k)) ≤
      mediumPrimeSecondMomentConstant * sieveMass K := by
  let m : nearShifts K := ⟨k, mem_nearShifts.mpr ⟨hk1, hkK⟩⟩
  have hraw := mediumWeightedSecondMoment_le_of_single_pairMajorants
    (mediumSingleMajorant K m) (mediumPairMajorant K m)
    (fun p hp q hq ↦ by
      apply mediumPairMajorant_nonneg m <;> simpa [m] using ‹_›)
    (fun p hp ↦ by
      simpa [m] using mediumSingleEventMass_le_majorant hA hreg m
        (by simpa [m] using hp))
    (fun p hp q hq hpq ↦ by
      simpa [m] using mediumPairEventMass_le_majorant hA hreg m
        (by simpa [m] using hp) (by simpa [m] using hq) hpq)
  have hsingle := sum_mediumSingleAnalyticCost_le hreg.1 m
  have hpair := sum_mediumPairAnalyticCost_le hreg.1 m
  have hcost :
      (∑ p ∈ mediumPrimes K k, mediumSingleAnalyticCost K m p) +
          ∑ p ∈ mediumPrimes K k,
            ∑ q ∈ mediumPrimes K k, mediumPairAnalyticCost K m p q ≤
        mediumAnalyticCostConstant := by
    calc
      _ ≤
          (768 * normalizedPrimeLogSquareConstant + 16 +
            16 * 196608 * farPrimeReciprocalConstant) +
          (6144 * normalizedPrimeLogSquareConstant ^ 2 +
            128 * normalizedPrimeLogSquareConstant +
            (128 * normalizedPrimeLogSquareConstant + 256) +
            256 * 196608 * farPrimeReciprocalConstant ^ 2) := by
              simpa [m] using add_le_add hsingle hpair
      _ = mediumAnalyticCostConstant := by
        unfold mediumAnalyticCostConstant
        ring
  have hsumMajorants :
      (∑ p ∈ mediumPrimes K k, mediumSingleMajorant K m p) +
          ∑ p ∈ mediumPrimes K k,
            ∑ q ∈ mediumPrimes K k, mediumPairMajorant K m p q =
        mediumEnergyScale K *
          ((∑ p ∈ mediumPrimes K k, mediumSingleAnalyticCost K m p) +
            ∑ p ∈ mediumPrimes K k,
              ∑ q ∈ mediumPrimes K k, mediumPairAnalyticCost K m p q) +
        ((mediumPrimes K k).card : ℝ) *
            (16 * (radiusProduct K : ℝ) ^ 6) +
        ((mediumPrimes K k).card : ℝ) ^ 2 *
            (256 * (radiusProduct K : ℝ) ^ 6) := by
    simp [mediumSingleMajorant, mediumPairMajorant,
      Finset.sum_add_distrib]
    rw [double_sum_const_mul]
    rw [sum_const_mul]
    ring
  have hscale0 : 0 ≤ mediumEnergyScale K := by
    unfold mediumEnergyScale
    exact mul_nonneg (div_nonneg (by positivity) (by positivity))
      (productCoordinateEnergy_nonneg K)
  have hquarter := quarter_scaled_energy_lt_sieveMass hA hreg
  have hscale : mediumEnergyScale K < 4 * sieveMass K := by
    unfold mediumEnergyScale
    nlinarith
  have hmass0 : 0 ≤ sieveMass K := (sieveMass_pos hA hreg).le
  have hinterval := mediumAccumulatedIntervalErrors_lt_sieveMass
    hA hreg hk1 hkK
  calc
    weightedSecondMoment
        (Finset.Ico (intervalStart K) (2 * intervalStart K))
        (sieveWeight K)
        (fun n ↦ ∑ p ∈ mediumPrimes K k,
          realIndicator (p ∣ n + k)) ≤
        (∑ p ∈ mediumPrimes K k, mediumSingleMajorant K m p) +
          ∑ p ∈ mediumPrimes K k,
            ∑ q ∈ mediumPrimes K k, mediumPairMajorant K m p q := hraw
    _ = _ := hsumMajorants
    _ = mediumEnergyScale K *
          ((∑ p ∈ mediumPrimes K k, mediumSingleAnalyticCost K m p) +
            ∑ p ∈ mediumPrimes K k,
              ∑ q ∈ mediumPrimes K k, mediumPairAnalyticCost K m p q) +
        (((mediumPrimes K k).card : ℝ) *
            (16 * (radiusProduct K : ℝ) ^ 6) +
          ((mediumPrimes K k).card : ℝ) ^ 2 *
            (256 * (radiusProduct K : ℝ) ^ 6)) := by ring
    _ ≤ mediumEnergyScale K * mediumAnalyticCostConstant + sieveMass K := by
      exact add_le_add (mul_le_mul_of_nonneg_left hcost hscale0) hinterval.le
    _ ≤ (4 * sieveMass K) * mediumAnalyticCostConstant + sieveMass K := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hscale.le
          mediumAnalyticCostConstant_nonneg) le_rfl
    _ = mediumPrimeSecondMomentConstant * sieveMass K := by
      unfold mediumPrimeSecondMomentConstant
      ring

/-- There is one fixed natural threshold giving the required uniform
reciprocal-square medium-prime exceptional-mass tail. -/
theorem exists_uniform_mediumPrimeBadMass_tail :
    ∃ T : ℕ, ∀ {A : ℝ}, HasUniformWirsingBound A →
      ∀ {K : ℕ}, NormalizationRegular A K →
        ∀ k, 1 ≤ k → k ≤ K →
          mediumPrimeBadMass K T k ≤
            sieveMass K * (1 / (16 * (k : ℝ) ^ 2)) := by
  have hmoment : ∀ {A : ℝ}, HasUniformWirsingBound A →
      ∀ {K k : ℕ}, NormalizationRegular A K → 1 ≤ k → k ≤ K →
        weightedSecondMoment
            (Finset.Ico (intervalStart K) (2 * intervalStart K))
            (sieveWeight K)
            (fun n ↦ ∑ p ∈ mediumPrimes K k,
              realIndicator (p ∣ n + k)) ≤
          mediumPrimeSecondMomentConstant * sieveMass K := by
    intro A hA K k hreg hk1 hkK
    exact mediumWeightedSecondMoment_le_absolute hA hreg hk1 hkK
  obtain ⟨T, hT⟩ := exists_uniform_mediumPrimeBadMass_tail_of_secondMoment
    mediumPrimeSecondMomentConstant mediumPrimeSecondMomentConstant_pos hmoment
  refine ⟨T, ?_⟩
  intro A hA K hreg k hk1 hkK
  exact hT hA hreg hk1 hkK

end Erdos248
