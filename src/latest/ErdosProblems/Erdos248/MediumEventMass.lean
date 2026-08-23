import ErdosProblems.Erdos248.EventMass
import ErdosProblems.Erdos248.MediumEnergy

/-!
# Erdős Problem 248: medium-prime event masses

This file realizes one- and two-prime divisibility events at a near
coordinate by the corresponding `differencePrimeY` transforms, then applies
the sharp transformed-mass bound while retaining the medium-prime diagonal
energy estimates.
-/

noncomputable section

open scoped BigOperators
open BoundedGaps.Maynard

namespace Erdos248

local instance mediumEventMassDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

def mediumSingleTransformY (K : ℕ) (m : nearShifts K) (p : ℕ) :
    (nearShifts K → ℕ) → ℝ :=
  differencePrimeY (globalRadius K) (preSieveModulus K) p m (sieveY K)

theorem mediumSingleTransformY_supported (K : ℕ) (m : nearShifts K)
    (p : ℕ) :
    IsSupportedMaynardY (nearShifts K) (globalRadius K)
      (preSieveModulus K * p) (mediumSingleTransformY K m p) := by
  exact differencePrimeY_supported _ _ _ _ _

theorem mediumSingleTransformY_varyingSupported
    {K p : ℕ} (hp : 0 < p) (m : nearShifts K) :
    IsVaryingSupported K (mediumSingleTransformY K m p) := by
  exact differencePrimeY_varyingSupported hp (sieveY_varyingSupported K) m

theorem mediumPrime_separated {K p : ℕ}
    (hpCut : tinyCutoff K < p) (m h : nearShifts K) (hhm : h ≠ m) :
    Nat.dist m.1 h.1 < p := by
  exact (nearShifts_diameter K (Ne.symm hhm)).trans_lt
    ((K_le_tinyCutoff K).trans_lt hpCut)

theorem sieveWeight_eq_fromYWeight (K : ℕ) :
    sieveWeight K =
      fromYWeight (globalRadius K) (preSieveModulus K) 0 (sieveY K) := by
  funext n
  unfold fromYWeight sieveWeight sieveDivisorSupport sieveCoefficient sieveY
  rw [show maynardCoefficient (nearShifts K) (globalRadius K)
      (preSieveModulus K) (tupleCutoff K) =
      maynardCoefficientFromY (nearShifts K) (globalRadius K)
        (preSieveModulus K)
        (maynardYValue (nearShifts K) (globalRadius K)
          (preSieveModulus K) (tupleCutoff K)) by
    funext d
    exact maynardCoefficient_eq_fromYValue _ _ _ _ d]

/-- Exact pointwise realization of one medium-prime event. -/
theorem exists_mediumSinglePrimePointwiseTransform
    {K p : ℕ} (hp : p.Prime) (hpCut : tinyCutoff K < p)
    (m : nearShifts K) :
    ∃ v : ℕ, ∀ n,
      (if p ∣ n + m.1 then sieveWeight K n else 0) =
        fromYWeight (globalRadius K) (preSieveModulus K * p) v
          (mediumSingleTransformY K m p) n := by
  have hpW := prime_coprime_preSieveModulus hp hpCut
  refine ⟨extendPrimeEventResidue hpW.symm 0 m.1, ?_⟩
  intro n
  rw [sieveWeight_eq_fromYWeight]
  exact indicator_coordinatePrime_fromYWeight hp hpW (sieveY_supported K) m
    (mediumPrime_separated hpCut m)

/-- Exact pointwise realization of two distinct medium-prime events. -/
theorem exists_mediumPairPrimePointwiseTransform
    {K p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpCut : tinyCutoff K < p) (hqCut : tinyCutoff K < q)
    (m : nearShifts K) :
    ∃ v : ℕ, ∀ n,
      (if p ∣ n + m.1 ∧ q ∣ n + m.1 then sieveWeight K n else 0) =
        fromYWeight (globalRadius K) ((preSieveModulus K * p) * q) v
          (mediumPairTransformY K m p q) n := by
  have hpW := prime_coprime_preSieveModulus hp hpCut
  have hqW : Nat.Coprime q (preSieveModulus K * p) := by
    rw [Nat.coprime_mul_iff_right]
    exact ⟨prime_coprime_preSieveModulus hq hqCut,
      (Nat.coprime_primes hq hp).mpr (Ne.symm hpq)⟩
  let v₁ := extendPrimeEventResidue hpW.symm 0 m.1
  let v₂ := extendPrimeEventResidue hqW.symm v₁ m.1
  refine ⟨v₂, ?_⟩
  intro n
  have hfirst := indicator_coordinatePrime_fromYWeight
    (R := globalRadius K) (v := 0) (n := n) hp hpW (sieveY_supported K) m
    (mediumPrime_separated hpCut m)
  have hsecond := indicator_coordinatePrime_fromYWeight
    (R := globalRadius K) (v := v₁) (n := n) hq hqW
    (mediumSingleTransformY_supported K m p) m
    (mediumPrime_separated hqCut m)
  rw [show (if p ∣ n + m.1 ∧ q ∣ n + m.1 then sieveWeight K n else 0) =
      if q ∣ n + m.1 then
        (if p ∣ n + m.1 then sieveWeight K n else 0) else 0 by
    by_cases hpN : p ∣ n + m.1 <;> by_cases hqN : q ∣ n + m.1 <;>
      simp [hpN, hqN]]
  rw [sieveWeight_eq_fromYWeight]
  rw [hfirst]
  simpa [v₁, v₂, mediumSingleTransformY, mediumPairTransformY] using hsecond

theorem mediumPrimeFactor_le_four {K p : ℕ} (hp : p.Prime)
    (hpCut : tinyCutoff K < p) :
    (2 : ℝ) + ((K : ℝ) + 1) / (p - 1 : ℕ) ≤ 4 := by
  have hden : (0 : ℝ) < (p - 1 : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt hp.one_lt
  have hKp : K ≤ p - 1 := (K_le_tinyCutoff K).trans (by omega)
  have hone : (1 : ℕ) ≤ p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hnum : K + 1 ≤ 2 * (p - 1) := by omega
  have hdiv : ((K : ℝ) + 1) / (p - 1 : ℕ) ≤ 2 := by
    apply (div_le_iff₀ hden).2
    exact_mod_cast hnum
  linarith

theorem abs_mediumSingleTransformY_le_four
    {K p : ℕ} (hp : p.Prime) (hpCut : tinyCutoff K < p)
    (m : nearShifts K) (r : nearShifts K → ℕ) :
    |mediumSingleTransformY K m p r| ≤ 4 := by
  have hraw := abs_differencePrimeY_le (H := nearShifts K)
    (R := globalRadius K) (W := preSieveModulus K)
    (p := p) (y := sieveY K) (B := (1 : ℝ)) (by norm_num)
    (abs_sieveY_le_one K) hp m r
  rw [Fintype.card_coe, nearShifts_card] at hraw
  exact hraw.trans (by simpa [mediumSingleTransformY] using
    mediumPrimeFactor_le_four hp hpCut)

theorem abs_mediumPairTransformY_le_sixteen
    {K p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpCut : tinyCutoff K < p) (hqCut : tinyCutoff K < q)
    (m : nearShifts K) (r : nearShifts K → ℕ) :
    |mediumPairTransformY K m p q r| ≤ 16 := by
  have hraw := abs_differencePrimeY_le (H := nearShifts K)
    (R := globalRadius K) (W := preSieveModulus K * p)
    (p := q) (y := mediumSingleTransformY K m p) (B := (4 : ℝ))
    (by norm_num) (abs_mediumSingleTransformY_le_four hp hpCut m) hq m r
  rw [Fintype.card_coe, nearShifts_card] at hraw
  have hfactor := mediumPrimeFactor_le_four hq hqCut
  have hle := hraw.trans (mul_le_mul_of_nonneg_left hfactor (by norm_num))
  norm_num at hle
  simpa [mediumPairTransformY, mediumSingleTransformY] using hle

/-- Diagonal energy of the one-medium-prime transform. -/
theorem varyingYEnergy_mediumSingleTransformY_le
    {K p : ℕ} (hK : 0 < K) (hp : p.Prime)
    (hpCut : tinyCutoff K < p) (m : nearShifts K)
    (hpRadius : p < shiftRadius K m) :
    varyingYEnergy K (mediumSingleTransformY K m p) ≤
      (2 * primeLogDisplacement K m p + (K : ℝ) / (p - 1 : ℕ)) ^ 2 *
        ∏ h : nearShifts K, varyingCoordinateMajorant K h := by
  let C : ℝ :=
    (2 * primeLogDisplacement K m p + (K : ℝ) / (p - 1 : ℕ)) ^ 2
  have hC : 0 ≤ C := sq_nonneg _
  calc
    varyingYEnergy K (mediumSingleTransformY K m p) ≤
        ∑ r ∈ varyingTupleBox K,
          C * reciprocalTotientTupleWeight (nearShifts K) r := by
      unfold varyingYEnergy
      apply Finset.sum_le_sum
      intro r hrBox
      apply mul_le_mul_of_nonneg_right _ (by
        unfold reciprocalTotientTupleWeight
        positivity)
      by_cases hz : mediumSingleTransformY K m p r = 0
      · rw [hz, zero_pow (by norm_num : 2 ≠ 0)]
        exact hC
      · have hr := mediumSingleTransformY_supported K m p r hz
        have habs := abs_differencePrimeY_sieveY_le hK hp hpCut m hpRadius hr hrBox
        have hbase : 0 ≤
            2 * primeLogDisplacement K m p + (K : ℝ) / (p - 1 : ℕ) := by
          have hδ := primeLogDisplacement_nonneg hp.one_le m
          positivity
        rw [← sq_abs]
        exact (sq_le_sq₀ (abs_nonneg _) hbase).mpr
          (by simpa [mediumSingleTransformY] using habs)
    _ = C * (∑ r ∈ varyingTupleBox K,
        reciprocalTotientTupleWeight (nearShifts K) r) := by
      rw [Finset.mul_sum]
    _ ≤ C * ∏ h : nearShifts K, varyingCoordinateMajorant K h :=
      mul_le_mul_of_nonneg_left (varyingTupleReciprocalWeightSum_le K) hC
    _ = _ := rfl

theorem mediumSinglePrimeEventMass_le
    {K p : ℕ} (hK : 0 < K) (hp : p.Prime)
    (hpCut : tinyCutoff K < p) (m : nearShifts K)
    (hpRadius : p < shiftRadius K m) :
    primeProductEventMass K m.1 {p} ≤
      (intervalStart K : ℝ) / (preSieveModulus K * p) *
        (((2 * primeLogDisplacement K m p +
              (K : ℝ) / (p - 1 : ℕ)) ^ 2 +
            16 * roughCrossTupleTotientSquareTail (nearShifts K)
              (tinyCutoff K) (globalRadius K)) *
          ∏ h : nearShifts K, varyingCoordinateMajorant K h) +
        (radiusProduct K : ℝ) ^ 6 * 16 := by
  obtain ⟨v, hpoint⟩ := exists_mediumSinglePrimePointwiseTransform hp hpCut m
  have hmass : primeProductEventMass K m.1 {p} =
      sieveWeightSum (intervalStart K)
        (fromYWeight (globalRadius K) (preSieveModulus K * p) v
          (mediumSingleTransformY K m p)) := by
    unfold primeProductEventMass sieveWeightSum
    apply Finset.sum_congr rfl
    intro n hn
    simpa using hpoint n
  rw [hmass]
  have hraw := fromYWeightMass_le_varyingYEnergy
    (dvd_mul_right (preSieveModulus K) p)
    (mul_pos (preSieveModulus_pos K) hp.pos)
    (mediumSingleTransformY_supported K m p)
    (mediumSingleTransformY_varyingSupported hp.pos m)
    (B := (4 : ℝ)) (by norm_num)
    (abs_mediumSingleTransformY_le_four hp hpCut m) (v := v)
  have henergy := varyingYEnergy_mediumSingleTransformY_le
    hK hp hpCut m hpRadius
  norm_num at hraw
  calc
    sieveWeightSum (intervalStart K)
        (fromYWeight (globalRadius K) (preSieveModulus K * p) v
          (mediumSingleTransformY K m p)) ≤
        (intervalStart K : ℝ) / (preSieveModulus K * p) *
          (varyingYEnergy K (mediumSingleTransformY K m p) +
            16 * roughCrossTupleTotientSquareTail (nearShifts K)
              (tinyCutoff K) (globalRadius K) *
              ∏ h : nearShifts K, varyingCoordinateMajorant K h) +
          (radiusProduct K : ℝ) ^ 6 * 16 := hraw
    _ ≤ (intervalStart K : ℝ) / (preSieveModulus K * p) *
        (((2 * primeLogDisplacement K m p +
              (K : ℝ) / (p - 1 : ℕ)) ^ 2 *
            ∏ h : nearShifts K, varyingCoordinateMajorant K h) +
          16 * roughCrossTupleTotientSquareTail (nearShifts K)
            (tinyCutoff K) (globalRadius K) *
            ∏ h : nearShifts K, varyingCoordinateMajorant K h) +
        (radiusProduct K : ℝ) ^ 6 * 16 := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add henergy le_rfl
      · exact le_rfl
    _ = _ := by ring

theorem mediumSinglePrimeEventMass_le_productEnergy
    {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K p : ℕ} (hreg : NormalizationRegular A K) (hp : p.Prime)
    (hpCut : tinyCutoff K < p) (m : nearShifts K)
    (hpRadius : p < shiftRadius K m) :
    primeProductEventMass K m.1 {p} ≤
      (intervalStart K : ℝ) / (preSieveModulus K * p) *
        (((2 * primeLogDisplacement K m p +
              (K : ℝ) / (p - 1 : ℕ)) ^ 2 +
            16 * roughCrossTupleTotientSquareTail (nearShifts K)
              (tinyCutoff K) (globalRadius K)) *
          (96 ^ K * productCoordinateEnergy K)) +
        (radiusProduct K : ℝ) ^ 6 * 16 := by
  have hraw := mediumSinglePrimeEventMass_le hreg.1 hp hpCut m hpRadius
  have hcoef : 0 ≤
      (2 * primeLogDisplacement K m p + (K : ℝ) / (p - 1 : ℕ)) ^ 2 +
        16 * roughCrossTupleTotientSquareTail (nearShifts K)
          (tinyCutoff K) (globalRadius K) := by
    have htail : 0 ≤ roughCrossTupleTotientSquareTail (nearShifts K)
        (tinyCutoff K) (globalRadius K) := by
      unfold roughCrossTupleTotientSquareTail
      exact Finset.sum_nonneg fun s hs => by
        unfold crossTotientSquareWeight
        positivity
    positivity
  apply hraw.trans
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_left
      (varyingMajorantProduct_le_energy hA hreg) hcoef
  · exact le_rfl

theorem mediumPairPrimeEventMass_le
    {K p q : ℕ} (hK : 0 < K) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hpCut : tinyCutoff K < p)
    (hqCut : tinyCutoff K < q) (m : nearShifts K)
    (hpRadius : p < shiftRadius K m) (hqRadius : q < shiftRadius K m) :
    primeProductEventMass K m.1 {p, q} ≤
      (intervalStart K : ℝ) / ((preSieveModulus K * p) * q) *
        ((64 * primeLogDisplacement K m p * primeLogDisplacement K m q +
            4 * (2 * (K : ℝ) * primeLogDisplacement K m q /
              (p - 1 : ℕ)) ^ 2 +
            2 * ((K : ℝ) *
              (2 * primeLogDisplacement K m p + (K : ℝ) / (p - 1 : ℕ)) /
              (q - 1 : ℕ)) ^ 2 +
            256 * roughCrossTupleTotientSquareTail (nearShifts K)
              (tinyCutoff K) (globalRadius K)) *
          ∏ h : nearShifts K, varyingCoordinateMajorant K h) +
        (radiusProduct K : ℝ) ^ 6 * 256 := by
  obtain ⟨v, hpoint⟩ :=
    exists_mediumPairPrimePointwiseTransform hp hq hpq hpCut hqCut m
  have hmass : primeProductEventMass K m.1 {p, q} =
      sieveWeightSum (intervalStart K)
        (fromYWeight (globalRadius K) ((preSieveModulus K * p) * q) v
          (mediumPairTransformY K m p q)) := by
    unfold primeProductEventMass sieveWeightSum
    apply Finset.sum_congr rfl
    intro n hn
    simpa [hpq] using hpoint n
  rw [hmass]
  have hraw := fromYWeightMass_le_varyingYEnergy
    ((dvd_mul_right (preSieveModulus K) p).trans
      (dvd_mul_right (preSieveModulus K * p) q))
    (mul_pos (mul_pos (preSieveModulus_pos K) hp.pos) hq.pos)
    (mediumPairTransformY_supported K m p q)
    (mediumPairTransformY_varyingSupported hp.pos hq.pos m)
    (B := (16 : ℝ)) (by norm_num)
    (abs_mediumPairTransformY_le_sixteen hp hq hpCut hqCut m) (v := v)
  have henergy := varyingYEnergy_mediumPairTransformY_le
    hK hp hq hpq hpCut hqCut m hpRadius hqRadius
  norm_num at hraw
  calc
    sieveWeightSum (intervalStart K)
        (fromYWeight (globalRadius K) ((preSieveModulus K * p) * q) v
          (mediumPairTransformY K m p q)) ≤
        (intervalStart K : ℝ) / ((preSieveModulus K * p) * q) *
          (varyingYEnergy K (mediumPairTransformY K m p q) +
            256 * roughCrossTupleTotientSquareTail (nearShifts K)
              (tinyCutoff K) (globalRadius K) *
              ∏ h : nearShifts K, varyingCoordinateMajorant K h) +
          (radiusProduct K : ℝ) ^ 6 * 256 := hraw
    _ ≤ (intervalStart K : ℝ) / ((preSieveModulus K * p) * q) *
        ((64 * primeLogDisplacement K m p * primeLogDisplacement K m q +
            4 * (2 * (K : ℝ) * primeLogDisplacement K m q /
              (p - 1 : ℕ)) ^ 2 +
            2 * ((K : ℝ) *
              (2 * primeLogDisplacement K m p + (K : ℝ) / (p - 1 : ℕ)) /
              (q - 1 : ℕ)) ^ 2) *
              ∏ h : nearShifts K, varyingCoordinateMajorant K h +
          256 * roughCrossTupleTotientSquareTail (nearShifts K)
            (tinyCutoff K) (globalRadius K) *
              ∏ h : nearShifts K, varyingCoordinateMajorant K h) +
        (radiusProduct K : ℝ) ^ 6 * 256 := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add henergy le_rfl
      · exact le_rfl
    _ = _ := by ring

theorem mediumPairPrimeEventMass_le_productEnergy
    {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K p q : ℕ} (hreg : NormalizationRegular A K)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpCut : tinyCutoff K < p) (hqCut : tinyCutoff K < q)
    (m : nearShifts K) (hpRadius : p < shiftRadius K m)
    (hqRadius : q < shiftRadius K m) :
    primeProductEventMass K m.1 {p, q} ≤
      (intervalStart K : ℝ) / ((preSieveModulus K * p) * q) *
        ((64 * primeLogDisplacement K m p * primeLogDisplacement K m q +
            4 * (2 * (K : ℝ) * primeLogDisplacement K m q /
              (p - 1 : ℕ)) ^ 2 +
            2 * ((K : ℝ) *
              (2 * primeLogDisplacement K m p + (K : ℝ) / (p - 1 : ℕ)) /
              (q - 1 : ℕ)) ^ 2 +
            256 * roughCrossTupleTotientSquareTail (nearShifts K)
              (tinyCutoff K) (globalRadius K)) *
          (96 ^ K * productCoordinateEnergy K)) +
        (radiusProduct K : ℝ) ^ 6 * 256 := by
  have hraw := mediumPairPrimeEventMass_le hreg.1 hp hq hpq hpCut hqCut m
    hpRadius hqRadius
  have hcoef : 0 ≤
      64 * primeLogDisplacement K m p * primeLogDisplacement K m q +
        4 * (2 * (K : ℝ) * primeLogDisplacement K m q /
          (p - 1 : ℕ)) ^ 2 +
        2 * ((K : ℝ) *
          (2 * primeLogDisplacement K m p + (K : ℝ) / (p - 1 : ℕ)) /
          (q - 1 : ℕ)) ^ 2 +
        256 * roughCrossTupleTotientSquareTail (nearShifts K)
          (tinyCutoff K) (globalRadius K) := by
    have hδp := primeLogDisplacement_nonneg hp.one_le m
    have hδq := primeLogDisplacement_nonneg hq.one_le m
    have htail : 0 ≤ roughCrossTupleTotientSquareTail (nearShifts K)
        (tinyCutoff K) (globalRadius K) := by
      unfold roughCrossTupleTotientSquareTail
      exact Finset.sum_nonneg fun s hs => by
        unfold crossTotientSquareWeight
        positivity
    positivity
  apply hraw.trans
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_left
      (varyingMajorantProduct_le_energy hA hreg) hcoef
  · exact le_rfl

end Erdos248
