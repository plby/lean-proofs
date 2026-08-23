import ErdosProblems.Erdos248.MediumEventMass

/-!
# Erdős Problem 248: sharp medium-prime event masses

This file keeps the actual diagonal energy of the one- and two-medium-prime
transforms in the principal term of the event-mass estimate.  Thus later
arguments can insert estimates which charge the logarithmic displacement
terms directly to `productCoordinateEnergy`, without first losing them to a
uniform bound for the whole varying majorant product.
-/

noncomputable section

open scoped BigOperators
open BoundedGaps.Maynard

namespace Erdos248

local instance mediumSharpEventMassDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The sharp one-prime event estimate, with the transformed diagonal energy
left unchanged. -/
theorem mediumSinglePrimeEventMass_le_actualEnergy
    {K p : ℕ} (hp : p.Prime) (hpCut : tinyCutoff K < p)
    (m : nearShifts K) :
    primeProductEventMass K m.1 {p} ≤
      (intervalStart K : ℝ) / (preSieveModulus K * p) *
        (varyingYEnergy K (mediumSingleTransformY K m p) +
          16 * roughCrossTupleTotientSquareTail (nearShifts K)
            (tinyCutoff K) (globalRadius K) *
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
  norm_num at hraw
  exact hraw

/-- The sharp two-prime event estimate, with the pair-transform diagonal
energy left unchanged. -/
theorem mediumPairPrimeEventMass_le_actualEnergy
    {K p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpCut : tinyCutoff K < p) (hqCut : tinyCutoff K < q)
    (m : nearShifts K) :
    primeProductEventMass K m.1 {p, q} ≤
      (intervalStart K : ℝ) / ((preSieveModulus K * p) * q) *
        (varyingYEnergy K (mediumPairTransformY K m p q) +
          256 * roughCrossTupleTotientSquareTail (nearShifts K)
            (tinyCutoff K) (globalRadius K) *
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
  norm_num at hraw
  exact hraw

/-- A normalized variant of the sharp one-prime estimate.  Only the cross
tail pays the comparison factor `96 ^ K`; the diagonal energy remains exact. -/
theorem mediumSinglePrimeEventMass_le_actualEnergy_productCross
    {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K p : ℕ} (hreg : NormalizationRegular A K)
    (hp : p.Prime) (hpCut : tinyCutoff K < p) (m : nearShifts K) :
    primeProductEventMass K m.1 {p} ≤
      (intervalStart K : ℝ) / (preSieveModulus K * p) *
        (varyingYEnergy K (mediumSingleTransformY K m p) +
          16 * roughCrossTupleTotientSquareTail (nearShifts K)
            (tinyCutoff K) (globalRadius K) *
            (96 ^ K * productCoordinateEnergy K)) +
        (radiusProduct K : ℝ) ^ 6 * 16 := by
  have hraw := mediumSinglePrimeEventMass_le_actualEnergy hp hpCut m
  have htail : 0 ≤ roughCrossTupleTotientSquareTail (nearShifts K)
      (tinyCutoff K) (globalRadius K) := by
    unfold roughCrossTupleTotientSquareTail
    exact Finset.sum_nonneg fun s hs => by
      unfold crossTotientSquareWeight
      positivity
  apply hraw.trans
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add le_rfl
    exact mul_le_mul_of_nonneg_left
      (varyingMajorantProduct_le_energy hA hreg)
      (mul_nonneg (by norm_num) htail)
  · exact le_rfl

/-- A normalized variant of the sharp two-prime estimate.  Only the cross
tail pays the comparison factor `96 ^ K`; the pair diagonal remains exact. -/
theorem mediumPairPrimeEventMass_le_actualEnergy_productCross
    {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K p q : ℕ} (hreg : NormalizationRegular A K)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpCut : tinyCutoff K < p) (hqCut : tinyCutoff K < q)
    (m : nearShifts K) :
    primeProductEventMass K m.1 {p, q} ≤
      (intervalStart K : ℝ) / ((preSieveModulus K * p) * q) *
        (varyingYEnergy K (mediumPairTransformY K m p q) +
          256 * roughCrossTupleTotientSquareTail (nearShifts K)
            (tinyCutoff K) (globalRadius K) *
            (96 ^ K * productCoordinateEnergy K)) +
        (radiusProduct K : ℝ) ^ 6 * 256 := by
  have hraw := mediumPairPrimeEventMass_le_actualEnergy
    hp hq hpq hpCut hqCut m
  have htail : 0 ≤ roughCrossTupleTotientSquareTail (nearShifts K)
      (tinyCutoff K) (globalRadius K) := by
    unfold roughCrossTupleTotientSquareTail
    exact Finset.sum_nonneg fun s hs => by
      unfold crossTotientSquareWeight
      positivity
  apply hraw.trans
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add le_rfl
    exact mul_le_mul_of_nonneg_left
      (varyingMajorantProduct_le_energy hA hreg)
      (mul_nonneg (by norm_num) htail)
  · exact le_rfl

end Erdos248
