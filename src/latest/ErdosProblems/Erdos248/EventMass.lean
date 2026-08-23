import ErdosProblems.Erdos248.PrimeProducts

/-!
# Erdős Problem 248: mass of finite prime-product events

This file packages the finite prime transforms as estimates for the actual
weighted event on the dyadic interval.  There are two deliberately separate
entry points: a shift outside `nearShifts K`, and a near coordinate for primes
larger than its coordinate radius.

The event primes are stored in a `Finset`, so their product is squarefree.
The applications use at most four primes; consequently the transformed
`Y`-variable is bounded by `16`, and all quadratic terms by `256`.
-/

noncomputable section

open scoped BigOperators
open BoundedGaps.Maynard

namespace Erdos248

local instance eventMassDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The unnormalized sieve mass of the event that every prime in `P` divides
`n + k`. -/
def primeProductEventMass (K k : ℕ) (P : Finset ℕ) : ℝ :=
  sieveWeightSum (intervalStart K) fun n =>
    if ∀ p ∈ P, p ∣ n + k then sieveWeight K n else 0

theorem primeProductEventMass_nonneg (K k : ℕ) (P : Finset ℕ) :
    0 ≤ primeProductEventMass K k P := by
  unfold primeProductEventMass sieveWeightSum
  apply Finset.sum_nonneg
  intro n hn
  split_ifs
  · exact sieveWeight_nonneg K n
  · exact le_rfl

/-- A finite set of primes has squarefree product. -/
theorem primeProduct_squarefree {P : Finset ℕ}
    (hPprime : ∀ p ∈ P, p.Prime) :
    Squarefree (∏ p ∈ P, p) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_
    (fun p hp => (hPprime p hp).squarefree)
  intro p hp q hq hpq
  exact Nat.coprime_iff_isRelPrime.mp
    ((Nat.coprime_primes (hPprime p hp) (hPprime q hq)).mpr hpq)

theorem primeProduct_pos {P : Finset ℕ}
    (hPprime : ∀ p ∈ P, p.Prime) :
    0 < ∏ p ∈ P, p := by
  exact Finset.prod_pos fun p hp => (hPprime p hp).pos

/-- Pointwise control of a sharply supported `Y` controls its diagonal
energy by the reciprocal-totient mass of the sharp box. -/
theorem varyingYEnergy_le_pointwise
    {K : ℕ} {y : (nearShifts K → ℕ) → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hyBound : ∀ r, |y r| ≤ B) :
    varyingYEnergy K y ≤
      B ^ 2 * ∏ h : nearShifts K, varyingCoordinateMajorant K h := by
  calc
    varyingYEnergy K y ≤
        ∑ u ∈ varyingTupleBox K,
          B ^ 2 * reciprocalTotientTupleWeight (nearShifts K) u := by
      unfold varyingYEnergy
      apply Finset.sum_le_sum
      intro u hu
      apply mul_le_mul_of_nonneg_right _ (by
        unfold reciprocalTotientTupleWeight
        positivity)
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) hB).mpr (hyBound u)
    _ = B ^ 2 *
        (∑ u ∈ varyingTupleBox K,
          reciprocalTotientTupleWeight (nearShifts K) u) := by
      rw [Finset.mul_sum]
    _ ≤ B ^ 2 *
        ∏ h : nearShifts K, varyingCoordinateMajorant K h := by
      exact mul_le_mul_of_nonneg_left
        (varyingTupleReciprocalWeightSum_le K) (sq_nonneg B)

/-- Exact mass formula for any sharply supported transformed `Y` whose
modulus extends the original pre-sieve modulus. -/
theorem fromYWeightMass_eq_diagonal_sub_cross_add_error
    {K W v : ℕ} {y : (nearShifts K → ℕ) → ℝ}
    (hmod : preSieveModulus K ∣ W)
    (hy : IsSupportedMaynardY (nearShifts K) (globalRadius K) W y)
    (hySharp : IsVaryingSupported K y) :
    sieveWeightSum (intervalStart K)
        (fromYWeight (globalRadius K) W v y) =
      (intervalStart K : ℝ) / W *
          (varyingYEnergy K y -
            incompatibleDivisorPairCommonDivisorTupleSum (nearShifts K)
              (maynardDivisorTupleSupport (nearShifts K) (globalRadius K) W)
              (maynardCoefficientFromY (nearShifts K) (globalRadius K) W y)) +
        compatibleDivisorPairErrorSum (nearShifts K)
          (maynardDivisorTupleSupport (nearShifts K) (globalRadius K) W)
          v W (intervalStart K)
          (maynardCoefficientFromY (nearShifts K) (globalRadius K) W y) := by
  unfold fromYWeight
  rw [sieveWeightSum_fromY_eq_main_add_error hy
    (CoversShiftDifferencePrimes.mono_modulus (nearShifts_cover K) hmod)]
  rw [maynardYDiagonalSum_eq_varyingYEnergy hmod hy hySharp]

/-- Sharp transformed-mass upper bound which retains the actual diagonal
energy.  This is preferable to the coarser pointwise majorant when a
one- or two-prime transform has a useful displacement estimate. -/
theorem fromYWeightMass_le_varyingYEnergy
    {K W v : ℕ} {y : (nearShifts K → ℕ) → ℝ} {B : ℝ}
    (hmod : preSieveModulus K ∣ W) (hW : 0 < W)
    (hy : IsSupportedMaynardY (nearShifts K) (globalRadius K) W y)
    (hySharp : IsVaryingSupported K y)
    (hB : 0 ≤ B) (hyBound : ∀ r, |y r| ≤ B) :
    sieveWeightSum (intervalStart K)
        (fromYWeight (globalRadius K) W v y) ≤
      (intervalStart K : ℝ) / W *
          (varyingYEnergy K y +
            B ^ 2 * roughCrossTupleTotientSquareTail (nearShifts K)
              (tinyCutoff K) (globalRadius K) *
              ∏ h : nearShifts K, varyingCoordinateMajorant K h) +
        (radiusProduct K : ℝ) ^ 6 * B ^ 2 := by
  let C : ℝ := incompatibleDivisorPairCommonDivisorTupleSum (nearShifts K)
    (maynardDivisorTupleSupport (nearShifts K) (globalRadius K) W)
    (maynardCoefficientFromY (nearShifts K) (globalRadius K) W y)
  let E : ℝ := compatibleDivisorPairErrorSum (nearShifts K)
    (maynardDivisorTupleSupport (nearShifts K) (globalRadius K) W)
    v W (intervalStart K)
    (maynardCoefficientFromY (nearShifts K) (globalRadius K) W y)
  have hcross : |C| ≤
      B ^ 2 * roughCrossTupleTotientSquareTail (nearShifts K)
          (tinyCutoff K) (globalRadius K) *
        ∏ h : nearShifts K, varyingCoordinateMajorant K h := by
    simpa [C] using abs_incompatibleSum_le_sharp_varying
      (globalRadius_pos K) hmod hy hySharp hB hyBound
  have herr : |E| ≤ (radiusProduct K : ℝ) ^ 6 * B ^ 2 := by
    simpa [E] using abs_transformedIntervalError_le (v := v)
      (N := intervalStart K) hmod hW hy hySharp hB hyBound
  rw [fromYWeightMass_eq_diagonal_sub_cross_add_error hmod hy hySharp]
  change (intervalStart K : ℝ) / W * (varyingYEnergy K y - C) + E ≤ _
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc
      varyingYEnergy K y - C ≤ varyingYEnergy K y + |C| := by
        linarith [neg_le_abs C]
      _ ≤ varyingYEnergy K y +
          B ^ 2 * roughCrossTupleTotientSquareTail (nearShifts K)
              (tinyCutoff K) (globalRadius K) *
            ∏ h : nearShifts K, varyingCoordinateMajorant K h :=
        add_le_add le_rfl hcross
  · exact (le_abs_self E).trans herr

/-- Uniform upper bound for a transformed mass.  This is the common analytic
estimate used by both finite-product event transforms below. -/
theorem fromYWeightMass_le_productCoordinateEnergy
    {A B : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K W v : ℕ} (hreg : NormalizationRegular A K)
    {y : (nearShifts K → ℕ) → ℝ}
    (hmod : preSieveModulus K ∣ W) (hW : 0 < W)
    (hy : IsSupportedMaynardY (nearShifts K) (globalRadius K) W y)
    (hySharp : IsVaryingSupported K y)
    (hB : 0 ≤ B) (hyBound : ∀ r, |y r| ≤ B) :
    sieveWeightSum (intervalStart K)
        (fromYWeight (globalRadius K) W v y) ≤
      (intervalStart K : ℝ) / W *
          (B ^ 2 *
            (1 + roughCrossTupleTotientSquareTail (nearShifts K)
              (tinyCutoff K) (globalRadius K)) *
            96 ^ K * productCoordinateEnergy K) +
        (radiusProduct K : ℝ) ^ 6 * B ^ 2 := by
  let C : ℝ := incompatibleDivisorPairCommonDivisorTupleSum (nearShifts K)
    (maynardDivisorTupleSupport (nearShifts K) (globalRadius K) W)
    (maynardCoefficientFromY (nearShifts K) (globalRadius K) W y)
  let E : ℝ := compatibleDivisorPairErrorSum (nearShifts K)
    (maynardDivisorTupleSupport (nearShifts K) (globalRadius K) W)
    v W (intervalStart K)
    (maynardCoefficientFromY (nearShifts K) (globalRadius K) W y)
  let M : ℝ := ∏ h : nearShifts K, varyingCoordinateMajorant K h
  let T : ℝ := roughCrossTupleTotientSquareTail (nearShifts K)
    (tinyCutoff K) (globalRadius K)
  have hM : 0 ≤ M := by
    dsimp [M]
    apply Finset.prod_nonneg
    intro h hh
    unfold varyingCoordinateMajorant squarefreeCoprimeInvTotientMean
    positivity
  have hT : 0 ≤ T := by
    dsimp [T]
    unfold roughCrossTupleTotientSquareTail crossTotientSquareWeight
    positivity
  have hdiag : varyingYEnergy K y ≤ B ^ 2 * M := by
    simpa [M] using varyingYEnergy_le_pointwise hB hyBound
  have hcross : |C| ≤ B ^ 2 * T * M := by
    simpa [C, T, M] using
      (abs_incompatibleSum_le_sharp_varying
        (globalRadius_pos K) hmod hy hySharp hB hyBound)
  have hbracket : varyingYEnergy K y - C ≤ B ^ 2 * (1 + T) * M := by
    calc
      varyingYEnergy K y - C ≤ varyingYEnergy K y + |C| := by
        linarith [neg_le_abs C]
      _ ≤ B ^ 2 * M + B ^ 2 * T * M := add_le_add hdiag hcross
      _ = B ^ 2 * (1 + T) * M := by ring
  have hmajorant : M ≤ 96 ^ K * productCoordinateEnergy K := by
    simpa [M] using varyingMajorantProduct_le_energy hA hreg
  have hbracket' : varyingYEnergy K y - C ≤
      B ^ 2 * (1 + T) * (96 ^ K * productCoordinateEnergy K) := by
    exact hbracket.trans
      (mul_le_mul_of_nonneg_left hmajorant
        (mul_nonneg (sq_nonneg B) (add_nonneg zero_le_one hT)))
  have herr : |E| ≤ (radiusProduct K : ℝ) ^ 6 * B ^ 2 := by
    simpa [E] using abs_transformedIntervalError_le hmod hW hy hySharp hB hyBound
  rw [fromYWeightMass_eq_diagonal_sub_cross_add_error hmod hy hySharp]
  change (intervalStart K : ℝ) / W * (varyingYEnergy K y - C) + E ≤ _
  calc
    (intervalStart K : ℝ) / W * (varyingYEnergy K y - C) + E ≤
        (intervalStart K : ℝ) / W *
            (B ^ 2 * (1 + T) *
              (96 ^ K * productCoordinateEnergy K)) +
          (radiusProduct K : ℝ) ^ 6 * B ^ 2 := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hbracket' (by positivity)
      · exact (le_abs_self E).trans herr
    _ = (intervalStart K : ℝ) / W *
          (B ^ 2 * (1 +
            roughCrossTupleTotientSquareTail (nearShifts K)
              (tinyCutoff K) (globalRadius K)) *
            96 ^ K * productCoordinateEnergy K) +
        (radiusProduct K : ℝ) ^ 6 * B ^ 2 := by
      dsimp [T]
      ring

theorem two_pow_card_sq_le_256 {P : Finset ℕ} (hcard : P.card ≤ 4) :
    ((2 : ℝ) ^ P.card) ^ 2 ≤ 256 := by
  interval_cases h : P.card <;> norm_num at hcard ⊢

theorem two_pow_card_le_16 {P : Finset ℕ} (hcard : P.card ≤ 4) :
    (2 : ℝ) ^ P.card ≤ 16 := by
  interval_cases h : P.card <;> norm_num at hcard ⊢

/-- A convenient uniform form of the one-prime energy perturbation estimate.
It is tailored to the at-most-four-prime iteration. -/
theorem abs_varyingYEnergy_erasePrimeY_sub_le_uniform
    {K R W p : ℕ} {y : (nearShifts K → ℕ) → ℝ} {B : ℝ}
    (hp : p.Prime) (hKp : K ≤ p - 1)
    (hy : IsSupportedMaynardY (nearShifts K) R W y)
    (hB : 0 ≤ B) (hB16 : B ≤ 16) (hyBound : ∀ r, |y r| ≤ B) :
    |varyingYEnergy K (erasePrimeY R W p y) - varyingYEnergy K y| ≤
      2048 * ((K : ℝ) / Nat.totient p) *
        ∏ h : nearShifts K, varyingCoordinateMajorant K h := by
  have htot : Nat.totient p = p - 1 := Nat.totient_prime hp
  have hden : (0 : ℝ) < (p - 1 : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt hp.one_lt
  let δ : ℝ := (K : ℝ) / (p - 1 : ℕ)
  have hδ0 : 0 ≤ δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    apply (div_le_one hden).mpr
    exact_mod_cast hKp
  have hBsum : B * (1 + δ) ≤ 32 := by nlinarith
  have hBsq : B ^ 2 ≤ 256 := by nlinarith [sq_nonneg (B - 16)]
  have hBsumsq : (B * (1 + δ)) ^ 2 ≤ 1024 := by
    nlinarith [sq_nonneg (B * (1 + δ) - 32),
      mul_nonneg hB (add_nonneg zero_le_one hδ0)]
  have hsecondRight : 2 * B + B * δ ≤ 48 := by nlinarith
  have hsecond : B * (2 * B + B * δ) ≤ 768 := by
    simpa only [show (16 : ℝ) * 48 = 768 by norm_num] using
      (mul_le_mul hB16 hsecondRight
        (add_nonneg (mul_nonneg (by norm_num) hB) (mul_nonneg hB hδ0))
        (by norm_num))
  have hcoef :
      (B * (1 + δ)) ^ 2 + B ^ 2 + B * (2 * B + B * δ) ≤ 2048 := by
    linarith
  have hM : 0 ≤ ∏ h : nearShifts K, varyingCoordinateMajorant K h := by
    apply Finset.prod_nonneg
    intro h hh
    unfold varyingCoordinateMajorant squarefreeCoprimeInvTotientMean
    positivity
  have hraw := abs_varyingYEnergy_erasePrimeY_sub_le hp hy hB hyBound
  rw [htot] at hraw ⊢
  change |varyingYEnergy K (erasePrimeY R W p y) - varyingYEnergy K y| ≤
      2048 * δ * ∏ h : nearShifts K, varyingCoordinateMajorant K h
  calc
    |varyingYEnergy K (erasePrimeY R W p y) - varyingYEnergy K y| ≤
        ((B * (1 + δ)) ^ 2 + B ^ 2) * δ *
            (∏ h : nearShifts K, varyingCoordinateMajorant K h) +
          (B * δ) * (2 * B + B * δ) *
            (∏ h : nearShifts K, varyingCoordinateMajorant K h) := by
      convert hraw using 1 <;> dsimp [δ] <;> ring
    _ = δ * ((B * (1 + δ)) ^ 2 + B ^ 2 +
          B * (2 * B + B * δ)) *
        (∏ h : nearShifts K, varyingCoordinateMajorant K h) := by ring
    _ ≤ δ * 2048 *
        (∏ h : nearShifts K, varyingCoordinateMajorant K h) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcoef hδ0) hM
    _ = 2048 * δ *
        ∏ h : nearShifts K, varyingCoordinateMajorant K h := by ring

/-- Abstract iteration of prime-erasing transforms, retaining quantitative
closeness of the final diagonal energy to the original sieve diagonal. -/
theorem exists_primeProductEraseTransform_energy
    {K k : ℕ} {P : Finset ℕ} (hcard : P.card ≤ 4)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPcut : ∀ p ∈ P, tinyCutoff K < p)
    (hstep : ∀ {W v p : ℕ} {y : (nearShifts K → ℕ) → ℝ}
      (hpMem : p ∈ P) (hpW : Nat.Coprime p W)
      (hy : IsSupportedMaynardY (nearShifts K) (globalRadius K) W y)
      (hySharp : IsVaryingSupported K y),
      ∀ n,
        (if p ∣ n + k then fromYWeight (globalRadius K) W v y n else 0) =
          fromYWeight (globalRadius K) (W * p)
            (extendPrimeEventResidue hpW.symm v k)
            (erasePrimeY (globalRadius K) W p y) n) :
    ∃ (y : (nearShifts K → ℕ) → ℝ) (v : ℕ),
      IsSupportedMaynardY (nearShifts K) (globalRadius K)
          (preSieveModulus K * ∏ p ∈ P, p) y ∧
      IsVaryingSupported K y ∧
      (∀ r, |y r| ≤ (2 : ℝ) ^ P.card) ∧
      (∀ n, (if ∀ p ∈ P, p ∣ n + k then sieveWeight K n else 0) =
        fromYWeight (globalRadius K)
          (preSieveModulus K * ∏ p ∈ P, p) v y n) ∧
      |varyingYEnergy K y - varyingYEnergy K (sieveY K)| ≤
        2048 * (∑ p ∈ P, (K : ℝ) / Nat.totient p) *
          ∏ h : nearShifts K, varyingCoordinateMajorant K h := by
  classical
  induction P using Finset.induction_on with
  | empty =>
      refine ⟨sieveY K, 0, ?_, sieveY_varyingSupported K, ?_, ?_, ?_⟩
      · simpa using sieveY_supported K
      · intro r
        simpa using abs_sieveY_le_one K r
      · intro n
        unfold fromYWeight sieveWeight sieveDivisorSupport sieveCoefficient sieveY
        rw [show maynardCoefficient (nearShifts K) (globalRadius K)
            (preSieveModulus K) (tupleCutoff K) =
            maynardCoefficientFromY (nearShifts K) (globalRadius K)
              (preSieveModulus K)
              (maynardYValue (nearShifts K) (globalRadius K)
                (preSieveModulus K) (tupleCutoff K)) by
          funext d
          exact maynardCoefficient_eq_fromYValue _ _ _ _ d]
        simp
      · simp
  | @insert p P hpP ih =>
      have hp := hPprime p (Finset.mem_insert_self p P)
      have hpCut := hPcut p (Finset.mem_insert_self p P)
      have hPprime' : ∀ q ∈ P, q.Prime := fun q hq =>
        hPprime q (Finset.mem_insert_of_mem hq)
      have hPcut' : ∀ q ∈ P, tinyCutoff K < q := fun q hq =>
        hPcut q (Finset.mem_insert_of_mem hq)
      have hcard' : P.card ≤ 4 := by
        rw [Finset.card_insert_of_notMem hpP] at hcard
        omega
      have hstep' : ∀ {W v q : ℕ}
          {y : (nearShifts K → ℕ) → ℝ}
          (hq : q ∈ P) (hqW : Nat.Coprime q W)
          (hyq : IsSupportedMaynardY (nearShifts K) (globalRadius K) W y)
          (hyqSharp : IsVaryingSupported K y), ∀ n,
          (if q ∣ n + k then fromYWeight (globalRadius K) W v y n else 0) =
            fromYWeight (globalRadius K) (W * q)
              (extendPrimeEventResidue hqW.symm v k)
              (erasePrimeY (globalRadius K) W q y) n := by
        intro W v q y hq hqW hyq hyqSharp
        exact hstep (Finset.mem_insert_of_mem hq) hqW hyq hyqSharp
      obtain ⟨y, v, hy, hySharp, hyBound, hpoint, henergy⟩ :=
        ih hcard' hPprime' hPcut' hstep'
      have hpW := prime_coprime_preSieve_mul_prod hp hpCut hpP hPprime'
      let z := erasePrimeY (globalRadius K)
        (preSieveModulus K * ∏ q ∈ P, q) p y
      let v' := extendPrimeEventResidue hpW.symm v k
      refine ⟨z, v', ?_, ?_, ?_, ?_, ?_⟩
      · simpa [z, Finset.prod_insert hpP, mul_assoc, mul_left_comm,
          mul_comm] using erasePrimeY_supported (globalRadius K)
            (preSieveModulus K * ∏ q ∈ P, q) p y
      · exact erasePrimeY_varyingSupported hp.pos hySharp
      · intro r
        have hraw := abs_erasePrimeY_le
          (R := globalRadius K)
          (W := preSieveModulus K * ∏ q ∈ P, q)
          (B := (2 : ℝ) ^ P.card) (by positivity) hyBound hp r
        have hfactor : (1 : ℝ) + (Fintype.card (nearShifts K) : ℝ) /
            (p - 1 : ℕ) ≤ 2 := by
          rw [Fintype.card_coe, nearShifts_card]
          have hKle : K ≤ p - 1 := (K_le_tinyCutoff K).trans (by omega)
          have hden : (0 : ℝ) < (p - 1 : ℕ) := by
            exact_mod_cast Nat.sub_pos_of_lt hp.one_lt
          have hdiv : (K : ℝ) / (p - 1 : ℕ) ≤ 1 := by
            apply (div_le_iff₀ hden).2
            norm_num
            exact_mod_cast hKle
          linarith
        calc
          |z r| ≤ (2 : ℝ) ^ P.card *
              (1 + (Fintype.card (nearShifts K) : ℝ) / (p - 1 : ℕ)) := by
            simpa [z] using hraw
          _ ≤ (2 : ℝ) ^ P.card * 2 :=
            mul_le_mul_of_nonneg_left hfactor (by positivity)
          _ = (2 : ℝ) ^ (Finset.card (insert p P)) := by
            rw [Finset.card_insert_of_notMem hpP, pow_succ]
      · intro n
        have hone := hstep (v := v) (Finset.mem_insert_self p P) hpW hy hySharp n
        rw [show (if ∀ q ∈ insert p P, q ∣ n + k then sieveWeight K n else 0) =
            if p ∣ n + k then
              (if ∀ q ∈ P, q ∣ n + k then sieveWeight K n else 0)
            else 0 by
          by_cases hpn : p ∣ n + k <;> simp [hpn]]
        rw [hpoint n, hone]
        simpa only [z, v', Finset.prod_insert hpP, mul_assoc, mul_left_comm,
          mul_comm]
      · have hKp : K ≤ p - 1 :=
          (K_le_tinyCutoff K).trans (by omega)
        have hpEnergy := abs_varyingYEnergy_erasePrimeY_sub_le_uniform hp hKp
          hy (B := (2 : ℝ) ^ P.card) (by positivity)
          (two_pow_card_le_16 hcard') hyBound
        have htri := abs_sub_le (varyingYEnergy K z) (varyingYEnergy K y)
          (varyingYEnergy K (sieveY K))
        calc
          |varyingYEnergy K z - varyingYEnergy K (sieveY K)| ≤
              |varyingYEnergy K z - varyingYEnergy K y| +
                |varyingYEnergy K y - varyingYEnergy K (sieveY K)| := htri
          _ ≤ 2048 * ((K : ℝ) / Nat.totient p) *
                (∏ h : nearShifts K, varyingCoordinateMajorant K h) +
              2048 * (∑ q ∈ P, (K : ℝ) / Nat.totient q) *
                ∏ h : nearShifts K, varyingCoordinateMajorant K h := by
            exact add_le_add (by simpa [z] using hpEnergy) henergy
          _ = 2048 * (∑ q ∈ insert p P,
                (K : ℝ) / Nat.totient q) *
              ∏ h : nearShifts K, varyingCoordinateMajorant K h := by
            rw [Finset.sum_insert hpP]
            ring

/-- The common (unperturbed) CRT main mass.  All centered prime-product
correlations are compared with this same quantity divided by the prime
product. -/
def sieveCommonMainMass (K : ℕ) : ℝ :=
  (intervalStart K : ℝ) / preSieveModulus K *
    (varyingYEnergy K (sieveY K) -
      incompatibleDivisorPairCommonDivisorTupleSum (nearShifts K)
        (sieveDivisorSupport K) (sieveCoefficient K))

theorem sieveMass_eq_commonMain_add_error (K : ℕ) :
    sieveMass K = sieveCommonMainMass K +
      compatibleDivisorPairErrorSum (nearShifts K) (sieveDivisorSupport K)
        0 (preSieveModulus K) (intervalStart K) (sieveCoefficient K) := by
  rw [sieveMass_eq_main_add_error, sieveMain_eq_diagonal_sub_cross]
  rw [maynardYDiagonalSum_eq_varyingYEnergy (dvd_refl _)
    (sieveY_supported K) (sieveY_varyingSupported K)]
  rfl

/-- Centered correlation estimate from any quantitative prime-product erase
transform.  It compares the actual event mass with `sieveMass / ∏ P`.
The three terms in the explicit error are respectively the accumulated
diagonal perturbation, the two cross corrections (`256 + 1`), and the two
interval errors (`256 + 1`). -/
theorem primeProductEventMass_sub_sieveMass_div_le_of_transform
    {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K k : ℕ} {P : Finset ℕ} (hreg : NormalizationRegular A K)
    (hcard : P.card ≤ 4) (hPprime : ∀ p ∈ P, p.Prime)
    {y : (nearShifts K → ℕ) → ℝ} {v : ℕ}
    (hy : IsSupportedMaynardY (nearShifts K) (globalRadius K)
      (preSieveModulus K * ∏ p ∈ P, p) y)
    (hySharp : IsVaryingSupported K y)
    (hyBound : ∀ r, |y r| ≤ (2 : ℝ) ^ P.card)
    (hpoint : ∀ n,
      (if ∀ p ∈ P, p ∣ n + k then sieveWeight K n else 0) =
        fromYWeight (globalRadius K)
          (preSieveModulus K * ∏ p ∈ P, p) v y n)
    (henergy :
      |varyingYEnergy K y - varyingYEnergy K (sieveY K)| ≤
        2048 * (∑ p ∈ P, (K : ℝ) / Nat.totient p) *
          ∏ h : nearShifts K, varyingCoordinateMajorant K h) :
    |primeProductEventMass K k P -
        sieveMass K / (∏ p ∈ P, p : ℕ)| ≤
      (intervalStart K : ℝ) /
          (preSieveModulus K * ∏ p ∈ P, p) *
        ((2048 * (∑ p ∈ P, (K : ℝ) / Nat.totient p) +
            257 * roughCrossTupleTotientSquareTail (nearShifts K)
              (tinyCutoff K) (globalRadius K)) *
          96 ^ K * productCoordinateEnergy K) +
        (radiusProduct K : ℝ) ^ 6 * 257 := by
  let q : ℕ := ∏ p ∈ P, p
  let W : ℕ := preSieveModulus K * q
  let M : ℝ := ∏ h : nearShifts K, varyingCoordinateMajorant K h
  let T : ℝ := roughCrossTupleTotientSquareTail (nearShifts K)
    (tinyCutoff K) (globalRadius K)
  let C : ℝ := incompatibleDivisorPairCommonDivisorTupleSum (nearShifts K)
    (maynardDivisorTupleSupport (nearShifts K) (globalRadius K) W)
    (maynardCoefficientFromY (nearShifts K) (globalRadius K) W y)
  let E : ℝ := compatibleDivisorPairErrorSum (nearShifts K)
    (maynardDivisorTupleSupport (nearShifts K) (globalRadius K) W)
    v W (intervalStart K)
    (maynardCoefficientFromY (nearShifts K) (globalRadius K) W y)
  let C₀ : ℝ := incompatibleDivisorPairCommonDivisorTupleSum (nearShifts K)
    (maynardDivisorTupleSupport (nearShifts K) (globalRadius K)
      (preSieveModulus K))
    (maynardCoefficientFromY (nearShifts K) (globalRadius K)
      (preSieveModulus K) (sieveY K))
  let E₀ : ℝ := compatibleDivisorPairErrorSum (nearShifts K)
    (maynardDivisorTupleSupport (nearShifts K) (globalRadius K)
      (preSieveModulus K)) 0 (preSieveModulus K) (intervalStart K)
    (maynardCoefficientFromY (nearShifts K) (globalRadius K)
      (preSieveModulus K) (sieveY K))
  have hq : 0 < q := by simpa [q] using primeProduct_pos hPprime
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hW : 0 < W := mul_pos (preSieveModulus_pos K) hq
  have hmod : preSieveModulus K ∣ W := by
    dsimp [W]
    exact dvd_mul_right _ _
  have hX : 0 ≤ (intervalStart K : ℝ) / W := by positivity
  have hM : 0 ≤ M := by
    dsimp [M]
    apply Finset.prod_nonneg
    intro h hh
    unfold varyingCoordinateMajorant squarefreeCoprimeInvTotientMean
    positivity
  have hT : 0 ≤ T := by
    dsimp [T]
    unfold roughCrossTupleTotientSquareTail
    apply Finset.sum_nonneg
    intro s hs
    unfold crossTotientSquareWeight
    positivity
  have hyBound16 : ∀ r, |y r| ≤ 16 := fun r =>
    (hyBound r).trans (two_pow_card_le_16 hcard)
  have hC : |C| ≤ 256 * T * M := by
    have hbase := abs_incompatibleSum_le_sharp_varying (globalRadius_pos K)
      hmod hy hySharp (B := (16 : ℝ)) (by norm_num) hyBound16
    norm_num at hbase
    simpa [C, T, M, W] using hbase
  have hC₀ : |C₀| ≤ T * M := by
    have hbase := abs_incompatibleSum_le_sharp_varying (globalRadius_pos K)
      (dvd_refl (preSieveModulus K)) (sieveY_supported K)
      (sieveY_varyingSupported K) (B := (1 : ℝ)) (by norm_num)
      (abs_sieveY_le_one K)
    simpa [C₀, T, M] using hbase
  have hE : |E| ≤ (radiusProduct K : ℝ) ^ 6 * 256 := by
    have herr := abs_transformedIntervalError_le (v := v)
      (N := intervalStart K) hmod hW hy hySharp
      (B := (16 : ℝ)) (by norm_num) hyBound16
    norm_num at herr
    simpa [E, W] using herr
  have hE₀ : |E₀| ≤ (radiusProduct K : ℝ) ^ 6 := by
    have herr := abs_transformedIntervalError_le (v := 0)
      (N := intervalStart K)
      (dvd_refl (preSieveModulus K)) (preSieveModulus_pos K)
      (sieveY_supported K) (sieveY_varyingSupported K)
      (B := (1 : ℝ)) (by norm_num) (abs_sieveY_le_one K)
    simpa [E₀] using herr
  have hmajorant : M ≤ 96 ^ K * productCoordinateEnergy K := by
    simpa [M] using varyingMajorantProduct_le_energy hA hreg
  have hevent : primeProductEventMass K k P =
      (intervalStart K : ℝ) / W * (varyingYEnergy K y - C) + E := by
    calc
      primeProductEventMass K k P =
          sieveWeightSum (intervalStart K)
            (fromYWeight (globalRadius K) W v y) := by
        unfold primeProductEventMass sieveWeightSum
        apply Finset.sum_congr rfl
        intro n hn
        simpa [W, q] using hpoint n
      _ = _ := by
        simpa [C, E] using
          fromYWeightMass_eq_diagonal_sub_cross_add_error hmod hy hySharp
  have hsieve : sieveMass K =
      (intervalStart K : ℝ) / preSieveModulus K *
        (varyingYEnergy K (sieveY K) - C₀) + E₀ := by
    have hsievePoint : sieveWeight K =
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
    unfold sieveMass
    rw [hsievePoint]
    simpa [C₀, E₀] using
      fromYWeightMass_eq_diagonal_sub_cross_add_error
        (dvd_refl (preSieveModulus K)) (sieveY_supported K)
        (sieveY_varyingSupported K) (v := 0)
  have hscale : (intervalStart K : ℝ) / W =
      ((intervalStart K : ℝ) / preSieveModulus K) / q := by
    dsimp [W]
    push_cast
    field_simp
  have hdecomp : primeProductEventMass K k P - sieveMass K / q =
      (intervalStart K : ℝ) / W *
          ((varyingYEnergy K y - varyingYEnergy K (sieveY K)) - C + C₀) +
        (E - E₀ / q) := by
    rw [hevent, hsieve, hscale]
    ring
  rw [show (∏ p ∈ P, p : ℕ) = q by rfl, hdecomp]
  have hz :
      |(varyingYEnergy K y - varyingYEnergy K (sieveY K)) - C + C₀| ≤
        2048 * (∑ p ∈ P, (K : ℝ) / Nat.totient p) * M +
          257 * T * M := by
    calc
      |(varyingYEnergy K y - varyingYEnergy K (sieveY K)) - C + C₀| ≤
          |varyingYEnergy K y - varyingYEnergy K (sieveY K)| + |C| + |C₀| := by
        have hsub :
            |(varyingYEnergy K y - varyingYEnergy K (sieveY K)) - C| ≤
              |varyingYEnergy K y - varyingYEnergy K (sieveY K)| + |C| := by
          simpa using abs_sub_le
            (varyingYEnergy K y - varyingYEnergy K (sieveY K)) 0 C
        calc
          _ ≤ |(varyingYEnergy K y - varyingYEnergy K (sieveY K)) - C| +
              |C₀| := abs_add_le _ _
          _ ≤ (|varyingYEnergy K y - varyingYEnergy K (sieveY K)| + |C|) +
              |C₀| := add_le_add hsub le_rfl
      _ ≤ 2048 * (∑ p ∈ P, (K : ℝ) / Nat.totient p) * M +
          256 * T * M + T * M := by
        exact add_le_add (add_le_add (by simpa [M] using henergy) hC) hC₀
      _ = _ := by ring
  have herrorPart : |E - E₀ / q| ≤
      (radiusProduct K : ℝ) ^ 6 * 257 := by
    calc
      |E - E₀ / q| ≤ |E| + |E₀ / q| := by
        simpa using abs_sub_le E 0 (E₀ / q)
      _ = |E| + |E₀| / q := by rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ q)]
      _ ≤ (radiusProduct K : ℝ) ^ 6 * 256 +
          (radiusProduct K : ℝ) ^ 6 := by
        apply add_le_add hE
        exact (div_le_self (abs_nonneg E₀) hq1).trans
          (by simpa using hE₀)
      _ = _ := by ring
  calc
    |(intervalStart K : ℝ) / W *
          ((varyingYEnergy K y - varyingYEnergy K (sieveY K)) - C + C₀) +
        (E - E₀ / q)| ≤
        (intervalStart K : ℝ) / W *
          |(varyingYEnergy K y - varyingYEnergy K (sieveY K)) - C + C₀| +
        |E - E₀ / q| := by
      calc
        _ ≤ |(intervalStart K : ℝ) / W *
              ((varyingYEnergy K y - varyingYEnergy K (sieveY K)) - C + C₀)| +
            |E - E₀ / q| := abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_of_nonneg hX]
    _ ≤ (intervalStart K : ℝ) / W *
          (2048 * (∑ p ∈ P, (K : ℝ) / Nat.totient p) * M +
            257 * T * M) +
        (radiusProduct K : ℝ) ^ 6 * 257 :=
      add_le_add (mul_le_mul_of_nonneg_left hz hX) herrorPart
    _ = (intervalStart K : ℝ) / W *
          ((2048 * (∑ p ∈ P, (K : ℝ) / Nat.totient p) + 257 * T) * M) +
        (radiusProduct K : ℝ) ^ 6 * 257 := by ring
    _ ≤ (intervalStart K : ℝ) / W *
          ((2048 * (∑ p ∈ P, (K : ℝ) / Nat.totient p) + 257 * T) *
            (96 ^ K * productCoordinateEnergy K)) +
        (radiusProduct K : ℝ) ^ 6 * 257 := by
      apply add_le_add _ le_rfl
      apply mul_le_mul_of_nonneg_left _ hX
      apply mul_le_mul_of_nonneg_left hmajorant
      exact add_nonneg
        (mul_nonneg (by norm_num) (Finset.sum_nonneg fun p hp => by positivity))
        (mul_nonneg (by norm_num) hT)
    _ = _ := by
      dsimp [W, q, T]
      push_cast
      ring

/-- Exact transformed formula for a prime-product event at a far shift. -/
theorem exists_farPrimeProductEventMassFormula
    {K k : ℕ} {P : Finset ℕ}
    (hk : ∀ h : nearShifts K, k ≠ h.1)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPcut : ∀ p ∈ P, tinyCutoff K < p)
    (hPsep : ∀ p ∈ P, ∀ h : nearShifts K, Nat.dist k h.1 < p) :
    ∃ (y : (nearShifts K → ℕ) → ℝ) (v : ℕ),
      IsSupportedMaynardY (nearShifts K) (globalRadius K)
          (preSieveModulus K * ∏ p ∈ P, p) y ∧
      IsVaryingSupported K y ∧
      (∀ r, |y r| ≤ (2 : ℝ) ^ P.card) ∧
      primeProductEventMass K k P =
        (intervalStart K : ℝ) /
            (preSieveModulus K * ∏ p ∈ P, p) *
          (varyingYEnergy K y -
            incompatibleDivisorPairCommonDivisorTupleSum (nearShifts K)
              (maynardDivisorTupleSupport (nearShifts K) (globalRadius K)
                (preSieveModulus K * ∏ p ∈ P, p))
              (maynardCoefficientFromY (nearShifts K) (globalRadius K)
                (preSieveModulus K * ∏ p ∈ P, p) y)) +
          compatibleDivisorPairErrorSum (nearShifts K)
            (maynardDivisorTupleSupport (nearShifts K) (globalRadius K)
              (preSieveModulus K * ∏ p ∈ P, p)) v
            (preSieveModulus K * ∏ p ∈ P, p) (intervalStart K)
            (maynardCoefficientFromY (nearShifts K) (globalRadius K)
              (preSieveModulus K * ∏ p ∈ P, p) y) := by
  obtain ⟨y, v, hy, hySharp, hyBound, hpoint⟩ :=
    exists_separatedPrimeProductTransform hk hPprime hPcut hPsep
  refine ⟨y, v, hy, hySharp, hyBound, ?_⟩
  have hmod : preSieveModulus K ∣
      preSieveModulus K * ∏ p ∈ P, p := dvd_mul_right _ _
  calc
    primeProductEventMass K k P =
        sieveWeightSum (intervalStart K)
          (fromYWeight (globalRadius K)
            (preSieveModulus K * ∏ p ∈ P, p) v y) := by
      unfold primeProductEventMass sieveWeightSum
      apply Finset.sum_congr rfl
      intro n hn
      exact hpoint n
    _ = _ := by
      simpa only [Nat.cast_mul] using
        fromYWeightMass_eq_diagonal_sub_cross_add_error hmod hy hySharp

/-- Explicit `256`-bound for a far event involving at most four primes. -/
theorem farPrimeProductEventMass_le
    {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K k : ℕ} {P : Finset ℕ} (hreg : NormalizationRegular A K)
    (hcard : P.card ≤ 4)
    (hk : ∀ h : nearShifts K, k ≠ h.1)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPcut : ∀ p ∈ P, tinyCutoff K < p)
    (hPsep : ∀ p ∈ P, ∀ h : nearShifts K, Nat.dist k h.1 < p) :
    primeProductEventMass K k P ≤
      (intervalStart K : ℝ) /
          (preSieveModulus K * ∏ p ∈ P, p) *
        (256 * (1 + roughCrossTupleTotientSquareTail (nearShifts K)
            (tinyCutoff K) (globalRadius K)) *
          96 ^ K * productCoordinateEnergy K) +
        (radiusProduct K : ℝ) ^ 6 * 256 := by
  obtain ⟨y, v, hy, hySharp, hyBound, hpoint⟩ :=
    exists_separatedPrimeProductTransform hk hPprime hPcut hPsep
  let W := preSieveModulus K * ∏ p ∈ P, p
  have hmod : preSieveModulus K ∣ W := by
    exact dvd_mul_right _ _
  have hW : 0 < W := by
    exact mul_pos (preSieveModulus_pos K) (primeProduct_pos hPprime)
  have hraw := fromYWeightMass_le_productCoordinateEnergy hA hreg hmod hW
    hy hySharp (B := (2 : ℝ) ^ P.card) (by positivity) hyBound (v := v)
  have hmass : primeProductEventMass K k P =
      sieveWeightSum (intervalStart K) (fromYWeight (globalRadius K) W v y) := by
    unfold primeProductEventMass sieveWeightSum
    apply Finset.sum_congr rfl
    intro n hn
    simpa [W] using hpoint n
  rw [hmass]
  have htail : 0 ≤ roughCrossTupleTotientSquareTail (nearShifts K)
      (tinyCutoff K) (globalRadius K) := by
    unfold roughCrossTupleTotientSquareTail crossTotientSquareWeight
    positivity
  let L : ℝ :=
      (1 + roughCrossTupleTotientSquareTail (nearShifts K)
          (tinyCutoff K) (globalRadius K)) *
        96 ^ K * productCoordinateEnergy K
  have hL : 0 ≤ L := by
    dsimp [L]
    exact mul_nonneg
      (mul_nonneg (add_nonneg zero_le_one htail) (by positivity))
      (productCoordinateEnergy_nonneg K)
  calc
    sieveWeightSum (intervalStart K) (fromYWeight (globalRadius K) W v y) ≤
        (intervalStart K : ℝ) / W *
          ((((2 : ℝ) ^ P.card) ^ 2) *
            (1 + roughCrossTupleTotientSquareTail (nearShifts K)
              (tinyCutoff K) (globalRadius K)) *
            96 ^ K * productCoordinateEnergy K) +
          (radiusProduct K : ℝ) ^ 6 * (((2 : ℝ) ^ P.card) ^ 2) := hraw
    _ ≤ (intervalStart K : ℝ) / W *
          (256 * (1 + roughCrossTupleTotientSquareTail (nearShifts K)
            (tinyCutoff K) (globalRadius K)) *
            96 ^ K * productCoordinateEnergy K) +
        (radiusProduct K : ℝ) ^ 6 * 256 := by
      calc
        (intervalStart K : ℝ) / W *
              ((((2 : ℝ) ^ P.card) ^ 2) *
                (1 + roughCrossTupleTotientSquareTail (nearShifts K)
                  (tinyCutoff K) (globalRadius K)) *
                96 ^ K * productCoordinateEnergy K) +
            (radiusProduct K : ℝ) ^ 6 * (((2 : ℝ) ^ P.card) ^ 2) =
            (intervalStart K : ℝ) / W *
              ((((2 : ℝ) ^ P.card) ^ 2) * L) +
            (radiusProduct K : ℝ) ^ 6 * (((2 : ℝ) ^ P.card) ^ 2) := by
              dsimp [L]
              ring
        _ ≤ (intervalStart K : ℝ) / W * (256 * L) +
            (radiusProduct K : ℝ) ^ 6 * 256 := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (two_pow_card_sq_le_256 hcard) hL)
              (by positivity)
          · exact mul_le_mul_of_nonneg_left
              (two_pow_card_sq_le_256 hcard) (by positivity)
        _ = _ := by
          dsimp [L]
          ring
    _ = _ := by simp only [W, Nat.cast_mul]

/-- Exact transformed formula for a near-coordinate event whose event primes
all lie beyond that coordinate's radius. -/
theorem exists_nearLargePrimeProductEventMassFormula
    {K : ℕ} (m : nearShifts K) {P : Finset ℕ}
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPcut : ∀ p ∈ P, tinyCutoff K < p)
    (hPradius : ∀ p ∈ P, shiftRadius K m ≤ p)
    (hPsep : ∀ p ∈ P, ∀ h : nearShifts K,
      h ≠ m → Nat.dist m.1 h.1 < p) :
    ∃ (y : (nearShifts K → ℕ) → ℝ) (v : ℕ),
      IsSupportedMaynardY (nearShifts K) (globalRadius K)
          (preSieveModulus K * ∏ p ∈ P, p) y ∧
      IsVaryingSupported K y ∧
      (∀ r, |y r| ≤ (2 : ℝ) ^ P.card) ∧
      primeProductEventMass K m.1 P =
        (intervalStart K : ℝ) /
            (preSieveModulus K * ∏ p ∈ P, p) *
          (varyingYEnergy K y -
            incompatibleDivisorPairCommonDivisorTupleSum (nearShifts K)
              (maynardDivisorTupleSupport (nearShifts K) (globalRadius K)
                (preSieveModulus K * ∏ p ∈ P, p))
              (maynardCoefficientFromY (nearShifts K) (globalRadius K)
                (preSieveModulus K * ∏ p ∈ P, p) y)) +
          compatibleDivisorPairErrorSum (nearShifts K)
            (maynardDivisorTupleSupport (nearShifts K) (globalRadius K)
              (preSieveModulus K * ∏ p ∈ P, p)) v
            (preSieveModulus K * ∏ p ∈ P, p) (intervalStart K)
            (maynardCoefficientFromY (nearShifts K) (globalRadius K)
              (preSieveModulus K * ∏ p ∈ P, p) y) := by
  obtain ⟨y, v, hy, hySharp, hyBound, hpoint⟩ :=
    exists_largeCoordinatePrimeProductTransform m hPprime hPcut hPradius hPsep
  refine ⟨y, v, hy, hySharp, hyBound, ?_⟩
  have hmod : preSieveModulus K ∣
      preSieveModulus K * ∏ p ∈ P, p := dvd_mul_right _ _
  calc
    primeProductEventMass K m.1 P =
        sieveWeightSum (intervalStart K)
          (fromYWeight (globalRadius K)
            (preSieveModulus K * ∏ p ∈ P, p) v y) := by
      unfold primeProductEventMass sieveWeightSum
      apply Finset.sum_congr rfl
      intro n hn
      exact hpoint n
    _ = _ := by
      simpa only [Nat.cast_mul] using
        fromYWeightMass_eq_diagonal_sub_cross_add_error hmod hy hySharp

/-- Explicit `256`-bound for a near-coordinate large-prime event involving
at most four primes. -/
theorem nearLargePrimeProductEventMass_le
    {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K : ℕ} (m : nearShifts K) {P : Finset ℕ}
    (hreg : NormalizationRegular A K) (hcard : P.card ≤ 4)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPcut : ∀ p ∈ P, tinyCutoff K < p)
    (hPradius : ∀ p ∈ P, shiftRadius K m ≤ p)
    (hPsep : ∀ p ∈ P, ∀ h : nearShifts K,
      h ≠ m → Nat.dist m.1 h.1 < p) :
    primeProductEventMass K m.1 P ≤
      (intervalStart K : ℝ) /
          (preSieveModulus K * ∏ p ∈ P, p) *
        (256 * (1 + roughCrossTupleTotientSquareTail (nearShifts K)
            (tinyCutoff K) (globalRadius K)) *
          96 ^ K * productCoordinateEnergy K) +
        (radiusProduct K : ℝ) ^ 6 * 256 := by
  obtain ⟨y, v, hy, hySharp, hyBound, hpoint⟩ :=
    exists_largeCoordinatePrimeProductTransform m hPprime hPcut hPradius hPsep
  let W := preSieveModulus K * ∏ p ∈ P, p
  have hmod : preSieveModulus K ∣ W := dvd_mul_right _ _
  have hW : 0 < W :=
    mul_pos (preSieveModulus_pos K) (primeProduct_pos hPprime)
  have hraw := fromYWeightMass_le_productCoordinateEnergy hA hreg hmod hW
    hy hySharp (B := (2 : ℝ) ^ P.card) (by positivity) hyBound (v := v)
  have hmass : primeProductEventMass K m.1 P =
      sieveWeightSum (intervalStart K) (fromYWeight (globalRadius K) W v y) := by
    unfold primeProductEventMass sieveWeightSum
    apply Finset.sum_congr rfl
    intro n hn
    simpa [W] using hpoint n
  rw [hmass]
  have htail : 0 ≤ roughCrossTupleTotientSquareTail (nearShifts K)
      (tinyCutoff K) (globalRadius K) := by
    unfold roughCrossTupleTotientSquareTail crossTotientSquareWeight
    positivity
  let L : ℝ :=
      (1 + roughCrossTupleTotientSquareTail (nearShifts K)
          (tinyCutoff K) (globalRadius K)) *
        96 ^ K * productCoordinateEnergy K
  have hL : 0 ≤ L := by
    dsimp [L]
    exact mul_nonneg
      (mul_nonneg (add_nonneg zero_le_one htail) (by positivity))
      (productCoordinateEnergy_nonneg K)
  calc
    sieveWeightSum (intervalStart K) (fromYWeight (globalRadius K) W v y) ≤
        (intervalStart K : ℝ) / W *
          ((((2 : ℝ) ^ P.card) ^ 2) *
            (1 + roughCrossTupleTotientSquareTail (nearShifts K)
              (tinyCutoff K) (globalRadius K)) *
            96 ^ K * productCoordinateEnergy K) +
          (radiusProduct K : ℝ) ^ 6 * (((2 : ℝ) ^ P.card) ^ 2) := hraw
    _ ≤ (intervalStart K : ℝ) / W *
          (256 * (1 + roughCrossTupleTotientSquareTail (nearShifts K)
            (tinyCutoff K) (globalRadius K)) *
            96 ^ K * productCoordinateEnergy K) +
        (radiusProduct K : ℝ) ^ 6 * 256 := by
      calc
        (intervalStart K : ℝ) / W *
              ((((2 : ℝ) ^ P.card) ^ 2) *
                (1 + roughCrossTupleTotientSquareTail (nearShifts K)
                  (tinyCutoff K) (globalRadius K)) *
                96 ^ K * productCoordinateEnergy K) +
            (radiusProduct K : ℝ) ^ 6 * (((2 : ℝ) ^ P.card) ^ 2) =
            (intervalStart K : ℝ) / W *
              ((((2 : ℝ) ^ P.card) ^ 2) * L) +
            (radiusProduct K : ℝ) ^ 6 * (((2 : ℝ) ^ P.card) ^ 2) := by
              dsimp [L]
              ring
        _ ≤ (intervalStart K : ℝ) / W * (256 * L) +
            (radiusProduct K : ℝ) ^ 6 * 256 := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (two_pow_card_sq_le_256 hcard) hL)
              (by positivity)
          · exact mul_le_mul_of_nonneg_left
              (two_pow_card_sq_le_256 hcard) (by positivity)
        _ = _ := by
          dsimp [L]
          ring
    _ = _ := by simp only [W, Nat.cast_mul]

/-- Far-shift specialization of the quantitative erase-transform iteration. -/
theorem exists_farPrimeProductTransform_energy
    {K k : ℕ} {P : Finset ℕ} (hcard : P.card ≤ 4)
    (hk : ∀ h : nearShifts K, k ≠ h.1)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPcut : ∀ p ∈ P, tinyCutoff K < p)
    (hPsep : ∀ p ∈ P, ∀ h : nearShifts K, Nat.dist k h.1 < p) :
    ∃ (y : (nearShifts K → ℕ) → ℝ) (v : ℕ),
      IsSupportedMaynardY (nearShifts K) (globalRadius K)
          (preSieveModulus K * ∏ p ∈ P, p) y ∧
      IsVaryingSupported K y ∧
      (∀ r, |y r| ≤ (2 : ℝ) ^ P.card) ∧
      (∀ n, (if ∀ p ∈ P, p ∣ n + k then sieveWeight K n else 0) =
        fromYWeight (globalRadius K)
          (preSieveModulus K * ∏ p ∈ P, p) v y n) ∧
      |varyingYEnergy K y - varyingYEnergy K (sieveY K)| ≤
        2048 * (∑ p ∈ P, (K : ℝ) / Nat.totient p) *
          ∏ h : nearShifts K, varyingCoordinateMajorant K h := by
  apply exists_primeProductEraseTransform_energy hcard hPprime hPcut
  intro W v p y hpMem hpW hy hySharp n
  exact indicator_separatedPrime_fromYWeight
    (R := globalRadius K) (v := v) (n := n)
    (hPprime p hpMem) hpW hy hk (hPsep p hpMem)

/-- Near-coordinate specialization of the quantitative erase-transform
iteration when every event prime is beyond the distinguished radius. -/
theorem exists_nearLargePrimeProductTransform_energy
    {K : ℕ} (m : nearShifts K) {P : Finset ℕ} (hcard : P.card ≤ 4)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPcut : ∀ p ∈ P, tinyCutoff K < p)
    (hPradius : ∀ p ∈ P, shiftRadius K m ≤ p)
    (hPsep : ∀ p ∈ P, ∀ h : nearShifts K,
      h ≠ m → Nat.dist m.1 h.1 < p) :
    ∃ (y : (nearShifts K → ℕ) → ℝ) (v : ℕ),
      IsSupportedMaynardY (nearShifts K) (globalRadius K)
          (preSieveModulus K * ∏ p ∈ P, p) y ∧
      IsVaryingSupported K y ∧
      (∀ r, |y r| ≤ (2 : ℝ) ^ P.card) ∧
      (∀ n, (if ∀ p ∈ P, p ∣ n + m.1 then sieveWeight K n else 0) =
        fromYWeight (globalRadius K)
          (preSieveModulus K * ∏ p ∈ P, p) v y n) ∧
      |varyingYEnergy K y - varyingYEnergy K (sieveY K)| ≤
        2048 * (∑ p ∈ P, (K : ℝ) / Nat.totient p) *
          ∏ h : nearShifts K, varyingCoordinateMajorant K h := by
  apply exists_primeProductEraseTransform_energy hcard hPprime hPcut
  intro W v p y hpMem hpW hy hySharp n
  have hone := indicator_coordinatePrime_fromYWeight
    (R := globalRadius K) (v := v) (n := n)
    (hPprime p hpMem) hpW hy m (hPsep p hpMem)
  rw [differencePrimeY_eq_erasePrimeY_of_radius_le hy hySharp m
    (hPradius p hpMem)] at hone
  exact hone

/-- Centered far-shift correlation for every squarefree product of at most
four relevant primes. -/
theorem farPrimeProductEventMass_centered_le
    {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K k : ℕ} {P : Finset ℕ} (hreg : NormalizationRegular A K)
    (hcard : P.card ≤ 4)
    (hk : ∀ h : nearShifts K, k ≠ h.1)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPcut : ∀ p ∈ P, tinyCutoff K < p)
    (hPsep : ∀ p ∈ P, ∀ h : nearShifts K, Nat.dist k h.1 < p) :
    |primeProductEventMass K k P -
        sieveMass K / (∏ p ∈ P, p : ℕ)| ≤
      (intervalStart K : ℝ) /
          (preSieveModulus K * ∏ p ∈ P, p) *
        ((2048 * (∑ p ∈ P, (K : ℝ) / Nat.totient p) +
            257 * roughCrossTupleTotientSquareTail (nearShifts K)
              (tinyCutoff K) (globalRadius K)) *
          96 ^ K * productCoordinateEnergy K) +
        (radiusProduct K : ℝ) ^ 6 * 257 := by
  obtain ⟨y, v, hy, hySharp, hyBound, hpoint, henergy⟩ :=
    exists_farPrimeProductTransform_energy hcard hk hPprime hPcut hPsep
  exact primeProductEventMass_sub_sieveMass_div_le_of_transform hA hreg
    hcard hPprime hy hySharp hyBound hpoint henergy

/-- Centered near-coordinate correlation for squarefree products of at most
four primes beyond the coordinate radius. -/
theorem nearLargePrimeProductEventMass_centered_le
    {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K : ℕ} (m : nearShifts K) {P : Finset ℕ}
    (hreg : NormalizationRegular A K) (hcard : P.card ≤ 4)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPcut : ∀ p ∈ P, tinyCutoff K < p)
    (hPradius : ∀ p ∈ P, shiftRadius K m ≤ p)
    (hPsep : ∀ p ∈ P, ∀ h : nearShifts K,
      h ≠ m → Nat.dist m.1 h.1 < p) :
    |primeProductEventMass K m.1 P -
        sieveMass K / (∏ p ∈ P, p : ℕ)| ≤
      (intervalStart K : ℝ) /
          (preSieveModulus K * ∏ p ∈ P, p) *
        ((2048 * (∑ p ∈ P, (K : ℝ) / Nat.totient p) +
            257 * roughCrossTupleTotientSquareTail (nearShifts K)
              (tinyCutoff K) (globalRadius K)) *
          96 ^ K * productCoordinateEnergy K) +
        (radiusProduct K : ℝ) ^ 6 * 257 := by
  obtain ⟨y, v, hy, hySharp, hyBound, hpoint, henergy⟩ :=
    exists_nearLargePrimeProductTransform_energy m hcard hPprime hPcut
      hPradius hPsep
  exact primeProductEventMass_sub_sieveMass_div_le_of_transform hA hreg
    hcard hPprime hy hySharp hyBound hpoint henergy

end Erdos248
