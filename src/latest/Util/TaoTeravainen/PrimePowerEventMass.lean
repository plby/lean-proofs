import ErdosProblems.Erdos248.MediumEventMass
import Util.TaoTeravainen.PrimePowerTransform

/-!
# Tao--Teräväinen: weighted masses of prime-power events

For primes above the pre-sieve cutoff, a prime-power event has the same
one-prime Y-transform as the corresponding prime event. The lifted modulus
therefore gains the full density factor p^a while the transformed energy
remains uniformly bounded.
-/

noncomputable section

open scoped BigOperators
open BoundedGaps.Maynard

namespace TaoTeravainen

local instance primePowerEventMassDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- Unnormalized weighted mass of the event p^a ∣ n + k. -/
def primePowerEventMass (K k p a : ℕ) : ℝ :=
  sieveWeightSum (Erdos248.intervalStart K) fun n =>
    if p ^ a ∣ n + k then Erdos248.sieveWeight K n else 0

/-- Unnormalized weighted mass of the intersection of two prime-power
events at the same shift. -/
def primePowerPairEventMass (K k p a q b : ℕ) : ℝ :=
  sieveWeightSum (Erdos248.intervalStart K) fun n =>
    if p ^ a ∣ n + k ∧ q ^ b ∣ n + k then
      Erdos248.sieveWeight K n else 0

theorem primePowerEventMass_nonneg (K k p a : ℕ) :
    0 ≤ primePowerEventMass K k p a := by
  unfold primePowerEventMass sieveWeightSum
  apply Finset.sum_nonneg
  intro n hn
  split_ifs
  · exact Erdos248.sieveWeight_nonneg K n
  · exact le_rfl

theorem primePowerPairEventMass_nonneg (K k p a q b : ℕ) :
    0 ≤ primePowerPairEventMass K k p a q b := by
  unfold primePowerPairEventMass sieveWeightSum
  apply Finset.sum_nonneg
  intro n hn
  split_ifs
  · exact Erdos248.sieveWeight_nonneg K n
  · exact le_rfl

theorem primePowerPairEventMass_comm (K k p a q b : ℕ) :
    primePowerPairEventMass K k p a q b =
      primePowerPairEventMass K k q b p a := by
  unfold primePowerPairEventMass sieveWeightSum
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : p ^ a ∣ n + k <;>
    by_cases hq : q ^ b ∣ n + k <;> simp [hp, hq, and_comm]

/-- Generic packaging of a pointwise prime-power event transform into the
common transformed-mass estimate. -/
theorem primePowerEventMass_le_of_fromY_transform
    {A B : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K k p a W v : ℕ} (hreg : Erdos248.NormalizationRegular A K)
    {y : (Erdos248.nearShifts K → ℕ) → ℝ}
    (hpoint : ∀ n,
      (if p ^ a ∣ n + k then Erdos248.sieveWeight K n else 0) =
        Erdos248.fromYWeight (Erdos248.globalRadius K) W v y n)
    (hmod : Erdos248.preSieveModulus K ∣ W) (hW : 0 < W)
    (hy : IsSupportedMaynardY (Erdos248.nearShifts K)
      (Erdos248.globalRadius K) W y)
    (hySharp : Erdos248.IsVaryingSupported K y)
    (hB : 0 ≤ B) (hyBound : ∀ r, |y r| ≤ B) :
    primePowerEventMass K k p a ≤
      (Erdos248.intervalStart K : ℝ) / W *
        (B ^ 2 *
          (1 + roughCrossTupleTotientSquareTail (Erdos248.nearShifts K)
            (Erdos248.tinyCutoff K) (Erdos248.globalRadius K)) *
          96 ^ K * Erdos248.productCoordinateEnergy K) +
        (Erdos248.radiusProduct K : ℝ) ^ 6 * B ^ 2 := by
  have hmass : primePowerEventMass K k p a =
      sieveWeightSum (Erdos248.intervalStart K)
        (Erdos248.fromYWeight (Erdos248.globalRadius K) W v y) := by
    unfold primePowerEventMass sieveWeightSum
    apply Finset.sum_congr rfl
    intro n hn
    exact hpoint n
  rw [hmass]
  exact Erdos248.fromYWeightMass_le_productCoordinateEnergy
    hA hreg hmod hW hy hySharp hB hyBound

/-- Sharp version of the generic packaging which keeps the actual transformed
quadratic energy instead of replacing it by the coarse coordinate product. -/
theorem primePowerEventMass_le_of_fromY_transform_sharp
    {B : ℝ} {K k p a W v : ℕ}
    {y : (Erdos248.nearShifts K → ℕ) → ℝ}
    (hpoint : ∀ n,
      (if p ^ a ∣ n + k then Erdos248.sieveWeight K n else 0) =
        Erdos248.fromYWeight (Erdos248.globalRadius K) W v y n)
    (hmod : Erdos248.preSieveModulus K ∣ W) (hW : 0 < W)
    (hy : IsSupportedMaynardY (Erdos248.nearShifts K)
      (Erdos248.globalRadius K) W y)
    (hySharp : Erdos248.IsVaryingSupported K y)
    (hB : 0 ≤ B) (hyBound : ∀ r, |y r| ≤ B) :
    primePowerEventMass K k p a ≤
      (Erdos248.intervalStart K : ℝ) / W *
        (Erdos248.varyingYEnergy K y +
          B ^ 2 * roughCrossTupleTotientSquareTail (Erdos248.nearShifts K)
            (Erdos248.tinyCutoff K) (Erdos248.globalRadius K) *
            ∏ h : Erdos248.nearShifts K,
              Erdos248.varyingCoordinateMajorant K h) +
        (Erdos248.radiusProduct K : ℝ) ^ 6 * B ^ 2 := by
  have hmass : primePowerEventMass K k p a =
      sieveWeightSum (Erdos248.intervalStart K)
        (Erdos248.fromYWeight (Erdos248.globalRadius K) W v y) := by
    unfold primePowerEventMass sieveWeightSum
    apply Finset.sum_congr rfl
    intro n hn
    exact hpoint n
  rw [hmass]
  exact Erdos248.fromYWeightMass_le_varyingYEnergy hmod hW hy hySharp hB hyBound

/-- Sharp pair-event packaging for a pointwise transformed representation. -/
theorem primePowerPairEventMass_le_of_fromY_transform_sharp
    {B : ℝ} {K k p a q b W v : ℕ}
    {y : (Erdos248.nearShifts K → ℕ) → ℝ}
    (hpoint : ∀ n,
      (if p ^ a ∣ n + k ∧ q ^ b ∣ n + k then
          Erdos248.sieveWeight K n else 0) =
        Erdos248.fromYWeight (Erdos248.globalRadius K) W v y n)
    (hmod : Erdos248.preSieveModulus K ∣ W) (hW : 0 < W)
    (hy : IsSupportedMaynardY (Erdos248.nearShifts K)
      (Erdos248.globalRadius K) W y)
    (hySharp : Erdos248.IsVaryingSupported K y)
    (hB : 0 ≤ B) (hyBound : ∀ r, |y r| ≤ B) :
    primePowerPairEventMass K k p a q b ≤
      (Erdos248.intervalStart K : ℝ) / W *
        (Erdos248.varyingYEnergy K y +
          B ^ 2 * roughCrossTupleTotientSquareTail (Erdos248.nearShifts K)
            (Erdos248.tinyCutoff K) (Erdos248.globalRadius K) *
            ∏ h : Erdos248.nearShifts K,
              Erdos248.varyingCoordinateMajorant K h) +
        (Erdos248.radiusProduct K : ℝ) ^ 6 * B ^ 2 := by
  have hmass : primePowerPairEventMass K k p a q b =
      sieveWeightSum (Erdos248.intervalStart K)
        (Erdos248.fromYWeight (Erdos248.globalRadius K) W v y) := by
    unfold primePowerPairEventMass sieveWeightSum
    apply Finset.sum_congr rfl
    intro n hn
    exact hpoint n
  rw [hmass]
  exact Erdos248.fromYWeightMass_le_varyingYEnergy hmod hW hy hySharp hB hyBound

/-- Every prime above the tiny cutoff is either genuinely noncolliding with
the near shifts or collides with one coordinate; in both cases its
prime-power event has the same uniform transformed bound four. -/
theorem nonTinyPrimePowerEventMass_le_productCoordinateEnergy
    {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K k p a : ℕ} (hreg : Erdos248.NormalizationRegular A K)
    (hp : p.Prime) (ha : 0 < a)
    (hpCut : Erdos248.tinyCutoff K < p) :
    primePowerEventMass K k p a ≤
      (Erdos248.intervalStart K : ℝ) /
          (Erdos248.preSieveModulus K * p ^ a) *
        (16 *
          (1 + roughCrossTupleTotientSquareTail (Erdos248.nearShifts K)
            (Erdos248.tinyCutoff K) (Erdos248.globalRadius K)) *
          96 ^ K * Erdos248.productCoordinateEnergy K) +
        (Erdos248.radiusProduct K : ℝ) ^ 6 * 16 := by
  by_cases hcollision : ∃ m : Erdos248.nearShifts K,
      p ∣ Nat.dist k m.1
  · obtain ⟨m, hm⟩ := hcollision
    let z := Erdos248.mediumSingleTransformY K m p
    let vpow := extendPrimePowerEventResidue
      (Erdos248.prime_coprime_preSieveModulus hp hpCut).symm a 0 k
    have hpoint : ∀ n,
        (if p ^ a ∣ n + k then Erdos248.sieveWeight K n else 0) =
          Erdos248.fromYWeight (Erdos248.globalRadius K)
            (Erdos248.preSieveModulus K * p ^ a) vpow z n := by
      intro n
      rw [Erdos248.sieveWeight_eq_fromYWeight]
      simpa [z, vpow, Erdos248.mediumSingleTransformY] using
        (indicator_coordinatePrimePower_at_shift_fromYWeight
          (H := Erdos248.nearShifts K) (R := Erdos248.globalRadius K)
          (W := Erdos248.preSieveModulus K) (v := 0) (p := p)
          (a := a) (k := k) (n := n) (y := Erdos248.sieveY K)
          hp ha (Erdos248.prime_coprime_preSieveModulus hp hpCut)
          (Erdos248.sieveY_supported K) m
          (Erdos248.mediumPrime_separated hpCut m)
          (fun t => dvd_add_iff_of_dvd_dist hm))
    have hyBase : IsSupportedMaynardY (Erdos248.nearShifts K)
        (Erdos248.globalRadius K)
        (Erdos248.preSieveModulus K * p) z := by
      simpa [z, Erdos248.mediumSingleTransformY] using Erdos248.differencePrimeY_supported
        (Erdos248.globalRadius K) (Erdos248.preSieveModulus K) p m
        (Erdos248.sieveY K)
    have hy : IsSupportedMaynardY (Erdos248.nearShifts K)
        (Erdos248.globalRadius K)
        (Erdos248.preSieveModulus K * p ^ a) z := by
      have hraw := isSupportedMaynardY_mul_pow_of_dvd
        (H := Erdos248.nearShifts K) (R := Erdos248.globalRadius K)
        (W := Erdos248.preSieveModulus K * p) (p := p)
        (a := a - 1) (y := z) (dvd_mul_left p (Erdos248.preSieveModulus K))
        hyBase
      have hmod : (Erdos248.preSieveModulus K * p) * p ^ (a - 1) =
          Erdos248.preSieveModulus K * p ^ a := by
        have hpow : p * p ^ (a - 1) = p ^ a := by
          conv_rhs => rw [show a = (a - 1) + 1 by omega, pow_succ]
          ring
        calc
          (Erdos248.preSieveModulus K * p) * p ^ (a - 1) =
              Erdos248.preSieveModulus K * (p * p ^ (a - 1)) := by ring
          _ = Erdos248.preSieveModulus K * p ^ a := by rw [hpow]
      simpa [hmod] using hraw
    have hySharp : Erdos248.IsVaryingSupported K z := by
      simpa [z] using
        Erdos248.mediumSingleTransformY_varyingSupported hp.pos m
    have hyBound : ∀ r, |z r| ≤ (4 : ℝ) := by
      intro r
      simpa [z] using
        Erdos248.abs_mediumSingleTransformY_le_four hp hpCut m r
    have hraw := primePowerEventMass_le_of_fromY_transform hA hreg hpoint
      (dvd_mul_right _ _) (mul_pos (Erdos248.preSieveModulus_pos K)
        (pow_pos hp.pos _)) hy hySharp (by norm_num) hyBound
    norm_num at hraw
    simpa [Nat.cast_mul, Nat.cast_pow] using hraw
  · push Not at hcollision
    let z := Erdos248.erasePrimeY (Erdos248.globalRadius K)
      (Erdos248.preSieveModulus K) p (Erdos248.sieveY K)
    let vpow := extendPrimePowerEventResidue
      (Erdos248.prime_coprime_preSieveModulus hp hpCut).symm a 0 k
    have hpoint : ∀ n,
        (if p ^ a ∣ n + k then Erdos248.sieveWeight K n else 0) =
          Erdos248.fromYWeight (Erdos248.globalRadius K)
            (Erdos248.preSieveModulus K * p ^ a) vpow z n := by
      intro n
      rw [Erdos248.sieveWeight_eq_fromYWeight]
      simpa [z, vpow] using
        (indicator_separatedPrimePower_fromYWeight_of_not_dvd_dist
          (H := Erdos248.nearShifts K) (R := Erdos248.globalRadius K)
          (W := Erdos248.preSieveModulus K) (v := 0) (p := p)
          (a := a) (k := k) (n := n) (y := Erdos248.sieveY K)
          hp ha (Erdos248.prime_coprime_preSieveModulus hp hpCut)
          (Erdos248.sieveY_supported K) hcollision)
    have hyBase : IsSupportedMaynardY (Erdos248.nearShifts K)
        (Erdos248.globalRadius K)
        (Erdos248.preSieveModulus K * p) z := by
      simpa [z] using Erdos248.erasePrimeY_supported
        (Erdos248.globalRadius K) (Erdos248.preSieveModulus K) p
        (Erdos248.sieveY K)
    have hy : IsSupportedMaynardY (Erdos248.nearShifts K)
        (Erdos248.globalRadius K)
        (Erdos248.preSieveModulus K * p ^ a) z := by
      have hraw := isSupportedMaynardY_mul_pow_of_dvd
        (H := Erdos248.nearShifts K) (R := Erdos248.globalRadius K)
        (W := Erdos248.preSieveModulus K * p) (p := p)
        (a := a - 1) (y := z) (dvd_mul_left p (Erdos248.preSieveModulus K))
        hyBase
      have hmod : (Erdos248.preSieveModulus K * p) * p ^ (a - 1) =
          Erdos248.preSieveModulus K * p ^ a := by
        have hpow : p * p ^ (a - 1) = p ^ a := by
          conv_rhs => rw [show a = (a - 1) + 1 by omega, pow_succ]
          ring
        calc
          (Erdos248.preSieveModulus K * p) * p ^ (a - 1) =
              Erdos248.preSieveModulus K * (p * p ^ (a - 1)) := by ring
          _ = Erdos248.preSieveModulus K * p ^ a := by rw [hpow]
      simpa [hmod] using hraw
    have hySharp : Erdos248.IsVaryingSupported K z := by
      exact Erdos248.erasePrimeY_varyingSupported hp.pos
        (Erdos248.sieveY_varyingSupported K)
    have hyBound : ∀ r, |z r| ≤ (4 : ℝ) := by
      intro r
      have hraw := Erdos248.abs_erasePrimeY_le
        (H := Erdos248.nearShifts K) (R := Erdos248.globalRadius K)
        (W := Erdos248.preSieveModulus K) (p := p)
        (y := Erdos248.sieveY K) (B := (1 : ℝ)) (by norm_num)
        (Erdos248.abs_sieveY_le_one K) hp r
      rw [Fintype.card_coe, Erdos248.nearShifts_card] at hraw
      have hKle : K ≤ p - 1 :=
        (Erdos248.K_le_tinyCutoff K).trans (by omega)
      have hden : (0 : ℝ) < (p - 1 : ℕ) := by
        exact_mod_cast Nat.sub_pos_of_lt hp.one_lt
      have hdiv : (K : ℝ) / (p - 1 : ℕ) ≤ 1 := by
        apply (div_le_iff₀ hden).2
        norm_num
        exact_mod_cast hKle
      have htwo : |z r| ≤ (2 : ℝ) := by
        simpa [z] using hraw.trans
          (mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) +
            (K : ℝ) / (p - 1 : ℕ) ≤ 2) (by norm_num))
      exact htwo.trans (by norm_num)
    have hraw := primePowerEventMass_le_of_fromY_transform hA hreg hpoint
      (dvd_mul_right _ _) (mul_pos (Erdos248.preSieveModulus_pos K)
        (pow_pos hp.pos _)) hy hySharp (by norm_num) hyBound
    norm_num at hraw
    simpa [Nat.cast_mul, Nat.cast_pow] using hraw

/-- Two powers of the same base impose only the larger exponent. -/
theorem primePowerPairEventMass_same_eq_max
    (K k p a b : ℕ) :
    primePowerPairEventMass K k p a p b =
      primePowerEventMass K k p (max a b) := by
  unfold primePowerPairEventMass primePowerEventMass sieveWeightSum
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hab : a ≤ b
  · have hdvd : p ^ a ∣ p ^ b := pow_dvd_pow p hab
    rw [max_eq_right hab]
    by_cases hb : p ^ b ∣ n + k
    · simp [hb, hdvd.trans hb]
    · simp [hb]
  · have hba : b ≤ a := Nat.le_of_not_ge hab
    have hdvd : p ^ b ∣ p ^ a := pow_dvd_pow p hba
    rw [max_eq_left hba]
    by_cases ha : p ^ a ∣ n + k
    · simp [ha, hdvd.trans ha]
    · simp [ha]

/-- One separated prime erasure multiplies a pointwise Y-bound by at most
two, uniformly in the current modulus. -/
theorem abs_separatedErasePrimeY_le_two_mul
    {K W p : ℕ} {y : (Erdos248.nearShifts K → ℕ) → ℝ} {B : ℝ}
    (hp : p.Prime) (hpCut : Erdos248.tinyCutoff K < p)
    (hB : 0 ≤ B) (hyBound : ∀ r, |y r| ≤ B)
    (r : Erdos248.nearShifts K → ℕ) :
    |Erdos248.erasePrimeY (Erdos248.globalRadius K) W p y r| ≤ 2 * B := by
  have hraw := Erdos248.abs_erasePrimeY_le
    (H := Erdos248.nearShifts K) (R := Erdos248.globalRadius K)
    (W := W) (p := p) (y := y) (B := B) hB hyBound hp r
  rw [Fintype.card_coe, Erdos248.nearShifts_card] at hraw
  have hKle : K ≤ p - 1 :=
    (Erdos248.K_le_tinyCutoff K).trans (by omega)
  have hden : (0 : ℝ) < (p - 1 : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt hp.one_lt
  have hdiv : (K : ℝ) / (p - 1 : ℕ) ≤ 1 := by
    apply (div_le_iff₀ hden).2
    norm_num
    exact_mod_cast hKle
  have hfactor :
      (1 : ℝ) + (K : ℝ) / (p - 1 : ℕ) ≤ 2 := by linarith
  exact hraw.trans (by
    calc
      B * (1 + (K : ℝ) / (p - 1 : ℕ)) ≤ B * 2 :=
        mul_le_mul_of_nonneg_left hfactor hB
      _ = 2 * B := by ring)

/-- One coordinate-forcing transform multiplies a pointwise Y-bound by at
most four, uniformly in the current modulus. -/
theorem abs_coordinateDifferencePrimeY_le_four_mul
    {K W p : ℕ} {y : (Erdos248.nearShifts K → ℕ) → ℝ} {B : ℝ}
    (hp : p.Prime) (hpCut : Erdos248.tinyCutoff K < p)
    (hB : 0 ≤ B) (hyBound : ∀ r, |y r| ≤ B)
    (m : Erdos248.nearShifts K) (r : Erdos248.nearShifts K → ℕ) :
    |Erdos248.differencePrimeY (Erdos248.globalRadius K) W p m y r| ≤
      4 * B := by
  have hraw := Erdos248.abs_differencePrimeY_le
    (H := Erdos248.nearShifts K) (R := Erdos248.globalRadius K)
    (W := W) (p := p) (y := y) (B := B) hB hyBound hp m r
  rw [Fintype.card_coe, Erdos248.nearShifts_card] at hraw
  have hfactor := Erdos248.mediumPrimeFactor_le_four hp hpCut
  exact hraw.trans (by
    calc
      B * (2 + ((K : ℝ) + 1) / (p - 1 : ℕ)) ≤ B * 4 :=
        mul_le_mul_of_nonneg_left hfactor hB
      _ = 4 * B := by ring)

/-- A non-tiny prime-power event can always be absorbed into the outer
modulus.  If the prime meets a near coordinate modulo p we use that
coordinate; otherwise we use the separated erasure transform.  In either
case the pointwise bound grows by at most a factor four. -/
theorem exists_nonTinyPrimePower_transform
    {K W v p a k : ℕ} {y : (Erdos248.nearShifts K → ℕ) → ℝ}
    {B : ℝ} (hp : p.Prime) (ha : 0 < a)
    (hpCut : Erdos248.tinyCutoff K < p)
    (hpW : Nat.Coprime p W)
    (hy : IsSupportedMaynardY (Erdos248.nearShifts K)
      (Erdos248.globalRadius K) W y)
    (hySharp : Erdos248.IsVaryingSupported K y)
    (hB : 0 ≤ B) (hyBound : ∀ r, |y r| ≤ B) :
    ∃ v' : ℕ, ∃ z : (Erdos248.nearShifts K → ℕ) → ℝ,
      (∀ n,
        (if p ^ a ∣ n + k then
            Erdos248.fromYWeight (Erdos248.globalRadius K) W v y n else 0) =
          Erdos248.fromYWeight (Erdos248.globalRadius K)
            (W * p ^ a) v' z n) ∧
      IsSupportedMaynardY (Erdos248.nearShifts K)
        (Erdos248.globalRadius K) (W * p ^ a) z ∧
      Erdos248.IsVaryingSupported K z ∧
      ∀ r, |z r| ≤ 4 * B := by
  by_cases hcollision : ∃ m : Erdos248.nearShifts K,
      p ∣ Nat.dist k m.1
  · obtain ⟨m, hm⟩ := hcollision
    let z := Erdos248.differencePrimeY (Erdos248.globalRadius K) W p m y
    let v' := extendPrimePowerEventResidue hpW.symm a v k
    refine ⟨v', z, ?_, ?_, ?_, ?_⟩
    · intro n
      simpa [v', z] using
        (indicator_coordinatePrimePower_at_shift_fromYWeight
          (H := Erdos248.nearShifts K) (R := Erdos248.globalRadius K)
          (W := W) (v := v) (p := p) (a := a) (k := k)
          (n := n) (y := y) hp ha hpW hy m
          (Erdos248.mediumPrime_separated hpCut m)
          (fun t => dvd_add_iff_of_dvd_dist hm))
    · have hyBase : IsSupportedMaynardY (Erdos248.nearShifts K)
          (Erdos248.globalRadius K) (W * p) z := by
        simpa [z] using Erdos248.differencePrimeY_supported
          (Erdos248.globalRadius K) W p m y
      have hraw := isSupportedMaynardY_mul_pow_of_dvd
        (H := Erdos248.nearShifts K) (R := Erdos248.globalRadius K)
        (W := W * p) (p := p) (a := a - 1) (y := z)
        (dvd_mul_left p W) hyBase
      have hmod : (W * p) * p ^ (a - 1) = W * p ^ a := by
        have hpow : p * p ^ (a - 1) = p ^ a := by
          conv_rhs => rw [show a = (a - 1) + 1 by omega, pow_succ]
          ring
        calc
          (W * p) * p ^ (a - 1) = W * (p * p ^ (a - 1)) := by ring
          _ = W * p ^ a := by rw [hpow]
      simpa [hmod] using hraw
    · dsimp [z]
      exact Erdos248.differencePrimeY_varyingSupported hp.pos hySharp m
    · intro r
      simpa [z] using abs_coordinateDifferencePrimeY_le_four_mul
        hp hpCut hB hyBound m r
  · push Not at hcollision
    let z := Erdos248.erasePrimeY (Erdos248.globalRadius K) W p y
    let v' := extendPrimePowerEventResidue hpW.symm a v k
    refine ⟨v', z, ?_, ?_, ?_, ?_⟩
    · intro n
      simpa [v', z] using
        (indicator_separatedPrimePower_fromYWeight_of_not_dvd_dist
          (H := Erdos248.nearShifts K) (R := Erdos248.globalRadius K)
          (W := W) (v := v) (p := p) (a := a) (k := k)
          (n := n) (y := y) hp ha hpW hy hcollision)
    · have hyBase : IsSupportedMaynardY (Erdos248.nearShifts K)
          (Erdos248.globalRadius K) (W * p) z := by
        simpa [z] using Erdos248.erasePrimeY_supported
          (Erdos248.globalRadius K) W p y
      have hraw := isSupportedMaynardY_mul_pow_of_dvd
        (H := Erdos248.nearShifts K) (R := Erdos248.globalRadius K)
        (W := W * p) (p := p) (a := a - 1) (y := z)
        (dvd_mul_left p W) hyBase
      have hmod : (W * p) * p ^ (a - 1) = W * p ^ a := by
        have hpow : p * p ^ (a - 1) = p ^ a := by
          conv_rhs => rw [show a = (a - 1) + 1 by omega, pow_succ]
          ring
        calc
          (W * p) * p ^ (a - 1) = W * (p * p ^ (a - 1)) := by ring
          _ = W * p ^ a := by rw [hpow]
      simpa [hmod] using hraw
    · dsimp [z]
      exact Erdos248.erasePrimeY_varyingSupported hp.pos hySharp
    · intro r
      have htwo := abs_separatedErasePrimeY_le_two_mul (W := W) hp hpCut
        hB hyBound r
      dsimp [z]
      exact htwo.trans (by nlinarith)

/-- Two distinct primes above the tiny cutoff can be transformed
successively, regardless of whether either one collides with a near
coordinate. -/
theorem nonTinyDistinctPrimePowerPairEventMass_le_productCoordinateEnergy
    {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K k p a q b : ℕ} (hreg : Erdos248.NormalizationRegular A K)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (ha : 0 < a) (hb : 0 < b)
    (hpCut : Erdos248.tinyCutoff K < p)
    (hqCut : Erdos248.tinyCutoff K < q) :
    primePowerPairEventMass K k p a q b ≤
      (Erdos248.intervalStart K : ℝ) /
          ((Erdos248.preSieveModulus K * p ^ a) * q ^ b) *
        (256 *
          (1 + roughCrossTupleTotientSquareTail (Erdos248.nearShifts K)
            (Erdos248.tinyCutoff K) (Erdos248.globalRadius K)) *
          96 ^ K * Erdos248.productCoordinateEnergy K) +
        (Erdos248.radiusProduct K : ℝ) ^ 6 * 256 := by
  let W := Erdos248.preSieveModulus K
  obtain ⟨v₁, z₁, hfirst, hy₁, hy₁Sharp, hy₁Bound⟩ :=
    exists_nonTinyPrimePower_transform
      (K := K) (W := W) (v := 0) (p := p) (a := a) (k := k)
      (y := Erdos248.sieveY K) (B := (1 : ℝ))
      hp ha hpCut
      (by simpa [W] using Erdos248.prime_coprime_preSieveModulus hp hpCut)
      (by simpa [W] using Erdos248.sieveY_supported K)
      (Erdos248.sieveY_varyingSupported K) (by norm_num)
      (Erdos248.abs_sieveY_le_one K)
  have hqW : Nat.Coprime q (W * p ^ a) := by
    rw [Nat.coprime_mul_iff_right]
    exact ⟨by simpa [W] using
        Erdos248.prime_coprime_preSieveModulus hq hqCut,
      ((Nat.coprime_primes hq hp).mpr (Ne.symm hpq)).pow_right a⟩
  have hy₁Bound' : ∀ r, |z₁ r| ≤ (4 : ℝ) := by
    intro r
    simpa using hy₁Bound r
  obtain ⟨v₂, z₂, hsecond, hy₂, hy₂Sharp, hy₂Bound⟩ :=
    exists_nonTinyPrimePower_transform
      (K := K) (W := W * p ^ a) (v := v₁) (p := q) (a := b)
      (k := k) (y := z₁) (B := (4 : ℝ))
      hq hb hqCut hqW hy₁ hy₁Sharp (by norm_num) hy₁Bound'
  have hpoint : ∀ n,
      (if p ^ a ∣ n + k ∧ q ^ b ∣ n + k then
          Erdos248.sieveWeight K n else 0) =
        Erdos248.fromYWeight (Erdos248.globalRadius K)
          ((W * p ^ a) * q ^ b) v₂ z₂ n := by
    intro n
    rw [show (if p ^ a ∣ n + k ∧ q ^ b ∣ n + k then
          Erdos248.sieveWeight K n else 0) =
        if q ^ b ∣ n + k then
          (if p ^ a ∣ n + k then Erdos248.sieveWeight K n else 0)
        else 0 by
          by_cases hpN : p ^ a ∣ n + k <;>
            by_cases hqN : q ^ b ∣ n + k <;> simp [hpN, hqN]]
    rw [Erdos248.sieveWeight_eq_fromYWeight, hfirst n, hsecond n]
  have hmass : primePowerPairEventMass K k p a q b =
      sieveWeightSum (Erdos248.intervalStart K)
        (Erdos248.fromYWeight (Erdos248.globalRadius K)
          ((W * p ^ a) * q ^ b) v₂ z₂) := by
    unfold primePowerPairEventMass sieveWeightSum
    apply Finset.sum_congr rfl
    intro n hn
    exact hpoint n
  rw [hmass]
  have hy₂Bound' : ∀ r, |z₂ r| ≤ (16 : ℝ) := by
    intro r
    norm_num at hy₂Bound ⊢
    exact hy₂Bound r
  have hraw := Erdos248.fromYWeightMass_le_productCoordinateEnergy
    hA hreg
    (by
      dsimp [W]
      simpa [mul_assoc] using
        (dvd_mul_right (Erdos248.preSieveModulus K)
          (p ^ a * q ^ b)))
    (by
      dsimp [W]
      exact mul_pos
        (mul_pos (Erdos248.preSieveModulus_pos K) (pow_pos hp.pos _))
        (pow_pos hq.pos _))
    hy₂ hy₂Sharp (B := (16 : ℝ)) (by norm_num) hy₂Bound' (v := v₂)
  norm_num at hraw
  simpa [W, Nat.cast_mul, Nat.cast_pow, mul_assoc] using hraw

/-- A separated prime-power event has the generic transformed-mass bound,
with the full prime-power modulus in the density denominator. -/
theorem separatedPrimePowerEventMass_le_productCoordinateEnergy
    {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K k p a : ℕ} (hreg : Erdos248.NormalizationRegular A K)
    (hp : p.Prime) (ha : 0 < a)
    (hpCut : Erdos248.tinyCutoff K < p)
    (hk : ∀ h : Erdos248.nearShifts K, k ≠ h.1)
    (hsep : ∀ h : Erdos248.nearShifts K, Nat.dist k h.1 < p) :
    primePowerEventMass K k p a ≤
      (Erdos248.intervalStart K : ℝ) /
          (Erdos248.preSieveModulus K * p ^ a) *
        (4 *
          (1 + roughCrossTupleTotientSquareTail (Erdos248.nearShifts K)
            (Erdos248.tinyCutoff K) (Erdos248.globalRadius K)) *
          96 ^ K * Erdos248.productCoordinateEnergy K) +
        (Erdos248.radiusProduct K : ℝ) ^ 6 * 4 := by
  let z := Erdos248.erasePrimeY (Erdos248.globalRadius K)
    (Erdos248.preSieveModulus K) p (Erdos248.sieveY K)
  let vpow := extendPrimePowerEventResidue
    (Erdos248.prime_coprime_preSieveModulus hp hpCut).symm a 0 k
  have hpoint : ∀ n,
      (if p ^ a ∣ n + k then Erdos248.sieveWeight K n else 0) =
        Erdos248.fromYWeight (Erdos248.globalRadius K)
          (Erdos248.preSieveModulus K * p ^ a) vpow z n := by
    intro n
    rw [Erdos248.sieveWeight_eq_fromYWeight]
    simpa [z, vpow] using
      (indicator_separatedPrimePower_fromYWeight
        (H := Erdos248.nearShifts K) (R := Erdos248.globalRadius K)
        (W := Erdos248.preSieveModulus K) (v := 0) (p := p)
        (a := a) (k := k) (n := n) (y := Erdos248.sieveY K)
        hp ha (Erdos248.prime_coprime_preSieveModulus hp hpCut)
        (Erdos248.sieveY_supported K) hk hsep)
  have hmass : primePowerEventMass K k p a =
      sieveWeightSum (Erdos248.intervalStart K)
        (Erdos248.fromYWeight (Erdos248.globalRadius K)
          (Erdos248.preSieveModulus K * p ^ a) vpow z) := by
    unfold primePowerEventMass sieveWeightSum
    apply Finset.sum_congr rfl
    intro n hn
    exact hpoint n
  have hyBase : IsSupportedMaynardY (Erdos248.nearShifts K)
      (Erdos248.globalRadius K) (Erdos248.preSieveModulus K * p) z := by
    simpa [z] using Erdos248.erasePrimeY_supported
      (Erdos248.globalRadius K) (Erdos248.preSieveModulus K) p
      (Erdos248.sieveY K)
  have hy : IsSupportedMaynardY (Erdos248.nearShifts K)
      (Erdos248.globalRadius K)
      (Erdos248.preSieveModulus K * p ^ a) z := by
    have hraw := isSupportedMaynardY_mul_pow_of_dvd
      (H := Erdos248.nearShifts K) (R := Erdos248.globalRadius K)
      (W := Erdos248.preSieveModulus K * p) (p := p)
      (a := a - 1) (y := z) (dvd_mul_left p (Erdos248.preSieveModulus K))
      hyBase
    have hmod : (Erdos248.preSieveModulus K * p) * p ^ (a - 1) =
        Erdos248.preSieveModulus K * p ^ a := by
      have hpow : p * p ^ (a - 1) = p ^ a := by
        conv_rhs => rw [show a = (a - 1) + 1 by omega, pow_succ]
        ring
      calc
        (Erdos248.preSieveModulus K * p) * p ^ (a - 1) =
            Erdos248.preSieveModulus K * (p * p ^ (a - 1)) := by ring
        _ = Erdos248.preSieveModulus K * p ^ a := by rw [hpow]
    simpa [hmod] using hraw
  have hySharp : Erdos248.IsVaryingSupported K z := by
    exact Erdos248.erasePrimeY_varyingSupported hp.pos
      (Erdos248.sieveY_varyingSupported K)
  have hyBound : ∀ r, |z r| ≤ (2 : ℝ) := by
    intro r
    have hraw := Erdos248.abs_erasePrimeY_le
      (H := Erdos248.nearShifts K) (R := Erdos248.globalRadius K)
      (W := Erdos248.preSieveModulus K) (p := p)
      (y := Erdos248.sieveY K) (B := (1 : ℝ)) (by norm_num)
      (Erdos248.abs_sieveY_le_one K) hp r
    rw [Fintype.card_coe, Erdos248.nearShifts_card] at hraw
    have hKle : K ≤ p - 1 :=
      (Erdos248.K_le_tinyCutoff K).trans (by omega)
    have hden : (0 : ℝ) < (p - 1 : ℕ) := by
      exact_mod_cast Nat.sub_pos_of_lt hp.one_lt
    have hdiv : (K : ℝ) / (p - 1 : ℕ) ≤ 1 := by
      apply (div_le_iff₀ hden).2
      norm_num
      exact_mod_cast hKle
    have hfactor :
        (1 : ℝ) + (K : ℝ) / (p - 1 : ℕ) ≤ 2 := by linarith
    simpa [z] using hraw.trans
      (mul_le_mul_of_nonneg_left hfactor (by norm_num))
  rw [hmass]
  have hraw := Erdos248.fromYWeightMass_le_productCoordinateEnergy
    hA hreg
    (dvd_mul_right (Erdos248.preSieveModulus K) (p ^ a))
    (mul_pos (Erdos248.preSieveModulus_pos K) (pow_pos hp.pos _))
    hy hySharp (B := (2 : ℝ)) (by norm_num) hyBound (v := vpow)
  norm_num at hraw
  exact hraw

/-- At a near sieve coordinate, the coordinate-forcing transform gives the
same prime-power density gain with the standard bound four on the transformed
Y-variable. -/
theorem coordinatePrimePowerEventMass_le_productCoordinateEnergy
    {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K p a : ℕ} (hreg : Erdos248.NormalizationRegular A K)
    (hp : p.Prime) (ha : 0 < a)
    (hpCut : Erdos248.tinyCutoff K < p)
    (m : Erdos248.nearShifts K) :
    primePowerEventMass K m.1 p a ≤
      (Erdos248.intervalStart K : ℝ) /
          (Erdos248.preSieveModulus K * p ^ a) *
        (16 *
          (1 + roughCrossTupleTotientSquareTail (Erdos248.nearShifts K)
            (Erdos248.tinyCutoff K) (Erdos248.globalRadius K)) *
          96 ^ K * Erdos248.productCoordinateEnergy K) +
        (Erdos248.radiusProduct K : ℝ) ^ 6 * 16 := by
  let z := Erdos248.mediumSingleTransformY K m p
  let vpow := extendPrimePowerEventResidue
    (Erdos248.prime_coprime_preSieveModulus hp hpCut).symm a 0 m.1
  have hpoint : ∀ n,
      (if p ^ a ∣ n + m.1 then Erdos248.sieveWeight K n else 0) =
        Erdos248.fromYWeight (Erdos248.globalRadius K)
          (Erdos248.preSieveModulus K * p ^ a) vpow z n := by
    intro n
    rw [Erdos248.sieveWeight_eq_fromYWeight]
    simpa [z, vpow, Erdos248.mediumSingleTransformY] using
      (indicator_coordinatePrimePower_fromYWeight
        (H := Erdos248.nearShifts K) (R := Erdos248.globalRadius K)
        (W := Erdos248.preSieveModulus K) (v := 0) (p := p)
        (a := a) (n := n) (y := Erdos248.sieveY K)
        hp ha (Erdos248.prime_coprime_preSieveModulus hp hpCut)
        (Erdos248.sieveY_supported K) m
        (Erdos248.mediumPrime_separated hpCut m))
  have hmass : primePowerEventMass K m.1 p a =
      sieveWeightSum (Erdos248.intervalStart K)
        (Erdos248.fromYWeight (Erdos248.globalRadius K)
          (Erdos248.preSieveModulus K * p ^ a) vpow z) := by
    unfold primePowerEventMass sieveWeightSum
    apply Finset.sum_congr rfl
    intro n hn
    exact hpoint n
  have hyBase : IsSupportedMaynardY (Erdos248.nearShifts K)
      (Erdos248.globalRadius K) (Erdos248.preSieveModulus K * p) z := by
    simpa [z] using Erdos248.mediumSingleTransformY_supported K m p
  have hy : IsSupportedMaynardY (Erdos248.nearShifts K)
      (Erdos248.globalRadius K)
      (Erdos248.preSieveModulus K * p ^ a) z := by
    have hraw := isSupportedMaynardY_mul_pow_of_dvd
      (H := Erdos248.nearShifts K) (R := Erdos248.globalRadius K)
      (W := Erdos248.preSieveModulus K * p) (p := p)
      (a := a - 1) (y := z) (dvd_mul_left p (Erdos248.preSieveModulus K))
      hyBase
    have hmod : (Erdos248.preSieveModulus K * p) * p ^ (a - 1) =
        Erdos248.preSieveModulus K * p ^ a := by
      have hpow : p * p ^ (a - 1) = p ^ a := by
        conv_rhs => rw [show a = (a - 1) + 1 by omega, pow_succ]
        ring
      calc
        (Erdos248.preSieveModulus K * p) * p ^ (a - 1) =
            Erdos248.preSieveModulus K * (p * p ^ (a - 1)) := by ring
        _ = Erdos248.preSieveModulus K * p ^ a := by rw [hpow]
    simpa [hmod] using hraw
  have hySharp : Erdos248.IsVaryingSupported K z := by
    simpa [z] using
      Erdos248.mediumSingleTransformY_varyingSupported hp.pos m
  have hyBound : ∀ r, |z r| ≤ (4 : ℝ) := by
    intro r
    simpa [z] using Erdos248.abs_mediumSingleTransformY_le_four hp hpCut m r
  rw [hmass]
  have hraw := Erdos248.fromYWeightMass_le_productCoordinateEnergy
    hA hreg
    (dvd_mul_right (Erdos248.preSieveModulus K) (p ^ a))
    (mul_pos (Erdos248.preSieveModulus_pos K) (pow_pos hp.pos _))
    hy hySharp (B := (4 : ℝ)) (by norm_num) hyBound (v := vpow)
  norm_num at hraw
  exact hraw

/-- A prime at or below the tiny cutoff already divides the primorial
pre-sieve modulus. -/
theorem prime_dvd_preSieveModulus {K p : ℕ} (hp : p.Prime)
    (hpCut : p ≤ Erdos248.tinyCutoff K) :
    p ∣ Erdos248.preSieveModulus K := by
  unfold Erdos248.preSieveModulus
  exact hp.dvd_primorial_iff.mpr hpCut

/-- Removing one small prime from the squarefree primorial leaves a factor
coprime to that prime. -/
theorem coprime_preSieveModulus_div_prime {K p : ℕ} (hp : p.Prime)
    (hpCut : p ≤ Erdos248.tinyCutoff K) :
    Nat.Coprime (Erdos248.preSieveModulus K / p) p := by
  have hpW := prime_dvd_preSieveModulus hp hpCut
  apply Nat.coprime_of_squarefree_mul
  rw [Nat.div_mul_cancel hpW]
  unfold Erdos248.preSieveModulus
  exact squarefree_primorial _

/-- Removing two distinct small primes from the squarefree primorial leaves
a quotient coprime to either removed prime. -/
theorem coprime_preSieveModulus_div_two_primes
    {K p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpCut : p ≤ Erdos248.tinyCutoff K)
    (hqCut : q ≤ Erdos248.tinyCutoff K) :
    Nat.Coprime (Erdos248.preSieveModulus K / (p * q)) p ∧
      Nat.Coprime (Erdos248.preSieveModulus K / (p * q)) q := by
  let W := Erdos248.preSieveModulus K
  have hpW : p ∣ W := by
    simpa [W] using prime_dvd_preSieveModulus hp hpCut
  have hqW : q ∣ W := by
    simpa [W] using prime_dvd_preSieveModulus hq hqCut
  have hpqCop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hpqW : p * q ∣ W :=
    hpqCop.mul_dvd_of_dvd_of_dvd hpW hqW
  have hfactor : (p * q) * (W / (p * q)) = W :=
    Nat.mul_div_cancel' hpqW
  have hsqW : Squarefree W := by
    dsimp [W, Erdos248.preSieveModulus]
    exact squarefree_primorial _
  constructor
  · apply Nat.coprime_of_squarefree_mul
    apply hsqW.squarefree_of_dvd
    refine ⟨q, ?_⟩
    rw [← hfactor]
    ring
  · apply Nat.coprime_of_squarefree_mul
    apply hsqW.squarefree_of_dvd
    refine ⟨p, ?_⟩
    rw [← hfactor]
    ring

/-- For a small prime already present in the pre-sieve, a proper prime-power
event either vanishes (unless p divides the shift) or is represented by a
pure modulus lift with no Y-perturbation. -/
theorem smallPrimePowerEventMass_le_productCoordinateEnergy
    {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K k p a : ℕ} (hreg : Erdos248.NormalizationRegular A K)
    (hp : p.Prime) (ha : 2 ≤ a)
    (hpCut : p ≤ Erdos248.tinyCutoff K) :
    primePowerEventMass K k p a ≤
      (Erdos248.intervalStart K : ℝ) /
          (Erdos248.preSieveModulus K * p ^ (a - 1)) *
        ((1 + roughCrossTupleTotientSquareTail (Erdos248.nearShifts K)
            (Erdos248.tinyCutoff K) (Erdos248.globalRadius K)) *
          96 ^ K * Erdos248.productCoordinateEnergy K) +
        (Erdos248.radiusProduct K : ℝ) ^ 6 := by
  by_cases hpk : p ∣ k
  · obtain ⟨s, rfl⟩ := hpk
    let W := Erdos248.preSieveModulus K
    let W₀ := W / p
    have hpW : p ∣ W := by
      simpa [W] using prime_dvd_preSieveModulus hp hpCut
    have hfactor : p * W₀ = W := by
      simpa [W₀] using Nat.mul_div_cancel' hpW
    have hcop : Nat.Coprime W₀ p := by
      simpa [W, W₀] using coprime_preSieveModulus_div_prime hp hpCut
    let vpow := smallPrimePowerEventResidue hcop a s
    have hpoint : ∀ n,
        (if p ^ a ∣ n + p * s then Erdos248.sieveWeight K n else 0) =
          Erdos248.fromYWeight (Erdos248.globalRadius K)
            (W * p ^ (a - 1)) vpow (Erdos248.sieveY K) n := by
      intro n
      rw [Erdos248.sieveWeight_eq_fromYWeight]
      have hraw := indicator_smallPrimePower_fromYWeight
        (H := Erdos248.nearShifts K) (R := Erdos248.globalRadius K)
        (W₀ := W₀) (p := p) (a := a) (s := s) (n := n)
        (y := Erdos248.sieveY K) hp.pos ha hcop
      simpa [W, vpow, hfactor] using hraw
    have hmass : primePowerEventMass K (p * s) p a =
        sieveWeightSum (Erdos248.intervalStart K)
          (Erdos248.fromYWeight (Erdos248.globalRadius K)
            (W * p ^ (a - 1)) vpow (Erdos248.sieveY K)) := by
      unfold primePowerEventMass sieveWeightSum
      apply Finset.sum_congr rfl
      intro n hn
      exact hpoint n
    have hy : IsSupportedMaynardY (Erdos248.nearShifts K)
        (Erdos248.globalRadius K) (W * p ^ (a - 1))
        (Erdos248.sieveY K) := by
      exact isSupportedMaynardY_mul_pow_of_dvd
        (H := Erdos248.nearShifts K) (R := Erdos248.globalRadius K)
        (W := W) (p := p) (a := a - 1) (y := Erdos248.sieveY K)
        hpW (by simpa [W] using Erdos248.sieveY_supported K)
    rw [hmass]
    have hraw := Erdos248.fromYWeightMass_le_productCoordinateEnergy
      hA hreg
      (by
        dsimp [W]
        exact dvd_mul_right _ _)
      (mul_pos (by simpa [W] using Erdos248.preSieveModulus_pos K)
        (pow_pos hp.pos _))
      hy (Erdos248.sieveY_varyingSupported K)
      (B := (1 : ℝ)) (by norm_num) (Erdos248.abs_sieveY_le_one K)
      (v := vpow)
    norm_num at hraw
    simpa [W] using hraw
  · have hzero : primePowerEventMass K k p a = 0 := by
      unfold primePowerEventMass sieveWeightSum
      apply Finset.sum_eq_zero
      intro n hn
      by_cases hpow : p ^ a ∣ n + k
      · rw [if_pos hpow]
        by_contra hw
        have hnW := Erdos248.sieveWeight_ne_zero_primorial_dvd hw
        have hpn : p ∣ n :=
          (prime_dvd_preSieveModulus hp hpCut).trans hnW
        have hpadd : p ∣ n + k := (dvd_pow_self p (by omega)).trans hpow
        exact hpk ((Nat.dvd_add_right hpn).mp hpadd)
      · rw [if_neg hpow]
    rw [hzero]
    apply add_nonneg
    · apply mul_nonneg
      · positivity
      · apply mul_nonneg
        · apply mul_nonneg
          · have htail : 0 ≤ roughCrossTupleTotientSquareTail
                (Erdos248.nearShifts K) (Erdos248.tinyCutoff K)
                (Erdos248.globalRadius K) := by
              unfold roughCrossTupleTotientSquareTail crossTotientSquareWeight
              positivity
            linarith
          · positivity
        · exact Erdos248.productCoordinateEnergy_nonneg K
    · positivity

/-- A small pre-sieved prime power cannot occur at a positive-weight point
unless its base prime already divides the shift. -/
theorem smallPrimePowerEventMass_eq_zero_of_not_dvd
    {K k p a : ℕ} (hp : p.Prime) (ha : 2 ≤ a)
    (hpCut : p ≤ Erdos248.tinyCutoff K) (hpk : ¬ p ∣ k) :
    primePowerEventMass K k p a = 0 := by
  unfold primePowerEventMass sieveWeightSum
  apply Finset.sum_eq_zero
  intro n hn
  by_cases hpow : p ^ a ∣ n + k
  · rw [if_pos hpow]
    by_contra hw
    have hnW := Erdos248.sieveWeight_ne_zero_primorial_dvd hw
    have hpn : p ∣ n :=
      (prime_dvd_preSieveModulus hp hpCut).trans hnW
    have hpadd : p ∣ n + k := (dvd_pow_self p (by omega)).trans hpow
    exact hpk ((Nat.dvd_add_right hpn).mp hpadd)
  · rw [if_neg hpow]

/-- Sharp small-prime-power mass bound: because the base prime already lies
in the pre-sieve, lifting its exponent leaves the original Y-variable
unchanged and therefore keeps the actual sieve energy. -/
theorem smallPrimePowerEventMass_le_sharp
    {K k p a : ℕ} (hp : p.Prime) (ha : 2 ≤ a)
    (hpCut : p ≤ Erdos248.tinyCutoff K) :
    primePowerEventMass K k p a ≤
      (Erdos248.intervalStart K : ℝ) /
          (Erdos248.preSieveModulus K * p ^ (a - 1)) *
        (Erdos248.varyingYEnergy K (Erdos248.sieveY K) +
          roughCrossTupleTotientSquareTail (Erdos248.nearShifts K)
            (Erdos248.tinyCutoff K) (Erdos248.globalRadius K) *
            ∏ h : Erdos248.nearShifts K,
              Erdos248.varyingCoordinateMajorant K h) +
        (Erdos248.radiusProduct K : ℝ) ^ 6 := by
  by_cases hpk : p ∣ k
  · obtain ⟨s, rfl⟩ := hpk
    let W := Erdos248.preSieveModulus K
    let W₀ := W / p
    have hpW : p ∣ W := by
      simpa [W] using prime_dvd_preSieveModulus hp hpCut
    have hfactor : p * W₀ = W := by
      simpa [W₀] using Nat.mul_div_cancel' hpW
    have hcop : Nat.Coprime W₀ p := by
      simpa [W, W₀] using coprime_preSieveModulus_div_prime hp hpCut
    let vpow := smallPrimePowerEventResidue hcop a s
    have hpoint : ∀ n,
        (if p ^ a ∣ n + p * s then Erdos248.sieveWeight K n else 0) =
          Erdos248.fromYWeight (Erdos248.globalRadius K)
            (W * p ^ (a - 1)) vpow (Erdos248.sieveY K) n := by
      intro n
      rw [Erdos248.sieveWeight_eq_fromYWeight]
      simpa [W, vpow, hfactor] using
        (indicator_smallPrimePower_fromYWeight
          (H := Erdos248.nearShifts K) (R := Erdos248.globalRadius K)
          (W₀ := W₀) (p := p) (a := a) (s := s) (n := n)
          (y := Erdos248.sieveY K) hp.pos ha hcop)
    have hy : IsSupportedMaynardY (Erdos248.nearShifts K)
        (Erdos248.globalRadius K) (W * p ^ (a - 1))
        (Erdos248.sieveY K) := by
      exact isSupportedMaynardY_mul_pow_of_dvd
        (H := Erdos248.nearShifts K) (R := Erdos248.globalRadius K)
        (W := W) (p := p) (a := a - 1) (y := Erdos248.sieveY K)
        hpW (by simpa [W] using Erdos248.sieveY_supported K)
    have hraw := primePowerEventMass_le_of_fromY_transform_sharp
      (K := K) (k := p * s) (p := p) (a := a)
      (W := W * p ^ (a - 1)) (v := vpow) (y := Erdos248.sieveY K)
      hpoint (by dsimp [W]; exact dvd_mul_right _ _)
      (mul_pos (by simpa [W] using Erdos248.preSieveModulus_pos K)
        (pow_pos hp.pos _)) hy (Erdos248.sieveY_varyingSupported K)
      (B := (1 : ℝ)) (by norm_num) (Erdos248.abs_sieveY_le_one K)
    norm_num at hraw
    simpa [W] using hraw
  · rw [smallPrimePowerEventMass_eq_zero_of_not_dvd hp ha hpCut hpk]
    apply add_nonneg
    · apply mul_nonneg
      · positivity
      · apply add_nonneg
        · exact Erdos248.varyingYEnergy_nonneg K (Erdos248.sieveY K)
        · apply mul_nonneg
          · unfold roughCrossTupleTotientSquareTail crossTotientSquareWeight
            positivity
          · apply Finset.prod_nonneg
            intro h hh
            unfold Erdos248.varyingCoordinateMajorant squarefreeCoprimeInvTotientMean
            positivity
    · positivity

/-- The same vanishing applies to any pair event containing such a small
prime power. -/
theorem smallPrimePowerPairEventMass_eq_zero_of_not_dvd
    {K k p a q b : ℕ} (hp : p.Prime) (ha : 2 ≤ a)
    (hpCut : p ≤ Erdos248.tinyCutoff K) (hpk : ¬ p ∣ k) :
    primePowerPairEventMass K k p a q b = 0 := by
  unfold primePowerPairEventMass sieveWeightSum
  apply Finset.sum_eq_zero
  intro n hn
  by_cases hpow : p ^ a ∣ n + k ∧ q ^ b ∣ n + k
  · rw [if_pos hpow]
    by_contra hw
    have hnW := Erdos248.sieveWeight_ne_zero_primorial_dvd hw
    have hpn : p ∣ n :=
      (prime_dvd_preSieveModulus hp hpCut).trans hnW
    have hpadd : p ∣ n + k :=
      (dvd_pow_self p (by omega)).trans hpow.1
    exact hpk ((Nat.dvd_add_right hpn).mp hpadd)
  · rw [if_neg hpow]

/-- Two distinct small prime powers are represented by one pure modulus
lift.  If either base prime does not divide the shift, the event is empty. -/
theorem smallDistinctPrimePowerPairEventMass_le_productCoordinateEnergy
    {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K k p a q b : ℕ} (hreg : Erdos248.NormalizationRegular A K)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hpCut : p ≤ Erdos248.tinyCutoff K)
    (hqCut : q ≤ Erdos248.tinyCutoff K) :
    primePowerPairEventMass K k p a q b ≤
      (Erdos248.intervalStart K : ℝ) /
          (Erdos248.preSieveModulus K * p ^ (a - 1) * q ^ (b - 1)) *
        ((1 + roughCrossTupleTotientSquareTail (Erdos248.nearShifts K)
            (Erdos248.tinyCutoff K) (Erdos248.globalRadius K)) *
          96 ^ K * Erdos248.productCoordinateEnergy K) +
        (Erdos248.radiusProduct K : ℝ) ^ 6 := by
  by_cases hpk : p ∣ k
  · by_cases hqk : q ∣ k
    · have hpqCop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
      have hpqk : p * q ∣ k :=
        hpqCop.mul_dvd_of_dvd_of_dvd hpk hqk
      obtain ⟨s, rfl⟩ := hpqk
      let W := Erdos248.preSieveModulus K
      let W₀ := W / (p * q)
      have hpqW : p * q ∣ W := by
        apply hpqCop.mul_dvd_of_dvd_of_dvd
        · simpa [W] using prime_dvd_preSieveModulus hp hpCut
        · simpa [W] using prime_dvd_preSieveModulus hq hqCut
      have hfactor : (p * q) * W₀ = W := by
        simpa [W₀] using Nat.mul_div_cancel' hpqW
      have hcop := coprime_preSieveModulus_div_two_primes
        hp hq hpq hpCut hqCut
      let vpow := twoSmallPrimePowerEventResidue hcop.1 hcop.2 hpqCop a b s
      have hpoint : ∀ n,
          (if p ^ a ∣ n + (p * q) * s ∧ q ^ b ∣ n + (p * q) * s then
              Erdos248.sieveWeight K n else 0) =
            Erdos248.fromYWeight (Erdos248.globalRadius K)
              (W * p ^ (a - 1) * q ^ (b - 1)) vpow
              (Erdos248.sieveY K) n := by
        intro n
        rw [Erdos248.sieveWeight_eq_fromYWeight]
        simpa [W, W₀, vpow, hfactor] using
          (indicator_twoSmallPrimePower_fromYWeight
            (H := Erdos248.nearShifts K) (R := Erdos248.globalRadius K)
            (W₀ := W₀) (p := p) (q := q) (a := a) (b := b)
            (s := s) (n := n) (y := Erdos248.sieveY K)
            hp hq hpq ha hb hcop.1 hcop.2)
      have hmass : primePowerPairEventMass K ((p * q) * s) p a q b =
          sieveWeightSum (Erdos248.intervalStart K)
            (Erdos248.fromYWeight (Erdos248.globalRadius K)
              (W * p ^ (a - 1) * q ^ (b - 1)) vpow
              (Erdos248.sieveY K)) := by
        unfold primePowerPairEventMass sieveWeightSum
        apply Finset.sum_congr rfl
        intro n hn
        exact hpoint n
      have hpW : p ∣ W := by
        simpa [W] using prime_dvd_preSieveModulus hp hpCut
      have hqW : q ∣ W := by
        simpa [W] using prime_dvd_preSieveModulus hq hqCut
      have hy₁ : IsSupportedMaynardY (Erdos248.nearShifts K)
          (Erdos248.globalRadius K) (W * p ^ (a - 1))
          (Erdos248.sieveY K) := by
        exact isSupportedMaynardY_mul_pow_of_dvd hpW
          (by simpa [W] using Erdos248.sieveY_supported K)
      have hqW₁ : q ∣ W * p ^ (a - 1) :=
        dvd_mul_of_dvd_left hqW _
      have hy : IsSupportedMaynardY (Erdos248.nearShifts K)
          (Erdos248.globalRadius K)
          (W * p ^ (a - 1) * q ^ (b - 1))
          (Erdos248.sieveY K) := by
        exact isSupportedMaynardY_mul_pow_of_dvd hqW₁ hy₁
      rw [hmass]
      have hraw := Erdos248.fromYWeightMass_le_productCoordinateEnergy
        hA hreg
        (by
          show Erdos248.preSieveModulus K ∣
            Erdos248.preSieveModulus K * p ^ (a - 1) * q ^ (b - 1)
          simpa [mul_assoc] using
            (dvd_mul_right (Erdos248.preSieveModulus K)
              (p ^ (a - 1) * q ^ (b - 1))))
        (by
          dsimp [W]
          exact mul_pos
            (mul_pos (Erdos248.preSieveModulus_pos K) (pow_pos hp.pos _))
            (pow_pos hq.pos _))
        hy (Erdos248.sieveY_varyingSupported K)
        (B := (1 : ℝ)) (by norm_num) (Erdos248.abs_sieveY_le_one K)
        (v := vpow)
      norm_num at hraw
      simpa [W, mul_assoc] using hraw
    · have hzero : primePowerPairEventMass K k p a q b = 0 := by
        unfold primePowerPairEventMass sieveWeightSum
        apply Finset.sum_eq_zero
        intro n hn
        by_cases hpow : p ^ a ∣ n + k ∧ q ^ b ∣ n + k
        · rw [if_pos hpow]
          by_contra hw
          have hnW := Erdos248.sieveWeight_ne_zero_primorial_dvd hw
          have hqn : q ∣ n :=
            (prime_dvd_preSieveModulus hq hqCut).trans hnW
          have hqadd : q ∣ n + k :=
            (dvd_pow_self q (by omega)).trans hpow.2
          exact hqk ((Nat.dvd_add_right hqn).mp hqadd)
        · rw [if_neg hpow]
      rw [hzero]
      apply add_nonneg
      · apply mul_nonneg
        · positivity
        · apply mul_nonneg
          · apply mul_nonneg
            · have htail : 0 ≤ roughCrossTupleTotientSquareTail
                  (Erdos248.nearShifts K) (Erdos248.tinyCutoff K)
                  (Erdos248.globalRadius K) := by
                unfold roughCrossTupleTotientSquareTail crossTotientSquareWeight
                positivity
              linarith
            · positivity
          · exact Erdos248.productCoordinateEnergy_nonneg K
      · positivity
  · have hzero : primePowerPairEventMass K k p a q b = 0 := by
      unfold primePowerPairEventMass sieveWeightSum
      apply Finset.sum_eq_zero
      intro n hn
      by_cases hpow : p ^ a ∣ n + k ∧ q ^ b ∣ n + k
      · rw [if_pos hpow]
        by_contra hw
        have hnW := Erdos248.sieveWeight_ne_zero_primorial_dvd hw
        have hpn : p ∣ n :=
          (prime_dvd_preSieveModulus hp hpCut).trans hnW
        have hpadd : p ∣ n + k :=
          (dvd_pow_self p (by omega)).trans hpow.1
        exact hpk ((Nat.dvd_add_right hpn).mp hpadd)
      · rw [if_neg hpow]
    rw [hzero]
    apply add_nonneg
    · apply mul_nonneg
      · positivity
      · apply mul_nonneg
        · apply mul_nonneg
          · have htail : 0 ≤ roughCrossTupleTotientSquareTail
                (Erdos248.nearShifts K) (Erdos248.tinyCutoff K)
                (Erdos248.globalRadius K) := by
              unfold roughCrossTupleTotientSquareTail crossTotientSquareWeight
              positivity
            linarith
          · positivity
        · exact Erdos248.productCoordinateEnergy_nonneg K
    · positivity

/-- Sharp two-small-prime-power bound.  Both exponent lifts are already in
the pre-sieve, so the original Y-variable and its actual energy are retained. -/
theorem smallDistinctPrimePowerPairEventMass_le_sharp
    {K k p a q b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hpCut : p ≤ Erdos248.tinyCutoff K)
    (hqCut : q ≤ Erdos248.tinyCutoff K) :
    primePowerPairEventMass K k p a q b ≤
      (Erdos248.intervalStart K : ℝ) /
          (Erdos248.preSieveModulus K * p ^ (a - 1) * q ^ (b - 1)) *
        (Erdos248.varyingYEnergy K (Erdos248.sieveY K) +
          roughCrossTupleTotientSquareTail (Erdos248.nearShifts K)
            (Erdos248.tinyCutoff K) (Erdos248.globalRadius K) *
            ∏ h : Erdos248.nearShifts K,
              Erdos248.varyingCoordinateMajorant K h) +
        (Erdos248.radiusProduct K : ℝ) ^ 6 := by
  by_cases hpk : p ∣ k
  · by_cases hqk : q ∣ k
    · have hpqCop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
      have hpqk : p * q ∣ k := hpqCop.mul_dvd_of_dvd_of_dvd hpk hqk
      obtain ⟨s, rfl⟩ := hpqk
      let W := Erdos248.preSieveModulus K
      let W₀ := W / (p * q)
      have hpqW : p * q ∣ W := by
        apply hpqCop.mul_dvd_of_dvd_of_dvd
        · simpa [W] using prime_dvd_preSieveModulus hp hpCut
        · simpa [W] using prime_dvd_preSieveModulus hq hqCut
      have hfactor : (p * q) * W₀ = W := by
        simpa [W₀] using Nat.mul_div_cancel' hpqW
      have hcop := coprime_preSieveModulus_div_two_primes hp hq hpq hpCut hqCut
      let vpow := twoSmallPrimePowerEventResidue hcop.1 hcop.2 hpqCop a b s
      have hpoint : ∀ n,
          (if p ^ a ∣ n + (p * q) * s ∧ q ^ b ∣ n + (p * q) * s then
              Erdos248.sieveWeight K n else 0) =
            Erdos248.fromYWeight (Erdos248.globalRadius K)
              (W * p ^ (a - 1) * q ^ (b - 1)) vpow
              (Erdos248.sieveY K) n := by
        intro n
        rw [Erdos248.sieveWeight_eq_fromYWeight]
        simpa [W, W₀, vpow, hfactor] using
          (indicator_twoSmallPrimePower_fromYWeight
            (H := Erdos248.nearShifts K) (R := Erdos248.globalRadius K)
            (W₀ := W₀) (p := p) (q := q) (a := a) (b := b)
            (s := s) (n := n) (y := Erdos248.sieveY K)
            hp hq hpq ha hb hcop.1 hcop.2)
      have hpW : p ∣ W := by
        simpa [W] using prime_dvd_preSieveModulus hp hpCut
      have hqW : q ∣ W := by
        simpa [W] using prime_dvd_preSieveModulus hq hqCut
      have hy₁ : IsSupportedMaynardY (Erdos248.nearShifts K)
          (Erdos248.globalRadius K) (W * p ^ (a - 1))
          (Erdos248.sieveY K) := by
        exact isSupportedMaynardY_mul_pow_of_dvd hpW
          (by simpa [W] using Erdos248.sieveY_supported K)
      have hqW₁ : q ∣ W * p ^ (a - 1) := dvd_mul_of_dvd_left hqW _
      have hy : IsSupportedMaynardY (Erdos248.nearShifts K)
          (Erdos248.globalRadius K)
          (W * p ^ (a - 1) * q ^ (b - 1))
          (Erdos248.sieveY K) := by
        exact isSupportedMaynardY_mul_pow_of_dvd hqW₁ hy₁
      have hraw := primePowerPairEventMass_le_of_fromY_transform_sharp
        (K := K) (k := (p * q) * s) (p := p) (a := a) (q := q) (b := b)
        (W := W * p ^ (a - 1) * q ^ (b - 1)) (v := vpow)
        (y := Erdos248.sieveY K) hpoint
        (by
          show Erdos248.preSieveModulus K ∣
            Erdos248.preSieveModulus K * p ^ (a - 1) * q ^ (b - 1)
          simpa [W, mul_assoc] using
            (dvd_mul_right (Erdos248.preSieveModulus K)
              (p ^ (a - 1) * q ^ (b - 1))))
        (by
          dsimp [W]
          exact mul_pos
            (mul_pos (Erdos248.preSieveModulus_pos K) (pow_pos hp.pos _))
            (pow_pos hq.pos _))
        hy (Erdos248.sieveY_varyingSupported K)
        (B := (1 : ℝ)) (by norm_num) (Erdos248.abs_sieveY_le_one K)
      norm_num at hraw
      simpa [W, mul_assoc] using hraw
    · rw [primePowerPairEventMass_comm K k p a q b,
        smallPrimePowerPairEventMass_eq_zero_of_not_dvd hq hb hqCut hqk]
      apply add_nonneg
      · apply mul_nonneg
        · positivity
        · apply add_nonneg
          · exact Erdos248.varyingYEnergy_nonneg K (Erdos248.sieveY K)
          · apply mul_nonneg
            · unfold roughCrossTupleTotientSquareTail crossTotientSquareWeight
              positivity
            · apply Finset.prod_nonneg
              intro h hh
              unfold Erdos248.varyingCoordinateMajorant squarefreeCoprimeInvTotientMean
              positivity
      · positivity
  · rw [smallPrimePowerPairEventMass_eq_zero_of_not_dvd hp ha hpCut hpk]
    apply add_nonneg
    · apply mul_nonneg
      · positivity
      · apply add_nonneg
        · exact Erdos248.varyingYEnergy_nonneg K (Erdos248.sieveY K)
        · apply mul_nonneg
          · unfold roughCrossTupleTotientSquareTail crossTotientSquareWeight
            positivity
          · apply Finset.prod_nonneg
            intro h hh
            unfold Erdos248.varyingCoordinateMajorant squarefreeCoprimeInvTotientMean
            positivity
    · positivity

/-- A small prime power followed by an arbitrary non-tiny prime power has the
product density denominator.  The small event is a pure modulus lift, after
which the generic non-tiny transform handles either a collision or a
separated residue. -/
theorem smallNonTinyDistinctPrimePowerPairEventMass_le_productCoordinateEnergy
    {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K k p a q b : ℕ} (hreg : Erdos248.NormalizationRegular A K)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hpCut : p ≤ Erdos248.tinyCutoff K)
    (hqCut : Erdos248.tinyCutoff K < q) :
    primePowerPairEventMass K k p a q b ≤
      (Erdos248.intervalStart K : ℝ) /
          ((Erdos248.preSieveModulus K * p ^ (a - 1)) * q ^ b) *
        (16 *
          (1 + roughCrossTupleTotientSquareTail (Erdos248.nearShifts K)
            (Erdos248.tinyCutoff K) (Erdos248.globalRadius K)) *
          96 ^ K * Erdos248.productCoordinateEnergy K) +
        (Erdos248.radiusProduct K : ℝ) ^ 6 * 16 := by
  by_cases hpk : p ∣ k
  · obtain ⟨s, rfl⟩ := hpk
    let W := Erdos248.preSieveModulus K
    let W₀ := W / p
    have hpW : p ∣ W := by
      simpa [W] using prime_dvd_preSieveModulus hp hpCut
    have hfactor : p * W₀ = W := by
      simpa [W₀] using Nat.mul_div_cancel' hpW
    have hcop : Nat.Coprime W₀ p := by
      simpa [W, W₀] using coprime_preSieveModulus_div_prime hp hpCut
    let Wp := W * p ^ (a - 1)
    let v₁ := smallPrimePowerEventResidue hcop a s
    have hfirst : ∀ n,
        (if p ^ a ∣ n + p * s then Erdos248.sieveWeight K n else 0) =
          Erdos248.fromYWeight (Erdos248.globalRadius K) Wp v₁
            (Erdos248.sieveY K) n := by
      intro n
      rw [Erdos248.sieveWeight_eq_fromYWeight]
      simpa [W, W₀, Wp, v₁, hfactor] using
        (indicator_smallPrimePower_fromYWeight
          (H := Erdos248.nearShifts K) (R := Erdos248.globalRadius K)
          (W₀ := W₀) (p := p) (a := a) (s := s) (n := n)
          (y := Erdos248.sieveY K) hp.pos ha hcop)
    have hy₁ : IsSupportedMaynardY (Erdos248.nearShifts K)
        (Erdos248.globalRadius K) Wp (Erdos248.sieveY K) := by
      exact isSupportedMaynardY_mul_pow_of_dvd hpW
        (by simpa [W] using Erdos248.sieveY_supported K)
    have hqWp : Nat.Coprime q Wp := by
      dsimp [Wp]
      rw [Nat.coprime_mul_iff_right]
      exact ⟨Erdos248.prime_coprime_preSieveModulus hq hqCut,
        ((Nat.coprime_primes hq hp).mpr (Ne.symm hpq)).pow_right (a - 1)⟩
    obtain ⟨v₂, z, hsecond, hy, hySharp, hyBound⟩ :=
      exists_nonTinyPrimePower_transform
        (K := K) (W := Wp) (v := v₁) (p := q) (a := b)
        (k := p * s) (y := Erdos248.sieveY K) (B := (1 : ℝ))
        hq (by omega) hqCut hqWp hy₁
        (Erdos248.sieveY_varyingSupported K) (by norm_num)
        (Erdos248.abs_sieveY_le_one K)
    have hpoint : ∀ n,
        (if p ^ a ∣ n + p * s ∧ q ^ b ∣ n + p * s then
            Erdos248.sieveWeight K n else 0) =
          Erdos248.fromYWeight (Erdos248.globalRadius K)
            (Wp * q ^ b) v₂ z n := by
      intro n
      rw [show (if p ^ a ∣ n + p * s ∧ q ^ b ∣ n + p * s then
            Erdos248.sieveWeight K n else 0) =
          if q ^ b ∣ n + p * s then
            (if p ^ a ∣ n + p * s then Erdos248.sieveWeight K n else 0)
          else 0 by
            by_cases hpN : p ^ a ∣ n + p * s <;>
              by_cases hqN : q ^ b ∣ n + p * s <;> simp [hpN, hqN]]
      rw [hfirst n, hsecond n]
    have hmass : primePowerPairEventMass K (p * s) p a q b =
        sieveWeightSum (Erdos248.intervalStart K)
          (Erdos248.fromYWeight (Erdos248.globalRadius K)
            (Wp * q ^ b) v₂ z) := by
      unfold primePowerPairEventMass sieveWeightSum
      apply Finset.sum_congr rfl
      intro n hn
      exact hpoint n
    rw [hmass]
    have hraw := Erdos248.fromYWeightMass_le_productCoordinateEnergy
      hA hreg
      (by
        dsimp [Wp, W]
        simpa [mul_assoc] using
          (dvd_mul_right (Erdos248.preSieveModulus K)
            (p ^ (a - 1) * q ^ b)))
      (by
        dsimp [Wp, W]
        exact mul_pos
          (mul_pos (Erdos248.preSieveModulus_pos K) (pow_pos hp.pos _))
          (pow_pos hq.pos _))
      hy hySharp (B := (4 : ℝ)) (by norm_num) (by simpa using hyBound)
      (v := v₂)
    norm_num at hraw
    simpa [Wp, W, mul_assoc] using hraw
  · have hzero : primePowerPairEventMass K k p a q b = 0 := by
      unfold primePowerPairEventMass sieveWeightSum
      apply Finset.sum_eq_zero
      intro n hn
      by_cases hpow : p ^ a ∣ n + k ∧ q ^ b ∣ n + k
      · rw [if_pos hpow]
        by_contra hw
        have hnW := Erdos248.sieveWeight_ne_zero_primorial_dvd hw
        have hpn : p ∣ n :=
          (prime_dvd_preSieveModulus hp hpCut).trans hnW
        have hpadd : p ∣ n + k :=
          (dvd_pow_self p (by omega)).trans hpow.1
        exact hpk ((Nat.dvd_add_right hpn).mp hpadd)
      · rw [if_neg hpow]
    rw [hzero]
    apply add_nonneg
    · apply mul_nonneg
      · positivity
      · apply mul_nonneg
        · apply mul_nonneg
          · have htail : 0 ≤ roughCrossTupleTotientSquareTail
                (Erdos248.nearShifts K) (Erdos248.tinyCutoff K)
                (Erdos248.globalRadius K) := by
              unfold roughCrossTupleTotientSquareTail crossTotientSquareWeight
              positivity
            linarith
          · positivity
        · exact Erdos248.productCoordinateEnergy_nonneg K
    · positivity

/-- A small prime power followed by a separated large prime power has the
product density denominator; only the large prime perturbs the Y-variable. -/
theorem smallSeparatedDistinctPrimePowerPairEventMass_le_productCoordinateEnergy
    {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K k p a q b : ℕ} (hreg : Erdos248.NormalizationRegular A K)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (ha : 2 ≤ a) (hb : 0 < b)
    (hpCut : p ≤ Erdos248.tinyCutoff K)
    (hqCut : Erdos248.tinyCutoff K < q)
    (hk : ∀ h : Erdos248.nearShifts K, k ≠ h.1)
    (hqsep : ∀ h : Erdos248.nearShifts K, Nat.dist k h.1 < q) :
    primePowerPairEventMass K k p a q b ≤
      (Erdos248.intervalStart K : ℝ) /
          ((Erdos248.preSieveModulus K * p ^ (a - 1)) * q ^ b) *
        (4 *
          (1 + roughCrossTupleTotientSquareTail (Erdos248.nearShifts K)
            (Erdos248.tinyCutoff K) (Erdos248.globalRadius K)) *
          96 ^ K * Erdos248.productCoordinateEnergy K) +
        (Erdos248.radiusProduct K : ℝ) ^ 6 * 4 := by
  by_cases hpk : p ∣ k
  · obtain ⟨s, rfl⟩ := hpk
    let W := Erdos248.preSieveModulus K
    let W₀ := W / p
    have hpW : p ∣ W := by
      simpa [W] using prime_dvd_preSieveModulus hp hpCut
    have hfactor : p * W₀ = W := by
      simpa [W₀] using Nat.mul_div_cancel' hpW
    have hcop : Nat.Coprime W₀ p := by
      simpa [W, W₀] using coprime_preSieveModulus_div_prime hp hpCut
    let Wp := W * p ^ (a - 1)
    let v₁ := smallPrimePowerEventResidue hcop a s
    let z := Erdos248.erasePrimeY (Erdos248.globalRadius K) Wp q
      (Erdos248.sieveY K)
    have hqWp : Nat.Coprime q Wp := by
      dsimp [Wp]
      rw [Nat.coprime_mul_iff_right]
      exact ⟨Erdos248.prime_coprime_preSieveModulus hq hqCut,
        ((Nat.coprime_primes hq hp).mpr (Ne.symm hpq)).pow_right (a - 1)⟩
    let v₂ := extendPrimePowerEventResidue hqWp.symm b v₁ (p * s)
    have hfirst : ∀ n,
        (if p ^ a ∣ n + p * s then Erdos248.sieveWeight K n else 0) =
          Erdos248.fromYWeight (Erdos248.globalRadius K) Wp v₁
            (Erdos248.sieveY K) n := by
      intro n
      rw [Erdos248.sieveWeight_eq_fromYWeight]
      simpa [W, W₀, Wp, v₁, hfactor] using
        (indicator_smallPrimePower_fromYWeight
          (H := Erdos248.nearShifts K) (R := Erdos248.globalRadius K)
          (W₀ := W₀) (p := p) (a := a) (s := s) (n := n)
          (y := Erdos248.sieveY K) hp.pos ha hcop)
    have hy₁ : IsSupportedMaynardY (Erdos248.nearShifts K)
        (Erdos248.globalRadius K) Wp (Erdos248.sieveY K) := by
      exact isSupportedMaynardY_mul_pow_of_dvd hpW
        (by simpa [W] using Erdos248.sieveY_supported K)
    have hsecond : ∀ n,
        (if q ^ b ∣ n + p * s then
            Erdos248.fromYWeight (Erdos248.globalRadius K) Wp v₁
              (Erdos248.sieveY K) n else 0) =
          Erdos248.fromYWeight (Erdos248.globalRadius K)
            (Wp * q ^ b) v₂ z n := by
      intro n
      simpa [v₂, z] using
        (indicator_separatedPrimePower_fromYWeight
          (H := Erdos248.nearShifts K) (R := Erdos248.globalRadius K)
          (W := Wp) (v := v₁) (p := q) (a := b) (k := p * s)
          (n := n) (y := Erdos248.sieveY K) hq hb hqWp hy₁ hk hqsep)
    have hpoint : ∀ n,
        (if p ^ a ∣ n + p * s ∧ q ^ b ∣ n + p * s then
            Erdos248.sieveWeight K n else 0) =
          Erdos248.fromYWeight (Erdos248.globalRadius K)
            (Wp * q ^ b) v₂ z n := by
      intro n
      rw [show (if p ^ a ∣ n + p * s ∧ q ^ b ∣ n + p * s then
            Erdos248.sieveWeight K n else 0) =
          if q ^ b ∣ n + p * s then
            (if p ^ a ∣ n + p * s then Erdos248.sieveWeight K n else 0)
          else 0 by
            by_cases hpN : p ^ a ∣ n + p * s <;>
              by_cases hqN : q ^ b ∣ n + p * s <;> simp [hpN, hqN]]
      rw [hfirst n, hsecond n]
    have hmass : primePowerPairEventMass K (p * s) p a q b =
        sieveWeightSum (Erdos248.intervalStart K)
          (Erdos248.fromYWeight (Erdos248.globalRadius K)
            (Wp * q ^ b) v₂ z) := by
      unfold primePowerPairEventMass sieveWeightSum
      apply Finset.sum_congr rfl
      intro n hn
      exact hpoint n
    have hyBase : IsSupportedMaynardY (Erdos248.nearShifts K)
        (Erdos248.globalRadius K) (Wp * q) z := by
      simpa [z] using Erdos248.erasePrimeY_supported
        (Erdos248.globalRadius K) Wp q (Erdos248.sieveY K)
    have hy : IsSupportedMaynardY (Erdos248.nearShifts K)
        (Erdos248.globalRadius K) (Wp * q ^ b) z := by
      have hraw := isSupportedMaynardY_mul_pow_of_dvd
        (H := Erdos248.nearShifts K) (R := Erdos248.globalRadius K)
        (W := Wp * q) (p := q) (a := b - 1) (y := z)
        (dvd_mul_left q Wp) hyBase
      have hmod : (Wp * q) * q ^ (b - 1) = Wp * q ^ b := by
        have hpow : q * q ^ (b - 1) = q ^ b := by
          conv_rhs => rw [show b = (b - 1) + 1 by omega, pow_succ]
          ring
        calc
          (Wp * q) * q ^ (b - 1) = Wp * (q * q ^ (b - 1)) := by ring
          _ = Wp * q ^ b := by rw [hpow]
      simpa [hmod] using hraw
    have hySharp : Erdos248.IsVaryingSupported K z := by
      dsimp [z]
      exact Erdos248.erasePrimeY_varyingSupported hq.pos
        (Erdos248.sieveY_varyingSupported K)
    have hyBound : ∀ r, |z r| ≤ (2 : ℝ) := by
      intro r
      simpa [z] using abs_separatedErasePrimeY_le_two_mul hq hqCut
        (W := Wp) (y := Erdos248.sieveY K) (B := (1 : ℝ))
        (by norm_num) (Erdos248.abs_sieveY_le_one K) r
    rw [hmass]
    have hraw := Erdos248.fromYWeightMass_le_productCoordinateEnergy
      hA hreg
      (by
        dsimp [Wp, W]
        simpa [mul_assoc] using
          (dvd_mul_right (Erdos248.preSieveModulus K)
            (p ^ (a - 1) * q ^ b)))
      (by
        dsimp [Wp, W]
        exact mul_pos
          (mul_pos (Erdos248.preSieveModulus_pos K) (pow_pos hp.pos _))
          (pow_pos hq.pos _))
      hy hySharp (B := (2 : ℝ)) (by norm_num) hyBound (v := v₂)
    norm_num at hraw
    simpa [Wp, W, mul_assoc] using hraw
  · have hzero : primePowerPairEventMass K k p a q b = 0 := by
      unfold primePowerPairEventMass sieveWeightSum
      apply Finset.sum_eq_zero
      intro n hn
      by_cases hpow : p ^ a ∣ n + k ∧ q ^ b ∣ n + k
      · rw [if_pos hpow]
        by_contra hw
        have hnW := Erdos248.sieveWeight_ne_zero_primorial_dvd hw
        have hpn : p ∣ n :=
          (prime_dvd_preSieveModulus hp hpCut).trans hnW
        have hpadd : p ∣ n + k :=
          (dvd_pow_self p (by omega)).trans hpow.1
        exact hpk ((Nat.dvd_add_right hpn).mp hpadd)
      · rw [if_neg hpow]
    rw [hzero]
    apply add_nonneg
    · apply mul_nonneg
      · positivity
      · apply mul_nonneg
        · apply mul_nonneg
          · have htail : 0 ≤ roughCrossTupleTotientSquareTail
                (Erdos248.nearShifts K) (Erdos248.tinyCutoff K)
                (Erdos248.globalRadius K) := by
              unfold roughCrossTupleTotientSquareTail crossTotientSquareWeight
              positivity
            linarith
          · positivity
        · exact Erdos248.productCoordinateEnergy_nonneg K
    · positivity

/-- For two distinct separated primes, adjoining their prime powers
successively gives the product prime-power modulus and a uniform bound four
on the twice-erased Y-variable. -/
theorem separatedDistinctPrimePowerPairEventMass_le_productCoordinateEnergy
    {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K k p a q b : ℕ} (hreg : Erdos248.NormalizationRegular A K)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (ha : 0 < a) (hb : 0 < b)
    (hpCut : Erdos248.tinyCutoff K < p)
    (hqCut : Erdos248.tinyCutoff K < q)
    (hk : ∀ h : Erdos248.nearShifts K, k ≠ h.1)
    (hpsep : ∀ h : Erdos248.nearShifts K, Nat.dist k h.1 < p)
    (hqsep : ∀ h : Erdos248.nearShifts K, Nat.dist k h.1 < q) :
    primePowerPairEventMass K k p a q b ≤
      (Erdos248.intervalStart K : ℝ) /
          ((Erdos248.preSieveModulus K * p ^ a) * q ^ b) *
        (16 *
          (1 + roughCrossTupleTotientSquareTail (Erdos248.nearShifts K)
            (Erdos248.tinyCutoff K) (Erdos248.globalRadius K)) *
          96 ^ K * Erdos248.productCoordinateEnergy K) +
        (Erdos248.radiusProduct K : ℝ) ^ 6 * 16 := by
  let Wp := Erdos248.preSieveModulus K * p ^ a
  let v₁ := extendPrimePowerEventResidue
    (Erdos248.prime_coprime_preSieveModulus hp hpCut).symm a 0 k
  let z₁ := Erdos248.erasePrimeY (Erdos248.globalRadius K)
    (Erdos248.preSieveModulus K) p (Erdos248.sieveY K)
  have hqW : Nat.Coprime q Wp := by
    dsimp [Wp]
    rw [Nat.coprime_mul_iff_right]
    exact ⟨Erdos248.prime_coprime_preSieveModulus hq hqCut,
      ((Nat.coprime_primes hq hp).mpr (Ne.symm hpq)).pow_right a⟩
  let v₂ := extendPrimePowerEventResidue hqW.symm b v₁ k
  let z₂ := Erdos248.erasePrimeY (Erdos248.globalRadius K) Wp q z₁
  have hfirst : ∀ n,
      (if p ^ a ∣ n + k then Erdos248.sieveWeight K n else 0) =
        Erdos248.fromYWeight (Erdos248.globalRadius K) Wp v₁ z₁ n := by
    intro n
    rw [Erdos248.sieveWeight_eq_fromYWeight]
    simpa [Wp, v₁, z₁] using
      (indicator_separatedPrimePower_fromYWeight
        (H := Erdos248.nearShifts K) (R := Erdos248.globalRadius K)
        (W := Erdos248.preSieveModulus K) (v := 0) (p := p)
        (a := a) (k := k) (n := n) (y := Erdos248.sieveY K)
        hp ha (Erdos248.prime_coprime_preSieveModulus hp hpCut)
        (Erdos248.sieveY_supported K) hk hpsep)
  have hy₁base : IsSupportedMaynardY (Erdos248.nearShifts K)
      (Erdos248.globalRadius K) (Erdos248.preSieveModulus K * p) z₁ := by
    simpa [z₁] using Erdos248.erasePrimeY_supported
      (Erdos248.globalRadius K) (Erdos248.preSieveModulus K) p
      (Erdos248.sieveY K)
  have hy₁ : IsSupportedMaynardY (Erdos248.nearShifts K)
      (Erdos248.globalRadius K) Wp z₁ := by
    have hraw := isSupportedMaynardY_mul_pow_of_dvd
      (H := Erdos248.nearShifts K) (R := Erdos248.globalRadius K)
      (W := Erdos248.preSieveModulus K * p) (p := p)
      (a := a - 1) (y := z₁) (dvd_mul_left p (Erdos248.preSieveModulus K))
      hy₁base
    have hmod : (Erdos248.preSieveModulus K * p) * p ^ (a - 1) =
        Wp := by
      dsimp [Wp]
      have hpow : p * p ^ (a - 1) = p ^ a := by
        conv_rhs => rw [show a = (a - 1) + 1 by omega, pow_succ]
        ring
      calc
        (Erdos248.preSieveModulus K * p) * p ^ (a - 1) =
            Erdos248.preSieveModulus K * (p * p ^ (a - 1)) := by ring
        _ = Erdos248.preSieveModulus K * p ^ a := by rw [hpow]
    simpa [hmod] using hraw
  have hsecond : ∀ n,
      (if q ^ b ∣ n + k then
          Erdos248.fromYWeight (Erdos248.globalRadius K) Wp v₁ z₁ n else 0) =
        Erdos248.fromYWeight (Erdos248.globalRadius K)
          (Wp * q ^ b) v₂ z₂ n := by
    intro n
    simpa [v₂, z₂] using
      (indicator_separatedPrimePower_fromYWeight
        (H := Erdos248.nearShifts K) (R := Erdos248.globalRadius K)
        (W := Wp) (v := v₁) (p := q) (a := b) (k := k) (n := n)
        (y := z₁) hq hb hqW hy₁ hk hqsep)
  have hpoint : ∀ n,
      (if p ^ a ∣ n + k ∧ q ^ b ∣ n + k then
          Erdos248.sieveWeight K n else 0) =
        Erdos248.fromYWeight (Erdos248.globalRadius K)
          (Wp * q ^ b) v₂ z₂ n := by
    intro n
    rw [show (if p ^ a ∣ n + k ∧ q ^ b ∣ n + k then
          Erdos248.sieveWeight K n else 0) =
        if q ^ b ∣ n + k then
          (if p ^ a ∣ n + k then Erdos248.sieveWeight K n else 0)
        else 0 by
          by_cases hpN : p ^ a ∣ n + k <;>
            by_cases hqN : q ^ b ∣ n + k <;> simp [hpN, hqN]]
    rw [hfirst n, hsecond n]
  have hmass : primePowerPairEventMass K k p a q b =
      sieveWeightSum (Erdos248.intervalStart K)
        (Erdos248.fromYWeight (Erdos248.globalRadius K)
          (Wp * q ^ b) v₂ z₂) := by
    unfold primePowerPairEventMass sieveWeightSum
    apply Finset.sum_congr rfl
    intro n hn
    exact hpoint n
  have hy₂base : IsSupportedMaynardY (Erdos248.nearShifts K)
      (Erdos248.globalRadius K) (Wp * q) z₂ := by
    simpa [z₂] using Erdos248.erasePrimeY_supported
      (Erdos248.globalRadius K) Wp q z₁
  have hy₂ : IsSupportedMaynardY (Erdos248.nearShifts K)
      (Erdos248.globalRadius K) (Wp * q ^ b) z₂ := by
    have hraw := isSupportedMaynardY_mul_pow_of_dvd
      (H := Erdos248.nearShifts K) (R := Erdos248.globalRadius K)
      (W := Wp * q) (p := q) (a := b - 1) (y := z₂)
      (dvd_mul_left q Wp) hy₂base
    have hmod : (Wp * q) * q ^ (b - 1) = Wp * q ^ b := by
      have hpow : q * q ^ (b - 1) = q ^ b := by
        conv_rhs => rw [show b = (b - 1) + 1 by omega, pow_succ]
        ring
      calc
        (Wp * q) * q ^ (b - 1) = Wp * (q * q ^ (b - 1)) := by ring
        _ = Wp * q ^ b := by rw [hpow]
    simpa [hmod] using hraw
  have hySharp : Erdos248.IsVaryingSupported K z₂ := by
    dsimp [z₂, z₁]
    exact Erdos248.erasePrimeY_varyingSupported hq.pos
      (Erdos248.erasePrimeY_varyingSupported hp.pos
        (Erdos248.sieveY_varyingSupported K))
  have hyBound : ∀ r, |z₂ r| ≤ (4 : ℝ) := by
    intro r
    have hfirstBound : ∀ s, |z₁ s| ≤ (2 : ℝ) := by
      intro s
      simpa [z₁] using abs_separatedErasePrimeY_le_two_mul hp hpCut
        (B := (1 : ℝ)) (by norm_num) (Erdos248.abs_sieveY_le_one K) s
    have hsecondBound := abs_separatedErasePrimeY_le_two_mul hq hqCut
      (W := Wp) (y := z₁) (B := (2 : ℝ)) (by norm_num) hfirstBound r
    norm_num at hsecondBound ⊢
    simpa [z₂] using hsecondBound
  rw [hmass]
  have hmodBase : Erdos248.preSieveModulus K ∣ Wp * q ^ b := by
    dsimp [Wp]
    rw [mul_assoc]
    exact dvd_mul_right _ _
  have hWp : 0 < Wp := by
    dsimp [Wp]
    exact mul_pos (Erdos248.preSieveModulus_pos K) (pow_pos hp.pos _)
  have hW : 0 < Wp * q ^ b := mul_pos hWp (pow_pos hq.pos _)
  have hraw := Erdos248.fromYWeightMass_le_productCoordinateEnergy
    hA hreg
    hmodBase hW
    hy₂ hySharp (B := (4 : ℝ)) (by norm_num) hyBound (v := v₂)
  norm_num at hraw
  simpa [Wp, mul_assoc] using hraw

/-- The corresponding two-prime-power estimate at a near coordinate uses two
coordinate-forcing transforms, hence the uniform bound sixteen. -/
theorem coordinateDistinctPrimePowerPairEventMass_le_productCoordinateEnergy
    {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K p a q b : ℕ} (hreg : Erdos248.NormalizationRegular A K)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (ha : 0 < a) (hb : 0 < b)
    (hpCut : Erdos248.tinyCutoff K < p)
    (hqCut : Erdos248.tinyCutoff K < q)
    (m : Erdos248.nearShifts K) :
    primePowerPairEventMass K m.1 p a q b ≤
      (Erdos248.intervalStart K : ℝ) /
          ((Erdos248.preSieveModulus K * p ^ a) * q ^ b) *
        (256 *
          (1 + roughCrossTupleTotientSquareTail (Erdos248.nearShifts K)
            (Erdos248.tinyCutoff K) (Erdos248.globalRadius K)) *
          96 ^ K * Erdos248.productCoordinateEnergy K) +
        (Erdos248.radiusProduct K : ℝ) ^ 6 * 256 := by
  let Wp := Erdos248.preSieveModulus K * p ^ a
  let v₁ := extendPrimePowerEventResidue
    (Erdos248.prime_coprime_preSieveModulus hp hpCut).symm a 0 m.1
  let z₁ := Erdos248.differencePrimeY (Erdos248.globalRadius K)
    (Erdos248.preSieveModulus K) p m (Erdos248.sieveY K)
  have hqW : Nat.Coprime q Wp := by
    dsimp [Wp]
    rw [Nat.coprime_mul_iff_right]
    exact ⟨Erdos248.prime_coprime_preSieveModulus hq hqCut,
      ((Nat.coprime_primes hq hp).mpr (Ne.symm hpq)).pow_right a⟩
  let v₂ := extendPrimePowerEventResidue hqW.symm b v₁ m.1
  let z₂ := Erdos248.differencePrimeY (Erdos248.globalRadius K) Wp q m z₁
  have hfirst : ∀ n,
      (if p ^ a ∣ n + m.1 then Erdos248.sieveWeight K n else 0) =
        Erdos248.fromYWeight (Erdos248.globalRadius K) Wp v₁ z₁ n := by
    intro n
    rw [Erdos248.sieveWeight_eq_fromYWeight]
    simpa [Wp, v₁, z₁] using
      (indicator_coordinatePrimePower_fromYWeight
        (H := Erdos248.nearShifts K) (R := Erdos248.globalRadius K)
        (W := Erdos248.preSieveModulus K) (v := 0) (p := p)
        (a := a) (n := n) (y := Erdos248.sieveY K)
        hp ha (Erdos248.prime_coprime_preSieveModulus hp hpCut)
        (Erdos248.sieveY_supported K) m
        (Erdos248.mediumPrime_separated hpCut m))
  have hy₁base : IsSupportedMaynardY (Erdos248.nearShifts K)
      (Erdos248.globalRadius K) (Erdos248.preSieveModulus K * p) z₁ := by
    simpa [z₁] using Erdos248.differencePrimeY_supported
      (Erdos248.globalRadius K) (Erdos248.preSieveModulus K) p m
      (Erdos248.sieveY K)
  have hy₁ : IsSupportedMaynardY (Erdos248.nearShifts K)
      (Erdos248.globalRadius K) Wp z₁ := by
    have hraw := isSupportedMaynardY_mul_pow_of_dvd
      (H := Erdos248.nearShifts K) (R := Erdos248.globalRadius K)
      (W := Erdos248.preSieveModulus K * p) (p := p)
      (a := a - 1) (y := z₁) (dvd_mul_left p (Erdos248.preSieveModulus K))
      hy₁base
    have hmod : (Erdos248.preSieveModulus K * p) * p ^ (a - 1) =
        Wp := by
      dsimp [Wp]
      have hpow : p * p ^ (a - 1) = p ^ a := by
        conv_rhs => rw [show a = (a - 1) + 1 by omega, pow_succ]
        ring
      calc
        (Erdos248.preSieveModulus K * p) * p ^ (a - 1) =
            Erdos248.preSieveModulus K * (p * p ^ (a - 1)) := by ring
        _ = Erdos248.preSieveModulus K * p ^ a := by rw [hpow]
    simpa [hmod] using hraw
  have hsecond : ∀ n,
      (if q ^ b ∣ n + m.1 then
          Erdos248.fromYWeight (Erdos248.globalRadius K) Wp v₁ z₁ n else 0) =
        Erdos248.fromYWeight (Erdos248.globalRadius K)
          (Wp * q ^ b) v₂ z₂ n := by
    intro n
    simpa [v₂, z₂] using
      (indicator_coordinatePrimePower_fromYWeight
        (H := Erdos248.nearShifts K) (R := Erdos248.globalRadius K)
        (W := Wp) (v := v₁) (p := q) (a := b) (n := n)
        (y := z₁) hq hb hqW hy₁ m
        (Erdos248.mediumPrime_separated hqCut m))
  have hpoint : ∀ n,
      (if p ^ a ∣ n + m.1 ∧ q ^ b ∣ n + m.1 then
          Erdos248.sieveWeight K n else 0) =
        Erdos248.fromYWeight (Erdos248.globalRadius K)
          (Wp * q ^ b) v₂ z₂ n := by
    intro n
    rw [show (if p ^ a ∣ n + m.1 ∧ q ^ b ∣ n + m.1 then
          Erdos248.sieveWeight K n else 0) =
        if q ^ b ∣ n + m.1 then
          (if p ^ a ∣ n + m.1 then Erdos248.sieveWeight K n else 0)
        else 0 by
          by_cases hpN : p ^ a ∣ n + m.1 <;>
            by_cases hqN : q ^ b ∣ n + m.1 <;> simp [hpN, hqN]]
    rw [hfirst n, hsecond n]
  have hmass : primePowerPairEventMass K m.1 p a q b =
      sieveWeightSum (Erdos248.intervalStart K)
        (Erdos248.fromYWeight (Erdos248.globalRadius K)
          (Wp * q ^ b) v₂ z₂) := by
    unfold primePowerPairEventMass sieveWeightSum
    apply Finset.sum_congr rfl
    intro n hn
    exact hpoint n
  have hy₂base : IsSupportedMaynardY (Erdos248.nearShifts K)
      (Erdos248.globalRadius K) (Wp * q) z₂ := by
    simpa [z₂] using Erdos248.differencePrimeY_supported
      (Erdos248.globalRadius K) Wp q m z₁
  have hy₂ : IsSupportedMaynardY (Erdos248.nearShifts K)
      (Erdos248.globalRadius K) (Wp * q ^ b) z₂ := by
    have hraw := isSupportedMaynardY_mul_pow_of_dvd
      (H := Erdos248.nearShifts K) (R := Erdos248.globalRadius K)
      (W := Wp * q) (p := q) (a := b - 1) (y := z₂)
      (dvd_mul_left q Wp) hy₂base
    have hmod : (Wp * q) * q ^ (b - 1) = Wp * q ^ b := by
      have hpow : q * q ^ (b - 1) = q ^ b := by
        conv_rhs => rw [show b = (b - 1) + 1 by omega, pow_succ]
        ring
      calc
        (Wp * q) * q ^ (b - 1) = Wp * (q * q ^ (b - 1)) := by ring
        _ = Wp * q ^ b := by rw [hpow]
    simpa [hmod] using hraw
  have hySharp : Erdos248.IsVaryingSupported K z₂ := by
    dsimp [z₂, z₁]
    exact Erdos248.differencePrimeY_varyingSupported hq.pos
      (Erdos248.differencePrimeY_varyingSupported hp.pos
        (Erdos248.sieveY_varyingSupported K) m) m
  have hyBound : ∀ r, |z₂ r| ≤ (16 : ℝ) := by
    intro r
    have hfirstBound : ∀ s, |z₁ s| ≤ (4 : ℝ) := by
      intro s
      simpa [z₁] using abs_coordinateDifferencePrimeY_le_four_mul hp hpCut
        (B := (1 : ℝ)) (by norm_num) (Erdos248.abs_sieveY_le_one K) m s
    have hsecondBound := abs_coordinateDifferencePrimeY_le_four_mul hq hqCut
      (W := Wp) (y := z₁) (B := (4 : ℝ)) (by norm_num) hfirstBound m r
    norm_num at hsecondBound ⊢
    simpa [z₂] using hsecondBound
  rw [hmass]
  have hmodBase : Erdos248.preSieveModulus K ∣ Wp * q ^ b := by
    dsimp [Wp]
    rw [mul_assoc]
    exact dvd_mul_right _ _
  have hWp : 0 < Wp := by
    dsimp [Wp]
    exact mul_pos (Erdos248.preSieveModulus_pos K) (pow_pos hp.pos _)
  have hW : 0 < Wp * q ^ b := mul_pos hWp (pow_pos hq.pos _)
  have hraw := Erdos248.fromYWeightMass_le_productCoordinateEnergy
    hA hreg hmodBase hW hy₂ hySharp
    (B := (16 : ℝ)) (by norm_num) hyBound (v := v₂)
  norm_num at hraw
  simpa [Wp, mul_assoc] using hraw

end TaoTeravainen
