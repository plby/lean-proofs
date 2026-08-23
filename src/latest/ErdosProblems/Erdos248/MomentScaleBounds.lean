import ErdosProblems.Erdos248.SieveMassBounds
import ErdosProblems.Erdos248.PrimeSumBounds

/-!
# Erdős Problem 248: scale absorption for moment errors

The correlation estimates contain the factor `96^K`, while every event
prime is larger than `tinyCutoff K = 2^(100K)`.  The elementary inequalities
in this file record that the latter absorbs all powers of `K` needed in the
second- and fourth-moment expansions.
-/

noncomputable section

open scoped BigOperators
open BoundedGaps.Maynard

namespace Erdos248

theorem sixth_mul_ninetySixPow_le_tinyCutoff {K : ℕ} (hK : 0 < K) :
    K ^ 6 * 96 ^ K ≤ tinyCutoff K := by
  calc
    K ^ 6 * 96 ^ K ≤ (2 ^ K) ^ 6 * (128 : ℕ) ^ K := by
      exact Nat.mul_le_mul
        (Nat.pow_le_pow_left K.lt_two_pow_self.le 6)
        (Nat.pow_le_pow_left (by norm_num) K)
    _ = 2 ^ (13 * K) := by
      rw [show (128 : ℕ) = 2 ^ 7 by norm_num, ← pow_mul, ← pow_mul,
        ← pow_add]
      congr 1
      omega
    _ ≤ 2 ^ (100 * K) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = tinyCutoff K := rfl

theorem fifth_mul_ninetySixPow_le_tinyCutoff {K : ℕ} (hK : 0 < K) :
    K ^ 5 * 96 ^ K ≤ tinyCutoff K := by
  apply (Nat.mul_le_mul_right (96 ^ K) ?_).trans
    (sixth_mul_ninetySixPow_le_tinyCutoff hK)
  rw [show K ^ 6 = K ^ 5 * K by ring]
  exact Nat.le_mul_of_pos_right _ hK

theorem real_fifth_ninetySix_div_tiny_le_one {K : ℕ} (hK : 0 < K) :
    (K : ℝ) ^ 5 * 96 ^ K / tinyCutoff K ≤ 1 := by
  have hD : (0 : ℝ) < tinyCutoff K := by exact_mod_cast tinyCutoff_pos K
  apply (div_le_iff₀ hD).2
  norm_num
  exact_mod_cast fifth_mul_ninetySixPow_le_tinyCutoff hK

theorem real_sixth_ninetySix_div_tiny_le_one {K : ℕ} (hK : 0 < K) :
    (K : ℝ) ^ 6 * 96 ^ K / tinyCutoff K ≤ 1 := by
  have hD : (0 : ℝ) < tinyCutoff K := by exact_mod_cast tinyCutoff_pos K
  apply (div_le_iff₀ hD).2
  norm_num
  exact_mod_cast sixth_mul_ninetySixPow_le_tinyCutoff hK

theorem crossTail_mul_ninetySixPow_mul_fourth_le {K : ℕ} (hK : 0 < K) :
    roughCrossTupleTotientSquareTail (nearShifts K) (tinyCutoff K)
        (globalRadius K) * 96 ^ K * (K : ℝ) ^ 4 ≤ 196608 := by
  have htail := roughCrossTail_le_explicit hK
  have hexp := exp_eight_le_two_pow_thirteen
  have h96 : (0 : ℝ) ≤ 96 ^ K := by positivity
  have hK4 : (0 : ℝ) ≤ (K : ℝ) ^ 4 := by positivity
  calc
    roughCrossTupleTotientSquareTail (nearShifts K) (tinyCutoff K)
          (globalRadius K) * 96 ^ K * (K : ℝ) ^ 4 ≤
        (3 * (8 * Real.exp 8 / (tinyCutoff K : ℝ)) * (K : ℝ) ^ 2) *
          96 ^ K * (K : ℝ) ^ 4 := by
      gcongr
    _ ≤ (3 * (8 * (2 : ℝ) ^ 13 / (tinyCutoff K : ℝ)) *
          (K : ℝ) ^ 2) * 96 ^ K * (K : ℝ) ^ 4 := by
      gcongr
    _ = 196608 *
          ((K : ℝ) ^ 6 * 96 ^ K / tinyCutoff K) := by
      norm_num
      ring
    _ ≤ 196608 * 1 := by
      gcongr
      exact real_sixth_ninetySix_div_tiny_le_one hK
    _ = 196608 := by ring

theorem sum_card_four_K_div_totient_le
    {K : ℕ} {P : Finset ℕ} (hcard : P.card ≤ 4)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPcut : ∀ p ∈ P, tinyCutoff K < p) :
    (∑ p ∈ P, (K : ℝ) / Nat.totient p) ≤
      4 * (K : ℝ) / tinyCutoff K := by
  have hD : (0 : ℝ) < tinyCutoff K := by exact_mod_cast tinyCutoff_pos K
  calc
    (∑ p ∈ P, (K : ℝ) / Nat.totient p) ≤
        ∑ _p ∈ P, (K : ℝ) / tinyCutoff K := by
      apply Finset.sum_le_sum
      intro p hp
      have hpPrime := hPprime p hp
      have htot : Nat.totient p = p - 1 := Nat.totient_prime hpPrime
      have hpCut := hPcut p hp
      have hcut : tinyCutoff K ≤ p - 1 := by omega
      rw [htot]
      exact div_le_div_of_nonneg_left (by positivity) hD
        (by exact_mod_cast hcut)
    _ = (P.card : ℝ) * ((K : ℝ) / tinyCutoff K) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 4 * ((K : ℝ) / tinyCutoff K) := by
      gcongr
      exact_mod_cast hcard
    _ = 4 * (K : ℝ) / tinyCutoff K := by ring

/-- Uniform fourth-moment absorption of the relative correlation error for
any event involving at most four primes. -/
theorem primeProductRelativeError_mul_fourth_le
    {K : ℕ} (hK : 0 < K) {P : Finset ℕ} (hcard : P.card ≤ 4)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPcut : ∀ p ∈ P, tinyCutoff K < p) :
    (2048 * (∑ p ∈ P, (K : ℝ) / Nat.totient p) +
        257 * roughCrossTupleTotientSquareTail (nearShifts K)
          (tinyCutoff K) (globalRadius K)) *
        96 ^ K * (K : ℝ) ^ 4 ≤ 50536448 := by
  have hsum := sum_card_four_K_div_totient_le hcard hPprime hPcut
  have henergy :
      (4 * (K : ℝ) / tinyCutoff K) * 96 ^ K * (K : ℝ) ^ 4 ≤ 4 := by
    calc
      (4 * (K : ℝ) / tinyCutoff K) * 96 ^ K * (K : ℝ) ^ 4 =
          4 * ((K : ℝ) ^ 5 * 96 ^ K / tinyCutoff K) := by ring
      _ ≤ 4 * 1 := by
        gcongr
        exact real_fifth_ninetySix_div_tiny_le_one hK
      _ = 4 := by ring
  have hcross := crossTail_mul_ninetySixPow_mul_fourth_le hK
  calc
    (2048 * (∑ p ∈ P, (K : ℝ) / Nat.totient p) +
          257 * roughCrossTupleTotientSquareTail (nearShifts K)
            (tinyCutoff K) (globalRadius K)) *
          96 ^ K * (K : ℝ) ^ 4 ≤
        (2048 * (4 * (K : ℝ) / tinyCutoff K) +
          257 * roughCrossTupleTotientSquareTail (nearShifts K)
            (tinyCutoff K) (globalRadius K)) *
          96 ^ K * (K : ℝ) ^ 4 := by
      gcongr
    _ = 2048 * ((4 * (K : ℝ) / tinyCutoff K) *
          96 ^ K * (K : ℝ) ^ 4) +
        257 * (roughCrossTupleTotientSquareTail (nearShifts K)
          (tinyCutoff K) (globalRadius K) * 96 ^ K * (K : ℝ) ^ 4) := by
      ring
    _ ≤ 2048 * 4 + 257 * 196608 := by gcongr
    _ = 50536448 := by norm_num

theorem eightThousand_le_radiusProduct {K : ℕ} (hK : 0 < K) :
    8192 ≤ radiusProduct K := by
  have hexp : 13 ≤ 100 ^ (100 * K - 1) := by
    have hpow : 100 ≤ 100 ^ (100 * K - 1) := by
      rw [show 100 = 100 ^ 1 by norm_num]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  calc
    8192 = 2 ^ 13 := by norm_num
    _ ≤ 2 ^ (100 ^ (100 * K - 1)) :=
      Nat.pow_le_pow_right (by norm_num) hexp
    _ ≤ 2 ^ radiusExponentBudget K :=
      Nat.pow_le_pow_right (by norm_num) (firstRadiusExponent_le_budget hK)
    _ = radiusProduct K := (radiusProduct_eq_pow K).symm

theorem largestRadius_le_radiusProduct {K : ℕ} (hK : 0 < K) :
    shiftRadius K 1 ≤ radiusProduct K := by
  rw [shiftRadius, radiusProduct_eq_pow]
  exact Nat.pow_le_pow_right (by norm_num) (firstRadiusExponent_le_budget hK)

/-- Even after summing one interval error over sixteen centered terms and
all ordered prime quadruples, the dyadic interval dwarfs the error. -/
theorem accumulatedFourthIntervalError_scaled_lt
    {K J : ℕ} (hK : 0 < K) (hJ : J ≤ shiftRadius K 1) :
    16 * J ^ 4 * 257 * radiusProduct K ^ 6 *
        (preSieveModulus K * 4 * 16 ^ K) < intervalStart K := by
  have hRone : 1 ≤ radiusProduct K := by
    rw [radiusProduct_eq_pow]
    exact Nat.one_le_pow _ _ (by norm_num)
  have hconst : 16 * 257 ≤ radiusProduct K := by
    exact (by norm_num : 16 * 257 ≤ 8192).trans
      (eightThousand_le_radiusProduct hK)
  have hJR : J ≤ radiusProduct K :=
    hJ.trans (largestRadius_le_radiusProduct hK)
  have hJpow : J ^ 4 ≤ radiusProduct K ^ 4 :=
    Nat.pow_le_pow_left hJR 4
  have hnuis : preSieveModulus K * 4 * 16 ^ K ≤ radiusProduct K := by
    have hfull := nuisanceNaturalProduct_le_radiusProduct hK
    have hfactorPos : 0 < (2 * intervalExponent K) ^ (4 * K ^ 2) := by
      exact pow_pos (Nat.mul_pos (by norm_num) (intervalExponent_pos K)) _
    calc
      preSieveModulus K * 4 * 16 ^ K ≤
          preSieveModulus K * 4 * 16 ^ K *
            (2 * intervalExponent K) ^ (4 * K ^ 2) :=
        Nat.le_mul_of_pos_right _ hfactorPos
      _ ≤ radiusProduct K := hfull
  calc
    16 * J ^ 4 * 257 * radiusProduct K ^ 6 *
          (preSieveModulus K * 4 * 16 ^ K) =
        (16 * 257) * J ^ 4 * radiusProduct K ^ 6 *
          (preSieveModulus K * 4 * 16 ^ K) := by ring
    _ ≤ radiusProduct K * radiusProduct K ^ 4 * radiusProduct K ^ 6 *
          radiusProduct K := by gcongr
    _ = radiusProduct K ^ 12 := by ring
    _ ≤ radiusProduct K ^ 99 :=
      pow_le_pow_right' hRone (by norm_num)
    _ < intervalStart K := radiusProduct_pow_lt_intervalStart hK

theorem accumulatedFourthIntervalError_lt_sieveMass
    {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K J : ℕ} (hreg : NormalizationRegular A K)
    (hJ : J ≤ shiftRadius K 1) :
    16 * (J : ℝ) ^ 4 * ((radiusProduct K : ℝ) ^ 6 * 257) <
      sieveMass K := by
  let F : ℝ := (preSieveModulus K : ℝ) * 4 * 16 ^ K
  have hF : 0 < F := by
    dsimp [F]
    exact mul_pos
      (mul_pos (by exact_mod_cast preSieveModulus_pos K) (by norm_num))
      (pow_pos (by norm_num) K)
  have hscaledNat := accumulatedFourthIntervalError_scaled_lt hreg.1 hJ
  have hscaledNat' :
      16 * J ^ 4 * (radiusProduct K ^ 6 * 257) *
          (preSieveModulus K * 4 * 16 ^ K) < intervalStart K := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hscaledNat
  have hscaled :
      (16 * (J : ℝ) ^ 4 * ((radiusProduct K : ℝ) ^ 6 * 257)) * F <
        intervalStart K := by
    dsimp [F]
    exact_mod_cast hscaledNat'
  have herr :
      16 * (J : ℝ) ^ 4 * ((radiusProduct K : ℝ) ^ 6 * 257) <
        (intervalStart K : ℝ) / F := (lt_div_iff₀ hF).2 hscaled
  have henergy := one_div_sixteen_pow_le_productCoordinateEnergy hreg.1
  calc
    16 * (J : ℝ) ^ 4 * ((radiusProduct K : ℝ) ^ 6 * 257) <
        (intervalStart K : ℝ) / F := herr
    _ = (intervalStart K : ℝ) / preSieveModulus K *
        ((1 / 4 : ℝ) * (1 / 16 : ℝ) ^ K) := by
      dsimp [F]
      have hpow : (16 : ℝ) ^ K ≠ 0 := by positivity
      field_simp
      simpa [div_pow, hpow] using (inv_mul_cancel₀ hpow).symm
    _ ≤ (intervalStart K : ℝ) / preSieveModulus K *
        ((1 / 4 : ℝ) * productCoordinateEnergy K) := by gcongr
    _ < sieveMass K := quarter_scaled_energy_lt_sieveMass hA hreg

end Erdos248
