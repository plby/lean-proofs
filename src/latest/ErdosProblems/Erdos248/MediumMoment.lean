import ErdosProblems.Erdos248.MediumEnergy
import ErdosProblems.Erdos248.RangeMomentIdentities

/-!
# Erdős Problem 248: the medium-prime second moment

This file assembles single- and two-prime event estimates into the weighted
second moment of the medium-prime divisor count.  The analytic event-mass
input is deliberately isolated in the hypotheses of the main assembly lemma;
`MediumEventMass` can discharge those hypotheses without changing the finite
moment argument.
-/

noncomputable section

open scoped BigOperators
open BoundedGaps.Maynard

namespace Erdos248

local instance mediumMomentDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The normalized logarithmic weight occurring in a medium-prime event. -/
def mediumPrimeLogWeight (K k p : ℕ) : ℝ :=
  (Real.log (p : ℝ) / Real.log (shiftRadius K k : ℝ)) ^ 2 / (p : ℝ)

/-- Linear normalized logarithmic weight.  Distinct-prime correlations use
the product of two such weights. -/
def mediumPrimeLinearLogWeight (K k p : ℕ) : ℝ :=
  (Real.log (p : ℝ) / Real.log (shiftRadius K k : ℝ)) / (p : ℝ)

theorem mediumPrimeLogWeight_nonneg (K k p : ℕ) :
    0 ≤ mediumPrimeLogWeight K k p := by
  unfold mediumPrimeLogWeight
  positivity

theorem mediumPrimeLinearLogWeight_nonneg {K k p : ℕ}
    (hp : p ∈ mediumPrimes K k) :
    0 ≤ mediumPrimeLinearLogWeight K k p := by
  unfold mediumPrimeLinearLogWeight
  have hpPrime := (mem_primesBetween.mp hp).2.2
  exact div_nonneg
    (div_nonneg (Real.log_natCast_nonneg p)
      (Real.log_nonneg (by exact_mod_cast (one_lt_shiftRadius K k).le)))
    (by positivity)

theorem sum_mediumPrimeLogWeight_le (K k : ℕ) :
    (∑ p ∈ mediumPrimes K k, mediumPrimeLogWeight K k p) ≤
      normalizedPrimeLogSquareConstant := by
  simpa [mediumPrimeLogWeight] using
    sum_mediumPrimes_normalized_log_sq_le K k

/-- Exact double-sum expansion of the medium-prime weighted second moment. -/
theorem mediumWeightedSecondMoment_eq_doubleEventMass (K k : ℕ) :
    weightedSecondMoment
        (Finset.Ico (intervalStart K) (2 * intervalStart K))
        (sieveWeight K)
        (fun n => ∑ p ∈ mediumPrimes K k,
          realIndicator (p ∣ n + k)) =
      ∑ p ∈ mediumPrimes K k, ∑ q ∈ mediumPrimes K k,
        primeProductEventMass K k {p, q} := by
  classical
  let s := Finset.Ico (intervalStart K) (2 * intervalStart K)
  let I := mediumPrimes K k
  let e : ℕ → ℕ → ℝ := fun p n => realIndicator (p ∣ n + k)
  calc
    weightedSecondMoment s (sieveWeight K)
        (fun n => ∑ p ∈ I, e p n) =
        ∑ n ∈ s, ∑ p ∈ I, ∑ q ∈ I,
          sieveWeight K n * (e p n * e q n) := by
      unfold weightedSecondMoment weightedMoment weightedSum
      apply Finset.sum_congr rfl
      intro n hn
      change sieveWeight K n * (∑ p ∈ I, e p n) ^ 2 = _
      rw [pow_two, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    _ = ∑ p ∈ I, ∑ q ∈ I, ∑ n ∈ s,
          sieveWeight K n * (e p n * e q n) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_comm]
    _ = ∑ p ∈ I, ∑ q ∈ I,
        primeProductEventMass K k {p, q} := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      rw [← weightedMass_primeDivisibility_eq_primeProductEventMass]
      unfold weightedMass weightedSum
      apply Finset.sum_congr rfl
      intro n hn
      dsimp [e]
      by_cases hpdiv : p ∣ n + k <;> by_cases hqdiv : q ∣ n + k <;>
        simp [realIndicator, hpdiv, hqdiv]

/-- Abstract assembly of the medium second moment.  The diagonal event is
bounded linearly in `u(p)`, while distinct pairs are bounded by
`u(p)u(q)`. -/
theorem mediumWeightedSecondMoment_le_of_eventMass
    {K k : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hsingle : ∀ p ∈ mediumPrimes K k,
      primeProductEventMass K k {p} ≤
        B * mediumPrimeLogWeight K k p)
    (hpair : ∀ p ∈ mediumPrimes K k, ∀ q ∈ mediumPrimes K k,
      p ≠ q → primeProductEventMass K k {p, q} ≤
        B * mediumPrimeLogWeight K k p * mediumPrimeLogWeight K k q) :
    weightedSecondMoment
        (Finset.Ico (intervalStart K) (2 * intervalStart K))
        (sieveWeight K)
        (fun n => ∑ p ∈ mediumPrimes K k,
          realIndicator (p ∣ n + k)) ≤
      B * (normalizedPrimeLogSquareConstant +
        normalizedPrimeLogSquareConstant ^ 2) := by
  rw [mediumWeightedSecondMoment_eq_doubleEventMass]
  let I := mediumPrimes K k
  let u : ℕ → ℝ := mediumPrimeLogWeight K k
  let S : ℝ := ∑ p ∈ I, u p
  calc
    (∑ p ∈ I, ∑ q ∈ I, primeProductEventMass K k {p, q}) ≤
        ∑ p ∈ I, ∑ q ∈ I,
          if p = q then B * u p else B * u p * u q := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      by_cases hpq : p = q
      · subst q
        simpa using hsingle p hp
      · simpa [hpq] using hpair p hp q hq hpq
    _ ≤ ∑ p ∈ I, ∑ q ∈ I,
          ((if p = q then B * u p else 0) + B * u p * u q) := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      by_cases hpq : p = q
      · subst q
        simp only [if_pos rfl]
        apply le_add_of_nonneg_right
        exact mul_nonneg
          (mul_nonneg hB (by simpa [u] using mediumPrimeLogWeight_nonneg K k p))
          (by simpa [u] using mediumPrimeLogWeight_nonneg K k p)
      · simp [hpq]
    _ = B * S + B * S ^ 2 := by
      dsimp [S]
      simp_rw [Finset.sum_add_distrib]
      have hdiag :
          (∑ p ∈ I, ∑ q ∈ I, if p = q then B * u p else 0) =
            B * ∑ p ∈ I, u p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        simp [hp]
      rw [hdiag]
      have hpairSum :
          (∑ p ∈ I, ∑ q ∈ I, B * u p * u q) =
            B * (∑ p ∈ I, u p) ^ 2 := by
        calc
          (∑ p ∈ I, ∑ q ∈ I, B * u p * u q) =
              ∑ p ∈ I, (B * u p) * (∑ q ∈ I, u q) := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [Finset.mul_sum]
          _ = (∑ p ∈ I, B * u p) * (∑ q ∈ I, u q) := by
            rw [Finset.sum_mul]
          _ = B * (∑ p ∈ I, u p) ^ 2 := by
            rw [← Finset.mul_sum]
            ring
      rw [hpairSum]
    _ ≤ B * (normalizedPrimeLogSquareConstant +
        normalizedPrimeLogSquareConstant ^ 2) := by
      have hS : S ≤ normalizedPrimeLogSquareConstant := by
        simpa [S, I, u] using sum_mediumPrimeLogWeight_le K k
      have hS0 : 0 ≤ S := by
        dsimp [S]
        exact Finset.sum_nonneg fun p hp => mediumPrimeLogWeight_nonneg K k p
      have hC0 := normalizedPrimeLogSquareConstant_nonneg
      have hSsq : S ^ 2 ≤ normalizedPrimeLogSquareConstant ^ 2 :=
        (sq_le_sq₀ hS0 hC0).mpr hS
      nlinarith

/-- Correctly scaled medium-moment assembly: diagonal events use
`(δ_p)^2/p`, while distinct pairs use `(δ_p/p)(δ_q/q)`. -/
theorem mediumWeightedSecondMoment_le_of_diagonal_pairEventMass
    {K k : ℕ} {Bdiag Bpair : ℝ}
    (hBdiag : 0 ≤ Bdiag) (hBpair : 0 ≤ Bpair)
    (hsingle : ∀ p ∈ mediumPrimes K k,
      primeProductEventMass K k {p} ≤
        Bdiag * mediumPrimeLogWeight K k p)
    (hpair : ∀ p ∈ mediumPrimes K k, ∀ q ∈ mediumPrimes K k,
      p ≠ q → primeProductEventMass K k {p, q} ≤
        Bpair * mediumPrimeLinearLogWeight K k p *
          mediumPrimeLinearLogWeight K k q) :
    weightedSecondMoment
        (Finset.Ico (intervalStart K) (2 * intervalStart K))
        (sieveWeight K)
        (fun n => ∑ p ∈ mediumPrimes K k,
          realIndicator (p ∣ n + k)) ≤
      Bdiag * (∑ p ∈ mediumPrimes K k, mediumPrimeLogWeight K k p) +
        Bpair *
          (∑ p ∈ mediumPrimes K k, mediumPrimeLinearLogWeight K k p) ^ 2 := by
  rw [mediumWeightedSecondMoment_eq_doubleEventMass]
  let I := mediumPrimes K k
  let u : ℕ → ℝ := mediumPrimeLinearLogWeight K k
  let v : ℕ → ℝ := mediumPrimeLogWeight K k
  calc
    (∑ p ∈ I, ∑ q ∈ I, primeProductEventMass K k {p, q}) ≤
        ∑ p ∈ I, ∑ q ∈ I,
          if p = q then Bdiag * v p else Bpair * u p * u q := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      by_cases hpq : p = q
      · subst q
        simpa [I, v] using hsingle p hp
      · simpa [I, u, hpq] using hpair p hp q hq hpq
    _ ≤ ∑ p ∈ I, ∑ q ∈ I,
          ((if p = q then Bdiag * v p else 0) + Bpair * u p * u q) := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      by_cases hpq : p = q
      · subst q
        simp only [if_pos rfl]
        exact le_add_of_nonneg_right <|
          mul_nonneg
            (mul_nonneg hBpair (mediumPrimeLinearLogWeight_nonneg hp))
            (mediumPrimeLinearLogWeight_nonneg hp)
      · simp [hpq]
    _ = Bdiag * (∑ p ∈ I, v p) +
        Bpair * (∑ p ∈ I, u p) ^ 2 := by
      simp_rw [Finset.sum_add_distrib]
      have hdiag :
          (∑ p ∈ I, ∑ q ∈ I,
              if p = q then Bdiag * v p else 0) =
            Bdiag * ∑ p ∈ I, v p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        simp [hp]
      rw [hdiag]
      have hpairSum :
          (∑ p ∈ I, ∑ q ∈ I, Bpair * u p * u q) =
            Bpair * (∑ p ∈ I, u p) ^ 2 := by
        calc
          (∑ p ∈ I, ∑ q ∈ I, Bpair * u p * u q) =
              ∑ p ∈ I, (Bpair * u p) * (∑ q ∈ I, u q) := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [Finset.mul_sum]
          _ = (∑ p ∈ I, Bpair * u p) *
              (∑ q ∈ I, u q) := by rw [Finset.sum_mul]
          _ = Bpair * (∑ p ∈ I, u p) ^ 2 := by
            rw [← Finset.mul_sum]
            ring
      rw [hpairSum]
    _ = Bdiag * (∑ p ∈ mediumPrimes K k, mediumPrimeLogWeight K k p) +
        Bpair *
          (∑ p ∈ mediumPrimes K k, mediumPrimeLinearLogWeight K k p) ^ 2 :=
      rfl

/-- The preceding assembly with externally supplied uniform bounds for the
two elementary prime sums. -/
theorem mediumWeightedSecondMoment_le_of_eventMass_and_sums
    {K k : ℕ} {Bdiag Bpair U V : ℝ}
    (hBdiag : 0 ≤ Bdiag) (hBpair : 0 ≤ Bpair)
    (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hsumU : (∑ p ∈ mediumPrimes K k,
      mediumPrimeLinearLogWeight K k p) ≤ U)
    (hsumV : (∑ p ∈ mediumPrimes K k,
      mediumPrimeLogWeight K k p) ≤ V)
    (hsingle : ∀ p ∈ mediumPrimes K k,
      primeProductEventMass K k {p} ≤
        Bdiag * mediumPrimeLogWeight K k p)
    (hpair : ∀ p ∈ mediumPrimes K k, ∀ q ∈ mediumPrimes K k,
      p ≠ q → primeProductEventMass K k {p, q} ≤
        Bpair * mediumPrimeLinearLogWeight K k p *
          mediumPrimeLinearLogWeight K k q) :
    weightedSecondMoment
        (Finset.Ico (intervalStart K) (2 * intervalStart K))
        (sieveWeight K)
        (fun n => ∑ p ∈ mediumPrimes K k,
          realIndicator (p ∣ n + k)) ≤
      Bdiag * V + Bpair * U ^ 2 := by
  have hraw := mediumWeightedSecondMoment_le_of_diagonal_pairEventMass
    hBdiag hBpair hsingle hpair
  have hsumU0 : 0 ≤ ∑ p ∈ mediumPrimes K k,
      mediumPrimeLinearLogWeight K k p :=
    Finset.sum_nonneg fun p hp => mediumPrimeLinearLogWeight_nonneg hp
  have hUsq :
      (∑ p ∈ mediumPrimes K k, mediumPrimeLinearLogWeight K k p) ^ 2 ≤
        U ^ 2 := (sq_le_sq₀ hsumU0 hU).mpr hsumU
  nlinarith

/-- A finite-sum assembly lemma with arbitrary nonnegative diagonal and
off-diagonal majorants.  It is useful when the small reciprocal-prime
remainders are only summable after all medium primes have been added. -/
theorem mediumWeightedSecondMoment_le_of_single_pairMajorants
    {K k : ℕ} (F : ℕ → ℝ) (G : ℕ → ℕ → ℝ)
    (hG : ∀ p ∈ mediumPrimes K k, ∀ q ∈ mediumPrimes K k, 0 ≤ G p q)
    (hsingle : ∀ p ∈ mediumPrimes K k,
      primeProductEventMass K k {p} ≤ F p)
    (hpair : ∀ p ∈ mediumPrimes K k, ∀ q ∈ mediumPrimes K k,
      p ≠ q → primeProductEventMass K k {p, q} ≤ G p q) :
    weightedSecondMoment
        (Finset.Ico (intervalStart K) (2 * intervalStart K))
        (sieveWeight K)
        (fun n => ∑ p ∈ mediumPrimes K k,
          realIndicator (p ∣ n + k)) ≤
      (∑ p ∈ mediumPrimes K k, F p) +
        ∑ p ∈ mediumPrimes K k, ∑ q ∈ mediumPrimes K k, G p q := by
  rw [mediumWeightedSecondMoment_eq_doubleEventMass]
  let I := mediumPrimes K k
  calc
    (∑ p ∈ I, ∑ q ∈ I, primeProductEventMass K k {p, q}) ≤
        ∑ p ∈ I, ∑ q ∈ I, if p = q then F p else G p q := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      by_cases hpq : p = q
      · subst q
        simpa [I] using hsingle p hp
      · simpa [hpq, I] using hpair p hp q hq hpq
    _ ≤ ∑ p ∈ I, ∑ q ∈ I,
          ((if p = q then F p else 0) + G p q) := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      by_cases hpq : p = q
      · subst q
        simp only [if_pos rfl]
        exact le_add_of_nonneg_right (hG p hp p hp)
      · simp [hpq]
    _ = (∑ p ∈ I, F p) + ∑ p ∈ I, ∑ q ∈ I, G p q := by
      simp_rw [Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      simp [hp]
    _ = (∑ p ∈ mediumPrimes K k, F p) +
        ∑ p ∈ mediumPrimes K k, ∑ q ∈ mediumPrimes K k, G p q := rfl

/-- Direct raw-moment tail consequence of the abstract event bounds. -/
theorem threshold_sq_mul_mediumPrimeBadMass_le_of_eventMass
    {K T k : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hsingle : ∀ p ∈ mediumPrimes K k,
      primeProductEventMass K k {p} ≤
        B * mediumPrimeLogWeight K k p)
    (hpair : ∀ p ∈ mediumPrimes K k, ∀ q ∈ mediumPrimes K k,
      p ≠ q → primeProductEventMass K k {p, q} ≤
        B * mediumPrimeLogWeight K k p * mediumPrimeLogWeight K k q) :
    (((T * k + 1 : ℕ) : ℝ) ^ 2) * mediumPrimeBadMass K T k ≤
      B * (normalizedPrimeLogSquareConstant +
        normalizedPrimeLogSquareConstant ^ 2) := by
  exact (threshold_sq_mul_mediumPrimeBadMass_le_secondMoment K T k).trans
    (mediumWeightedSecondMoment_le_of_eventMass hB hsingle hpair)

/-- Normalized variant: if each event is bounded relative to the total sieve
mass, then so are the second moment and the Markov tail. -/
theorem threshold_sq_mul_mediumPrimeBadMass_le_of_relativeEventMass
    {K T k : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hsingle : ∀ p ∈ mediumPrimes K k,
      primeProductEventMass K k {p} ≤
        B * sieveMass K * mediumPrimeLogWeight K k p)
    (hpair : ∀ p ∈ mediumPrimes K k, ∀ q ∈ mediumPrimes K k,
      p ≠ q → primeProductEventMass K k {p, q} ≤
        B * sieveMass K * mediumPrimeLogWeight K k p *
          mediumPrimeLogWeight K k q) :
    (((T * k + 1 : ℕ) : ℝ) ^ 2) * mediumPrimeBadMass K T k ≤
      B * (normalizedPrimeLogSquareConstant +
        normalizedPrimeLogSquareConstant ^ 2) * sieveMass K := by
  have hmass : 0 ≤ sieveMass K := by
    unfold sieveMass sieveWeightSum
    exact Finset.sum_nonneg fun n hn => sieveWeight_nonneg K n
  have hraw := threshold_sq_mul_mediumPrimeBadMass_le_of_eventMass
    (K := K) (T := T) (k := k) (B := B * sieveMass K)
    (mul_nonneg hB hmass) hsingle hpair
  nlinarith

private theorem exists_mediumNaturalMomentThreshold (L : ℝ) (hL : 0 < L) :
    ∃ T : ℕ, 0 < T ∧ 16 * L ≤ (T : ℝ) ^ 2 := by
  obtain ⟨T : ℕ, hT⟩ := exists_nat_gt (max 16 (16 * L))
  have hT16 : (16 : ℝ) < T := (le_max_left _ _).trans_lt hT
  have hTL : 16 * L < T := (le_max_right _ _).trans_lt hT
  have hTnat : 0 < T := by exact_mod_cast (show (0 : ℝ) < T by linarith)
  have hTone : (1 : ℝ) ≤ T := by exact_mod_cast hTnat
  have hTsq : (T : ℝ) ≤ (T : ℝ) ^ 2 := by nlinarith
  exact ⟨T, hTnat, hTL.le.trans hTsq⟩

private theorem mediumTail_le_sixteenth_inv_sq
    {D L M B k : ℝ} (hD : 0 < D) (hM : 0 ≤ M)
    (hk : 0 < k) (hsize : 16 * L ≤ D ^ 2)
    (hmoment : (D * k) ^ 2 * B ≤ L * M) :
    B ≤ M * (1 / (16 * k ^ 2)) := by
  have hden : 0 < (D * k) ^ 2 := sq_pos_of_pos (mul_pos hD hk)
  have hkden : 0 < 16 * k ^ 2 := mul_pos (by norm_num) (sq_pos_of_pos hk)
  have hfirst : B ≤ (L * M) / ((D * k) ^ 2) :=
    (le_div_iff₀ hden).2 (by simpa [mul_comm] using hmoment)
  have hcross : (L * M) * (16 * k ^ 2) ≤ M * ((D * k) ^ 2) := by
    have hscale : L * (16 * k ^ 2) ≤ (D * k) ^ 2 := by
      calc
        L * (16 * k ^ 2) = (16 * L) * k ^ 2 := by ring
        _ ≤ D ^ 2 * k ^ 2 :=
          mul_le_mul_of_nonneg_right hsize (sq_nonneg k)
        _ = (D * k) ^ 2 := by ring
    nlinarith [mul_le_mul_of_nonneg_left hscale hM]
  calc
    B ≤ (L * M) / ((D * k) ^ 2) := hfirst
    _ ≤ M / (16 * k ^ 2) := (div_le_div_iff₀ hden hkden).2 hcross
    _ = M * (1 / (16 * k ^ 2)) := by ring

/-- Once a uniform relative second-moment constant is available, a single
natural threshold gives the exact reciprocal-square medium-prime tail needed
by the global union bound. -/
theorem exists_uniform_mediumPrimeBadMass_tail_of_secondMoment
    (L : ℝ) (hL : 0 < L)
    (hmoment : ∀ {A : ℝ}, HasUniformWirsingBound A →
      ∀ {K k : ℕ}, NormalizationRegular A K → 1 ≤ k → k ≤ K →
        weightedSecondMoment
            (Finset.Ico (intervalStart K) (2 * intervalStart K))
            (sieveWeight K)
            (fun n => ∑ p ∈ mediumPrimes K k,
              realIndicator (p ∣ n + k)) ≤ L * sieveMass K) :
    ∃ T : ℕ, ∀ {A : ℝ}, HasUniformWirsingBound A →
      ∀ {K k : ℕ}, NormalizationRegular A K → 1 ≤ k → k ≤ K →
        mediumPrimeBadMass K T k ≤
          sieveMass K * (1 / (16 * (k : ℝ) ^ 2)) := by
  obtain ⟨T, hT, hTsize⟩ := exists_mediumNaturalMomentThreshold L hL
  refine ⟨T, ?_⟩
  intro A hA K k hreg hk1 hkK
  have hmass : 0 ≤ sieveMass K := by
    unfold sieveMass sieveWeightSum
    exact Finset.sum_nonneg fun n hn => sieveWeight_nonneg K n
  have hbad : 0 ≤ mediumPrimeBadMass K T k :=
    mediumPrimeBadMass_nonneg K T k
  have hmarkov := threshold_sq_mul_mediumPrimeBadMass_le_secondMoment K T k
  have hsecond := hmoment hA hreg hk1 hkK
  have hthreshold : (T : ℝ) * (k : ℝ) ≤ ((T * k + 1 : ℕ) : ℝ) := by
    push_cast
    norm_num
  have hthresholdSq : ((T : ℝ) * (k : ℝ)) ^ 2 ≤
      ((T * k + 1 : ℕ) : ℝ) ^ 2 := by
    exact (sq_le_sq₀ (by positivity) (by positivity)).mpr hthreshold
  have hraw : (((T : ℝ) * (k : ℝ)) ^ 2) *
      mediumPrimeBadMass K T k ≤ L * sieveMass K := by
    calc
      (((T : ℝ) * (k : ℝ)) ^ 2) * mediumPrimeBadMass K T k ≤
          (((T * k + 1 : ℕ) : ℝ) ^ 2) *
            mediumPrimeBadMass K T k :=
        mul_le_mul_of_nonneg_right hthresholdSq hbad
      _ ≤ weightedSecondMoment
          (Finset.Ico (intervalStart K) (2 * intervalStart K))
          (sieveWeight K)
          (fun n => ∑ p ∈ mediumPrimes K k,
            realIndicator (p ∣ n + k)) := hmarkov
      _ ≤ L * sieveMass K := hsecond
  exact mediumTail_le_sixteenth_inv_sq
    (by exact_mod_cast hT) hmass (by exact_mod_cast hk1) hTsize hraw

end Erdos248
