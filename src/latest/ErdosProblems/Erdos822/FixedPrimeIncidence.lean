/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.DivisibleSmallMass

/-!
# Summing a fixed-prime incidence over the odd cofactor layer

The odd cofactor product map is injective.  Consequently the reciprocal
mass on which a fixed prime divides the shifted totient can be expanded
exactly into nested small-, middle-, and large-prime sums.
-/

namespace Erdos822

open scoped BigOperators

/-- Exact triple expansion of one shifted-divisibility incidence sum. -/
theorem sum_inv_shiftedDivisibleOddCofactors_eq_triple_sum
    {N p : ℕ} (hN : 2 ≤ N) :
    ∑ m ∈ shiftedDivisibleOddCofactors N p, (1 : ℝ) / m =
      ∑ k ∈ oddSmallFactors N,
        ∑ r ∈ middlePrimes N,
          ∑ q ∈ shiftedDivisibleLargePrimes N p k r,
            (1 : ℝ) / (k * r * q) := by
  unfold shiftedDivisibleOddCofactors oddRawCofactors
  rw [Finset.sum_filter]
  rw [Finset.sum_image (cofactorProduct_injOn_oddCofactorTriples hN)]
  rw [oddCofactorTriples]
  change
    (∑ t ∈ oddSmallFactors N ×ˢ (middlePrimes N ×ˢ largePrimes N),
      if p ∣ shiftedTotient (cofactorProduct t) then
        (1 : ℝ) / cofactorProduct t else 0) = _
  rw [Finset.sum_product]
  simp_rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro r hr
  unfold shiftedDivisibleLargePrimes
  rw [Finset.sum_filter]
  simp [cofactorProduct, Nat.cast_mul]

/-- Pure finite summation lemma: divisible small factors are charged to
the unrestricted large-prime mass, while the remaining factors use a
uniform reciprocal bound for their shifted-divisible q-fibers. -/
theorem sum_inv_shiftedDivisibleOddCofactors_le_split
    {N p : ℕ} (hN : 2 ≤ N) {F : ℝ} (hF : 0 ≤ F)
    (hfiber : ∀ k ∈ oddSmallFactors N, ¬ p ∣ k →
      ∀ r ∈ middlePrimes N,
        ∑ q ∈ shiftedDivisibleLargePrimes N p k r,
          (1 : ℝ) / q ≤ F) :
    ∑ m ∈ shiftedDivisibleOddCofactors N p, (1 : ℝ) / m ≤
      (∑ k ∈ (oddSmallFactors N).filter (fun k => p ∣ k),
          (1 : ℝ) / k) *
        (∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
          (∑ q ∈ largePrimes N, (1 : ℝ) / q) +
      (∑ k ∈ (oddSmallFactors N).filter (fun k => ¬ p ∣ k),
          (1 : ℝ) / k) *
        (∑ r ∈ middlePrimes N, (1 : ℝ) / r) * F := by
  classical
  rw [sum_inv_shiftedDivisibleOddCofactors_eq_triple_sum hN]
  let T : ℕ → ℝ := fun k =>
    ∑ r ∈ middlePrimes N,
      ∑ q ∈ shiftedDivisibleLargePrimes N p k r,
        (1 : ℝ) / (k * r * q)
  have hdiv : ∀ k ∈ (oddSmallFactors N).filter (fun k => p ∣ k),
      T k ≤
        ((1 : ℝ) / k) *
          (∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
            (∑ q ∈ largePrimes N, (1 : ℝ) / q) := by
    intro k hk
    dsimp [T]
    calc
      (∑ r ∈ middlePrimes N,
          ∑ q ∈ shiftedDivisibleLargePrimes N p k r,
            (1 : ℝ) / (k * r * q)) ≤
          ∑ r ∈ middlePrimes N,
            ((1 : ℝ) / k * ((1 : ℝ) / r)) *
              ∑ q ∈ largePrimes N, (1 : ℝ) / q := by
        apply Finset.sum_le_sum
        intro r hr
        calc
          (∑ q ∈ shiftedDivisibleLargePrimes N p k r,
              (1 : ℝ) / (k * r * q)) ≤
              ∑ q ∈ largePrimes N,
                (1 : ℝ) / (k * r * q) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.filter_subset _ _)
            intro q hq hnot
            positivity
          _ = ((1 : ℝ) / k * ((1 : ℝ) / r)) *
              ∑ q ∈ largePrimes N, (1 : ℝ) / q := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro q hq
            push_cast
            ring
      _ = ((1 : ℝ) / k) *
          (∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
            (∑ q ∈ largePrimes N, (1 : ℝ) / q) := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hnondvd : ∀ k ∈ (oddSmallFactors N).filter (fun k => ¬ p ∣ k),
      T k ≤
        ((1 : ℝ) / k) *
          (∑ r ∈ middlePrimes N, (1 : ℝ) / r) * F := by
    intro k hk
    have hkdata := Finset.mem_filter.mp hk
    dsimp [T]
    calc
      (∑ r ∈ middlePrimes N,
          ∑ q ∈ shiftedDivisibleLargePrimes N p k r,
            (1 : ℝ) / (k * r * q)) ≤
          ∑ r ∈ middlePrimes N,
            ((1 : ℝ) / k * ((1 : ℝ) / r)) * F := by
        apply Finset.sum_le_sum
        intro r hr
        have hqr := hfiber k hkdata.1 hkdata.2 r hr
        calc
          (∑ q ∈ shiftedDivisibleLargePrimes N p k r,
              (1 : ℝ) / (k * r * q)) =
              ((1 : ℝ) / k * ((1 : ℝ) / r)) *
                ∑ q ∈ shiftedDivisibleLargePrimes N p k r,
                  (1 : ℝ) / q := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro q hq
            push_cast
            ring
          _ ≤ ((1 : ℝ) / k * ((1 : ℝ) / r)) * F := by
            exact mul_le_mul_of_nonneg_left hqr (by positivity)
      _ = ((1 : ℝ) / k) *
          (∑ r ∈ middlePrimes N, (1 : ℝ) / r) * F := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
  let s := oddSmallFactors N
  let P : ℕ → Prop := fun k => p ∣ k
  have hsplit :
      ∑ k ∈ s, T k =
        ∑ k ∈ s.filter P, T k +
          ∑ k ∈ s.filter (fun k => ¬ P k), T k := by
    symm
    exact Finset.sum_filter_add_sum_filter_not s P T
  calc
    (∑ k ∈ oddSmallFactors N,
        ∑ r ∈ middlePrimes N,
          ∑ q ∈ shiftedDivisibleLargePrimes N p k r,
            (1 : ℝ) / (k * r * q)) =
        ∑ k ∈ s, T k := by rfl
    _ = ∑ k ∈ s.filter P, T k +
          ∑ k ∈ s.filter (fun k => ¬ P k), T k := hsplit
    _ ≤
        ∑ k ∈ s.filter P,
            ((1 : ℝ) / k) *
              (∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
                (∑ q ∈ largePrimes N, (1 : ℝ) / q) +
          ∑ k ∈ s.filter (fun k => ¬ P k),
            ((1 : ℝ) / k) *
              (∑ r ∈ middlePrimes N, (1 : ℝ) / r) * F := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro k hk
        exact hdiv k hk
      · apply Finset.sum_le_sum
        intro k hk
        exact hnondvd k hk
    _ =
        (∑ k ∈ (oddSmallFactors N).filter (fun k => p ∣ k),
            (1 : ℝ) / k) *
          (∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
            (∑ q ∈ largePrimes N, (1 : ℝ) / q) +
        (∑ k ∈ (oddSmallFactors N).filter (fun k => ¬ p ∣ k),
            (1 : ℝ) / k) *
          (∑ r ∈ middlePrimes N, (1 : ℝ) / r) * F := by
      dsimp [s, P]
      rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul,
        Finset.sum_mul]

/-- A prime below the middle scale cannot divide a middle-layer prime. -/
theorem not_dvd_middlePrime_of_lt_pow_four
    {N p r : ℕ} (hp : p.Prime) (hpN : p < N ^ 4)
    (hr : r ∈ middlePrimes N) :
    ¬ p ∣ r := by
  intro hpr
  have hrPrime := (mem_middlePrimes_iff.mp hr).2.2
  have heq : p = r :=
    (Nat.prime_dvd_prime_iff_eq hp hrPrime).mp hpr
  have hrge := (mem_middlePrimes_iff.mp hr).1
  omega

/-- Concrete fixed-p incidence estimate.  The first term is the p-divisible
small-factor contribution; the second uses the residue-class sieve on every
remaining large-q fiber. -/
theorem exists_sum_inv_shiftedDivisibleOddCofactors_upper_bound :
    ∃ A C : ℝ, 1 ≤ A ∧ 0 < C ∧
      ∀ N p y S : ℕ,
        2 ≤ N → p.Prime → p < N ^ 4 → p ≤ N ^ 21 →
        2 ≤ y → y < N ^ 21 → 101 ≤ S →
        Real.log A ≤ 4 * (S - 100 : ℕ) / 99 →
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        let W :=
          (1 + eta) *
            (C * (Real.log (2 : ℝ) / Real.log (y : ℝ)) *
              Real.exp 3)
        let E := ((y ^ S : ℕ) : ℝ) ^ 2
        let F :=
          (2 * W / (p : ℝ) + E / ((N ^ 21 : ℕ) : ℝ)) *
            (harmonic N : ℝ)
        ∑ m ∈ shiftedDivisibleOddCofactors N p, (1 : ℝ) / m ≤
          ((harmonic (N / p) : ℝ) / (p : ℝ)) *
            (∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
              (∑ q ∈ largePrimes N, (1 : ℝ) / q) +
          (∑ k ∈ (oddSmallFactors N).filter (fun k => ¬ p ∣ k),
              (1 : ℝ) / k) *
            (∑ r ∈ middlePrimes N, (1 : ℝ) / r) * F := by
  obtain ⟨A, C, hA, hC, hfiber⟩ :=
    exists_sum_inv_shiftedDivisibleLargePrimes_upper_bound
  refine ⟨A, C, hA, hC, ?_⟩
  intro N p y S hN hp hpN hpN21 hy hyN hS hlog
  dsimp only
  let W : ℝ :=
    (1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
      (C * (Real.log (2 : ℝ) / Real.log (y : ℝ)) *
        Real.exp 3)
  let E : ℝ := ((y ^ S : ℕ) : ℝ) ^ 2
  let F : ℝ :=
    (2 * W / (p : ℝ) + E / ((N ^ 21 : ℕ) : ℝ)) *
      (harmonic N : ℝ)
  have hlog2 : 0 ≤ Real.log (2 : ℝ) :=
    Real.log_nonneg (by norm_num)
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hW : 0 ≤ W := by
    dsimp [W]
    positivity
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  have hH : 0 ≤ (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    exact Finset.sum_nonneg fun j hj => by positivity
  have hF : 0 ≤ F := by
    dsimp [F]
    positivity
  have hsplit := sum_inv_shiftedDivisibleOddCofactors_le_split
    hN hF (F := F) (fun k hk hpk r hr => by
      have hpr : ¬ p ∣ r :=
        not_dvd_middlePrime_of_lt_pow_four hp hpN hr
      have hbound := hfiber N p k r y S hN hp hpN21 hk hr hpk hpr
        hy hyN hS hlog
      simpa [W, E, F] using hbound)
  have hK :
      ∑ k ∈ (oddSmallFactors N).filter (fun k => p ∣ k),
          (1 : ℝ) / k ≤
        (harmonic (N / p) : ℝ) / (p : ℝ) :=
    sum_inv_oddSmallFactors_filter_dvd_le_harmonic_div hp.pos
  have hR :
      0 ≤ ∑ r ∈ middlePrimes N, (1 : ℝ) / r :=
    Finset.sum_nonneg fun r hr => by positivity
  have hQ :
      0 ≤ ∑ q ∈ largePrimes N, (1 : ℝ) / q :=
    Finset.sum_nonneg fun q hq => by positivity
  calc
    (∑ m ∈ shiftedDivisibleOddCofactors N p, (1 : ℝ) / m) ≤
        (∑ k ∈ (oddSmallFactors N).filter (fun k => p ∣ k),
            (1 : ℝ) / k) *
          (∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
            (∑ q ∈ largePrimes N, (1 : ℝ) / q) +
        (∑ k ∈ (oddSmallFactors N).filter (fun k => ¬ p ∣ k),
            (1 : ℝ) / k) *
          (∑ r ∈ middlePrimes N, (1 : ℝ) / r) * F := hsplit
    _ ≤
        ((harmonic (N / p) : ℝ) / (p : ℝ)) *
          (∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
            (∑ q ∈ largePrimes N, (1 : ℝ) / q) +
          (∑ k ∈ (oddSmallFactors N).filter (fun k => ¬ p ∣ k),
            (1 : ℝ) / k) *
          (∑ r ∈ middlePrimes N, (1 : ℝ) / r) * F := by
      gcongr

end Erdos822
