/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.PrimeSquareSieve
import ErdosProblems.Erdos822.PrimeSquareIncidence

/-! # The sieved reciprocal mass of one repeated prime factor -/

namespace Erdos822

open scoped BigOperators Classical
open Filter

theorem exists_fixed_depth_squareDivisibleCofactors_bound :
    ∃ S : ℕ, ∃ D : ℝ, 101 ≤ S ∧ 0 < D ∧
      ∀ N p y : ℕ, 2 ≤ N → p.Prime → p ^ 2 ≤ N ^ 21 → 2 ≤ y → y < N ^ 21 →
        (∑ m ∈ squareDivisibleCoprimeOddCofactors N p, (1 : ℝ) / m) ≤
          (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k) *
            (∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
              ((2 * (D / Real.log (y : ℝ)) / (p : ℝ) ^ 2 +
                ((y ^ S : ℕ) : ℝ) ^ 2 / (N : ℝ) ^ 21) * (harmonic N : ℝ)) := by
  obtain ⟨S, D, hS, hD, hbound⟩ := exists_fixed_depth_largePrimeSquareResidue_bound
  refine ⟨S, D, hS, hD, ?_⟩
  intro N p y hN hp hpN hy hyN
  have hH : 0 ≤ (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    exact Finset.sum_nonneg fun n hn ↦ by positivity
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  apply sum_inv_squareDivisibleCoprimeOddCofactors_le_of_fiber_bound hN (by positivity)
  intro k hk r hr hpk hpr
  by_cases hne : (shiftedSquareDivisibleLargePrimes N p k r).Nonempty
  · have hsub := shiftedSquareDivisibleLargePrimes_subset_largePrimeResidueClass
      hN hp hk hr hpk hpr hyN hne
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q hq hnot ↦ by positivity)).trans
      (hbound N p _ y hN hp hpN hy)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.sum_empty]
    positivity

theorem exists_eventually_squareDivisibleCofactors_sharp_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ N : ℕ in atTop, ∀ p : ℕ,
      p.Prime → p ^ 2 ≤ N ^ 21 →
      (∑ m ∈ squareDivisibleCoprimeOddCofactors N p, (1 : ℝ) / m) ≤
        (harmonic N : ℝ) * (B / (p : ℝ) ^ 2 + 1 / (N : ℝ) ^ 19) := by
  obtain ⟨S, D, hS, hD, hbound⟩ := exists_fixed_depth_squareDivisibleCofactors_bound
  have hSpos : 0 < S := by omega
  let B : ℝ := 2 * D * (1 / Real.log 2 + 8 * S)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  filter_upwards [eventually_nthRoot_ge (4 * S) 2 (by omega),
    eventually_reciprocalPrimeIntervalSum_four_five_upper_one, eventually_ge_atTop 2]
    with N hU hR hN
  let U := Nat.nthRoot (4 * S) N
  have hUN : U ≤ N := nthRoot_le_self_of_pos (by omega)
  have hNlt : N < N ^ 21 := by
    simpa only [pow_one] using Nat.pow_lt_pow_right (by omega : 1 < N) (show 1 < 21 by norm_num)
  have hUN21 : U < N ^ 21 := hUN.trans_lt hNlt
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hH : 0 ≤ (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    exact Finset.sum_nonneg fun n hn ↦ by positivity
  have hR' : (∑ r ∈ middlePrimes N, (1 : ℝ) / r) ≤ 1 := by
    simpa [reciprocalPrimeIntervalSum, middlePrimes_eq_primesLE_sdiff] using hR
  have hlogU : 0 < Real.log (U : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < U by omega))
  have hmain : 2 * (D / Real.log (U : ℝ)) * (harmonic N : ℝ) ≤ B := by
    have h := mul_le_mul_of_nonneg_left (harmonic_div_log_slowSieveCutoff_le hSpos hU)
      (show (0 : ℝ) ≤ 2 * D by positivity)
    calc
      _ = (2 * D) * ((harmonic N : ℝ) / Real.log (U : ℝ)) := by ring
      _ ≤ B := h
  have hE : (((U ^ S : ℕ) : ℝ) ^ 2) ≤ (N : ℝ) := by
    exact_mod_cast slowSieveCutoff_error_sq_le N S hSpos
  have herror : (((U ^ S : ℕ) : ℝ) ^ 2) / (N : ℝ) ^ 21 * (harmonic N : ℝ) ≤
      1 / (N : ℝ) ^ 19 := by
    calc
      _ = ((((U ^ S : ℕ) : ℝ) ^ 2) * (harmonic N : ℝ)) / (N : ℝ) ^ 21 := by ring
      _ ≤ ((N : ℝ) * N) / (N : ℝ) ^ 21 := by
        gcongr
        exact harmonic_le_natCast N
      _ = 1 / (N : ℝ) ^ 19 := by
        rw [show 21 = 2 + 19 by norm_num, pow_add]
        field_simp
        <;> ring
  intro p hp hpN
  have hF : (2 * (D / Real.log (U : ℝ)) / (p : ℝ) ^ 2 +
      ((U ^ S : ℕ) : ℝ) ^ 2 / (N : ℝ) ^ 21) * (harmonic N : ℝ) ≤
        B / (p : ℝ) ^ 2 + 1 / (N : ℝ) ^ 19 := by
    calc
      _ = (2 * (D / Real.log (U : ℝ)) * (harmonic N : ℝ)) / (p : ℝ) ^ 2 +
          ((U ^ S : ℕ) : ℝ) ^ 2 / (N : ℝ) ^ 21 * (harmonic N : ℝ) := by ring
      _ ≤ _ := add_le_add (div_le_div_of_nonneg_right hmain (by positivity)) herror
  calc
    _ ≤ (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k) *
        (∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
          ((2 * (D / Real.log (U : ℝ)) / (p : ℝ) ^ 2 +
            ((U ^ S : ℕ) : ℝ) ^ 2 / (N : ℝ) ^ 21) * (harmonic N : ℝ)) :=
      hbound N p U hN hp hpN hU hUN21
    _ ≤ (harmonic N : ℝ) * 1 * (B / (p : ℝ) ^ 2 + 1 / (N : ℝ) ^ 19) := by
      gcongr
      exact sum_inv_oddSmallFactors_le_harmonic N
    _ = _ := by ring

#print axioms exists_eventually_squareDivisibleCofactors_sharp_bound

end Erdos822
