/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The global determinant lower bound with an additional prime-power congruence.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.OptimizedDeterminant
import ErdosProblems.Erdos477.Counting.LocalExponent

namespace Erdos477.Counting

open scoped BigOperators

/-- The contribution from a prescribed prime-power class is added to the
global contributions from all other primes, without counting any prime twice. -/
theorem exists_global_det_lower_congruence (c : ℤ) (hc : c ≠ 0)
    (p : ℕ) [Fact p.Prime] (h6 : p.Coprime 6) (hpc : ¬ (p : ℤ) ∣ c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N s r : ℕ), 1 ≤ N → 0 < s →
      ∀ (center : Fin 3 → ℤ),
      center 0 ^ 6 + center 1 ^ 6 - center 2 ^ 6 = c →
      ∀ (z : Fin s → Fin 3 → ℤ),
      (∀ j k, (p : ℤ) ^ r ∣ z j k - center k) →
      (∀ j, z j 0 ^ 6 + z j 1 ^ 6 - z j 2 ^ 6 = c) →
      ∀ (F : Fin s → MvPolynomial (Fin 3) ℤ),
      (Matrix.det (Matrix.of fun i j => MvPolynomial.eval (z j) (F i)) ≠ 0) →
      (2 : ℝ) / 3 * s * Real.sqrt (2 * s) * (Real.log N + r * Real.log p - C) -
        3 * s * (Real.log 4 * N + r * Real.log p) ≤
      Real.log |((Matrix.det (Matrix.of fun i j => MvPolynomial.eval (z j) (F i)) : ℤ) : ℝ)| := by
  obtain ⟨C₀, hC₀, hCsum⟩ := exists_reciprocal_sqrt_prime_bound
  let E := insert p (excludedPrimes c)
  let B : ℝ := ∑ q ∈ E, Real.log q / (q : ℝ)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun q _ =>
    div_nonneg (Real.log_natCast_nonneg q) (Nat.cast_nonneg q))
  refine ⟨C₀ + B, by positivity, ?_⟩
  intro N s r hN hs center hcenter z hres hz F hD
  let S := Nat.primesLE N \ E
  let q : ℕ → ℝ := fun l => residueCount l c
  let A : ℝ := (2 : ℝ) / 3 * s * Real.sqrt (2 * s)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hprime (l : ℕ) (hl : l ∈ S) : l.Prime :=
    (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hl).1).2
  have hpS : p ∉ S := by simp [S, E]
  have hqpos (l : ℕ) (hl : l ∈ S) : 0 < residueCount l c := by
    let : Fact l.Prime := ⟨hprime l hl⟩
    exact residueCount_pos_of_point l c (z ⟨0, hs⟩) (hz ⟨0, hs⟩)
  have hq (l : ℕ) (hl : l ∈ S) :
      0 < q l ∧ q l ≤ (l : ℝ) ^ 2 + 343 * l * Real.sqrt l := by
    let : Fact l.Prime := ⟨hprime l hl⟩
    refine ⟨Nat.cast_pos.mpr (hqpos l hl), ?_⟩
    dsimp only [q]
    rw [residueCount_eq]
    exact sexticResidues_card_upper l c
  have hweight := hCsum N hN E q hq
  have hexp (l : ℕ) (hl : l ∈ S) :
      A * (Real.log l / Real.sqrt (q l)) - 3 * s * Real.log l ≤
        (sexticPrimeExponent l c s : ℝ) * Real.log l := by
    have h := residueExponent_lower_bound (residueCount l c) s (hqpos l hl)
    rw [Real.sqrt_div (by positivity)] at h
    have hmul := mul_le_mul_of_nonneg_right h (Real.log_natCast_nonneg l)
    dsimp only [A, q, sexticPrimeExponent]
    convert hmul using 1 <;> first | rfl | ring
  have hexpsum :
      A * (∑ l ∈ S, Real.log l / Real.sqrt (q l)) -
        3 * s * (∑ l ∈ S, Real.log l) ≤
      ∑ l ∈ S, (sexticPrimeExponent l c s : ℝ) * Real.log l := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum hexp
  have hlogs : (∑ l ∈ S, Real.log l) ≤ Real.log 4 * N := by
    calc
      _ ≤ ∑ l ∈ Nat.primesLE N, Real.log l :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
          (fun l _ _ => Real.log_natCast_nonneg l)
      _ = Chebyshev.theta N := (Chebyshev.theta_eq_sum_primesLE_log N).symm
      _ ≤ _ := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N)
  have hdiv (l : ℕ) (hl : l ∈ S) :
      (l : ℤ) ^ sexticPrimeExponent l c s ∣
        Matrix.det (Matrix.of fun i j => MvPolynomial.eval (z j) (F i)) := by
    let : Fact l.Prime := ⟨hprime l hl⟩
    have hnot : l ∉ excludedPrimes c := fun h =>
      (Finset.mem_sdiff.mp hl).2 (Finset.mem_insert_of_mem h)
    have hgood := (not_mem_excludedPrimes c hc l (hprime l hl)).mp hnot
    have h := pow_dvd_sextic_eval_det_all l hgood.1 c hgood.2 z hz F
      (Nat.sqrt (2 * s / residueCount l c))
    rw [← residueCount_eq] at h
    exact h
  have hpr := prime_pow_dvd_sextic_eval_det p r h6 c hpc center hcenter z hres hz F
    (Nat.sqrt (2 * s))
  have hdet := log_prime_power_add_sum_le p Fact.out
    (r * localExponent s (Nat.sqrt (2 * s))) S hpS hprime
    (fun l => sexticPrimeExponent l c s) _ hD hpr hdiv
  have hlocal := mul_le_mul_of_nonneg_right (localExponent_lower_bound s)
    (show 0 ≤ (r : ℝ) * Real.log p by positivity)
  have hweight' : Real.log N - (C₀ + B) ≤
      ∑ l ∈ S, Real.log l / Real.sqrt (q l) := by
    dsimp only [B]
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hweight' hA
  have hlogscaled := mul_le_mul_of_nonneg_left hlogs (show (0 : ℝ) ≤ 3 * s by positivity)
  push_cast only [Nat.cast_mul] at hdet
  change A * (Real.log N + r * Real.log p - (C₀ + B)) -
    3 * s * (Real.log 4 * N + r * Real.log p) ≤ _
  apply le_trans ?_ hdet
  change (A - 3 * s) * ((r : ℝ) * Real.log p) ≤ _ at hlocal
  nlinarith only [hscaled, hlogscaled, hexpsum, hlocal]

#print axioms exists_global_det_lower_congruence
-- 'Erdos477.Counting.exists_global_det_lower_congruence' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
