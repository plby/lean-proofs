/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
A global logarithmic determinant lower bound on the affine diagonal sextic.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.SurfaceCount
import ErdosProblems.Erdos477.Counting.ResidueExponent
import ErdosProblems.Erdos477.Counting.WeightedPrimeSums
import ErdosProblems.Erdos477.Counting.PrimeDivisors

namespace Erdos477.Counting

open scoped BigOperators

/-- The finitely many primes where the local sextic argument is unavailable. -/
def excludedPrimes (c : ℤ) : Finset ℕ := (6 * c.natAbs).primeFactors

lemma not_mem_excludedPrimes (c : ℤ) (hc : c ≠ 0) (p : ℕ) (hp : p.Prime) :
    p ∉ excludedPrimes c ↔ p.Coprime 6 ∧ ¬ (p : ℤ) ∣ c := by
  have hc' : 6 * c.natAbs ≠ 0 := mul_ne_zero (by decide) (Int.natAbs_ne_zero.mpr hc)
  simp only [excludedPrimes, Nat.mem_primeFactors, hp, true_and,
    hp.dvd_mul, hp.coprime_iff_not_dvd, Int.natCast_dvd]
  tauto

lemma exists_good_sextic_prime (c : ℤ) (hc : c ≠ 0) :
    ∃ p : ℕ, p.Prime ∧ p.Coprime 6 ∧ ¬ (p : ℤ) ∣ c := by
  obtain ⟨p, hlarge, hp⟩ := Nat.exists_infinite_primes (6 * c.natAbs + 1)
  have hpos : 0 < 6 * c.natAbs := Nat.mul_pos (by decide) (Int.natAbs_pos.mpr hc)
  have hnot : ¬ p ∣ 6 * c.natAbs := by
    intro h
    have hle := Nat.le_of_dvd hpos h
    omega
  have hgood : p ∉ excludedPrimes c := by
    intro h
    exact hnot (Nat.mem_primeFactors.mp h).2.1
  exact ⟨p, hp, (not_mem_excludedPrimes c hc p hp).mp hgood⟩

/-- The integral local exponent with its threshold chosen for the number of
residue classes modulo a given prime. -/
noncomputable def sexticPrimeExponent (p : ℕ) (c : ℤ) (s : ℕ) : ℕ :=
  residueExponent (residueCount p c) s (Nat.sqrt (2 * s / residueCount p c))

/-- The local prime-power divisors give a global lower bound for every
nonzero evaluation determinant. No height bound, auxiliary polynomial, or
integer-point count is assumed here. -/
theorem exists_global_det_lower (c : ℤ) (hc : c ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N s : ℕ), 1 ≤ N → 0 < s →
      ∀ (z : Fin s → Fin 3 → ℤ),
      (∀ j, z j 0 ^ 6 + z j 1 ^ 6 - z j 2 ^ 6 = c) →
      ∀ (F : Fin s → MvPolynomial (Fin 3) ℤ),
      (Matrix.det (Matrix.of fun i j => MvPolynomial.eval (z j) (F i)) ≠ 0) →
      (2 : ℝ) / 3 * s * Real.sqrt (2 * s) * (Real.log N - C) -
        3 * Real.log 4 * s * N ≤
      Real.log |((Matrix.det (Matrix.of fun i j => MvPolynomial.eval (z j) (F i)) : ℤ) : ℝ)| := by
  obtain ⟨C₀, hC₀, hCsum⟩ := exists_reciprocal_sqrt_prime_bound
  let E := excludedPrimes c
  let B : ℝ := ∑ p ∈ E, Real.log p / (p : ℝ)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun p _ =>
    div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
  refine ⟨C₀ + B, by positivity, ?_⟩
  intro N s hN hs z hz F hD
  let S := Nat.primesLE N \ E
  let q : ℕ → ℝ := fun p => residueCount p c
  let A : ℝ := (2 : ℝ) / 3 * s * Real.sqrt (2 * s)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hprime (p : ℕ) (hp : p ∈ S) : p.Prime :=
    (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2
  have hqpos (p : ℕ) (hp : p ∈ S) : 0 < residueCount p c := by
    let : Fact p.Prime := ⟨hprime p hp⟩
    exact residueCount_pos_of_point p c (z ⟨0, hs⟩) (hz ⟨0, hs⟩)
  have hq (p : ℕ) (hp : p ∈ S) :
      0 < q p ∧ q p ≤ (p : ℝ) ^ 2 + 343 * p * Real.sqrt p := by
    let : Fact p.Prime := ⟨hprime p hp⟩
    refine ⟨Nat.cast_pos.mpr (hqpos p hp), ?_⟩
    dsimp only [q]
    rw [residueCount_eq]
    exact sexticResidues_card_upper p c
  have hweight := hCsum N hN E q hq
  have hexp (p : ℕ) (hp : p ∈ S) :
      A * (Real.log p / Real.sqrt (q p)) - 3 * s * Real.log p ≤
        (sexticPrimeExponent p c s : ℝ) * Real.log p := by
    have h := residueExponent_lower_bound (residueCount p c) s (hqpos p hp)
    rw [Real.sqrt_div (by positivity)] at h
    have hmul := mul_le_mul_of_nonneg_right h (Real.log_natCast_nonneg p)
    dsimp only [A, q, sexticPrimeExponent]
    convert hmul using 1 <;> first | rfl | ring
  have hexpsum :
      A * (∑ p ∈ S, Real.log p / Real.sqrt (q p)) -
        3 * s * (∑ p ∈ S, Real.log p) ≤
      ∑ p ∈ S, (sexticPrimeExponent p c s : ℝ) * Real.log p := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum hexp
  have hlogs : (∑ p ∈ S, Real.log p) ≤ Real.log 4 * N := by
    calc
      _ ≤ ∑ p ∈ Nat.primesLE N, Real.log p :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
          (fun p _ _ => Real.log_natCast_nonneg p)
      _ = Chebyshev.theta N := (Chebyshev.theta_eq_sum_primesLE_log N).symm
      _ ≤ _ := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N)
  have hdiv (p : ℕ) (hp : p ∈ S) :
      (p : ℤ) ^ sexticPrimeExponent p c s ∣
        Matrix.det (Matrix.of fun i j => MvPolynomial.eval (z j) (F i)) := by
    let : Fact p.Prime := ⟨hprime p hp⟩
    have hgood := (not_mem_excludedPrimes c hc p (hprime p hp)).mp
      (Finset.mem_sdiff.mp hp).2
    have h := pow_dvd_sextic_eval_det_all p hgood.1 c hgood.2 z hz F
      (Nat.sqrt (2 * s / residueCount p c))
    rw [← residueCount_eq] at h
    exact h
  have hdet := sum_log_prime_powers_le S hprime (fun p => sexticPrimeExponent p c s)
    _ hD hdiv
  have hweight' : Real.log N - (C₀ + B) ≤
      ∑ p ∈ S, Real.log p / Real.sqrt (q p) := by
    dsimp only [B]
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hweight' hA
  have hlogscaled := mul_le_mul_of_nonneg_left hlogs (show (0 : ℝ) ≤ 3 * s by positivity)
  change A * (Real.log N - (C₀ + B)) - 3 * Real.log 4 * s * N ≤ _
  apply le_trans ?_ hdet
  nlinarith only [hscaled, hlogscaled, hexpsum]

#print axioms exists_global_det_lower
-- 'Erdos477.Counting.exists_global_det_lower' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
