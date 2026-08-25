import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Tactic

/-!
# Elementary reductions for Linnik's theorem

The analytic estimate only needs to hold for sufficiently large moduli.
The finitely many smaller moduli can be absorbed into an absolute constant.
Dirichlet's theorem is used here only for those finitely many moduli; it
does not supply the uniform polynomial estimate.
-/

namespace Linnik

open Filter

/-- Existence without a quantitative bound, used for the finite initial
segment of moduli. -/
theorem exists_prime_dvd_sub_one (M : ℕ) (hM : 1 ≤ M) :
    ∃ p : ℕ, p.Prime ∧ M ∣ p - 1 := by
  obtain ⟨p, _, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq 1 (q := M) (a := 1)
      (by omega) (Nat.coprime_one_left M)
  exact ⟨p, hp, hmod.symm.dvd'⟩

/-- An eventual polynomial bound for primes in the class `1` extends to
every positive modulus, with the same exponent and one absolute constant. -/
theorem exists_uniform_prime_bound_of_eventually
    {L : ℕ}
    (h : ∀ᶠ M : ℕ in atTop,
      ∃ p : ℕ, p.Prime ∧ M ∣ p - 1 ∧ (p : ℝ) ≤ (M : ℝ) ^ L) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ M : ℕ, 1 ≤ M →
        ∃ p : ℕ, p.Prime ∧ M ∣ p - 1 ∧ (p : ℝ) ≤ C * (M : ℝ) ^ L := by
  classical
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  have hex (M : ℕ) : ∃ p : ℕ, p.Prime ∧ (1 ≤ M → M ∣ p - 1) := by
    by_cases hM : 1 ≤ M
    · obtain ⟨p, hp, hd⟩ := exists_prime_dvd_sub_one M hM
      exact ⟨p, hp, fun _ ↦ hd⟩
    · exact ⟨2, Nat.prime_two, fun hM' ↦ (hM hM').elim⟩
  choose p hp hd using hex
  let C : ℝ := (∑ M ∈ Finset.range N, (p M : ℝ)) + 1
  have hsum : 0 ≤ ∑ M ∈ Finset.range N, (p M : ℝ) := by positivity
  have hC : 1 ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro M hM
  have hMpow : 1 ≤ (M : ℝ) ^ L := one_le_pow₀ (by exact_mod_cast hM)
  by_cases hMN : N ≤ M
  · obtain ⟨q, hq, hqd, hqle⟩ := hN M hMN
    refine ⟨q, hq, hqd, hqle.trans ?_⟩
    exact le_mul_of_one_le_left (by positivity) hC
  · refine ⟨p M, hp M, hd M hM, ?_⟩
    have hpSum : (p M : ℝ) ≤ ∑ i ∈ Finset.range N, (p i : ℝ) :=
      Finset.single_le_sum (fun i _ ↦ Nat.cast_nonneg (p i))
        (Finset.mem_range.mpr (by omega))
    have hpC : (p M : ℝ) ≤ C := by dsimp [C]; linarith
    exact hpC.trans (le_mul_of_one_le_right (by linarith) hMpow)

end Linnik
