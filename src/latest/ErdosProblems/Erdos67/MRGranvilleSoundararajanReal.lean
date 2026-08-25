import ErdosProblems.Erdos67.MRGranvilleSoundararajanVariation

/-!
# The real Granville--Soundararajan Euler discrepancy

For a real-valued coefficient in the closed unit disk, the first local
coefficient in the Granville--Soundararajan convolution is exactly the
zero-frequency pretentious deficit.  The remaining prime-power terms have
uniformly bounded total mass.  This is the deterministic comparison used in
the slow-variation side of the real Halasz dichotomy.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace Erdos67

noncomputable section

theorem norm_sub_one_eq_one_sub_re_of_real_of_norm_le_one
    {z : ℂ} (hreal : conj z = z) (hbound : ‖z‖ ≤ 1) :
    ‖z - 1‖ = 1 - z.re := by
  have him : z.im = 0 := by
    have h := congrArg Complex.im hreal
    simp only [Complex.conj_im] at h
    linarith
  have hre : z.re ≤ 1 :=
    (le_abs_self z.re).trans ((Complex.abs_re_le_norm z).trans hbound)
  have hz : z = (z.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa [him]
  rw [hz, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hre)]
  simp

theorem archimedeanTwist_zero_of_pos {n : ℕ} (hn : 0 < n) :
    archimedeanTwist 0 n = 1 := by
  rw [archimedeanTwist]
  simp [Nat.ne_of_gt hn]

theorem pretentiousTerm_archimedeanTwist_zero {f : ℕ → ℂ}
    {p : ℕ} (hp : 0 < p) :
    pretentiousTerm f (archimedeanTwist 0) p =
      (1 - (f p).re) / (p : ℝ) := by
  rw [pretentiousTerm, archimedeanTwist_zero_of_pos hp]
  simp

theorem gs_real_prime_discrepancy_eq_pretentiousTerm_zero
    {f : ℕ → ℂ} {p : ℕ} (hp : p.Prime)
    (hreal : conj (f p) = f p) (hbound : ‖f p‖ ≤ 1) :
    ‖f p - 1‖ / (p : ℝ) =
      pretentiousTerm f (archimedeanTwist 0) p := by
  rw [norm_sub_one_eq_one_sub_re_of_real_of_norm_le_one hreal hbound,
    pretentiousTerm_archimedeanTwist_zero hp.pos]

private theorem two_div_mul_sub_one_le_four_div_sq
    {p : ℕ} (hp : 2 ≤ p) :
    2 / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 4 / (p : ℝ) ^ 2 := by
  have hpR : (0 : ℝ) < p := by positivity
  have hp1R : (0 : ℝ) < (p : ℝ) - 1 := by
    have hpR' : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
    linarith
  have hpR2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  rw [div_le_div_iff₀ (mul_pos hpR hp1R) (sq_pos_of_pos hpR)]
  nlinarith

private theorem sum_Icc_inv_sq_le_two (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (((n : ℝ) ^ 2)⁻¹)) ≤ 2 := by
  have hset : Finset.Icc 1 N = Finset.Ioo 0 (N + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioo]
    omega
  rw [hset]
  simpa using (sum_Ioo_inv_sq_le (α := ℝ) 0 (N + 1))

theorem sum_primesBelow_two_div_mul_sub_one_le_eight (N : ℕ) :
    (∑ p ∈ (N + 1).primesBelow,
        2 / ((p : ℝ) * ((p : ℝ) - 1))) ≤ 8 := by
  calc
    (∑ p ∈ (N + 1).primesBelow,
        2 / ((p : ℝ) * ((p : ℝ) - 1))) ≤
        ∑ p ∈ (N + 1).primesBelow, 4 * (((p : ℝ) ^ 2)⁻¹) := by
      apply Finset.sum_le_sum
      intro p hp
      simpa [div_eq_mul_inv] using
        two_div_mul_sub_one_le_four_div_sq
          (Nat.Prime.two_le (Nat.prime_of_mem_primesBelow hp))
    _ ≤ ∑ p ∈ Finset.Icc 1 N, 4 * (((p : ℝ) ^ 2)⁻¹) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have hpPrime := Nat.prime_of_mem_primesBelow hp
        have hpLt : p < N + 1 := Nat.lt_of_mem_primesBelow hp
        exact Finset.mem_Icc.mpr ⟨hpPrime.one_le, by omega⟩
      · intro p _hp _hnot
        positivity
    _ = 4 * ∑ p ∈ Finset.Icc 1 N, (((p : ℝ) ^ 2)⁻¹) := by
      rw [Finset.mul_sum]
    _ ≤ 4 * 2 := mul_le_mul_of_nonneg_left (sum_Icc_inv_sq_le_two N) (by norm_num)
    _ = 8 := by norm_num

theorem primesBelow_succ_eq_primesUpTo (N : ℕ) :
    (N + 1).primesBelow = primesUpTo N := by
  ext p
  constructor
  · intro hp
    have hpPrime := Nat.prime_of_mem_primesBelow hp
    have hpLt := Nat.lt_of_mem_primesBelow hp
    rw [mem_primesUpTo]
    exact ⟨hpPrime, by omega⟩
  · intro hp
    rw [mem_primesUpTo] at hp
    exact Nat.mem_primesBelow.mpr ⟨by omega, hp.1⟩

/-- For real one-bounded coefficients, the GS Euler exponent is controlled by
the zero-frequency pretentious distance plus one absolute constant. -/
theorem gsEulerExponent_le_pretentiousDistSq_zero_add_eight
    {f : ℕ → ℂ}
    (hreal : ∀ n, 0 < n → conj (f n) = f n)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (N : ℕ) :
    gsEulerExponent f N ≤
      pretentiousDistSq f (archimedeanTwist 0) N + 8 := by
  unfold gsEulerExponent pretentiousDistSq
  rw [← primesBelow_succ_eq_primesUpTo N]
  calc
    (∑ p ∈ (N + 1).primesBelow,
        (‖f p - 1‖ / (p : ℝ) +
          2 / ((p : ℝ) * ((p : ℝ) - 1)))) =
        (∑ p ∈ (N + 1).primesBelow,
          pretentiousTerm f (archimedeanTwist 0) p) +
        ∑ p ∈ (N + 1).primesBelow,
          2 / ((p : ℝ) * ((p : ℝ) - 1)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      have hpPrime := Nat.prime_of_mem_primesBelow hp
      rw [gs_real_prime_discrepancy_eq_pretentiousTerm_zero
        hpPrime (hreal p hpPrime.pos) (hbound p hpPrime.pos)]
    _ ≤ (∑ p ∈ (N + 1).primesBelow,
          pretentiousTerm f (archimedeanTwist 0) p) + 8 := by
      gcongr
      exact sum_primesBelow_two_div_mul_sub_one_le_eight N

end

end Erdos67
