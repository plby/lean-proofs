import ErdosProblems.Erdos67b.MRPrimeSelbergMajorant

/-!
# Finite progression-to-Selberg-kernel transfer

The progression error is an explicit hypothesis of this finite algebraic
lemma. The oscillatory progression estimates are proved separately; they
are not presumed by the prime-weight construction.
-/

open scoped BigOperators

namespace Erdos67b

noncomputable section

theorem mrPrimeSelberg_quadratic_main_complex (D : ℕ) (hD : 1 ≤ D) (I : ℂ) :
    (∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
      ((mrPrimeSelbergCoefficient D hD d * mrPrimeSelbergCoefficient D hD e : ℝ) : ℂ) *
        (I / (Nat.lcm d e : ℂ))) = ((mrPrimeSelbergMass D hD)⁻¹ : ℝ) * I := by
  calc
    _ = ((∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
        mrPrimeSelbergCoefficient D hD d * mrPrimeSelbergCoefficient D hD e /
          (Nat.lcm d e : ℝ) : ℝ) : ℂ) * I := by
      simp only [Complex.ofReal_sum, Finset.sum_mul, Complex.ofReal_div, Complex.ofReal_natCast]
      apply Finset.sum_congr rfl
      intro d _hd
      apply Finset.sum_congr rfl
      intro e _he
      ring
    _ = _ := by rw [mrPrimeSelberg_quadratic_eq_mass_inv]

theorem mrPrimeSelberg_weighted_error_le (D : ℕ) (hD : 1 ≤ D)
    (S : Finset ℕ) (a : ℕ → ℂ) (I : ℂ) {E : ℝ} (hE : 0 ≤ E)
    (hprogression : ∀ q : ℕ, 0 < q → q ≤ D ^ 2 →
      ‖(∑ n ∈ S with q ∣ n, a n) - I / (q : ℂ)‖ ≤ E) :
    ‖(∑ n ∈ S, (mrPrimeSelbergMajorant D hD n : ℂ) * a n) -
      ((mrPrimeSelbergMass D hD)⁻¹ : ℝ) * I‖ ≤ (D : ℝ) ^ 2 * E := by
  classical
  have heq : (∑ n ∈ S, (mrPrimeSelbergMajorant D hD n : ℂ) * a n) -
      ((mrPrimeSelbergMass D hD)⁻¹ : ℝ) * I =
      ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
        ((mrPrimeSelbergCoefficient D hD d * mrPrimeSelbergCoefficient D hD e : ℝ) : ℂ) *
          ((∑ n ∈ S with Nat.lcm d e ∣ n, a n) - I / (Nat.lcm d e : ℂ)) := by
    rw [mrPrimeSelberg_weighted_sum_eq, ← mrPrimeSelberg_quadratic_main_complex]
    simp only [mul_sub, Finset.sum_sub_distrib]
  rw [heq]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 D, ‖∑ e ∈ Finset.Icc 1 D,
        ((mrPrimeSelbergCoefficient D hD d * mrPrimeSelbergCoefficient D hD e : ℝ) : ℂ) *
          ((∑ n ∈ S with Nat.lcm d e ∣ n, a n) - I / (Nat.lcm d e : ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
        ‖((mrPrimeSelbergCoefficient D hD d * mrPrimeSelbergCoefficient D hD e : ℝ) : ℂ) *
          ((∑ n ∈ S with Nat.lcm d e ∣ n, a n) - I / (Nat.lcm d e : ℂ))‖ :=
      Finset.sum_le_sum (fun d hd ↦ norm_sum_le _ _)
    _ ≤ ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
        |mrPrimeSelbergCoefficient D hD d * mrPrimeSelbergCoefficient D hD e| * E := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      have hdRange := Finset.mem_Icc.mp hd
      have heRange := Finset.mem_Icc.mp he
      have hqpos : 0 < Nat.lcm d e := Nat.lcm_pos hdRange.1 heRange.1
      have hqD : Nat.lcm d e ≤ D ^ 2 := by
        calc
          _ ≤ d * e := Nat.div_le_self _ _
          _ ≤ D ^ 2 := by nlinarith
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hprogression _ hqpos hqD) (abs_nonneg _)
    _ = (∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
        |mrPrimeSelbergCoefficient D hD d * mrPrimeSelbergCoefficient D hD e|) * E := by
      simp only [Finset.sum_mul]
    _ ≤ (D : ℝ) ^ 2 * E :=
      mul_le_mul_of_nonneg_right (mrPrimeSelberg_coefficient_abs_sum_le D hD) hE

theorem mrNorm_primeSelberg_weighted_sum_le (D : ℕ) (hD : 2 ≤ D)
    (S : Finset ℕ) (a : ℕ → ℂ) (I : ℂ) {E : ℝ} (hE : 0 ≤ E)
    (hprogression : ∀ q : ℕ, 0 < q → q ≤ D ^ 2 →
      ‖(∑ n ∈ S with q ∣ n, a n) - I / (q : ℂ)‖ ≤ E) :
    ‖∑ n ∈ S, (mrPrimeSelbergMajorant D (by omega) n : ℂ) * a n‖ ≤
      ‖I‖ / Real.log (D : ℝ) + (D : ℝ) ^ 2 * E := by
  let z : ℂ := ∑ n ∈ S, (mrPrimeSelbergMajorant D (by omega) n : ℂ) * a n
  let m : ℂ := ((mrPrimeSelbergMass D (by omega))⁻¹ : ℝ) * I
  have herr : ‖z - m‖ ≤ (D : ℝ) ^ 2 * E :=
    mrPrimeSelberg_weighted_error_le D (by omega) S a I hE hprogression
  have hm : ‖m‖ ≤ ‖I‖ / Real.log (D : ℝ) := by
    dsimp only [m]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (mrPrimeSelbergMass_pos D (by omega)).le)]
    calc
      _ ≤ (1 / Real.log (D : ℝ)) * ‖I‖ :=
        mul_le_mul_of_nonneg_right (mrPrimeSelbergMass_inv_le D hD) (norm_nonneg _)
      _ = _ := by ring
  change ‖z‖ ≤ _
  calc
    _ = ‖(z - m) + m‖ := by rw [sub_add_cancel]
    _ ≤ ‖z - m‖ + ‖m‖ := norm_add_le _ _
    _ ≤ (D : ℝ) ^ 2 * E + ‖I‖ / Real.log (D : ℝ) := add_le_add herr hm
    _ = _ := add_comm _ _

end

end Erdos67b
