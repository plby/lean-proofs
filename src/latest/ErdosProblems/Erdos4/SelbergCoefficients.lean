import ErdosProblems.Erdos4.SieveMajorant
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Concrete one-dimensional Selberg coefficients

The coefficients are normalized at one and have an elementary pointwise
bound. The remaining optimization identity is not assumed here.
-/

open scoped BigOperators

namespace Erdos4.SelbergCoefficients

noncomputable def mu (n : ℕ) : ℝ := (ArithmeticFunction.moebius n : ℤ)

theorem abs_mu_le_one (n : ℕ) : |mu n| ≤ 1 := by
  unfold mu
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))

theorem abs_mu_eq_sq (n : ℕ) : |mu n| = mu n ^ 2 := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> norm_num [mu, h]

noncomputable def harmonicMass (D : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 D, mu r ^ 2 / (Nat.totient r : ℝ)

theorem harmonicMass_pos {D : ℕ} (hD : 1 ≤ D) : 0 < harmonicMass D := by
  have hterm : ∀ r ∈ Finset.Icc 1 D, 0 ≤ mu r ^ 2 / (Nat.totient r : ℝ) :=
    fun r _hr => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  have hone : (1 : ℕ) ∈ Finset.Icc 1 D := Finset.mem_Icc.mpr ⟨le_rfl, hD⟩
  have hle := Finset.single_le_sum hterm hone
  have hval : mu 1 ^ 2 / (Nat.totient 1 : ℝ) = 1 := by norm_num [mu]
  rw [hval] at hle
  exact lt_of_lt_of_le zero_lt_one hle

noncomputable def coefficient (D d : ℕ) : ℝ :=
  ((d : ℝ) / harmonicMass D) * ∑ r ∈ Finset.Icc 1 D,
    if d ∣ r then mu (r / d) * mu r / (Nat.totient r : ℝ) else 0

theorem coefficient_one {D : ℕ} (hD : 1 ≤ D) : coefficient D 1 = 1 := by
  have hH := harmonicMass_pos hD
  unfold coefficient
  simp only [Nat.cast_one, one_dvd, ↓reduceIte, Nat.div_one, ← pow_two]
  change (1 / harmonicMass D) * harmonicMass D = 1
  exact div_mul_cancel₀ 1 hH.ne'

theorem abs_mobius_product_le (d r : ℕ) : |mu (r / d) * mu r| ≤ mu r ^ 2 := by
  rw [abs_mul]
  calc
    |mu (r / d)| * |mu r| ≤ 1 * |mu r| :=
      mul_le_mul_of_nonneg_right (abs_mu_le_one _) (abs_nonneg _)
    _ = mu r ^ 2 := by rw [one_mul, abs_mu_eq_sq]

theorem abs_coefficient_le {D : ℕ} (hD : 1 ≤ D) (d : ℕ) : |coefficient D d| ≤ d := by
  have hH := harmonicMass_pos hD
  have hterm : ∀ r ∈ Finset.Icc 1 D,
      |if d ∣ r then mu (r / d) * mu r / (Nat.totient r : ℝ) else 0| ≤
        mu r ^ 2 / (Nat.totient r : ℝ) := by
    intro r _hr
    by_cases hd : d ∣ r
    · rw [if_pos hd, abs_div]
      have hphi : |(Nat.totient r : ℝ)| = (Nat.totient r : ℝ) :=
        abs_of_nonneg (Nat.cast_nonneg _)
      rw [hphi]
      exact div_le_div_of_nonneg_right (abs_mobius_product_le d r) (Nat.cast_nonneg _)
    · rw [if_neg hd, abs_zero]
      exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  have hsum : |∑ r ∈ Finset.Icc 1 D,
      if d ∣ r then mu (r / d) * mu r / (Nat.totient r : ℝ) else 0| ≤ harmonicMass D := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
  unfold coefficient
  rw [abs_mul, abs_of_nonneg (div_nonneg (Nat.cast_nonneg d) hH.le)]
  calc
    ((d : ℝ) / harmonicMass D) *
        |∑ r ∈ Finset.Icc 1 D,
          if d ∣ r then mu (r / d) * mu r / (Nat.totient r : ℝ) else 0| ≤
        ((d : ℝ) / harmonicMass D) * harmonicMass D :=
      mul_le_mul_of_nonneg_left hsum (div_nonneg (Nat.cast_nonneg _) hH.le)
    _ = d := div_mul_cancel₀ _ hH.ne'

theorem sum_abs_coefficient_le {D : ℕ} (hD : 1 ≤ D) :
    (∑ d ∈ Finset.Icc 1 D, |coefficient D d|) ≤ (D : ℝ) ^ 2 := by
  calc
    (∑ d ∈ Finset.Icc 1 D, |coefficient D d|) ≤ ∑ _d ∈ Finset.Icc 1 D, (D : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact (abs_coefficient_le hD d).trans (by exact_mod_cast (Finset.mem_Icc.mp hd).2)
    _ = (D : ℝ) ^ 2 := by simp [pow_two]

theorem weight_prime {D p : ℕ} (hD : 1 ≤ D) (hp : p.Prime) (hDp : D < p) :
    SieveMajorant.weight D (coefficient D) p = 1 :=
  SieveMajorant.weight_prime hD hp hDp _ (coefficient_one hD)

end Erdos4.SelbergCoefficients
