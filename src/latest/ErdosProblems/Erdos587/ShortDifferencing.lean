import ErdosProblems.Erdos387.FiniteWeylInequality
import Mathlib.Algebra.Order.Chebyshev

/-!
# Short-shift differencing

Average a bounded number of translates before applying Cauchy--Schwarz.
The finite-group formulation makes the averaging identity exact; an
interval-supported sequence can subsequently be embedded in a large cycle.
-/

open scoped BigOperators ComplexConjugate

namespace Erdos587

lemma norm_finset_sum_sq_le_card_mul_sum_norm_sq {α : Type*} (s : Finset α) (f : α → ℂ) :
    ‖∑ x ∈ s, f x‖ ^ 2 ≤ (s.card : ℝ) * ∑ x ∈ s, ‖f x‖ ^ 2 := by
  calc
    _ ≤ (∑ x ∈ s, ‖f x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s f) 2
    _ ≤ _ := sq_sum_le_card_mul_sum_sq

lemma sum_finite_translate {G R : Type*} [AddCommGroup G] [Fintype G] [AddCommMonoid R]
    (f : G → R) (g : G) : (∑ x : G, f (x + g)) = ∑ x : G, f x := by
  exact Fintype.sum_equiv (Equiv.addRight g) _ _ (fun x => rfl)

lemma sum_finite_shift_average {G : Type*} [AddCommGroup G] [Fintype G]
    (f : G → ℂ) (g : G) (K : ℕ) :
    (∑ x : G, ∑ h ∈ Finset.range K, f (x + h • g)) = (K : ℂ) * ∑ x : G, f x := by
  rw [Finset.sum_comm]
  simp_rw [sum_finite_translate]
  simp

lemma finite_shift_cauchy {G : Type*} [AddCommGroup G] [Fintype G]
    (f : G → ℂ) (g : G) (K : ℕ) :
    (K : ℝ) ^ 2 * ‖∑ x : G, f x‖ ^ 2 ≤
      Fintype.card G * ∑ x : G, ‖∑ h ∈ Finset.range K, f (x + h • g)‖ ^ 2 := by
  have hh := norm_finset_sum_sq_le_card_mul_sum_norm_sq Finset.univ
    (fun x : G => ∑ h ∈ Finset.range K, f (x + h • g))
  rw [sum_finite_shift_average, norm_mul, Complex.norm_natCast, mul_pow] at hh
  simpa only [Finset.card_univ] using hh

noncomputable def finiteShiftCorrelation {G : Type*} [AddCommGroup G] [Fintype G]
    (f : G → ℂ) (g : G) (r : ℕ) : ℂ := ∑ x : G, f (x + r • g) * conj (f x)

lemma sum_shifted_correlation {G : Type*} [AddCommGroup G] [Fintype G]
    (f : G → ℂ) (g : G) (r h : ℕ) :
    (∑ x : G, f (x + (h + r + 1) • g) * conj (f (x + h • g))) =
      finiteShiftCorrelation f g (r + 1) := by
  have heq (x : G) : x + (h + r + 1) • g = (x + h • g) + (r + 1) • g := by
    simp only [add_nsmul]
    abel
  simp_rw [heq]
  exact sum_finite_translate (fun x : G => f (x + (r + 1) • g) * conj (f x)) (h • g)

lemma norm_sum_range_sq_eq_diagonal_add_correlations (z : ℕ → ℂ) (K : ℕ) :
    ‖∑ h ∈ Finset.range K, z h‖ ^ 2 = (∑ h ∈ Finset.range K, ‖z h‖ ^ 2) +
      2 * ∑ r ∈ Finset.range K, ∑ h ∈ Finset.range (K - r - 1),
        (z (h + r + 1) * conj (z h)).re := by
  have hh := congrArg Complex.re
    (Erdos387.FiniteWeyl.sum_mul_conj_sum_eq_diagonal_add_strictUpper z K)
  rw [Erdos387.FiniteWeyl.strictUpperCorrelation_eq_sum_positiveShift] at hh
  simp only [Complex.add_re, Complex.conj_re, Complex.re_sum,
    Erdos387.InverseWeyl.positiveShiftCorrelation, Complex.mul_conj', ← Complex.ofReal_pow,
    Complex.ofReal_re] at hh
  linarith

lemma sum_shifted_correlation_re {G : Type*} [AddCommGroup G] [Fintype G]
    (f : G → ℂ) (g : G) (r h : ℕ) :
    (∑ x : G, (f (x + (h + r + 1) • g) * conj (f (x + h • g))).re) =
      (finiteShiftCorrelation f g (r + 1)).re := by
  have hh := congrArg Complex.re (sum_shifted_correlation f g r h)
  simpa only [Complex.re_sum] using hh

lemma finite_shift_energy_identity {G : Type*} [AddCommGroup G] [Fintype G]
    (f : G → ℂ) (g : G) (K : ℕ) :
    (∑ x : G, ‖∑ h ∈ Finset.range K, f (x + h • g)‖ ^ 2) =
      (K : ℝ) * (∑ x : G, ‖f x‖ ^ 2) +
        2 * ∑ r ∈ Finset.range K, ((K - r - 1 : ℕ) : ℝ) *
          (finiteShiftCorrelation f g (r + 1)).re := by
  simp_rw [norm_sum_range_sq_eq_diagonal_add_correlations]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  · rw [Finset.sum_comm]
    simp_rw [sum_finite_translate (fun x : G => ‖f x‖ ^ 2)]
    simp
  · congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.sum_comm]
    simp_rw [sum_shifted_correlation_re]
    simp

theorem finite_short_shift_differencing {G : Type*} [AddCommGroup G] [Fintype G]
    (f : G → ℂ) (g : G) (K : ℕ) :
    (K : ℝ) ^ 2 * ‖∑ x : G, f x‖ ^ 2 ≤ Fintype.card G *
      ((K : ℝ) * (∑ x : G, ‖f x‖ ^ 2) +
        2 * K * ∑ r ∈ Finset.range K, ‖finiteShiftCorrelation f g (r + 1)‖) := by
  have hh := finite_shift_cauchy f g K
  rw [finite_shift_energy_identity] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply add_le_add le_rfl
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  have hkr : ((K - r - 1 : ℕ) : ℝ) ≤ K := by exact_mod_cast (show K - r - 1 ≤ K by omega)
  exact (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (Nat.cast_nonneg _)).trans
    (mul_le_mul_of_nonneg_right hkr (norm_nonneg _))

end Erdos587
