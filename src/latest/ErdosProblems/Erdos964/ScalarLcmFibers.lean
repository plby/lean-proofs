import ErdosProblems.Erdos964.ScalarCoefficientBounds

/-!
# Scalar lcm fibers in distribution errors

For a squarefree modulus `u`, every pair with lcm `u` lies in the square
of its divisor set. This gives the sufficient bound `4^ω(u)`, converting
the double coefficient sum into a divisor-weighted distribution error.
-/

namespace Erdos964

open scoped BigOperators ArithmeticFunction.omega
open BoundedGaps.Maynard

def scalarLcmFiber (D : Finset ℕ) (u : ℕ) : Finset (ℕ × ℕ) :=
  (D ×ˢ D).filter (fun z => Nat.lcm z.1 z.2 = u)

theorem scalarLcmFiber_card_le (D : Finset ℕ) (u : ℕ) (hu : Squarefree u) :
    (scalarLcmFiber D u).card ≤ 4 ^ ω u := by
  have hsub : scalarLcmFiber D u ⊆ u.divisors ×ˢ u.divisors := by
    intro z hz
    have heq := (Finset.mem_filter.mp hz).2
    apply Finset.mem_product.mpr
    constructor
    · exact Nat.mem_divisors.mpr ⟨heq ▸ Nat.dvd_lcm_left z.1 z.2, hu.ne_zero⟩
    · exact Nat.mem_divisors.mpr ⟨heq ▸ Nat.dvd_lcm_right z.1 z.2, hu.ne_zero⟩
  calc
    _ ≤ (u.divisors ×ˢ u.divisors).card := Finset.card_le_card hsub
    _ = (2 ^ ω u) ^ 2 := by rw [Finset.card_product, card_divisors_eq_two_pow_omega hu, pow_two]
    _ = (2 ^ 2) ^ ω u := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ = _ := rfl

theorem sum_scalar_lcm_eq_fibers (D T : Finset ℕ) (F : ℕ → ℝ)
    (hmap : ∀ d ∈ D, ∀ e ∈ D, Nat.lcm d e ∈ T) :
    (∑ d ∈ D, ∑ e ∈ D, F (Nat.lcm d e)) =
      ∑ u ∈ T, ((scalarLcmFiber D u).card : ℝ) * F u := by
  have hmap' : ∀ z ∈ D ×ˢ D, Nat.lcm z.1 z.2 ∈ T := by
    intro z hz
    exact hmap z.1 (Finset.mem_product.mp hz).1 z.2 (Finset.mem_product.mp hz).2
  have h := Finset.sum_fiberwise_of_maps_to' hmap' F
  rw [Finset.sum_product] at h
  simpa only [scalarLcmFiber, Finset.sum_const, nsmul_eq_mul] using h.symm

theorem sum_scalar_lcm_weight_le (D T : Finset ℕ) (k : ℕ) (E : ℕ → ℝ)
    (hmap : ∀ d ∈ D, ∀ e ∈ D, Nat.lcm d e ∈ T)
    (hsq : ∀ u ∈ T, Squarefree u) (hE : ∀ u ∈ T, 0 ≤ E u) :
    (∑ d ∈ D, ∑ e ∈ D, ((k ^ ω (Nat.lcm d e) : ℕ) : ℝ) * E (Nat.lcm d e)) ≤
      ∑ u ∈ T, (((4 * k) ^ ω u : ℕ) : ℝ) * E u := by
  rw [sum_scalar_lcm_eq_fibers D T (fun u => ((k ^ ω u : ℕ) : ℝ) * E u) hmap]
  apply Finset.sum_le_sum
  intro u hu
  have hcard : ((scalarLcmFiber D u).card : ℝ) ≤ ((4 ^ ω u : ℕ) : ℝ) := by
    exact_mod_cast scalarLcmFiber_card_le D u (hsq u hu)
  calc
    _ ≤ ((4 ^ ω u : ℕ) : ℝ) * (((k ^ ω u : ℕ) : ℝ) * E u) :=
      mul_le_mul_of_nonneg_right hcard (mul_nonneg (Nat.cast_nonneg _) (hE u hu))
    _ = _ := by rw [← mul_assoc, ← Nat.cast_mul, ← mul_pow]

theorem sum_scalar_lcm_coefficients_le (D T : Finset ℕ) (k : ℕ) (E w : ℕ → ℝ)
    (hmap : ∀ d ∈ D, ∀ e ∈ D, Nat.lcm d e ∈ T)
    (hsq : ∀ u ∈ T, Squarefree u) (hE : ∀ u ∈ T, 0 ≤ E u)
    (L : ℝ) (hL : 0 ≤ L) (hw : ∀ d ∈ D, |w d| ≤ L) :
    (∑ d ∈ D, ∑ e ∈ D,
      ((k ^ ω (Nat.lcm d e) : ℕ) : ℝ) * |w d * w e| * E (Nat.lcm d e)) ≤
      L ^ 2 * ∑ u ∈ T, (((4 * k) ^ ω u : ℕ) : ℝ) * E u := by
  calc
    _ ≤ ∑ d ∈ D, ∑ e ∈ D,
        L ^ 2 * (((k ^ ω (Nat.lcm d e) : ℕ) : ℝ) * E (Nat.lcm d e)) := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      have hwprod : |w d * w e| ≤ L ^ 2 := by
        rw [abs_mul, pow_two]
        exact mul_le_mul (hw d hd) (hw e he) (abs_nonneg _) hL
      have h := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hwprod (Nat.cast_nonneg (k ^ ω (Nat.lcm d e))))
        (hE _ (hmap d hd e he))
      convert h using 1
      ring
    _ = L ^ 2 * ∑ d ∈ D, ∑ e ∈ D,
        ((k ^ ω (Nat.lcm d e) : ℕ) : ℝ) * E (Nat.lcm d e) := by
      simp_rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_scalar_lcm_weight_le D T k E hmap hsq hE)
      (sq_nonneg L)

end Erdos964
