import ErdosProblems.Erdos421.UpperDivisorMobius
import Mathlib.NumberTheory.SelbergSieve

/-! # Explicit optimized weights for the Selberg upper sieve -/

namespace Erdos421

open scoped ArithmeticFunction.Moebius

noncomputable def selbergNormalizer (s : BoundingSieve) (D : ℕ) : ℝ :=
  ∑ d ∈ s.prodPrimes.divisors.filter (fun d ↦ d ≤ D), s.selbergTerms d

noncomputable def selbergTarget (s : BoundingSieve) (D d : ℕ) : ℝ :=
  if d ≤ D then (μ d : ℝ) * s.selbergTerms d / selbergNormalizer s D else 0

noncomputable def selbergOptimizedWeight (s : BoundingSieve) (D d : ℕ) : ℝ :=
  if d ∣ s.prodPrimes then
    (s.nu d)⁻¹ * upperMobiusTransform s.prodPrimes (selbergTarget s D) d else 0

theorem selbergNormalizer_pos (s : BoundingSieve) {D : ℕ} (hD : 1 ≤ D) :
    0 < selbergNormalizer s D := by
  unfold selbergNormalizer
  apply Finset.sum_pos'
  · intro d hd
    exact (BoundingSieve.selbergTerms_pos (s := s)
      (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1)).le
  · refine ⟨1, Finset.mem_filter.mpr ⟨?_, hD⟩, ?_⟩
    · exact Nat.mem_divisors.mpr ⟨one_dvd _, BoundingSieve.prodPrimes_ne_zero (s := s)⟩
    · exact BoundingSieve.selbergTerms_pos (s := s) (one_dvd _)

theorem selbergOptimizedWeight_row (s : BoundingSieve) (D : ℕ) {l : ℕ} (hl : l ∣ s.prodPrimes) :
    (∑ d ∈ s.prodPrimes.divisors,
      if l ∣ d then s.nu d * selbergOptimizedWeight s D d else 0) = selbergTarget s D l := by
  calc
    _ = ∑ d ∈ s.prodPrimes.divisors,
        if l ∣ d then upperMobiusTransform s.prodPrimes (selbergTarget s D) d else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      split_ifs
      · rw [selbergOptimizedWeight, if_pos (Nat.dvd_of_mem_divisors hd), ← mul_assoc,
          mul_inv_cancel₀ (BoundingSieve.nu_ne_zero (s := s) (Nat.dvd_of_mem_divisors hd)), one_mul]
      · rfl
    _ = _ := sum_upperMobiusTransform _ (BoundingSieve.prodPrimes_ne_zero (s := s)) hl

theorem selbergOptimizedWeight_one (s : BoundingSieve) {D : ℕ} (hD : 1 ≤ D) :
    selbergOptimizedWeight s D 1 = 1 := by
  have hG := selbergNormalizer_pos s hD
  rw [selbergOptimizedWeight, if_pos (one_dvd _), s.nu_mult.map_one, inv_one, one_mul,
    upperMobiusTransform_one _ (BoundingSieve.prodPrimes_ne_zero (s := s))]
  have he : (∑ d ∈ s.prodPrimes.divisors, (μ d : ℝ) * selbergTarget s D d) =
      selbergNormalizer s D / selbergNormalizer s D := by
    rw [selbergNormalizer, Finset.sum_div, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    have hsq : (μ d : ℝ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
        (BoundingSieve.squarefree_of_mem_divisors_prodPrimes (s := s) hd)
    rw [selbergTarget]
    split_ifs
    · calc
        _ = (μ d : ℝ) ^ 2 * s.selbergTerms d / selbergNormalizer s D := by ring
        _ = _ := by rw [hsq, one_mul]; rfl
    · simp
  rw [he, div_self hG.ne']

end Erdos421
