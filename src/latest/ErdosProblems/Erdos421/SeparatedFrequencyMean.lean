import ErdosProblems.Erdos421.MeanSquare
import ErdosProblems.Erdos421.TimeRows

/-! # A continuous large-sieve bound with a logarithmic loss -/

namespace Erdos421

open Complex MeasureTheory
open scoped ComplexConjugate

theorem separated_frequency_reciprocal_row (S : Finset ℕ) (ω : ℕ → ℝ)
    {δ A B : ℝ} (hδ : 0 < δ)
    (hω : ∀ n ∈ S, A ≤ ω n ∧ ω n ≤ B)
    (hsep : ∀ m ∈ S, ∀ n ∈ S, m ≠ n → δ ≤ |ω m - ω n|)
    {m : ℕ} (hm : m ∈ S) :
    (∑ n ∈ S, 1 / |ω m - ω n|) ≤
      8 / δ * Real.log ((B - A) / δ + 2) := by
  let t : ℕ → ℝ := fun n ↦ ω n / δ
  have ht : ∀ n ∈ S, A / δ ≤ t n ∧ t n ≤ B / δ := by
    intro n hn
    exact ⟨div_le_div_of_nonneg_right (hω n hn).1 hδ.le,
      div_le_div_of_nonneg_right (hω n hn).2 hδ.le⟩
  have hd (i j : ℕ) : |t i - t j| = |ω i - ω j| / δ := by
    dsimp only [t]
    rw [← sub_div, abs_div, abs_of_pos hδ]
  have hts : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |t i - t j| := by
    intro i hi j hj hij
    rw [hd]
    exact (le_div_iff₀ hδ).mpr (by simpa using hsep i hi j hj hij)
  have hrow := separated_inverse_distance_row_le S t ht hts hm
  have hpoint : ∀ n ∈ S, 1 / |ω m - ω n| ≤ (2 / δ) * (1 / (1 + |t m - t n|)) := by
    intro n hn
    by_cases hmn : m = n
    · subst n
      simp only [sub_self, abs_zero, div_zero]
      positivity
    have hlow := hsep m hm n hn hmn
    have hp : 0 < |ω m - ω n| := hδ.trans_le hlow
    rw [hd]
    have hsum : 0 < δ + |ω m - ω n| := by positivity
    have he : (2 / δ) * (1 / (1 + |ω m - ω n| / δ)) =
        2 / (δ + |ω m - ω n|) := by field_simp
    rw [he]
    apply (div_le_div_iff₀ hp hsum).mpr
    linarith
  calc
    _ ≤ (2 / δ) * ∑ n ∈ S, 1 / (1 + |t m - t n|) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hpoint
    _ ≤ (2 / δ) * (4 * Real.log (B / δ - A / δ + 2)) :=
      mul_le_mul_of_nonneg_left hrow (by positivity)
    _ = _ := by rw [← sub_div]; ring

theorem separated_frequency_mean_square_error (S : Finset ℕ) (c : ℕ → ℂ)
    (ω : ℕ → ℝ) {δ A B : ℝ} (hδ : 0 < δ)
    (hω : ∀ n ∈ S, A ≤ ω n ∧ ω n ≤ B)
    (hsep : ∀ m ∈ S, ∀ n ∈ S, m ≠ n → δ ≤ |ω m - ω n|) (a b : ℝ) :
    ‖(∫ t in a..b, exponentialSum S c ω t * conj (exponentialSum S c ω t)) -
      ((b - a : ℝ) : ℂ) * (∑ n ∈ S, c n * conj (c n))‖ ≤
      (16 / δ * Real.log ((B - A) / δ + 2)) * ∑ n ∈ S, ‖c n‖ ^ 2 := by
  classical
  have hinj : Set.InjOn ω S := by
    intro m hm n hn heq
    by_contra hmn
    have h := hsep m hm n hn hmn
    rw [heq, sub_self, abs_zero] at h
    exact hδ.not_ge h
  apply (exponentialSum_mean_square_error S c ω hinj a b).trans
  let w : ℕ → ℕ → ℝ := fun m n ↦ 1 / |ω m - ω n|
  have hb := symmetric_weighted_sum_le S (fun n ↦ ‖c n‖) w
    (fun _ _ ↦ by dsimp only [w]; positivity)
    (fun m n ↦ by simp only [w, abs_sub_comm])
    (fun m hm ↦ separated_frequency_reciprocal_row S ω hδ hω hsep hm)
  have heq : (∑ m ∈ S, ∑ n ∈ S.erase m, 2 * ‖c m‖ * ‖c n‖ / |ω m - ω n|) =
      ∑ m ∈ S, ∑ n ∈ S, 2 * ‖c m‖ * ‖c n‖ * w m n := by
    apply Finset.sum_congr rfl
    intro m _
    rw [Finset.sum_erase]
    · apply Finset.sum_congr rfl
      intro n _
      dsimp only [w]
      ring
    · simp
  rw [heq]
  exact hb.trans_eq (by ring)

/-- The length of the integration interval plus the reciprocal frequency
spacing controls the mean square, with a logarithmic loss in the span. -/
theorem separated_frequency_mean_square_bound (S : Finset ℕ) (c : ℕ → ℂ)
    (ω : ℕ → ℝ) {δ A B : ℝ} (hδ : 0 < δ)
    (hω : ∀ n ∈ S, A ≤ ω n ∧ ω n ≤ B)
    (hsep : ∀ m ∈ S, ∀ n ∈ S, m ≠ n → δ ≤ |ω m - ω n|) (a b : ℝ) :
    (∫ t in a..b, ‖exponentialSum S c ω t‖ ^ 2) ≤
      (b - a + 16 / δ * Real.log ((B - A) / δ + 2)) * ∑ n ∈ S, ‖c n‖ ^ 2 := by
  have heq : (∫ t in a..b, exponentialSum S c ω t * conj (exponentialSum S c ω t)) =
      ((∫ t in a..b, ‖exponentialSum S c ω t‖ ^ 2 : ℝ) : ℂ) := by
    simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    exact intervalIntegral.integral_ofReal
  have hdiag : ((b - a : ℝ) : ℂ) * (∑ m ∈ S, c m * conj (c m)) =
      (((b - a) * (∑ m ∈ S, ‖c m‖ ^ 2) : ℝ) : ℂ) := by
    simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_mul,
      Complex.ofReal_sum]
  have h := separated_frequency_mean_square_error S c ω hδ hω hsep a b
  rw [heq, hdiag, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  have hle := (le_abs_self _).trans h
  nlinarith

end Erdos421
