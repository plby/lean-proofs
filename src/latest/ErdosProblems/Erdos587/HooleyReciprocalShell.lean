import ErdosProblems.Erdos587.HooleyReciprocalEncoding
import ErdosProblems.Erdos587.HooleySymmetricProgression
import ErdosProblems.Erdos587.HooleySparseErrors

/-! # Long and short reciprocal approximation tolerance classes -/

open scoped BigOperators

namespace Erdos587

theorem exists_delta_reciprocal_tolerance_bound (r : ℕ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ c q b X : ℕ, 0 < c → 0 < q → 2 ≤ X →
      ∀ (a v : ℤ) (A : ℕ → ℤ) (R T : ℝ), 0 < R → 8 ≤ T → X ≤ ⌊T⌋₊ ^ r →
      ∀ S : Finset DeltaApproximant,
      (∀ x ∈ S, R < x.index) → (∀ x ∈ S, (x.index : ℝ) ≤ 2 * R) →
      (∀ x ∈ S, x.denominator = b) →
      (∀ x ∈ S, ((c * x.index : ℕ) : ℤ) ∣ (q : ℤ) * A x.index - a * v) →
      (∀ t : ℤ, |(t : ℝ)| ≤ T →
        (b : ℤ) * a * v - q * t ≠ 0 ∧ ((b : ℤ) * a * v - q * t).natAbs ≤ X) →
      (∀ x ∈ S, |(deltaReciprocalApproximantError c A x : ℝ)| ≤ T) →
      (S.card : ℝ) ≤ C * (Int.gcd ((b : ℤ) * a * v) q).divisors.card * T *
        (max 1 (Real.log (Real.log (X : ℝ)))) ^ 6 := by
  classical
  obtain ⟨C, hC, hmean⟩ := exists_delta_symmetric_error_mean r hr
  refine ⟨C, hC, ?_⟩
  intro c q b X hc hq hX a v A R T hR hT hsize S hlow hupp hden hrel hvalues herror
  let E := S.image (deltaReciprocalApproximantError c A)
  have hE (t : ℤ) (ht : t ∈ E) : |(t : ℝ)| ≤ T := by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
    exact herror x hx
  have hcount := delta_reciprocal_approximant_card_le_delta_sum hc A hR S E hlow hupp hden hrel
    (fun t ht => (hvalues t (hE t ht)).1) (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  have hcountR : (S.card : ℝ) ≤
      ∑ t ∈ E, (hooleyDelta ((b : ℤ) * a * v - q * t).natAbs : ℝ) := by exact_mod_cast hcount
  have hqZ : -(q : ℤ) ≠ 0 := neg_ne_zero.mpr (by exact_mod_cast hq.ne')
  have h := hmean ((b : ℤ) * a * v) (-(q : ℤ)) hqZ X hX T hT hsize
    (fun t ht => by simpa only [neg_mul, sub_eq_add_neg] using (hvalues t ht).2) E hE
  apply hcountR.trans
  simpa only [neg_mul, ← sub_eq_add_neg, Int.gcd_neg] using h

theorem exists_delta_reciprocal_small_tolerance_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ c q b X : ℕ, 0 < c →
      ∀ (a v : ℤ) (A : ℕ → ℤ) (R T : ℝ), 0 < R → 0 ≤ T →
      ∀ S : Finset DeltaApproximant,
      (∀ x ∈ S, R < x.index) → (∀ x ∈ S, (x.index : ℝ) ≤ 2 * R) →
      (∀ x ∈ S, x.denominator = b) →
      (∀ x ∈ S, ((c * x.index : ℕ) : ℤ) ∣ (q : ℤ) * A x.index - a * v) →
      (∀ t : ℤ, |(t : ℝ)| ≤ T →
        (b : ℤ) * a * v - q * t ≠ 0 ∧ ((b : ℤ) * a * v - q * t).natAbs ≤ X) →
      (∀ x ∈ S, |(deltaReciprocalApproximantError c A x : ℝ)| ≤ T) →
      (S.card : ℝ) ≤ C * (2 * T + 1) * (X : ℝ) ^ ε := by
  classical
  obtain ⟨C, hC, hmean⟩ := exists_delta_sparse_error_mean hε
  refine ⟨C, hC, ?_⟩
  intro c q b X hc a v A R T hR hT S hlow hupp hden hrel hvalues herror
  let E := S.image (deltaReciprocalApproximantError c A)
  have hE (t : ℤ) (ht : t ∈ E) : |(t : ℝ)| ≤ T := by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
    exact herror x hx
  have hcount := delta_reciprocal_approximant_card_le_delta_sum hc A hR S E hlow hupp hden hrel
    (fun t ht => (hvalues t (hE t ht)).1) (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  have hcountR : (S.card : ℝ) ≤
      ∑ t ∈ E, (hooleyDelta ((b : ℤ) * a * v - q * t).natAbs : ℝ) := by exact_mod_cast hcount
  have h := hmean ((b : ℤ) * a * v) (-(q : ℤ)) X T hT E hE
    (fun t ht => by simpa only [neg_mul, sub_eq_add_neg] using (hvalues t (hE t ht)).2)
  apply hcountR.trans
  simpa only [neg_mul, ← sub_eq_add_neg] using h

end Erdos587
