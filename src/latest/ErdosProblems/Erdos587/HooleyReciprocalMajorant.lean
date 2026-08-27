import ErdosProblems.Erdos587.HooleyReciprocalEncoding
import ErdosProblems.Erdos587.HooleyAffineShellCount

/-! # Summing the reciprocal major-arc kernel at a fixed approximant denominator -/

open scoped BigOperators

namespace Erdos587

noncomputable def deltaReciprocalFrequencyError (c : ℕ) (A : ℕ → ℤ)
    (x : DeltaApproximant) : ℝ :=
  (A x.index : ℝ) / (c * x.index : ℕ) - (x.numerator : ℝ) / x.denominator

noncomputable def deltaReciprocalMajorant (K : ℝ) (c : ℕ) (A : ℕ → ℤ)
    (x : DeltaApproximant) : ℝ :=
  K ^ 2 / ((x.denominator : ℝ) * (1 + K ^ 2 * |deltaReciprocalFrequencyError c A x|))

lemma delta_reciprocal_error_cast {c : ℕ} (hc : 0 < c) (A : ℕ → ℤ)
    {x : DeltaApproximant} (hx : 0 < x.index) (hb : 0 < x.denominator) :
    (deltaReciprocalApproximantError c A x : ℝ) =
      (c * x.index : ℕ) * (x.denominator : ℝ) * deltaReciprocalFrequencyError c A x := by
  have hcx : ((c * x.index : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.mul_pos hc hx).ne'
  have hbR : (x.denominator : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  dsimp only [deltaReciprocalApproximantError, deltaReciprocalFrequencyError]
  push_cast
  field_simp

lemma delta_reciprocal_error_tolerance {c : ℕ} (hc : 0 < c) (A : ℕ → ℤ)
    {x : DeltaApproximant} (hx : 0 < x.index) (hb : 0 < x.denominator)
    {δ : ℝ} (hδ : |deltaReciprocalFrequencyError c A x| ≤ δ) :
    |(deltaReciprocalApproximantError c A x : ℝ)| ≤
      (c * x.index : ℕ) * (x.denominator : ℝ) * δ := by
  rw [delta_reciprocal_error_cast hc A hx hb, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (c * x.index : ℕ) * (x.denominator : ℝ))]
  exact mul_le_mul_of_nonneg_left hδ (by positivity)

theorem delta_sum_reciprocal_majorant_of_error_count {c b : ℕ} (hc : 0 < c) (hb : 0 < b)
    (A : ℕ → ℤ) (S : Finset DeltaApproximant) {K R H G : ℝ}
    (hK : 0 < K) (hR : 0 < R) (hH : 0 ≤ H) (hG : 0 ≤ G) (J : ℕ)
    (hindex : ∀ x ∈ S, 0 < x.index)
    (hupp : ∀ x ∈ S, (x.index : ℝ) ≤ 2 * R)
    (hden : ∀ x ∈ S, x.denominator = b)
    (hscale : ∀ x ∈ S, K ^ 2 * |deltaReciprocalFrequencyError c A x| ≤ 2 ^ J)
    (hcount : ∀ j ≤ J,
      ((S.filter (fun x => |(deltaReciprocalApproximantError c A x : ℝ)| ≤
        (2 * c * R * b / K ^ 2) * 2 ^ j)).card : ℝ) ≤
          H * ((2 * c * R * b / K ^ 2) * 2 ^ j) + G) :
    (∑ x ∈ S, deltaReciprocalMajorant K c A x) ≤
      4 * H * c * R * (J + 1) + 4 * G * K ^ 2 / b := by
  classical
  let u := fun x => K ^ 2 * |deltaReciprocalFrequencyError c A x|
  let T₀ := 2 * (c : ℝ) * R * b / K ^ 2
  let P := H * T₀
  let D := K ^ 2 / (b : ℝ)
  have hP : 0 ≤ P := by dsimp only [P, T₀]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hlevels (j : ℕ) (hj : j ≤ J) :
      ((S.filter (fun x => u x ≤ 2 ^ j)).card : ℝ) ≤ P * 2 ^ j + G := by
    have hsub : S.filter (fun x => u x ≤ 2 ^ j) ⊆
        S.filter (fun x => |(deltaReciprocalApproximantError c A x : ℝ)| ≤ T₀ * 2 ^ j) := by
      intro x hx
      obtain ⟨hxS, hxlevel⟩ := Finset.mem_filter.mp hx
      refine Finset.mem_filter.mpr ⟨hxS, ?_⟩
      have hδ : |deltaReciprocalFrequencyError c A x| ≤ 2 ^ j / K ^ 2 := by
        apply (le_div_iff₀ (sq_pos_of_pos hK)).mpr
        simpa only [u, mul_comm] using hxlevel
      have hb' : 0 < x.denominator := by rw [hden x hxS]; exact hb
      have h := delta_reciprocal_error_tolerance hc A (hindex x hxS) hb' hδ
      rw [hden x hxS] at h
      calc
        _ ≤ ((c * x.index : ℕ) : ℝ) * b * (2 ^ j / K ^ 2) := h
        _ ≤ ((c : ℝ) * (2 * R)) * b * (2 ^ j / K ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg b)
          simpa only [Nat.cast_mul] using
            mul_le_mul_of_nonneg_left (hupp x hxS) (Nat.cast_nonneg c)
        _ = _ := by dsimp only [T₀]; ring
    calc
      _ ≤ ((S.filter (fun x =>
          |(deltaReciprocalApproximantError c A x : ℝ)| ≤ T₀ * 2 ^ j)).card : ℝ) :=
        by exact_mod_cast Finset.card_le_card hsub
      _ ≤ H * (T₀ * 2 ^ j) + G := hcount j hj
      _ = _ := by dsimp only [P]; ring
  have hpoint (x : DeltaApproximant) (hx : x ∈ S) :
      deltaReciprocalMajorant K c A x ≤ D / (1 + u x) := by
    apply le_of_eq
    dsimp only [deltaReciprocalMajorant, D, u]
    rw [hden x hx, div_mul_eq_div_div]
  have h := delta_sum_majorant_of_dyadic_affine_count S (deltaReciprocalMajorant K c A) u J
    hP hD hG (fun x hx => by dsimp only [deltaReciprocalMajorant]; positivity)
    (fun x hx => by dsimp only [u]; positivity) hscale hlevels hpoint
  apply h.trans_eq
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  dsimp only [P, T₀, D]
  field_simp
  ring

end Erdos587
