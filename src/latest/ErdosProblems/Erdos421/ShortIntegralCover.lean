import ErdosProblems.Erdos421.IntegralFromSamples

/-! # Covering a long integral by uniformly controlled short integrals -/

namespace Erdos421

open MeasureTheory

theorem integral_le_of_short_integrals {f : ℝ → ℝ} (hf : Continuous f)
    {A B Y Q : ℝ} (hAB : A ≤ B) (hY : 0 < Y) (hQ : 0 ≤ Q)
    (hlocal : ∀ u v : ℝ, A ≤ u → u ≤ v → v ≤ B → v - u ≤ Y →
      (∫ x in u..v, f x) ≤ Q) :
    (∫ x in A..B, f x) ≤ ((B - A) / Y + 2) * Q := by
  let N : ℕ := ⌈(B - A) / Y⌉₊ + 1
  have hN : 0 < N := by dsimp only [N]; omega
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hT : 0 ≤ B - A := sub_nonneg.mpr hAB
  have hNlo : (B - A) / Y ≤ N := by
    have h := Nat.le_ceil ((B - A) / Y)
    dsimp only [N]
    push_cast
    linarith
  have hNhi : (N : ℝ) ≤ (B - A) / Y + 2 := by
    have h := (Nat.ceil_lt_add_one (div_nonneg hT hY.le)).le
    dsimp only [N]
    push_cast
    linarith
  let w : ℝ := (B - A) / N
  let p : ℕ → ℝ := fun n ↦ A + n * w
  have hw : 0 ≤ w := div_nonneg hT hNp.le
  have hwY : w ≤ Y := by
    apply (div_le_iff₀ hNp).mpr
    have h := (div_le_iff₀ hY).mp hNlo
    nlinarith
  have hNw : (N : ℝ) * w = B - A := by dsimp only [w]; field_simp
  have hp0 : p 0 = A := by simp only [p, Nat.cast_zero, zero_mul, add_zero]
  have hpN : p N = B := by dsimp only [p]; rw [hNw]; ring
  have hcell : ∀ n < N, (∫ x in p n..p (n + 1), f x) ≤ Q := by
    intro n hn
    have hnN : (n : ℝ) + 1 ≤ N := by exact_mod_cast (show n + 1 ≤ N by omega)
    have hmul := mul_le_mul_of_nonneg_right hnN hw
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hdelta : p (n + 1) - p n = w := by dsimp only [p]; push_cast; ring
    apply hlocal (p n) (p (n + 1))
    · dsimp only [p]
      linarith [mul_nonneg hn0 hw]
    · rw [← sub_nonneg, hdelta]
      exact hw
    · dsimp only [p]
      push_cast
      linarith
    · rwa [hdelta]
  have hpartition := intervalIntegral.sum_integral_adjacent_intervals
    (μ := volume) (a := p) (n := N)
    (fun n _ ↦ hf.intervalIntegrable (p n) (p (n + 1)))
  rw [hp0, hpN] at hpartition
  calc
    _ = ∑ n ∈ Finset.range N, ∫ x in p n..p (n + 1), f x := hpartition.symm
    _ ≤ ∑ _n ∈ Finset.range N, Q := Finset.sum_le_sum fun n hn ↦ hcell n (Finset.mem_range.mp hn)
    _ = (N : ℝ) * Q := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hNhi hQ

theorem min_reciprocal_cover_bound {T Y : ℝ} (hT : 0 < T) (hY : 0 < Y) :
    (min (1 / Y) (1 / T)) ^ 2 * (T / Y + 2) ≤ 3 / Y ^ 2 := by
  rcases le_total T Y with hTY | hYT
  · rw [min_eq_left (one_div_le_one_div_of_le hT hTY)]
    have hfrac : T / Y ≤ 1 := (div_le_one hY).mpr hTY
    calc
      _ ≤ (1 / Y) ^ 2 * 3 := mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
      _ = _ := by ring
  · rw [min_eq_right (one_div_le_one_div_of_le hY hYT)]
    apply (le_div_iff₀ (sq_pos_of_pos hY)).mpr
    have he : ((1 / T) ^ 2 * (T / Y + 2)) * Y ^ 2 = (T * Y + 2 * Y ^ 2) / T ^ 2 := by
      field_simp
    rw [he]
    apply (div_le_iff₀ (sq_pos_of_pos hT)).mpr
    nlinarith

theorem weighted_integral_le_of_short_integrals {f : ℝ → ℝ} (hf : Continuous f)
    {A B Y Q : ℝ} (hAB : A ≤ B) (hY : 0 < Y) (hQ : 0 ≤ Q)
    (hlocal : ∀ u v : ℝ, A ≤ u → u ≤ v → v ≤ B → v - u ≤ Y →
      (∫ x in u..v, f x) ≤ Q) :
    (min (1 / Y) (1 / (B - A))) ^ 2 * (∫ x in A..B, f x) ≤ 3 * Q / Y ^ 2 := by
  rcases hAB.eq_or_lt with heq | hlt
  · subst B
    simp only [intervalIntegral.integral_same, mul_zero]
    positivity
  have hb := integral_le_of_short_integrals hf hAB hY hQ hlocal
  have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg (min (1 / Y) (1 / (B - A))))
  have hc := mul_le_mul_of_nonneg_right (min_reciprocal_cover_bound (sub_pos.mpr hlt) hY) hQ
  calc
    _ ≤ (min (1 / Y) (1 / (B - A))) ^ 2 * (((B - A) / Y + 2) * Q) := hm
    _ = ((min (1 / Y) (1 / (B - A))) ^ 2 * ((B - A) / Y + 2)) * Q := by ring
    _ ≤ (3 / Y ^ 2) * Q := hc
    _ = _ := by ring

end Erdos421
