import ErdosProblems.Erdos421.ShortIntegralCover

/-! # Summing short-interval estimates against a decaying window weight -/

namespace Erdos421

open MeasureTheory

theorem sum_inverse_succ_squares_le_two (N : ℕ) :
    (∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 1) ^ 2) ≤ 2 := by
  have hstrong : ∀ N : ℕ, (∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 1) ^ 2) ≤
      2 - 2 / ((N : ℝ) + 1) := by
    intro N
    induction N with
    | zero => norm_num
    | succ N ih =>
      have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have h₁ : (0 : ℝ) < N + 1 := by positivity
      have h₂ : (0 : ℝ) < N + 2 := by positivity
      have he : 2 / ((N : ℝ) + 1) - 2 / ((N : ℝ) + 2) =
          2 / (((N : ℝ) + 1) * ((N : ℝ) + 2)) := by field_simp; ring
      have hb : 1 / ((N : ℝ) + 1) ^ 2 ≤
          2 / ((N : ℝ) + 1) - 2 / ((N : ℝ) + 2) := by
        rw [he]
        apply (div_le_div_iff₀ (sq_pos_of_pos h₁) (mul_pos h₁ h₂)).mpr
        nlinarith
      rw [Finset.sum_range_succ]
      push_cast
      rw [show (N : ℝ) + 1 + 1 = N + 2 by ring]
      linarith
  have hnonneg : 0 ≤ 2 / ((N : ℝ) + 1) := by positivity
  linarith [hstrong N]

theorem min_window_cell_bound {A Y w t : ℝ} (hA : 0 ≤ A) (hY : 0 < Y)
    (hw : Y / 3 ≤ w) (n : ℕ) (ht : 0 < t) (hnt : A + n * w ≤ t) :
    (min 1 (Y / t)) ^ 2 ≤ 36 / ((n : ℝ) + 1) ^ 2 := by
  have hm0 : 0 ≤ min 1 (Y / t) := by positivity
  by_cases hn : n = 0
  · subst n
    norm_num only [Nat.cast_zero, zero_add, one_pow, div_one]
    have hm := min_le_left (1 : ℝ) (Y / t)
    nlinarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
  have hnp : (0 : ℝ) < n + 1 := by positivity
  have hprod := mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg n)
  have hq : Y / t ≤ 6 / ((n : ℝ) + 1) := by
    apply (div_le_div_iff₀ ht hnp).mpr
    nlinarith
  calc
    _ ≤ (6 / ((n : ℝ) + 1)) ^ 2 := pow_le_pow_left₀ hm0 ((min_le_right _ _).trans hq) 2
    _ = _ := by rw [div_pow]; norm_num

theorem integral_window_weight_le_of_short_integrals {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) {A B Y Q C : ℝ}
    (hA : 0 < A) (hAB : A ≤ B) (hY : 0 < Y) (hQ : 0 ≤ Q) (hC : 0 ≤ C)
    (hf0 : ∀ t ∈ Set.Icc A B, 0 ≤ f t)
    (hgweight : ∀ t ∈ Set.Icc A B, g t ≤ C * (min 1 (Y / t)) ^ 2)
    (hlocal : ∀ u v : ℝ, A ≤ u → u ≤ v → v ≤ B → v - u ≤ Y →
      (∫ t in u..v, f t) ≤ Q) :
    (∫ t in A..B, f t * g t) ≤ 72 * C * Q := by
  have hgC : ∀ t ∈ Set.Icc A B, g t ≤ C := by
    intro t ht
    have htp : 0 < t := hA.trans_le ht.1
    have hm : 0 ≤ min 1 (Y / t) := by positivity
    have hm1 := min_le_left (1 : ℝ) (Y / t)
    have hsq : (min 1 (Y / t)) ^ 2 ≤ 1 := by nlinarith
    exact (hgweight t ht).trans (by nlinarith)
  by_cases hshort : B - A ≤ Y
  · have hb := intervalIntegral.integral_mono_on (μ := volume) hAB
      ((hf.mul hg).intervalIntegrable A B) ((hf.mul_const C).intervalIntegrable A B)
      (fun t ht ↦ mul_le_mul_of_nonneg_left (hgC t ht) (hf0 t ht))
    rw [intervalIntegral.integral_mul_const] at hb
    simp only [Pi.mul_apply] at hb
    have hl := mul_le_mul_of_nonneg_right (hlocal A B le_rfl hAB le_rfl hshort) hC
    nlinarith [mul_nonneg hC hQ]
  have hlong : Y ≤ B - A := (lt_of_not_ge hshort).le
  let N : ℕ := ⌈(B - A) / Y⌉₊ + 1
  have hNp : (0 : ℝ) < N := by dsimp only [N]; positivity
  have hNlo : (B - A) / Y ≤ N := by
    have h := Nat.le_ceil ((B - A) / Y)
    dsimp only [N]
    push_cast
    linarith
  have hNhi : (N : ℝ) ≤ (B - A) / Y + 2 := by
    have h := (Nat.ceil_lt_add_one (div_nonneg (sub_nonneg.mpr hAB) hY.le)).le
    dsimp only [N]
    push_cast
    linarith
  let w : ℝ := (B - A) / N
  let p : ℕ → ℝ := fun n ↦ A + n * w
  have hw : 0 ≤ w := div_nonneg (sub_nonneg.mpr hAB) hNp.le
  have hwY : w ≤ Y := by
    apply (div_le_iff₀ hNp).mpr
    have h := (div_le_iff₀ hY).mp hNlo
    nlinarith
  have hwlo : Y / 3 ≤ w := by
    apply (le_div_iff₀ hNp).mpr
    have hb := mul_le_mul_of_nonneg_right hNhi hY.le
    rw [add_mul, div_mul_cancel₀ _ hY.ne'] at hb
    nlinarith
  have hNw : (N : ℝ) * w = B - A := by dsimp only [w]; field_simp
  have hp0 : p 0 = A := by simp only [p, Nat.cast_zero, zero_mul, add_zero]
  have hpN : p N = B := by dsimp only [p]; rw [hNw]; ring
  have hcell : ∀ n < N, (∫ t in p n..p (n + 1), f t * g t) ≤
      (36 * C * Q) * (1 / ((n : ℝ) + 1) ^ 2) := by
    intro n hn
    have hnN : (n : ℝ) + 1 ≤ N := by exact_mod_cast (show n + 1 ≤ N by omega)
    have hdelta : p (n + 1) - p n = w := by dsimp only [p]; push_cast; ring
    have hleft : A ≤ p n := by dsimp only [p]; linarith [mul_nonneg (Nat.cast_nonneg n) hw]
    have horder : p n ≤ p (n + 1) := by rw [← sub_nonneg, hdelta]; exact hw
    have hright : p (n + 1) ≤ B := by
      have hm := mul_le_mul_of_nonneg_right hnN hw
      dsimp only [p]
      push_cast
      linarith
    have hsub : Set.Icc (p n) (p (n + 1)) ⊆ Set.Icc A B :=
      fun _ ht ↦ ⟨hleft.trans ht.1, ht.2.trans hright⟩
    let c : ℝ := 36 * C / ((n : ℝ) + 1) ^ 2
    have hc : 0 ≤ c := by dsimp only [c]; positivity
    have hgcell : ∀ t ∈ Set.Icc (p n) (p (n + 1)), g t ≤ c := by
      intro t ht
      have hb := min_window_cell_bound hA.le hY hwlo n (hA.trans_le (hsub ht).1) ht.1
      have hm := mul_le_mul_of_nonneg_left hb hC
      apply (hgweight t (hsub ht)).trans
      convert hm using 1
      dsimp only [c]
      ring
    have hb := intervalIntegral.integral_mono_on (μ := volume) horder
      ((hf.mul hg).intervalIntegrable _ _) ((hf.mul_const c).intervalIntegrable _ _)
      (fun t ht ↦ mul_le_mul_of_nonneg_left (hgcell t ht) (hf0 t (hsub ht)))
    rw [intervalIntegral.integral_mul_const] at hb
    have hl := mul_le_mul_of_nonneg_right
      (hlocal (p n) (p (n + 1)) hleft horder hright (by rwa [hdelta])) hc
    calc
      _ ≤ Q * c := hb.trans hl
      _ = _ := by dsimp only [c]; ring
  have hpartition := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (a := p) (n := N) (fun n _ ↦ (hf.mul hg).intervalIntegrable (p n) (p (n + 1)))
  rw [hp0, hpN] at hpartition
  calc
    _ = ∑ n ∈ Finset.range N, ∫ t in p n..p (n + 1), f t * g t := hpartition.symm
    _ ≤ ∑ n ∈ Finset.range N, (36 * C * Q) * (1 / ((n : ℝ) + 1) ^ 2) :=
      Finset.sum_le_sum fun n hn ↦ hcell n (Finset.mem_range.mp hn)
    _ = (36 * C * Q) * ∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 1) ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ (36 * C * Q) * 2 :=
      mul_le_mul_of_nonneg_left (sum_inverse_succ_squares_le_two N) (by positivity)
    _ = _ := by ring

end Erdos421
