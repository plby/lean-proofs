import ErdosProblems.Erdos587.AlternativeLower

/-! The critical main term, with its root-plateau hypotheses explicit. -/

open MeasureTheory
open scoped BigOperators SchwartzMap

namespace Erdos587

lemma quarter_fiber_bounds {J y : ℕ} (hJ : 4 ≤ J)
    (hy : y ∈ Finset.Ico (J / 4) (J / 4 + J / 4)) :
    (J : ℝ) / 8 ≤ y ∧ (y : ℝ) ≤ (J : ℝ) / 2 := by
  have hlow := half_div_le_nat_div 4 J (by norm_num) hJ
  norm_num at hlow
  have hylo : ((J / 4 : ℕ) : ℝ) ≤ y := by exact_mod_cast (Finset.mem_Ico.mp hy).1
  have hyhi : (y : ℝ) ≤ ((J / 4 : ℕ) : ℝ) + ((J / 4 : ℕ) : ℝ) := by
    exact_mod_cast (Finset.mem_Ico.mp hy).2.le
  have hq : ((J / 4 : ℕ) : ℝ) * 4 ≤ J := by
    exact_mod_cast Nat.div_mul_le_self J 4
  exact ⟨hlow.trans hylo, by linarith⟩

theorem quarter_fiber_integral_lower (f g : 𝓢(ℝ, ℂ))
    {u v H J t y : ℕ} {L : ℝ} (hu : 0 < u) (hH : 0 < H) (hJ : 4 ≤ J)
    (hL : 0 < L) (hupper : (t : ℝ) + u * H + v * J ≤ L ^ 2)
    (hy : y ∈ Finset.Ico (J / 4) (J / 4 + J / 4))
    (hf : ∀ x : ℝ, (f x).im = 0)
    (hfpos : ∀ x : ℝ, 0 ≤ (f x).re) (hgpos : ∀ x : ℝ, 0 ≤ (g x).re)
    (hfplateau : ∀ z : ℝ, 0 ≤ z →
      (t : ℝ) + v * J / 8 + 5 * (u : ℝ) * H / 32 ≤ z ^ 2 →
      z ^ 2 ≤ t + (v : ℝ) * J / 2 + 7 * (u : ℝ) * H / 32 →
      1 ≤ (f (L⁻¹ * z)).re)
    (hgplateau : ∀ x ∈ Set.Icc (5 / 32 : ℝ) (7 / 32), 1 ≤ (g x).re) :
    (u : ℝ) * H / (32 * L) ≤
      ∫ z : ℝ, (f (L⁻¹ * z)).re * (g ((z ^ 2 - t - (v : ℝ) * y) / (u * H))).re := by
  obtain ⟨hylo, hyhi⟩ := quarter_fiber_bounds hJ hy
  have huH : 0 < (u : ℝ) * H := mul_pos (by exact_mod_cast hu) (by exact_mod_cast hH)
  have hv0 : (0 : ℝ) ≤ v := Nat.cast_nonneg _
  have hty : 0 ≤ (t : ℝ) + v * y := by positivity
  have hbound : (t : ℝ) + v * y + ((u : ℝ) * H) * (7 / 32) ≤ L ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hyhi hv0, Nat.cast_nonneg (α := ℝ) J]
  have hroot : ∀ z ∈ Set.Icc
      (Real.sqrt ((t : ℝ) + v * y + ((u : ℝ) * H) * (5 / 32)))
      (Real.sqrt ((t : ℝ) + v * y + ((u : ℝ) * H) * (7 / 32))),
      1 ≤ (f (L⁻¹ * z)).re := by
    intro z hz
    have hz0 := (Real.sqrt_nonneg _).trans hz.1
    have hsqlo := pow_le_pow_left₀ (Real.sqrt_nonneg _) hz.1 2
    have hsqhi := pow_le_pow_left₀ hz0 hz.2 2
    rw [Real.sq_sqrt (by positivity)] at hsqlo hsqhi
    apply hfplateau z hz0
    · nlinarith [mul_le_mul_of_nonneg_left hylo hv0]
    · nlinarith [mul_le_mul_of_nonneg_left hyhi hv0]
  have hh := quadratic_fiber_integral_lower f g hL huH hty
    (by norm_num : (0 : ℝ) ≤ 5 / 32) (by norm_num : (5 / 32 : ℝ) ≤ 7 / 32)
    hbound hf hfpos hgpos hroot hgplateau
  convert hh using 1
  · ring
  · congr 1
    funext z
    congr 2
    ring

theorem exists_critical_main_plateau_bound :
    ∃ A : ℝ, 0 < A ∧ ∃ C : ℝ, 0 < C ∧ ∃ O : ℕ, 0 < O ∧
      ∀ (f g : 𝓢(ℝ, ℂ)) (a u b v H J t : ℕ) (L : ℝ),
        0 < u → 0 < v → 0 < H → a * u = b * v + 1 → v.Coprime u →
        0 < L → (t : ℝ) + u * H + v * J ≤ L ^ 2 → A * Real.sqrt u ≤ J →
        (∀ x : ℝ, (f x).im = 0) →
        (∀ x : ℝ, 0 ≤ (f x).re) → (∀ x : ℝ, 0 ≤ (g x).re) →
        (∀ z : ℝ, 0 ≤ z →
          (t : ℝ) + v * J / 8 + 5 * (u : ℝ) * H / 32 ≤ z ^ 2 →
          z ^ 2 ≤ t + (v : ℝ) * J / 2 + 7 * (u : ℝ) * H / 32 →
          1 ≤ (f (L⁻¹ * z)).re) →
        (∀ x ∈ Set.Icc (5 / 32 : ℝ) (7 / 32), 1 ≤ (g x).re) →
        (H : ℝ) * J / (C * L * (1 + Real.log u) ^ O) ≤
          (alternativeSquareMain f g a u b v t L (((v : ℝ) / H)⁻¹)).re := by
  obtain ⟨A, hA, C, hC, O, hO, hden⟩ := exists_alternativeMain_density_bound
  refine ⟨8 * A + 8, by positivity, 256 * C, by positivity, O, hO, ?_⟩
  intro f g a u b v H J t L hu hv hH hab hvu hL hupper hJscale hf hfpos hgpos hfpl hgpl
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg _
  have hsqrt : 1 ≤ Real.sqrt (u : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hu)
  have hJ8 : (8 : ℝ) ≤ J := by
    have hA8 : 8 ≤ 8 * A + 8 := by linarith
    exact (hA8.trans (le_mul_of_one_le_right (by positivity) hsqrt)).trans hJscale
  have hJ4 : 4 ≤ J := by exact_mod_cast (show (4 : ℝ) ≤ J by linarith)
  have hM := half_div_le_nat_div 4 J (by norm_num) hJ4
  norm_num at hM
  have hscale : A * Real.sqrt (u : ℝ) ≤ ((J / 4 : ℕ) : ℝ) := by
    nlinarith [Real.sqrt_nonneg (u : ℝ)]
  have hI : 0 ≤ (u : ℝ) * H / (32 * L) := by positivity
  have hmain := hden f g a u b v H t (J / 4) (J / 4) L ((u : ℝ) * H / (32 * L))
    hu hv hH hab hvu hL hI hscale hf hfpos hgpos
    (fun y hy => quarter_fiber_integral_lower f g hu hH hJ4 hL hupper hy hf hfpos hgpos hfpl hgpl)
  have hlog : 0 < (1 + Real.log (u : ℝ)) ^ O := by
    apply pow_pos
    have := Real.log_nonneg (show (1 : ℝ) ≤ u by exact_mod_cast hu)
    linarith
  calc
    _ = ((u : ℝ) * H / (32 * L)) * ((J : ℝ) / 8) /
        (u * C * (1 + Real.log u) ^ O) := by field_simp; ring
    _ ≤ ((u : ℝ) * H / (32 * L)) * ((J / 4 : ℕ) : ℝ) /
        (u * C * (1 + Real.log u) ^ O) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hM hI) (by positivity)
    _ ≤ _ := hmain

end Erdos587
