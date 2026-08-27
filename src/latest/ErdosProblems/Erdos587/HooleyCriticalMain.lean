import ErdosProblems.Erdos587.CriticalMain
import ErdosProblems.Erdos587.HooleyAlternativeLower

/-! # The critical main term with one log-log loss -/

open MeasureTheory
open scoped BigOperators SchwartzMap

namespace Erdos587

theorem exists_delta_critical_main_plateau :
    ∃ A : ℝ, 0 < A ∧ ∃ C : ℝ, 0 < C ∧
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
        (H : ℝ) * J / (C * L * max 1 (Real.log (Real.log (u : ℝ)))) ≤
          (alternativeSquareMain f g a u b v t L (((v : ℝ) / H)⁻¹)).re := by
  obtain ⟨A, hA, C, hC, hden⟩ := exists_delta_alternativeMain_density
  refine ⟨8 * A + 8, by positivity, 256 * C, by positivity, ?_⟩
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
  have hlog : 0 < max 1 (Real.log (Real.log (u : ℝ))) := by positivity
  calc
    _ = ((u : ℝ) * H / (32 * L)) * ((J : ℝ) / 8) /
        (u * C * max 1 (Real.log (Real.log (u : ℝ)))) := by field_simp; ring
    _ ≤ ((u : ℝ) * H / (32 * L)) * ((J / 4 : ℕ) : ℝ) /
        (u * C * max 1 (Real.log (Real.log (u : ℝ)))) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hM hI) (by positivity)
    _ ≤ _ := hmain

end Erdos587
