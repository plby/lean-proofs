import ErdosProblems.Erdos4.PrimeExposure

/-! Numerical constant choices for the prime-exposure specialization. -/

namespace Erdos4.ExposureConstants

theorem exists_decay {c η : ℝ} (hc : 0 < c) (hη : 0 < η) (k : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 4 * (k : ℝ) ^ 2 * δ ^ 2 ≤ η * c := by
  let δ := min 1 (η * c / (4 * (k : ℝ) ^ 2 + 1))
  have hd : 0 < 4 * (k : ℝ) ^ 2 + 1 := by positivity
  have hδ : 0 < δ := lt_min zero_lt_one (div_pos (mul_pos hη hc) hd)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hh : δ * (4 * (k : ℝ) ^ 2 + 1) ≤ η * c :=
    (le_div_iff₀ hd).mp (min_le_right _ _)
  have hsq : δ ^ 2 ≤ δ := by nlinarith
  refine ⟨δ, hδ, hδ1, ?_⟩
  have hmul := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 4 * (k : ℝ) ^ 2)
  nlinarith

theorem exceptional_bound {c η L X Y S B : ℝ}
    (hc : 0 < c) (hL : 0 < L) (hX : 0 < X) (hY : 0 ≤ Y)
    (hB : 0 ≤ B) (hsmall : B ≤ η * c) (hS : c * X / L ≤ S) :
    B * X * Y / (L ^ 2 * S) ≤ η * Y / L := by
  have hlow : 0 < c * X / L := div_pos (mul_pos hc hX) hL
  calc
    _ ≤ B * X * Y / (L ^ 2 * (c * X / L)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hS (sq_nonneg L))
    _ = (B / c) * Y / L := by field_simp
    _ ≤ η * Y / L := by
      apply div_le_div_of_nonneg_right _ hL.le
      exact mul_le_mul_of_nonneg_right ((div_le_iff₀ hc).mpr hsmall) hY

theorem exposure_bound {c C M A L X Y S ρ V : ℝ}
    (hc : 0 < c) (hC : 0 < C) (hL : 0 < L) (hX : 0 < X)
    (hY : 0 < Y) (hρ : 0 < ρ) (hV : 0 < V) (hA : 0 ≤ A)
    (hS : c * X / L ≤ S) (hdensity : V * ρ * (5 * L) ≤ C)
    (hM : M ≤ 5 * A * c / (2 * C)) :
    M * X / Y ≤ A * S / (2 * ρ * Y * V) := by
  have hden : 2 * ρ * Y * V ≤ 2 * C * Y / (5 * L) := by
    apply (le_div_iff₀ (by positivity : 0 < 5 * L)).mpr
    have hh := mul_le_mul_of_nonneg_right hdensity (by positivity : 0 ≤ 2 * Y)
    nlinarith only [hh]
  calc
    _ ≤ (5 * A * c / (2 * C)) * X / Y :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hM hX.le) hY.le
    _ = (A * (c * X / L)) / (2 * C * Y / (5 * L)) := by field_simp
    _ ≤ A * (c * X / L) / (2 * ρ * Y * V) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hS hA) (by positivity)

end Erdos4.ExposureConstants
