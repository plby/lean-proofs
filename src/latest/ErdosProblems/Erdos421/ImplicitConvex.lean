import ErdosProblems.Erdos421.ProductRoots

/-!
# Increasing slopes on the positive solution branch
-/

namespace Erdos421

/-- A strictly convex function on the left and a concave increasing function
on the right force strictly increasing successive slopes of their equality curve. -/
theorem implicit_curve_slopes {F G : ℝ → ℝ} {D E : Set ℝ}
    (hF : StrictConvexOn ℝ D F) (hG : ConcaveOn ℝ E G) (hGmono : StrictMonoOn G E)
    {x₁ x₂ x₃ y₁ y₂ y₃ : ℝ}
    (hx₁ : x₁ ∈ D) (hx₃ : x₃ ∈ D) (hy₁ : y₁ ∈ E) (hy₂ : y₂ ∈ E) (hy₃ : y₃ ∈ E)
    (h₁₂ : x₁ < x₂) (h₂₃ : x₂ < x₃)
    (h₁ : F x₁ = G y₁) (h₂ : F x₂ = G y₂) (h₃ : F x₃ = G y₃) :
    (y₂ - y₁) / (x₂ - x₁) < (y₃ - y₂) / (x₃ - x₂) := by
  have hd : 0 < x₃ - x₁ := by linarith
  let a := (x₃ - x₂) / (x₃ - x₁)
  let b := (x₂ - x₁) / (x₃ - x₁)
  have ha : 0 < a := div_pos (sub_pos.mpr h₂₃) hd
  have hb : 0 < b := div_pos (sub_pos.mpr h₁₂) hd
  have hab : a + b = 1 := by dsimp [a, b]; field_simp; ring
  have hxlin : a * x₁ + b * x₃ = x₂ := by dsimp [a, b]; field_simp; ring
  have hconv := hF.2 hx₁ hx₃ (ne_of_lt (h₁₂.trans h₂₃)) ha hb hab
  simp only [smul_eq_mul, hxlin, h₁, h₂, h₃] at hconv
  have hconc := hG.2 hy₁ hy₃ ha.le hb.le hab
  simp only [smul_eq_mul] at hconc
  have hchordE : a * y₁ + b * y₃ ∈ E := by
    simpa only [smul_eq_mul] using hG.1 hy₁ hy₃ ha.le hb.le hab
  have hychord : y₂ < a * y₁ + b * y₃ := by
    by_contra h
    have hle := hGmono.monotoneOn hchordE hy₂ (not_lt.mp h)
    linarith
  have hmul := mul_lt_mul_of_pos_right hychord hd
  have hclear : (a * y₁ + b * y₃) * (x₃ - x₁) =
      (x₃ - x₂) * y₁ + (x₂ - x₁) * y₃ := by
    dsimp [a, b]
    field_simp
  rw [hclear] at hmul
  apply (div_lt_div_iff₀ (sub_pos.mpr h₁₂) (sub_pos.mpr h₂₃)).mpr
  nlinarith

/-- Specialized to the falling/rising product equation used for raw gaps. -/
theorem falling_rising_root_slopes {r s : ℕ} (hs : 0 < s) (hrs : s < r)
    {x₁ x₂ x₃ y₁ y₂ y₃ : ℝ}
    (hx₁ : 2 * (r : ℝ) ^ 2 ≤ x₁) (h₁₂ : x₁ < x₂) (h₂₃ : x₂ < x₃)
    (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) (hy₃ : 0 < y₃)
    (h₁ : productRoot s (fun i : Fin r ↦ (i : ℝ)) x₁ =
      productRoot s (fun i : Fin s ↦ -(i : ℝ)) y₁)
    (h₂ : productRoot s (fun i : Fin r ↦ (i : ℝ)) x₂ =
      productRoot s (fun i : Fin s ↦ -(i : ℝ)) y₂)
    (h₃ : productRoot s (fun i : Fin r ↦ (i : ℝ)) x₃ =
      productRoot s (fun i : Fin s ↦ -(i : ℝ)) y₃) :
    (y₂ - y₁) / (x₂ - x₁) < (y₃ - y₂) / (x₃ - x₂) := by
  have hshifts : ∀ i : Fin s, -(i : ℝ) ≤ 0 := by intro i; exact neg_nonpos.mpr (by positivity)
  exact implicit_curve_slopes (fallingProductRoot_strictConvexOn hs hrs)
    (productRoot_concaveOn _ 0 hshifts) (productRoot_strictMonoOn hs hs _ 0 hshifts)
    hx₁ (hx₁.trans (h₁₂.trans h₂₃).le) hy₁ hy₂ hy₃ h₁₂ h₂₃ h₁ h₂ h₃

end Erdos421
