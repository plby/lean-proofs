import ErdosProblems.Erdos421.ZetaPerronTails
import ErdosProblems.Erdos421.ZetaPerronRectangle

/-! # A fully numerical bound for the smoothed von Mangoldt sum -/

namespace Erdos421

open Complex MeasureTheory

theorem smoothedVonMangoldtSum_eq_perronIntegral {x σ : ℝ}
    (hx : 0 < x) (hσ : 1 < σ) (t : ℝ) :
    smoothedVonMangoldtSum x t = -(1 / (2 * Real.pi) : ℝ) •
      (∫ y : ℝ, zetaPerronIntegrand x t ((σ : ℂ) + y * I)) := by
  rw [smoothedVonMangoldtSum_eq_integral hx hσ t]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y ↦ by
    have he : (σ : ℂ) + (t + y : ℝ) * I = (σ : ℂ) + y * I + t * I := by
      push_cast
      ring
    simp only [zetaPerronIntegrand, he])

theorem smoothedVonMangoldtSum_norm_eq {x σ : ℝ}
    (hx : 0 < x) (hσ : 1 < σ) (t : ℝ) :
    ‖smoothedVonMangoldtSum x t‖ = (1 / (2 * Real.pi)) *
      ‖∫ y : ℝ, zetaPerronIntegrand x t ((σ : ℂ) + y * I)‖ := by
  rw [smoothedVonMangoldtSum_eq_perronIntegral hx hσ t, norm_smul, Real.norm_eq_abs,
    abs_neg, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]

/-- The contour and tail estimates have no unproved analytic inputs. All
remaining hypotheses here are numerical constraints on the contour parameters. -/
theorem exists_smoothedVonMangoldt_numeric_bound :
    ∃ B > 0, ∃ r > 0, ∃ T₀ > 1, ∀ x t a b H δ : ℝ,
      1 ≤ x → 1 / 2 ≤ a → a ≤ b → 1 < b → b < 1 + r → 0 < H →
      1 - δ ≤ a → b ≤ 1 + δ → T₀ + H ≤ |t| →
      δ ≤ logPowerZeroWidth (|t| + H) / 64 →
      let Z := (2 : ℝ) ^ 52 * (Real.log (|t| + H)) ^ 2
      ‖smoothedVonMangoldtSum x t‖ ≤ (1 / (2 * Real.pi)) *
        (4 * Real.pi * x ^ a * Z + 2 * (b - a) * (x ^ b * Z / H ^ 2) +
          2 * (x ^ b * (1 / (b - 1) + B)) / H) := by
  obtain ⟨B, hB, r, hr, htail⟩ := exists_zetaPerron_tail_bound
  obtain ⟨T₀, hT₀, hrect⟩ := exists_zetaPerron_rectangle_bound
  refine ⟨B, hB, r, hr, T₀, hT₀, ?_⟩
  intro x t a b H δ hx ha hab hb hbr hH haδ hbδ ht hδ
  have hxp : 0 < x := by linarith
  have hfinite := hrect x t a b H δ hx ha hab hH haδ hbδ ht hδ
  have herror := htail x b H t hxp hb hbr hH
  have hnorm := norm_le_norm_sub_add
    (∫ y : ℝ, zetaPerronIntegrand x t ((b : ℂ) + y * I))
    (∫ y : ℝ in -H..H, zetaPerronIntegrand x t ((b : ℂ) + y * I))
  rw [smoothedVonMangoldtSum_norm_eq hxp hb t]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith only [hfinite, herror, hnorm]

end Erdos421
