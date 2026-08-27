import Arxiv.Arxiv2411_18291.PredictableIndicatorVariance

/-! # Conditional variance bounds from bounded increments and their absolute means -/

open MeasureTheory ProbabilityTheory

noncomputable section

namespace Arxiv2411_18291

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable [IsProbabilityMeasure P] {X : Ω → ℝ} {b : ℝ}

theorem conditional_variance_le_mul_abs_mean (hm : m ≤ mΩ)
    (hX : StronglyMeasurable X) (hXb : ∀ᵐ ω ∂P, |X ω| ≤ b) :
    Var[X; P | m] ≤ᵐ[P] fun ω => b * P[fun ω => |X ω| | m] ω := by
  have hX2 : MemLp X 2 P := MemLp.of_bound hX.aestronglyMeasurable b hXb
  have hXi : Integrable X P := Integrable.of_bound hX.aestronglyMeasurable b hXb
  have hpoint : (fun ω => (X ω) ^ 2) ≤ᵐ[P] fun ω => b * |X ω| := by
    filter_upwards [hXb] with ω hω
    have h := mul_le_mul_of_nonneg_right hω (abs_nonneg (X ω))
    simpa only [← sq, sq_abs] using h
  have hmul := condExp_smul (μ := P) b (fun ω => |X ω|) m
  filter_upwards [condVar_ae_le_condExp_sq hm hX2,
    condExp_mono (m := m) hX2.integrable_sq (hXi.abs.const_mul b) hpoint, hmul]
    with ω hvar hle hmul
  change P[fun ω => b * |X ω| | m] ω = b * P[fun ω => |X ω| | m] ω at hmul
  rw [hmul] at hle
  exact hvar.trans hle

theorem conditional_variance_le_sq_bound (hm : m ≤ mΩ)
    (hX : StronglyMeasurable X) (hXb : ∀ᵐ ω ∂P, |X ω| ≤ b) :
    Var[X; P | m] ≤ᵐ[P] fun _ => b ^ 2 := by
  have hX2 : MemLp X 2 P := MemLp.of_bound hX.aestronglyMeasurable b hXb
  have hpoint : ∀ᵐ ω ∂P, (X ω) ^ 2 ≤ b ^ 2 := by
    filter_upwards [hXb] with ω hω
    exact sq_le_sq.mpr (hω.trans (le_abs_self b))
  exact (condVar_ae_le_condExp_sq hm hX2).trans
    (condExp_le_nonneg_const (sq_nonneg b) hpoint)

end Arxiv2411_18291
