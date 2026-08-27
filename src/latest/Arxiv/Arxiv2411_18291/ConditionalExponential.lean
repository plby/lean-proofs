import Arxiv.Arxiv2411_18291.ExponentialBound
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-! # One-step exponential compensation by conditional means -/

open MeasureTheory ProbabilityTheory

noncomputable section

namespace Arxiv2411_18291

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable [IsProbabilityMeasure P]
variable {X W : Ω → ℝ} {C t g K : ℝ}

theorem integrable_exp_mul_of_bound (hX : StronglyMeasurable X)
    (hXC : ∀ᵐ ω ∂P, 0 ≤ X ω ∧ X ω ≤ C) (ht : 0 ≤ t) :
    Integrable (fun ω => Real.exp (t * X ω)) P := by
  apply Integrable.of_bound
    ((Real.continuous_exp.comp_stronglyMeasurable (hX.const_mul t)).aestronglyMeasurable)
    (Real.exp (t * C))
  filter_upwards [hXC] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω.2 ht)

/-- Conditional exponential bound for a bounded nonnegative variable. -/
theorem condExp_exp_mul_le (hm : m ≤ mΩ) (hX : StronglyMeasurable X)
    (hXC : ∀ᵐ ω ∂P, 0 ≤ X ω ∧ X ω ≤ C)
    (ht : 0 ≤ t) (htC : t * C < 2) :
    P[fun ω => Real.exp (t * X ω) | m] ≤ᵐ[P]
      fun ω => 1 + (2 * t / (2 - t * C)) * P[X | m] ω := by
  have hXi : Integrable X P := by
    apply Integrable.of_bound hX.aestronglyMeasurable C
    filter_upwards [hXC] with ω hω
    simpa only [Real.norm_eq_abs, abs_of_nonneg hω.1] using hω.2
  let g := 2 * t / (2 - t * C)
  have hexp := integrable_exp_mul_of_bound hX hXC ht
  have hlin : Integrable (fun ω => 1 + g * X ω) P :=
    (integrable_const 1).add (hXi.const_mul g)
  have hle : (fun ω => Real.exp (t * X ω)) ≤ᵐ[P] (fun ω => 1 + g * X ω) := by
    filter_upwards [hXC] with ω hω
    exact exp_mul_le_linear hω.1 hω.2 ht htC
  have hadd := condExp_add (μ := P) (integrable_const (1 : ℝ)) (hXi.const_mul g) m
  have hmul := condExp_smul (μ := P) g X m
  filter_upwards [condExp_mono (m := m) hexp hlin hle, hadd, hmul] with ω hω ha hb
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, condExp_const hm] at ha hb
  change P[fun ω => 1 + g * X ω | m] ω =
    1 + P[fun ω => g * X ω | m] ω at ha
  change P[fun ω => g * X ω | m] ω = g * P[X | m] ω at hb
  rw [ha, hb] at hω
  exact hω

/-- A bounded nonnegative weight measurable before the increment can be
multiplied by the compensated exponential without increasing its expectation. -/
theorem integral_compensated_step (hm : m ≤ mΩ)
    (hW : StronglyMeasurable[m] W) (hW0 : 0 ≤ᵐ[P] W)
    (hWK : ∀ᵐ ω ∂P, ‖W ω‖ ≤ K) (hX : StronglyMeasurable X)
    (hXC : ∀ᵐ ω ∂P, 0 ≤ X ω ∧ X ω ≤ C)
    (ht : 0 ≤ t) (htC : t * C < 2) :
    (∫ ω, W ω * Real.exp (t * X ω - (2 * t / (2 - t * C)) * P[X | m] ω) ∂P) ≤
      ∫ ω, W ω ∂P := by
  let g := 2 * t / (2 - t * C)
  have hg : 0 ≤ g := by dsimp [g]; positivity
  let Z := fun ω => W ω * Real.exp (-g * P[X | m] ω)
  have hZ : StronglyMeasurable[m] Z :=
    hW.mul (Real.continuous_exp.comp_stronglyMeasurable
      (stronglyMeasurable_condExp.const_mul (-g)))
  have hY0 : 0 ≤ᵐ[P] P[X | m] :=
    condExp_nonneg (hXC.mono fun _ h => h.1)
  have hZK : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ K := by
    filter_upwards [hWK, hY0] with ω hω hy
    have he : Real.exp (-g * P[X | m] ω) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hg) hy
    calc
      ‖Z ω‖ = ‖W ω‖ * Real.exp (-g * P[X | m] ω) := by
        simp [Z, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      _ ≤ ‖W ω‖ * 1 := mul_le_mul_of_nonneg_left he (norm_nonneg _)
      _ ≤ K := by simpa using hω
  have hpull := condExp_stronglyMeasurable_mul_of_bound hm hZ
    (integrable_exp_mul_of_bound hX hXC ht) K hZK
  have hcond : P[Z * (fun ω => Real.exp (t * X ω)) | m] ≤ᵐ[P] W := by
    filter_upwards [hpull, condExp_exp_mul_le hm hX hXC ht htC, hW0] with ω hp he hw
    rw [hp]
    change Z ω * P[fun ω => Real.exp (t * X ω) | m] ω ≤ W ω
    have hz : 0 ≤ Z ω := mul_nonneg hw (Real.exp_pos _).le
    calc
      _ ≤ Z ω * (1 + g * P[X | m] ω) := mul_le_mul_of_nonneg_left he hz
      _ ≤ Z ω * Real.exp (g * P[X | m] ω) :=
        mul_le_mul_of_nonneg_left
          (by simpa [add_comm] using (Real.add_one_le_exp (g * P[X | m] ω))) hz
      _ = W ω := by
        dsimp only [Z]
        rw [mul_assoc, ← Real.exp_add]
        ring_nf
        simp
  calc
    _ = ∫ ω, Z ω * Real.exp (t * X ω) ∂P := by
      apply integral_congr_ae
      filter_upwards [] with ω
      dsimp only [Z, g]
      simp only [Real.exp_sub, neg_mul, Real.exp_neg]
      ring
    _ = ∫ ω, P[Z * (fun ω => Real.exp (t * X ω)) | m] ω ∂P :=
      (integral_condExp hm).symm
    _ ≤ _ := integral_mono_ae integrable_condExp
      (Integrable.of_bound (hW.mono hm).aestronglyMeasurable K hWK) hcond

end Arxiv2411_18291
