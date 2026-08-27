import Arxiv.Arxiv2411_18291.ConditionalVarianceExponential

/-!
# One-step compensation by conditional second moments

A bounded nonnegative weight measurable before an increment remains a
supermartingale weight after multiplication by the compensated exponential.
The increment may be signed and may have a negative conditional mean.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

namespace Arxiv2411_18291

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable [IsProbabilityMeasure P] {X W : Ω → ℝ} {b t K : ℝ}

theorem condExp_variance_compensated_step (hm : m ≤ mΩ) (hb : 0 ≤ b)
    (hW : StronglyMeasurable[m] W) (hW0 : 0 ≤ᵐ[P] W)
    (hWK : ∀ᵐ ω ∂P, ‖W ω‖ ≤ K) (hX : StronglyMeasurable X)
    (hXb : ∀ᵐ ω ∂P, |X ω| ≤ b) (hmean : P[X | m] ≤ᵐ[P] 0)
    (ht : 0 ≤ t) (htb : t * b < 2) :
    P[fun ω => W ω * Real.exp (t * X ω -
      (t ^ 2 / (2 - t * b)) * P[fun ω => (X ω) ^ 2 | m] ω) | m] ≤ᵐ[P] W := by
  let g := t ^ 2 / (2 - t * b)
  let Q := P[fun ω => (X ω) ^ 2 | m]
  have hg : 0 ≤ g := by dsimp [g]; positivity
  let Z := fun ω => W ω * Real.exp (-g * Q ω)
  have hQ : StronglyMeasurable[m] Q := stronglyMeasurable_condExp
  have hQ0 : 0 ≤ᵐ[P] Q := condExp_nonneg (ae_of_all _ fun ω => sq_nonneg (X ω))
  have hZ : StronglyMeasurable[m] Z :=
    hW.mul (Real.continuous_exp.comp_stronglyMeasurable (hQ.const_mul (-g)))
  have hZK : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ K := by
    filter_upwards [hWK, hQ0] with ω hω hq
    have he : Real.exp (-g * Q ω) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hg) hq
    calc
      ‖Z ω‖ = ‖W ω‖ * Real.exp (-g * Q ω) := by
        simp [Z, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      _ ≤ ‖W ω‖ * 1 := mul_le_mul_of_nonneg_left he (norm_nonneg _)
      _ ≤ K := by simpa using hω
  have hpull := condExp_stronglyMeasurable_mul_of_bound hm hZ
    (integrable_exp_mul_of_abs_bound hX.measurable hXb t) K hZK
  have hcond : P[Z * (fun ω => Real.exp (t * X ω)) | m] ≤ᵐ[P] W := by
    filter_upwards [hpull, condExp_exp_mul_le_exp_secondMoment hm hb hX hXb hmean ht htb,
      hW0] with ω hp he hw
    rw [hp]
    change Z ω * P[fun ω => Real.exp (t * X ω) | m] ω ≤ W ω
    have hz : 0 ≤ Z ω := mul_nonneg hw (Real.exp_pos _).le
    calc
      _ ≤ Z ω * Real.exp (g * Q ω) := mul_le_mul_of_nonneg_left he hz
      _ = W ω := by
        dsimp only [Z]
        rw [mul_assoc, ← Real.exp_add]
        ring_nf
        simp
  have heq : (fun ω => W ω * Real.exp (t * X ω - g * Q ω)) =
      Z * (fun ω => Real.exp (t * X ω)) := by
    funext ω
    simp only [Z, Pi.mul_apply, Real.exp_sub, neg_mul, Real.exp_neg]
    ring
  change P[fun ω => W ω * Real.exp (t * X ω - g * Q ω) | m] ≤ᵐ[P] W
  rw [heq]
  exact hcond

end Arxiv2411_18291
