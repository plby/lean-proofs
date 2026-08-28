import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeBasic
import Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamilyAnalyticCoordinates

/-!
# The genuine holomorphic kernel of the full antiholomorphic differential

For real differentiable functions, vanishing of the actual anti-linear
Fréchet derivative is equivalent to complex differentiability.  On an
open set this gives genuine complex analyticity, in the unchanged model.
-/

noncomputable section

open Complex Set
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree

open HolomorphicAutomorphismNormalFamily.AnalyticThreefold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- A real covector commuting with the original complex structure is
the restriction of this genuine complex continuous linear map. -/
def complexCovector (L : E →L[ℝ] ℂ) (hL : ∀ v, L (I • v) = I * L v) :
    E →L[ℂ] ℂ where
  toFun := L
  map_add' := map_add L
  map_smul' := by
    intro c v
    have hr (r : ℝ) (w : E) : L ((r : ℂ) • w) = (r : ℂ) * L w := by
      change L ((algebraMap ℝ ℂ r) • w) = (r : ℂ) * L w
      rw [algebraMap_smul ℂ, map_smul, Complex.real_smul]
    change L (c • v) = c • L v
    rw [← re_add_im c]
    simp only [add_smul, mul_smul, map_add, hr, hL v, smul_eq_mul]
    ring
  cont := L.continuous

@[simp] theorem complexCovector_apply (L : E →L[ℝ] ℂ)
    (hL : ∀ v, L (I • v) = I * L v) (v : E) :
    complexCovector L hL v = L v := rfl

/-- Zero antiholomorphic part is precisely complex linearity of a real covector. -/
theorem antiPart_eq_zero_iff (L : E →L[ℝ] ℂ) :
    antiPart L = 0 ↔ ∀ v, L (I • v) = I * L v := by
  constructor
  · intro h v
    have hv := congrArg (fun K : E →L[ℝ] ℂ => K (I • v)) h
    rw [antiPart_apply] at hv
    simp only [smul_smul, I_mul_I, neg_one_smul, map_neg, zero_apply,
      mul_neg, ← sub_eq_add_neg, div_eq_zero_iff] at hv
    exact sub_eq_zero.mp (hv.resolve_right (by norm_num))
  · intro h
    exact antiPart_restrictScalars (complexCovector L h)

/-- The full Cauchy--Riemann criterion, with the original real derivative. -/
theorem differentiableAt_complex_iff_dbar_zero {f : E → ℂ} {q : E}
    (hf : DifferentiableAt ℝ f q) : DifferentiableAt ℂ f q ↔ dbar f q = 0 := by
  constructor
  · exact dbar_zero_of_differentiableAt
  · intro h
    have hL := (antiPart_eq_zero_iff (fderiv ℝ f q)).mp h
    apply (differentiableAt_iff_restrictScalars ℝ hf).mpr
    exact ⟨complexCovector (fderiv ℝ f q) hL, rfl⟩

/-- Actual vanishing on an open set gives joint complex analyticity there. -/
theorem analyticOnNhd_of_dbar_zero {f : Model → ℂ} {U : Set Model}
    (hU : IsOpen U) (hf : DifferentiableOn ℝ f U)
    (hz : ∀ q ∈ U, dbar f q = 0) : AnalyticOnNhd ℂ f U := by
  apply analyticOnNhd_nativeScalar_of_differentiableOn hU
  intro q hq
  exact ((differentiableAt_complex_iff_dbar_zero
    ((hf q hq).differentiableAt (hU.mem_nhds hq))).mpr (hz q hq)).differentiableWithinAt

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree
