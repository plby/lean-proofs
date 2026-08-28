import Wikipedia.SmoothSixDPoincare.SmoothFlowEquation

/-!
# Genuine local trajectories satisfy the rescaled implicit equation

Multiplying elapsed time by a parameter in `[0,1]` stays in the original
time interval, including negative elapsed times. The fundamental theorem
of calculus identifies the rescaled trajectory with a zero of the original
Banach-space flow equation.
-/

noncomputable section

open Set ContinuousMap Metric
open scoped unitInterval ContDiff

namespace Wikipedia.SmoothSixDPoincare.FunctionSpaceCalculus

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem time_mul_unitInterval {ε t : ℝ} (ht : t ∈ Ioo (-ε) ε) (s : I) :
    t * (s : ℝ) ∈ Ioo (-ε) ε := by
  apply abs_lt.mp
  calc
    |t * (s : ℝ)| = |t| * (s : ℝ) := by rw [abs_mul, abs_of_nonneg s.property.1]
    _ ≤ |t| := mul_le_of_le_one_right (abs_nonneg t) s.property.2
    _ < ε := abs_lt.mpr ht

theorem flowEquation_eq_zero_of_hasDerivAt (v : C(E, E)) (x : E) (t : ℝ)
    (a : C(I, E)) (γ : ℝ → E) (hγ : ∀ s : I, γ s = a s) (hzero : γ 0 = x)
    (hder : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt γ (t • v (γ s)) s) :
    flowEquation v ((x, t), a) = 0 := by
  ext s
  have hext (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      IccExtendCM (v.comp a) u = v (γ u) := by
    rw [IccExtendCM_of_mem hu]
    exact congrArg v (hγ ⟨u, hu⟩).symm
  have hFTC : (∫ u in 0..(s : ℝ), t • IccExtendCM (v.comp a) u) = γ s - γ 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro u hu
      have hu' : u ∈ Icc (0 : ℝ) 1 := by
        rw [uIcc_of_le s.property.1] at hu
        exact ⟨hu.1, hu.2.trans s.property.2⟩
      rw [hext u hu']
      exact hder u hu'
    · exact ((IccExtendCM (v.comp a)).continuous.const_smul t).intervalIntegrable _ _
  rw [intervalIntegral.integral_smul, hγ s, hzero] at hFTC
  change a s - x - t • curvePrimitive (v.comp a) s = 0
  exact sub_eq_zero.mpr hFTC.symm

def rescaledFlowCurve (α : E × ℝ → E) {x₀ : E} {r ε : ℝ}
    (hc : ContinuousOn α (ball x₀ r ×ˢ Ioo (-ε) ε))
    {x : E} (hx : x ∈ ball x₀ r) {t : ℝ} (ht : t ∈ Ioo (-ε) ε) : C(I, E) :=
  ⟨fun s => α (x, t * (s : ℝ)), hc.comp_continuous
    (continuous_const.prodMk (continuous_const.mul continuous_subtype_val))
    (fun s => ⟨hx, time_mul_unitInterval ht s⟩)⟩

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem rescaledFlowCurve_apply (α : E × ℝ → E) {x₀ : E} {r ε : ℝ}
    (hc : ContinuousOn α (ball x₀ r ×ˢ Ioo (-ε) ε))
    {x : E} (hx : x ∈ ball x₀ r) {t : ℝ} (ht : t ∈ Ioo (-ε) ε) (s : I) :
    rescaledFlowCurve α hc hx ht s = α (x, t * (s : ℝ)) := rfl

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem rescaledFlowCurve_one (α : E × ℝ → E) {x₀ : E} {r ε : ℝ}
    (hc : ContinuousOn α (ball x₀ r ×ˢ Ioo (-ε) ε))
    {x : E} (hx : x ∈ ball x₀ r) {t : ℝ} (ht : t ∈ Ioo (-ε) ε) :
    rescaledFlowCurve α hc hx ht 1 = α (x, t) := by
  simp [rescaledFlowCurve]

theorem flowEquation_rescaledFlowCurve (v : C(E, E)) (α : E × ℝ → E)
    {x₀ : E} {r ε : ℝ} (hc : ContinuousOn α (ball x₀ r ×ˢ Ioo (-ε) ε))
    {x : E} (hx : x ∈ ball x₀ r) {t : ℝ} (ht : t ∈ Ioo (-ε) ε)
    (hzero : α (x, 0) = x)
    (hder : ∀ u ∈ Ioo (-ε) ε, HasDerivAt (fun s => α (x, s)) (v (α (x, u))) u) :
    flowEquation v ((x, t), rescaledFlowCurve α hc hx ht) = 0 := by
  apply flowEquation_eq_zero_of_hasDerivAt v x t _ (fun s => α (x, t * s))
  · intro s
    rfl
  · simpa only [mul_zero] using hzero
  · intro s hs
    exact (hder (t * s) (time_mul_unitInterval ht ⟨s, hs⟩)).scomp s
      (hasDerivAt_const_mul t)

end Wikipedia.SmoothSixDPoincare.FunctionSpaceCalculus
