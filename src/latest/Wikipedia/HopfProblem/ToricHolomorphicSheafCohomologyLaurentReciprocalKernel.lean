import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyLaurentBoundary

/-!
# The joint Cauchy kernel with a reciprocal second coordinate

The first factor is the ordinary Cauchy kernel. The second factor is the
actual reciprocal-coordinate kernel, including at zero. Inversion in the
Banach algebra of continuous boundary functions proves genuine joint
analyticity of this kernel before any integral is applied.
-/

noncomputable section

open Complex Set Metric

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.Laurent

open CuspNormalization.Germs.NormalIntegral

def reciprocalDenominator (r R : ℝ) (q : ℂ × ℂ) : C(BoundaryTorus r R, ℂ) :=
  1 - boundarySecond r R * ContinuousMap.const _ q.2

theorem reciprocalDenominator_ne_zero {r R : ℝ} (hR : 0 < R) {q : ℂ × ℂ}
    (hq : q.2 ∈ ball (0 : ℂ) R⁻¹) (w : BoundaryTorus r R) :
    reciprocalDenominator r R q w ≠ 0 := by
  change 1 - (w.2.1 : ℂ) * q.2 ≠ 0
  have hu : ‖q.2‖ < R⁻¹ := by simpa only [mem_ball, dist_zero_right] using hq
  have hw : ‖(w.2.1 : ℂ)‖ = R := by
    simpa only [mem_sphere, dist_zero_right] using w.2.2
  have hnorm : ‖(w.2.1 : ℂ) * q.2‖ < 1 := by
    rw [norm_mul, hw]
    calc
      R * ‖q.2‖ < R * R⁻¹ := mul_lt_mul_of_pos_left hu hR
      _ = 1 := mul_inv_cancel₀ hR.ne'
  intro he
  have hprod : (w.2.1 : ℂ) * q.2 = 1 := (sub_eq_zero.mp he).symm
  rw [hprod, norm_one] at hnorm
  exact (lt_irrefl (1 : ℝ)) hnorm

theorem reciprocalDenominator_analyticAt (r R : ℝ) (q : ℂ × ℂ) :
    AnalyticAt ℂ (reciprocalDenominator r R) q := by
  have hc : AnalyticAt ℂ
      (fun p : ℂ × ℂ => ContinuousMap.const (BoundaryTorus r R) p.2) q :=
    ((ContinuousLinearMap.const (R := ℂ) (M := ℂ) (BoundaryTorus r R)).analyticAt q.2).comp
      analyticAt_snd
  exact analyticAt_const.sub (analyticAt_const.mul hc)

def reciprocalBoundaryKernel (r R : ℝ) (v : C(BoundaryTorus r R, ℂ)) (q : ℂ × ℂ) :
    C(BoundaryTorus r R, ℂ) :=
  Ring.inverse (firstDenominator r R q) *
    (ContinuousMap.const _ (-q.2) * Ring.inverse (reciprocalDenominator r R q)) * v

theorem reciprocalBoundaryKernel_apply {r R : ℝ} (hR : 0 < R)
    (v : C(BoundaryTorus r R, ℂ)) {q : ℂ × ℂ}
    (hq : q ∈ ball (0 : ℂ) r ×ˢ ball 0 R⁻¹) (w : BoundaryTorus r R) :
    reciprocalBoundaryKernel r R v q w =
      ((w.1.1 : ℂ) - q.1)⁻¹ * ((-q.2) * (1 - (w.2.1 : ℂ) * q.2)⁻¹) * v w := by
  simp only [reciprocalBoundaryKernel, ContinuousMap.mul_apply]
  rw [inverse_continuousMap_apply _ (firstDenominator_ne_zero hq.1),
    inverse_continuousMap_apply _ (reciprocalDenominator_ne_zero hR hq.2)]
  rfl

theorem reciprocalBoundaryKernel_analyticOnNhd (r R : ℝ) (hR : 0 < R)
    (v : C(BoundaryTorus r R, ℂ)) :
    AnalyticOnNhd ℂ (reciprocalBoundaryKernel r R v) (ball 0 r ×ˢ ball 0 R⁻¹) := by
  intro q hq
  have hfirst := (analyticAt_inverse_continuousMap (firstDenominator r R q)
    (firstDenominator_ne_zero hq.1)).comp (firstDenominator_analyticAt r R q)
  have hrecip := (analyticAt_inverse_continuousMap (reciprocalDenominator r R q)
    (reciprocalDenominator_ne_zero hR hq.2)).comp (reciprocalDenominator_analyticAt r R q)
  have hc : AnalyticAt ℂ
      (fun p : ℂ × ℂ => ContinuousMap.const (BoundaryTorus r R) (-p.2)) q :=
    AnalyticAt.comp (f := fun p : ℂ × ℂ => -p.2)
      ((ContinuousLinearMap.const (R := ℂ) (M := ℂ) (BoundaryTorus r R)).analyticAt (-q.2))
      analyticAt_snd.neg
  exact (hfirst.mul (hc.mul hrecip)).mul analyticAt_const

theorem analyticOnNhd_reciprocalBoundaryKernel_functional (r R : ℝ) (hR : 0 < R)
    (v : C(BoundaryTorus r R, ℂ)) (L : C(BoundaryTorus r R, ℂ) →L[ℂ] ℂ) :
    AnalyticOnNhd ℂ (fun q => L (reciprocalBoundaryKernel r R v q))
      (ball 0 r ×ˢ ball 0 R⁻¹) := by
  intro q hq
  exact (L.analyticAt _).comp (reciprocalBoundaryKernel_analyticOnNhd r R hR v q hq)

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.Laurent
