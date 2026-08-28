import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationRealModelCalculus
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCousinDifferential

/-!
# Local native-coordinate antiholomorphic calculus

The literal coordinate-update operator depends only on the local germ.
Its smoothness and mixed-derivative commutation at a smooth point follow
from the actual real Fréchet derivative. No smooth extension of a local
frame coefficient is assumed or chosen.
-/

noncomputable section

open Complex Filter Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationHolomorphicFrame

open PeriodTorusLineBundleClassification
open PeriodTorusLineBundleClassificationPolydiscAnalytic (complexPairEquiv)

/-- The actual coordinate derivative depends only on the local germ. -/
theorem dbarCoordinate_congr {f g : ComplexPlane₂ → ℂ} {z : ComplexPlane₂}
    (h : f =ᶠ[𝓝 z] g) (i : Fin 2) : dbarCoordinate f i z = dbarCoordinate g i z := by
  have hc : Continuous (fun w : ℂ => Function.update z i w) :=
    continuous_const.update i continuous_id
  have ht : Tendsto (fun w : ℂ => Function.update z i w) (𝓝 (z i)) (𝓝 z) := by
    simpa only [Function.update_eq_self] using hc.tendsto (z i)
  have he : (fun w : ℂ => f (Function.update z i w)) =ᶠ[𝓝 (z i)]
      (fun w => g (Function.update z i w)) := h.comp_tendsto ht
  unfold dbarCoordinate HolomorphicCousin.dbar
  rw [he.fderiv_eq (𝕜 := ℝ)]

/-- Equality of actual germs gives equality of the derivative germs. -/
theorem dbarCoordinate_eventuallyEq {f g : ComplexPlane₂ → ℂ} {z : ComplexPlane₂}
    (h : f =ᶠ[𝓝 z] g) (i : Fin 2) :
    dbarCoordinate f i =ᶠ[𝓝 z] dbarCoordinate g i :=
  h.eventuallyEq_nhds.mono fun _ hx => dbarCoordinate_congr hx i

/-- Local `C¹` regularity identifies the literal coordinate derivative
with the linear projection of the real differential on a neighborhood. -/
theorem dbarCoordinate_eventually_eq_linear {f : ComplexPlane₂ → ℂ} {z : ComplexPlane₂}
    (hf : ContDiffAt ℝ 1 f z) (i : Fin 2) :
    dbarCoordinate f i =ᶠ[𝓝 z] dbarCoordinateLinear i ∘ fderiv ℝ f := by
  filter_upwards [hf.eventually (by simp)] with x hx
  exact dbarCoordinate_eq_linear (hx.differentiableAt one_ne_zero) i

/-- At a smooth point, either actual coordinate derivative is smooth. -/
theorem contDiffAt_dbarCoordinate {f : ComplexPlane₂ → ℂ} {z : ComplexPlane₂}
    (hf : ContDiffAt ℝ ∞ f z) (i : Fin 2) :
    ContDiffAt ℝ ∞ (dbarCoordinate f i) z := by
  have hlin : ContDiffAt ℝ ∞ (dbarCoordinateLinear i ∘ fderiv ℝ f) z :=
    (dbarCoordinateLinear i).contDiff.contDiffAt.comp z (hf.fderiv_right (by simp))
  exact hlin.congr_of_eventuallyEq
    (dbarCoordinate_eventually_eq_linear (hf.of_le (by simp)) i)

/-- Actual mixed native-coordinate antiholomorphic derivatives commute
at a smooth point, by the real Schwarz theorem in product coordinates. -/
theorem dbarCoordinate_zero_one_commute_of_contDiffAt
    {f : ComplexPlane₂ → ℂ} {z : ComplexPlane₂} (hf : ContDiffAt ℝ ∞ f z) :
    dbarCoordinate (dbarCoordinate f 1) 0 z = dbarCoordinate (dbarCoordinate f 0) 1 z := by
  let g := f ∘ complexPairEquiv.symm
  have h0 : dbarCoordinate f 0 = dbarFirst g ∘ complexPairEquiv :=
    funext (dbarCoordinate_zero_eq_pair f)
  have h1 : dbarCoordinate f 1 = dbarSecond g ∘ complexPairEquiv :=
    funext (dbarCoordinate_one_eq_pair f)
  have he : ContDiff ℝ ∞ complexPairEquiv.symm :=
    complexPairEquiv.symm.contDiff.restrict_scalars ℝ
  have hf' : ContDiffAt ℝ ∞ f (complexPairEquiv.symm (complexPairEquiv z)) := by
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hf
  have hg : ContDiffAt ℝ ∞ g (complexPairEquiv z) :=
    hf'.comp (complexPairEquiv z) he.contDiffAt
  rw [h1, h0, dbarCoordinate_pair_zero, dbarCoordinate_pair_one]
  exact PeriodTorusLineBundleClassificationCousin.dbarFirst_dbarSecond_of_contDiffAt hg

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationHolomorphicFrame
