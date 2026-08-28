import Wikipedia.SmoothSixDPoincare.NativeArcEndpointGerms

/-!
# Transverse derivatives determined by an axis germ

Equality of a strip's vertical axis with a parametrized sheet germ determines
the actual vertical derivative. Nonvanishing of that derivative persists on
an open neighborhood, because the whole strip is smoothly differentiable.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.TransverseCoordinates

variable {Z B : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- A prescribed vertical axis germ determines the strip's normal-direction derivative. -/
theorem vertical_derivative_of_axis_germ {H : (ℝ × ℝ) → B} {a : Z → B} (v : Z)
    (hH : DifferentiableAt ℝ H 0) (ha : DifferentiableAt ℝ a 0)
    (heq : (fun t : ℝ => H (0, t)) =ᶠ[𝓝 0] (fun t => a (t • v))) :
    fderiv ℝ H (0, 0) (0, 1) = fderiv ℝ a 0 v := by
  let S : ℝ →L[ℝ] (ℝ × ℝ) := ContinuousLinearMap.inr ℝ ℝ ℝ
  let L : ℝ →L[ℝ] Z := NativeParametrization.line v
  have hHS : fderiv ℝ (H ∘ S) 0 = (fderiv ℝ H 0).comp S := by
    rw [fderiv_comp 0 (by simpa only [map_zero] using hH) S.differentiableAt,
      map_zero, S.fderiv]
  have haL : fderiv ℝ (a ∘ L) 0 = (fderiv ℝ a 0).comp L := by
    rw [fderiv_comp 0 (by simpa only [map_zero] using ha) L.differentiableAt,
      map_zero, L.fderiv]
  have heq' : (H ∘ S) =ᶠ[𝓝 (0 : ℝ)] (a ∘ L) := heq
  have hd : fderiv ℝ (H ∘ S) 0 = fderiv ℝ (a ∘ L) 0 := heq'.fderiv_eq
  rw [hHS, haL] at hd
  have hval := congrArg (fun T : ℝ →L[ℝ] B => T 1) hd
  change fderiv ℝ H (0 : ℝ × ℝ) (0, 1) = fderiv ℝ a 0 v
  simpa only [ContinuousLinearMap.comp_apply, S, L, NativeParametrization.line_apply,
    one_smul, ContinuousLinearMap.inr_apply] using hval

/-- A nonzero vertical derivative stays nonzero on a neighborhood of the whole planar point. -/
theorem eventually_vertical_derivative_ne_zero {H : (ℝ × ℝ) → B} {p : ℝ × ℝ}
    (hH : ContDiffAt ℝ ∞ H p) (hn : fderiv ℝ H p (0, 1) ≠ 0) :
    ∀ᶠ q in 𝓝 p, fderiv ℝ H q (0, 1) ≠ 0 := by
  have hd : ContinuousAt (fderiv ℝ H) p := hH.continuousAt_fderiv (by simp)
  have hv : ContinuousAt (fun q => fderiv ℝ H q (0, 1)) p := hd.clm_apply continuousAt_const
  exact hv.preimage_mem_nhds (isClosed_singleton.isOpen_compl.mem_nhds hn)

end Wikipedia.SmoothSixDPoincare.TransverseCoordinates
