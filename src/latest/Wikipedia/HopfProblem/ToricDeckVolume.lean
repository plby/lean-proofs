import Wikipedia.HopfProblem.ToricTwistVolume
import Wikipedia.HopfProblem.ToricVolumeCoordinates

/-!
# Volume preservation in arbitrary toric charts

The translated chart is convenient for computing the derivative of the
twisted action.  For descent through a covering, the source and target
charts are chosen independently.  This file proves the actual Jacobian
identity in those arbitrary charts, including their boundary points.
-/

noncomputable section

open Set Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.ToricSpace

open ToricCharts ToricFan

/-- The deck transformation has the prescribed signed determinant in any
two toric charts, not just in a chart and its translate. -/
theorem twistedTranslate_arbitrary_chart_det_fderiv (s t : Triangle)
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) {D : Set ℂ}
    (hD : IsOpen D) (hC : ∀ i j, ContDiffOn ℂ ω (fun r => C r i j) D)
    {z : CoordinateSpace 3} (hz : Triangle.time z ∈ D)
    (ht : twistedTranslate C v (inclusion s z) ∈ (parametrization t).target) :
    LinearMap.det (fderiv ℂ (fun w => (parametrization t).symm
      (twistedTranslate C v (inclusion s w))) z).toLinearMap =
        (s.rays.det : ℂ) / (t.rays.det : ℂ) := by
  let s' := s.shift (cuspVector v)
  let f : CoordinateSpace 3 → CoordinateSpace 3 := fun w =>
    scale s' (fibreMultiplier (exponentialMultiplier C v (Triangle.time w))) w
  let e := (parametrization s').trans (parametrization t).symm
  have hez : f z ∈ e.source := by
    refine ⟨mem_univ _, ?_⟩
    change inclusion s' (f z) ∈ (parametrization t).target
    simpa only [twistedTranslate_chart_formula] using ht
  have hf : DifferentiableAt ℂ f z :=
    ((varying_scale_holomorphic s' (exponentialMultiplier C v)
      (exponentialMultiplier_holomorphic C v hC)).contDiffAt
        ((hD.preimage Triangle.time_holomorphic.continuous).mem_nhds hz)).differentiableAt
          (by simp)
  have he : DifferentiableAt ℂ e (f z) :=
    ((transition_holomorphic s' t).contDiffAt (e.open_source.mem_nhds hez)).differentiableAt
      (by simp)
  have hfun : (fun w => (parametrization t).symm
      (twistedTranslate C v (inclusion s w))) = e ∘ f := by
    funext w
    change _ = (parametrization t).symm (inclusion s' (f w))
    rw [twistedTranslate_chart_formula]
  have hdetf : LinearMap.det (fderiv ℂ f z).toLinearMap = 1 := by
    rw [← jacobianMatrix_det_eq_fderiv_det]
    exact twistedTranslate_chart_det_fderiv s C v hD hC hz
  rw [hfun, fderiv_comp z he hf]
  change LinearMap.det ((fderiv ℂ e (f z)).toLinearMap.comp
    (fderiv ℂ f z).toLinearMap) = _
  rw [LinearMap.det_comp, hdetf, mul_one,
    parametrization_transition_det_fderiv s' t hez, Triangle.rays_det_shift]

/-- The inverse of the inherited tube chart agrees with the ambient
parametrization throughout its target. -/
theorem tube_chart_symm_val (D : TopologicalSpace.Opens ℂ) (a : Tube D)
    {z : CoordinateSpace 3} (hz : z ∈ (chartAt (CoordinateSpace 3) a).target) :
    ((chartAt (CoordinateSpace 3) a).symm z : Space) =
      inclusion (preferredTriangle (a : Space)) z := by
  exact (chartAt (CoordinateSpace 3) (a : Space)).subtypeRestr_symm_apply ⟨a⟩ hz

/-- Signed volume preservation also holds in the actual inherited charts
of the open tube, whose inverse maps are only locally ambient inverses. -/
theorem tubeTranslate_chart_det_fderiv
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (D : TopologicalSpace.Opens ℂ)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun r => C r i j) (D : Set ℂ))
    (v : Fin 2 → ℤ) (a b : Tube D) {z : CoordinateSpace 3}
    (hz : z ∈ (chartAt (CoordinateSpace 3) a).target)
    (hb : tubeTranslate C D v ((chartAt (CoordinateSpace 3) a).symm z) ∈
      (chartAt (CoordinateSpace 3) b).source) :
    LinearMap.det (fderiv ℂ (chartAt (CoordinateSpace 3) b ∘
      tubeTranslate C D v ∘ (chartAt (CoordinateSpace 3) a).symm) z).toLinearMap =
      ((preferredTriangle (a : Space)).rays.det : ℂ) /
        ((preferredTriangle (b : Space)).rays.det : ℂ) := by
  let s := preferredTriangle (a : Space)
  let t := preferredTriangle (b : Space)
  have htime : Triangle.time z ∈ (D : Set ℂ) := by
    rw [← time_inclusion s z, ← tube_chart_symm_val D a hz]
    exact ((chartAt (CoordinateSpace 3) a).symm z).property
  have htarget : twistedTranslate C v (inclusion s z) ∈ (parametrization t).target := by
    have hb' : twistedTranslate C v
        ((chartAt (CoordinateSpace 3) a).symm z : Space) ∈ (parametrization t).target := hb.2
    rwa [tube_chart_symm_val D a hz] at hb'
  have heq : (chartAt (CoordinateSpace 3) b ∘ tubeTranslate C D v ∘
      (chartAt (CoordinateSpace 3) a).symm) =ᶠ[𝓝 z]
      (fun w => (parametrization t).symm (twistedTranslate C v (inclusion s w))) := by
    filter_upwards [(chartAt (CoordinateSpace 3) a).open_target.mem_nhds hz] with w hw
    change (parametrization t).symm (twistedTranslate C v
      ((chartAt (CoordinateSpace 3) a).symm w : Space)) = _
    rw [tube_chart_symm_val D a hw]
  rw [heq.fderiv_eq]
  exact twistedTranslate_arbitrary_chart_det_fderiv s t C v D.isOpen hC htime htarget

end Wikipedia.HopfProblem.ToricSpace
