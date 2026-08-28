import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfFiniteFrame
import Wikipedia.NoExoticSixSphere.NormalFrameOfEquations

/-!
# The actual smooth normal frame of the finite Hopf fiber

The original stereographic fiber parametrization is a smooth immersion.
Its tangent image is the kernel of the actual finite Hopf derivative.
The explicit isometric right inverse is orthogonal to this image, hence
equals the canonical induced normal frame and varies smoothly.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff RealInnerProductSpace

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfFiniteNormal

open NoExoticSixSphere QuaternionicHopf QuaternionicHopfFiniteFrame
open QuaternionicHopfSouthPolynomialFrame hiding rightInverse contMDiff_rightInverse
open SphereCenteredAmbientChart hiding V

theorem contMDiff_finitePoint : ContMDiff (𝓡 3) 𝓘(ℝ, V 7) ∞ finitePoint := by
  intro q
  exact (SphereFiniteRepresentative.projection_contMDiffAt 7
    (QuaternionicHopfSouthFiber.fiberPoint_ne_pole q)).comp q
      QuaternionicHopfSouthFiber.contMDiff_fiberPoint.contMDiffAt

theorem point_finitePoint (q : Sphere 3) :
    SphereFiniteRepresentative.point 7 (finitePoint q) =
      QuaternionicHopfSouthFiber.fiberPoint q :=
  SphereFiniteRepresentative.point_projection 7
    (QuaternionicHopfSouthFiber.fiberPoint_ne_pole q)

theorem contDiffAt_value (q : Sphere 3) :
    ContDiffAt ℝ ∞ (SphereFiniteRepresentative.value sphereMap) (finitePoint q) := by
  apply SphereFiniteRepresentative.value_contDiffAt
  · rw [point_finitePoint]
    exact contMDiff_sphereMap.contMDiffAt
  · rw [point_finitePoint, QuaternionicHopfSouthFiber.sphereMap_fiberPoint]
    exact QuaternionicHopfSouthFiber.point_ne_pole

theorem value_zero (q : Sphere 3) :
    SphereFiniteRepresentative.value sphereMap (finitePoint q) = 0 := by
  rw [SphereFiniteRepresentative.value, point_finitePoint,
    QuaternionicHopfSouthFiber.sphereMap_fiberPoint, sphereProjection_ambientChart,
    ← target_center, ambientChart_self]

theorem ambientDifferential_injective (q : Sphere 3) :
    Function.Injective (NormalFrameOfEquations.ambientDifferential (𝓡 3) finitePoint q) := by
  change Function.Injective (mfderiv (𝓡 3) (𝓡 7)
    (sphereProjection 7 ∘ QuaternionicHopfSouthFiber.fiberPoint) q)
  rw [mfderiv_comp q
    ((SphereFiniteRepresentative.projection_contMDiffAt 7
      (QuaternionicHopfSouthFiber.fiberPoint_ne_pole q)).mdifferentiableAt (by simp))
    (QuaternionicHopfSouthFiber.contMDiff_fiberPoint.mdifferentiable (by simp) q)]
  exact (SphereFiniteRepresentative.projection_mfderiv_bijective 7
    (QuaternionicHopfSouthFiber.fiberPoint_ne_pole q)).injective.comp
      (QuaternionicHopfSouthRegularity.fiberPoint_mfderiv_injective q)

theorem tangent_range_eq_kernel (q : Sphere 3) :
    (NormalFrameOfEquations.ambientDifferential (𝓡 3) finitePoint q).range =
      (fderiv ℝ (SphereFiniteRepresentative.value sphereMap) (finitePoint q)).ker :=
  NormalFrameOfEquations.range_ambientDifferential_eq_kernel contMDiff_finitePoint
    contDiffAt_value value_zero finite_derivative_surjective ambientDifferential_injective
    (by simp) q

theorem ambientDifferential_eq (q : Sphere 3) :
    NormalFrameOfEquations.ambientDifferential (𝓡 3) finitePoint q =
      (sourceDifferential q).comp (mfderiv (𝓡 3) 𝓘(ℝ, V 8) inclusion q) := by
  have he : finitePoint = ambientChart (-spherePole 7) ∘ inclusion := by
    funext p
    exact sphereProjection_ambientChart 7 (QuaternionicHopfSouthFiber.fiberPoint p)
  change mfderiv (𝓡 3) 𝓘(ℝ, V 7) finitePoint q = _
  rw [he, mfderiv_comp q
    ((SphereEquatorialChartDifferential.hasFDerivAt_ambientChart _ _
      (source_equatorial q)).differentiableAt.mdifferentiableAt)
    (contMDiff_inclusion.mdifferentiable (by simp) q), mfderiv_eq_fderiv,
    ← sourceDifferential_eq_fderiv]
  rfl

theorem inclusionDerivative_tangent (q : Sphere 3) (v : V 3) :
    inner ℝ (inclusion q) (mfderiv (𝓡 3) 𝓘(ℝ, V 8) inclusion q v : V 8) = 0 := by
  have he : polynomial ∘ inclusion = fun _ : Sphere 3 ↦ QuaternionicHopfSouthFiber.point.val :=
    funext polynomial_inclusion
  have hd := mfderiv_comp q
    ((contDiff_polynomial.differentiable (by simp) (inclusion q)).mdifferentiableAt)
    (contMDiff_inclusion.mdifferentiable (by simp) q)
  rw [he, mfderiv_const, mfderiv_eq_fderiv] at hd
  have hz := congrArg (fun L : V 3 →L[ℝ] V 5 ↦ L v) hd
  change (0 : V 5) = fderiv ℝ polynomial (inclusion q)
    (mfderiv (𝓡 3) 𝓘(ℝ, V 8) inclusion q v) at hz
  have hn := QuaternionicHopfSouthSphereFrame.norm_compatibility q
    (mfderiv (𝓡 3) 𝓘(ℝ, V 8) inclusion q v)
  rw [← hz, inner_zero_right] at hn
  linarith

theorem rightInverse_orthogonal (q : Sphere 3) (w : V 4) (v : V 3) :
    inner ℝ (rightInverse q w)
      (NormalFrameOfEquations.ambientDifferential (𝓡 3) finitePoint q v) = 0 := by
  rw [rightInverse_apply, ambientDifferential_eq]
  change inner ℝ ((1 / 2 : ℝ) • sourceDifferential q
    (QuaternionicHopfSouthNormal.frame q (QuaternionicHopfSouthSphereFrame.targetTailEquiv w)))
    (sourceDifferential q (mfderiv (𝓡 3) 𝓘(ℝ, V 8) inclusion q v)) = 0
  rw [real_inner_smul_left]
  have h := SphereEquatorialChartDifferential.differential_inner_tangent (-spherePole 7)
    (QuaternionicHopfSouthFiber.fiberPoint q) (source_equatorial q)
    (QuaternionicHopfSouthNormal.frame q (QuaternionicHopfSouthSphereFrame.targetTailEquiv w))
    (mfderiv (𝓡 3) 𝓘(ℝ, V 8) inclusion q v)
    (QuaternionicHopfSouthNormal.frame_tangent_sphere q _) (inclusionDerivative_tangent q v)
  change inner ℝ (sourceDifferential q
    (QuaternionicHopfSouthNormal.frame q (QuaternionicHopfSouthSphereFrame.targetTailEquiv w)))
    (sourceDifferential q (mfderiv (𝓡 3) 𝓘(ℝ, V 8) inclusion q v)) = _ at h
  rw [h]
  have ho := QuaternionicHopfSouthNormal.frame_orthogonal_fiber_derivative q
    (QuaternionicHopfSouthSphereFrame.targetTailEquiv w) v
  change inner ℝ
    (QuaternionicHopfSouthNormal.frame q (QuaternionicHopfSouthSphereFrame.targetTailEquiv w))
    (mfderiv (𝓡 3) 𝓘(ℝ, V 8) inclusion q v) = 0 at ho
  rw [ho, mul_zero, mul_zero]

theorem rightInverse_range_orthogonal (q : Sphere 3) :
    (rightInverse q).range ≤
      (fderiv ℝ (SphereFiniteRepresentative.value sphereMap) (finitePoint q)).kerᗮ := by
  rintro _ ⟨w, rfl⟩
  rw [← tangent_range_eq_kernel]
  rintro _ ⟨v, rfl⟩
  exact (real_inner_comm _ _).trans (rightInverse_orthogonal q w v)

theorem canonical_rightInverse (q : Sphere 3) :
    orthogonalRightInverse (fderiv ℝ (SphereFiniteRepresentative.value sphereMap) (finitePoint q)) =
      rightInverse q :=
  orthogonalRightInverse_eq_of_rightInverse _ (finite_derivative_surjective q)
    (rightInverse q) (finite_derivative_rightInverse q) (rightInverse_range_orthogonal q)

theorem contMDiff_rightInverse : ContMDiff (𝓡 3) 𝓘(ℝ, V 4 →L[ℝ] V 7) ∞ rightInverse := by
  have hD := NormalFrameOfEquations.contMDiff_equationDifferential
    contMDiff_finitePoint contDiffAt_value
  have he : rightInverse = fun q ↦ orthogonalRightInverse
      (fderiv ℝ (SphereFiniteRepresentative.value sphereMap) (finitePoint q)) :=
    funext (fun q ↦ (canonical_rightInverse q).symm)
  rw [he]
  intro q
  exact contMDiffAt_orthogonalRightInverse (hD q) (finite_derivative_surjective q)

theorem contMDiff_rightInverse_apply :
    ContMDiff ((𝓡 3).prod 𝓘(ℝ, V 4)) 𝓘(ℝ, V 7) ∞
      (fun p : Sphere 3 × V 4 ↦ rightInverse p.1 p.2) :=
  (contMDiff_rightInverse.comp contMDiff_fst).clm_apply contMDiff_snd

def normalFrame : SmoothRangeFrame (𝓡 3)
    (fun q ↦ (NormalFrameOfEquations.ambientDifferential (𝓡 3) finitePoint q).rangeᗮ.starProjection)
    (V 4) :=
  NormalFrameOfEquations.inducedFrame contMDiff_finitePoint contDiffAt_value value_zero
    finite_derivative_surjective ambientDifferential_injective (by simp)

theorem normalFrame_ambient (q : Sphere 3) : (normalFrame.ambient q) = rightInverse q :=
  canonical_rightInverse q

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfFiniteNormal
