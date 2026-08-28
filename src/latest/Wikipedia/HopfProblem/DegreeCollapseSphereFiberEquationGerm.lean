import Wikipedia.NoExoticSixSphere.SphereFiberNormalFrame

/-!
# The actual ambient fiber equations depend only on the sphere-map germ

Equality of sphere-map germs survives the radial extension and the fixed
centered target chart. Thus the ambient differential and its canonical
orthogonal right inverse agree exactly, not merely up to isomorphism.
-/

noncomputable section

open Filter
open scoped Topology Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SphereFiberEquationGerm

open NoExoticSixSphere

variable {m n : ℕ} (f g : C(Sphere m, Sphere n)) (b : Sphere n) (a x : Sphere m)

theorem equations_eventuallyEq (h : (f : Sphere m → Sphere n) =ᶠ[𝓝 x] g) :
    SphereFiberNormalFrame.equations f b a =ᶠ[𝓝 x.val]
      SphereFiberNormalFrame.equations g b a := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have ht : Tendsto (SphereRadialRetraction.retract a) (𝓝 x.val) (𝓝 x) := by
    have hc : Tendsto (SphereRadialRetraction.retract a) (𝓝 x.val)
        (𝓝 (SphereRadialRetraction.retract a x.val)) :=
      (SphereRadialRetraction.contMDiffAt_retract (n := m) a
        (ne_zero_of_mem_unit_sphere x)).continuousAt
    rwa [SphereRadialRetraction.retract_coe] at hc
  filter_upwards [h.comp_tendsto ht] with y hy
  change f (SphereRadialRetraction.retract a y) = g (SphereRadialRetraction.retract a y) at hy
  unfold SphereFiberNormalFrame.equations SphereLevelEquations.equations
    SphereLevelEquations.rawEquations SphereLevelEquations.extend
    CenteredChartCoordinates.coordinates
  simp only [Function.comp_apply, hy]

theorem equations_fderiv_eq (h : (f : Sphere m → Sphere n) =ᶠ[𝓝 x] g) :
    fderiv ℝ (SphereFiberNormalFrame.equations f b a) x.val =
      fderiv ℝ (SphereFiberNormalFrame.equations g b a) x.val :=
  (equations_eventuallyEq f g b a x h).fderiv_eq

theorem equations_rightInverse_eq (h : (f : Sphere m → Sphere n) =ᶠ[𝓝 x] g) :
    orthogonalRightInverse (fderiv ℝ (SphereFiberNormalFrame.equations f b a) x.val) =
      orthogonalRightInverse (fderiv ℝ (SphereFiberNormalFrame.equations g b a) x.val) :=
  congrArg orthogonalRightInverse (equations_fderiv_eq f g b a x h)

end Wikipedia.HopfProblem.DegreeCollapse.SphereFiberEquationGerm
