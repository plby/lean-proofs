import Wikipedia.NoExoticSixSphere.CircleCylinderNormalEquations
import Wikipedia.NoExoticSixSphere.CircleCylinderRadialNormal
import Wikipedia.NoExoticSixSphere.SphereFiberNormalFrame
import Wikipedia.NoExoticSixSphere.HilbertProductEquations

/-!
# The actual double equations split at both original endpoint germs

Composing the retained endpoint germs with the genuine product radial
retraction identifies the actual ambient equations with the ordered
product of the circle equation and the original endpoint equations.
Differentiation gives their full block differential at each endpoint.
-/

noncomputable section

open Function Filter Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.CircleCylinder

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

local instance : Fact (Module.finrank ℝ V = 1 + 1) := ⟨finrank_euclideanSpace_fin⟩
local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

theorem ambientEquations_endpoint_germ (a p : Sphere 1 × Sphere m)
    (f : C(Sphere m, Sphere n))
    (h : (map d : Sphere 1 × Sphere m → Sphere n) =ᶠ[𝓝 p] fun q ↦ f q.2) :
    ambientEquations d a =ᶠ[𝓝 (ProductSphereLevelEquations.inclusion p)]
      HilbertProduct.equations circleNorm (SphereFiberNormalFrame.equations f b a.2) := by
  have hr := (ProductSphereLevelEquations.contMDiffAt_retract (m := 1) (n := m) a p
    ).continuousAt.tendsto
  rw [ProductSphereLevelEquations.retract_inclusion] at hr
  filter_upwards [h.comp_tendsto hr] with v hv
  exact congrArg
    (fun z : Sphere n ↦ WithLp.toLp 2 (‖v.fst‖ ^ 2 - 1,
      WithLp.toLp 2 (‖v.snd‖ ^ 2 - 1,
        (modelChartPartialDiffeomorph (I := 𝓡 n) b) z -
          (modelChartPartialDiffeomorph (I := 𝓡 n) b) b))) hv

theorem ambientEquations_left_germ (a : Sphere 1 × Sphere m)
    (x : {x : Sphere m // d.leftMap x = b}) :
    ambientEquations d a =ᶠ[𝓝 (ambientInclusion d (leftInclusion d x))]
      HilbertProduct.equations circleNorm
        (SphereFiberNormalFrame.equations d.leftMap b a.2) :=
  ambientEquations_endpoint_germ d a (SphereCylinder.endPole 0 true, x.val) d.leftMap
    (left_germ d _ clock_left)

theorem ambientEquations_right_germ (a : Sphere 1 × Sphere m)
    (x : {x : Sphere m // d.rightMap x = b}) :
    ambientEquations d a =ᶠ[𝓝 (ambientInclusion d (rightInclusion d x))]
      HilbertProduct.equations circleNorm
        (SphereFiberNormalFrame.equations d.rightMap b a.2) :=
  ambientEquations_endpoint_germ d a (SphereCylinder.endPole 0 false, x.val) d.rightMap
    (right_germ d _ clock_right)

theorem fderiv_ambientEquations_left (a : Sphere 1 × Sphere m)
    (x : {x : Sphere m // d.leftMap x = b}) :
    fderiv ℝ (ambientEquations d a) (ambientInclusion d (leftInclusion d x)) =
      HilbertProduct.map (fderiv ℝ circleNorm (SphereCylinder.endPole 0 true).val)
        (fderiv ℝ (SphereFiberNormalFrame.equations d.leftMap b a.2) x.val.val) := by
  rw [(ambientEquations_left_germ d a x).fderiv_eq]
  exact HilbertProduct.fderiv_equations (contDiff_circleNorm.differentiable (by simp) _)
    ((SphereFiberNormalFrame.contDiffAt_equations d.leftMap d.smooth_left b a.2 x.val
      x.property).differentiableAt (by simp))

theorem fderiv_ambientEquations_right (a : Sphere 1 × Sphere m)
    (x : {x : Sphere m // d.rightMap x = b}) :
    fderiv ℝ (ambientEquations d a) (ambientInclusion d (rightInclusion d x)) =
      HilbertProduct.map (fderiv ℝ circleNorm (SphereCylinder.endPole 0 false).val)
        (fderiv ℝ (SphereFiberNormalFrame.equations d.rightMap b a.2) x.val.val) := by
  rw [(ambientEquations_right_germ d a x).fderiv_eq]
  exact HilbertProduct.fderiv_equations (contDiff_circleNorm.differentiable (by simp) _)
    ((SphereFiberNormalFrame.contDiffAt_equations d.rightMap d.smooth_right b a.2 x.val
      x.property).differentiableAt (by simp))

end NoExoticSixSphere.CircleCylinder
