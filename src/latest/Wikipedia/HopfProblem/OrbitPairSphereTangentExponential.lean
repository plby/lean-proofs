import Wikipedia.HopfProblem.OrbitPairSphereGreatCircle
import Wikipedia.NoExoticSixSphere.SkewWedge
import Wikipedia.NoExoticSixSphere.SkewShortExponential
import Wikipedia.NoExoticSixSphere.OrthogonalExponentialCoordinates

/-!
# Smooth sphere geodesics from actual tangent vectors

For a unit vector x and v perpendicular to x, the rank-two skew operator
`z ↦ inner(x,z)v - inner(v,z)x` generates the sphere geodesic with initial
velocity v. Using the actual operator exponential makes the construction
smooth at v=0 as well as away from zero. No singular choice of a normalized
direction or of an endpoint angle is needed for smoothness.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.OrbitPair.SphereTangentExponential

open NoExoticSixSphere GLOrthonormalization CayleyTransform OrthogonalExponential
  SkewWedge SkewSpectralPlane

variable {n : ℕ}

abbrev Tangent (x : Vector n) := ↥((ℝ ∙ x)ᗮ)

theorem inner_tangent (x : Vector n) (v : Tangent x) : inner ℝ x (v : Vector n) = 0 :=
  (Submodule.mem_orthogonal_singleton_iff_inner_right.mp v.property)

def generatorLinear (x : Vector n) : Tangent x →ₗ[ℝ] SkewOperators n where
  toFun v := skew x (v : Vector n)
  map_add' u v := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro z
    change operator x ((u : Vector n) + v) z = operator x u z + operator x v z
    simp only [operator_apply, inner_add_left, add_smul, smul_add]
    module
  map_smul' a v := by
    apply Subtype.ext
    exact operator_smul_right a x v

def generator (x : Vector n) : Tangent x →L[ℝ] SkewOperators n :=
  (generatorLinear x).toContinuousLinearMap

theorem generator_apply (x : Vector n) (v : Tangent x) (z : Vector n) :
    (generator x v : Vector n →L[ℝ] Vector n) z =
      inner ℝ x z • (v : Vector n) - inner ℝ (v : Vector n) z • x := rfl

theorem generator_base {x : Vector n} (hx : ‖x‖ = 1) (v : Tangent x) :
    (generator x v : Vector n →L[ℝ] Vector n) x = (v : Vector n) := by
  have hzero : inner ℝ (v : Vector n) x = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp v.property
  rw [generator_apply, real_inner_self_eq_norm_sq, hx, one_pow,
    hzero, zero_smul, sub_zero, one_smul]

theorem generator_velocity (x : Vector n) (v : Tangent x) :
    (generator x v : Vector n →L[ℝ] Vector n) (v : Vector n) = (-‖v‖ ^ 2) • x := by
  rw [generator_apply, inner_tangent, zero_smul, real_inner_self_eq_norm_sq, zero_sub, neg_smul]
  rfl

theorem gram_base {x : Vector n} (hx : ‖x‖ = 1) (v : Tangent x) :
    gram (generator x v) x = ‖v‖ ^ 2 • x := by
  simp only [gram, adjoint_eq_neg, ContinuousLinearMap.neg_comp,
    neg_apply, ContinuousLinearMap.comp_apply,
    generator_base hx, generator_velocity, neg_smul, neg_neg]

theorem norm_generator_le {x : Vector n} (hx : ‖x‖ = 1) (v : Tangent x) :
    ‖(generator x v : Vector n →L[ℝ] Vector n)‖ ≤ 2 * ‖v‖ := by
  change ‖InnerProductSpace.rankOne ℝ (v : Vector n) x -
    InnerProductSpace.rankOne ℝ x (v : Vector n)‖ ≤ _
  have h := norm_sub_le (InnerProductSpace.rankOne ℝ (v : Vector n) x)
    (InnerProductSpace.rankOne ℝ x (v : Vector n))
  simpa only [InnerProductSpace.norm_rankOne, hx, mul_one, one_mul, two_mul] using! h

def curve (x : Vector n) (v : Tangent x) (t : ℝ) : Vector n :=
  (exp (t • generator x v)).1.1 x

theorem contDiff_family (x : Vector n) :
    ContDiff ℝ ∞ (fun p : ℝ × Tangent x => curve x p.2 p.1) :=
  (contDiff_exp_operator.comp
    (contDiff_fst.smul ((generator x).contDiff.comp contDiff_snd))).clm_apply contDiff_const

theorem contDiff_curve (x : Vector n) (v : Tangent x) : ContDiff ℝ ∞ (curve x v) :=
  (contDiff_family x).comp (contDiff_id.prodMk contDiff_const)

theorem curve_zero (x : Vector n) (v : Tangent x) : curve x v 0 = x := by
  simp only [curve, zero_smul, exp_zero]
  rfl

theorem curve_zero_velocity (x : Vector n) (t : ℝ) : curve x 0 t = x := by
  simp only [curve, map_zero, smul_zero, exp_zero]
  rfl

theorem norm_curve {x : Vector n} (hx : ‖x‖ = 1) (v : Tangent x) (t : ℝ) :
    ‖curve x v t‖ = 1 := ((exp (t • generator x v)).property x).trans hx

theorem hasDerivAt_curve {x : Vector n} (hx : ‖x‖ = 1) (v : Tangent x) (t : ℝ) :
    HasDerivAt (curve x v) ((exp (t • generator x v)).1.1 (v : Vector n)) t := by
  change HasDerivAt (fun r => (exp (r • generator x v)).1.1 x) _ t
  have hd := HilbertSchmidt.hasDerivAt_apply (hasDerivAt_exp_smul_operator (generator x v) t) x
  simpa only [ContinuousLinearMap.comp_apply, generator_base hx] using! hd

theorem speed_sq {x : Vector n} (hx : ‖x‖ = 1) (v : Tangent x) (t : ℝ) :
    ‖deriv (curve x v) t‖ ^ 2 = ‖v‖ ^ 2 := by
  rw [(hasDerivAt_curve hx v t).deriv, (exp (t • generator x v)).property]
  rfl

theorem energy_curve {x : Vector n} (hx : ‖x‖ = 1) (v : Tangent x) :
    SpherePathEnergy.energy (curve x v) 0 1 = ‖v‖ ^ 2 := by
  unfold SpherePathEnergy.energy
  simp_rw [speed_sq hx]
  simp

theorem hasFDerivAt_endpoint_zero {x : Vector n} (hx : ‖x‖ = 1) :
    HasFDerivAt (fun v : Tangent x => curve x v 1) ((ℝ ∙ x)ᗮ).subtypeL 0 := by
  have he : HasFDerivAt (fun K : SkewOperators n => (exp K).1.1)
      (skewAdjoint.submodule ℝ (Vector n →L[ℝ] Vector n)).subtypeL (generator x 0) := by
    rw [map_zero]
    exact hasFDerivAt_exp_operator_zero
  have hd := (he.comp 0 (generator x).hasFDerivAt).clm_apply (hasFDerivAt_const x 0)
  convert! hd using 1
  · funext v
    simp only [curve, one_smul, Function.comp_apply]
  · rw [ContinuousLinearMap.comp_zero, zero_add]
    apply ContinuousLinearMap.ext
    intro v
    change (v : Vector n) = (generator x v : Vector n →L[ℝ] Vector n) x
    rw [generator_base hx]

end Wikipedia.HopfProblem.OrbitPair.SphereTangentExponential
