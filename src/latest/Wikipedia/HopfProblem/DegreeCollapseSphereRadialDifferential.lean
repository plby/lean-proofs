import Wikipedia.NoExoticSixSphere.SphereRadialRetraction
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# The actual radial retraction has the tangent projection as derivative

At a unit vector, normalization differentiates to v ↦ v - inner(x,v) x.
The existing sphere-valued retraction has this same ambient derivative;
its fallback at zero does not affect the germ.
-/

noncomputable section

open Filter
open scoped Topology Manifold ContDiff RealInnerProductSpace

namespace Wikipedia.HopfProblem.DegreeCollapse.SphereRadialDifferential

open NoExoticSixSphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem hasFDerivAt_norm_unit (x : UnitSphere E) :
    HasFDerivAt (fun y : E ↦ ‖y‖) (innerSL ℝ x.val) x.val := by
  have hN := ((contDiffAt_norm ℝ (ne_zero_of_mem_unit_sphere x) :
    ContDiffAt ℝ ∞ (fun y : E ↦ ‖y‖) x.val).differentiableAt (by simp)).hasFDerivAt
  have he : fderiv ℝ (fun y : E ↦ ‖y‖) x.val + fderiv ℝ (fun y : E ↦ ‖y‖) x.val =
      innerSL ℝ x.val + innerSL ℝ x.val := by
    simpa only [ClosedHemisphere.unit_norm, Nat.cast_ofNat, Nat.reduceSub, pow_one,
      nsmul_eq_mul, mul_one, two_smul, add_smul, one_smul]
      using (hN.pow 2).unique (hasStrictFDerivAt_norm_sq x.val).hasFDerivAt
  have hd : fderiv ℝ (fun y : E ↦ ‖y‖) x.val = innerSL ℝ x.val := by
    ext v
    have hv := congrArg (fun L : E →L[ℝ] ℝ ↦ L v) he
    change fderiv ℝ (fun y : E ↦ ‖y‖) x.val v + fderiv ℝ (fun y : E ↦ ‖y‖) x.val v =
      innerSL ℝ x.val v + innerSL ℝ x.val v at hv
    linarith
  rwa [hd] at hN

def tangentProjection (x : UnitSphere E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - ContinuousLinearMap.smulRight (innerSL ℝ x.val) x.val

theorem tangentProjection_apply (x : UnitSphere E) (v : E) :
    tangentProjection x v = v - inner ℝ x.val v • x.val := rfl

theorem tangentProjection_radial (x : UnitSphere E) : tangentProjection x x.val = 0 := by
  rw [tangentProjection_apply, real_inner_self_eq_norm_sq, ClosedHemisphere.unit_norm,
    one_pow, one_smul, sub_self]

theorem tangentProjection_tangent (x : UnitSphere E) (v : E) (hv : inner ℝ x.val v = 0) :
    tangentProjection x v = v := by rw [tangentProjection_apply, hv, zero_smul, sub_zero]

theorem hasFDerivAt_normalize_unit (x : UnitSphere E) :
    HasFDerivAt (NormedSpace.normalize : E → E) (tangentProjection x) x.val := by
  have hn : ‖x.val‖ ≠ 0 := by rw [ClosedHemisphere.unit_norm]; norm_num
  have hi := (hasDerivAt_inv hn).comp_hasFDerivAt x.val (hasFDerivAt_norm_unit x)
  have h := hi.smul (hasFDerivAt_id x.val)
  convert! h using 1
  ext v
  simp [tangentProjection, sub_eq_add_neg]

def ambientRetract (a : UnitSphere E) (y : E) : E :=
  (SphereRadialRetraction.retract a y).val

theorem ambientRetract_coe (a x : UnitSphere E) : ambientRetract a x.val = x.val :=
  congrArg Subtype.val (SphereRadialRetraction.retract_coe a x)

theorem ambientRetract_eventuallyEq (a x : UnitSphere E) :
    ambientRetract a =ᶠ[𝓝 x.val] NormedSpace.normalize := by
  have hn : {y : E | y ≠ 0} ∈ 𝓝 x.val := isOpen_ne.mem_nhds (ne_zero_of_mem_unit_sphere x)
  filter_upwards [hn] with y hy
  simp only [ambientRetract, SphereRadialRetraction.retract, dif_neg hy]

theorem hasFDerivAt_ambientRetract (a x : UnitSphere E) :
    HasFDerivAt (ambientRetract a) (tangentProjection x) x.val :=
  (hasFDerivAt_normalize_unit x).congr_of_eventuallyEq (ambientRetract_eventuallyEq a x)

theorem fderiv_ambientRetract (a x : UnitSphere E) :
    fderiv ℝ (ambientRetract a) x.val = tangentProjection x :=
  (hasFDerivAt_ambientRetract a x).fderiv

end Wikipedia.HopfProblem.DegreeCollapse.SphereRadialDifferential
