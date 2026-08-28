import Wikipedia.NoExoticSixSphere.QuaternionicHopfRadialRotation
import Wikipedia.NoExoticSixSphere.OrthogonalPaths
import Wikipedia.NoExoticSixSphere.SmoothSphereRotation

/-!
# A genuine homotopy to the radial Hopf-frame rotation

The two reflection normals never vanish along the interpolating segment.
This gives a homotopy through actual orthogonal operators, with a smooth
action, from the identity to the computed quarter turn. It fixes the
common orthogonal complement of the source pole and the fiber radius.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff
open unitInterval

namespace NoExoticSixSphere.QuaternionicHopf

def southRadialSegment (t : ℝ) (q : Sphere 3) : V 8 :=
  (1 - t) • (spherePole 7).val + t • (southFiberPoint q).val

theorem southRadialSegment_pole_inner (t : ℝ) (q : Sphere 3) :
    inner ℝ (spherePole 7).val (southRadialSegment t q) = 1 - t := by
  rw [southRadialSegment, inner_add_right, real_inner_smul_right,
    real_inner_smul_right, southFiber_orthogonal_sourcePole, real_inner_self_eq_norm_sq,
    mem_sphere_zero_iff_norm.mp (spherePole 7).property]
  ring

theorem southRadialSegment_fiber_inner (t : ℝ) (q : Sphere 3) :
    inner ℝ (southFiberPoint q).val (southRadialSegment t q) = t := by
  have h : inner ℝ (southFiberPoint q).val (spherePole 7).val = 0 := by
    rw [real_inner_comm]
    exact southFiber_orthogonal_sourcePole q
  rw [southRadialSegment, inner_add_right, real_inner_smul_right,
    real_inner_smul_right, h, real_inner_self_eq_norm_sq,
    mem_sphere_zero_iff_norm.mp (southFiberPoint q).property]
  ring

theorem southRadialSegment_ne_zero (t : ℝ) (q : Sphere 3) :
    southRadialSegment t q ≠ 0 := by
  intro h
  have hp := southRadialSegment_pole_inner t q
  have hx := southRadialSegment_fiber_inner t q
  rw [h, inner_zero_right] at hp hx
  linarith

theorem pole_add_southRadialSegment_ne_zero (t : ℝ) (q : Sphere 3) :
    (spherePole 7).val + southRadialSegment t q ≠ 0 := by
  intro h
  have hp := congrArg (inner ℝ (spherePole 7).val) h
  have hx := congrArg (inner ℝ (southFiberPoint q).val) h
  have hxp : inner ℝ (southFiberPoint q).val (spherePole 7).val = 0 := by
    rw [real_inner_comm]
    exact southFiber_orthogonal_sourcePole q
  rw [inner_add_right, southRadialSegment_pole_inner, inner_zero_right,
    real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp (spherePole 7).property] at hp
  rw [inner_add_right, southRadialSegment_fiber_inner, inner_zero_right, hxp] at hx
  linarith

theorem contMDiff_southRadialSegment :
    ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) 𝓘(ℝ, V 8) ∞
      (fun p : ℝ × Sphere 3 ↦ southRadialSegment p.1 p.2) := by
  exact ((contMDiff_const.sub contMDiff_fst).smul contMDiff_const).add
    (contMDiff_fst.smul (contMDiff_southFiberAmbient.comp contMDiff_snd))

def southRadialRotation (t : ℝ) (q : Sphere 3) : V 8 ≃ₗᵢ[ℝ] V 8 :=
  localRotationEquiv (spherePole 7).val (southRadialSegment t q)

theorem southRadialRotation_zero (q : Sphere 3) :
    (southRadialRotation 0 q).toContinuousLinearEquiv.toContinuousLinearMap = 1 := by
  change localRotationOperator (spherePole 7).val (southRadialSegment 0 q) = 1
  simpa only [southRadialSegment, sub_zero, one_smul, zero_smul, add_zero] using
    localRotationOperator_self (spherePole 7).val

theorem southRadialRotation_one (q : Sphere 3) :
    southRadialRotation 1 q = southQuarterTurn q := by
  simp only [southRadialRotation, southRadialSegment, sub_self, zero_smul, one_smul,
    zero_add, southQuarterTurn]

theorem continuous_southRadialRotation :
    Continuous (fun p : ℝ × Sphere 3 ↦
      (southRadialRotation p.1 p.2).toContinuousLinearEquiv.toContinuousLinearMap) :=
  continuous_localRotationOperator _ _ continuous_const
    contMDiff_southRadialSegment.continuous
    (fun p ↦ southRadialSegment_ne_zero p.1 p.2)
    (fun p ↦ pole_add_southRadialSegment_ne_zero p.1 p.2)

theorem contMDiff_southRadialRotation_apply
    (z : ℝ × Sphere 3 → V 8)
    (hz : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) 𝓘(ℝ, V 8) ∞ z) :
    ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) 𝓘(ℝ, V 8) ∞
      (fun p : ℝ × Sphere 3 ↦ southRadialRotation p.1 p.2 (z p)) :=
  contMDiff_localRotation_apply contMDiff_const contMDiff_southRadialSegment hz
    (fun p ↦ southRadialSegment_ne_zero p.1 p.2)
    (fun p ↦ pole_add_southRadialSegment_ne_zero p.1 p.2)

theorem southRadialRotation_fixes (t : ℝ) (q : Sphere 3) (v : V 8)
    (hp : inner ℝ (spherePole 7).val v = 0)
    (hx : inner ℝ (southFiberPoint q).val v = 0) :
    southRadialRotation t q v = v := by
  have hw : inner ℝ (southRadialSegment t q) v = 0 := by
    simp only [southRadialSegment, inner_add_left, real_inner_smul_left, hp, hx,
      mul_zero, add_zero]
  have hsum : inner ℝ ((spherePole 7).val + southRadialSegment t q) v = 0 := by
    rw [inner_add_left, hp, hw, add_zero]
  change localRotationOperator (spherePole 7).val (southRadialSegment t q) v = v
  rw [localRotationOperator_eq_comp, ContinuousLinearMap.comp_apply,
    hyperplaneReflectionOperator_apply ((spherePole 7).val + southRadialSegment t q) v,
    hsum, mul_zero, zero_smul, sub_zero,
    hyperplaneReflectionOperator_apply, hw, mul_zero, zero_smul, sub_zero]

def southQuarterTurnMap : C(Sphere 3, GLOrthonormalization.OrthogonalOperators 8) where
  toFun q := OrthogonalPaths.ofEquiv (southQuarterTurn q)
  continuous_toFun := by
    have h := continuous_southRadialRotation.comp
      ((continuous_const : Continuous (fun _ : Sphere 3 ↦ (1 : ℝ))).prodMk continuous_id)
    simp only [Function.comp_def, southRadialRotation_one] at h
    exact (h.subtype_mk _).subtype_mk _

def southQuarterTurnHomotopy :
    (ContinuousMap.const (Sphere 3) (OrthogonalPaths.identity 8)).Homotopy
      southQuarterTurnMap where
  toFun p := OrthogonalPaths.ofEquiv (southRadialRotation (p.1 : ℝ) p.2)
  continuous_toFun := by
    have h := continuous_southRadialRotation.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_snd : Continuous (fun p : I × Sphere 3 ↦ p.2)))
    exact (h.subtype_mk _).subtype_mk _
  map_zero_left q := by
    apply Subtype.ext
    apply Subtype.ext
    exact southRadialRotation_zero q
  map_one_left q := by
    change OrthogonalPaths.ofEquiv (southRadialRotation 1 q) = _
    rw [southRadialRotation_one]
    rfl

end NoExoticSixSphere.QuaternionicHopf
