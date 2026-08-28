import Wikipedia.NoExoticSixSphere.WhitneyCuspDeformation
import Wikipedia.NoExoticSixSphere.RectangularSmoothNormalization
import Wikipedia.NoExoticSixSphere.PartialFrameSphereObstruction

/-!
# The cusp derivative's frame class reduces to its linear residual column

On the unit parameter sphere, the explicit injective deformation normalizes
to an actual frame homotopy. Its simple endpoint has two fixed columns and
one orthogonal unit residual column. The other endpoint is the normalized
actual cusp derivative, not a separately prescribed plane family.
-/

noncomputable section

namespace NoExoticSixSphere.WhitneyCusp

open GLOrthonormalization Stiefel

theorem norm_deformation_zero (q : Sphere 3) (v : Vector 3) :
    ‖deformation 0 q.val v‖ = ‖v‖ := by
  have hq : q.val 0 ^ 2 + q.val 1 ^ 2 + q.val 2 ^ 2 + q.val 3 ^ 2 = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq q.val
    rw [ClosedHemisphere.unit_norm] at h
    norm_num [Fin.sum_univ_succ] at h
    change 1 = q.val 0 ^ 2 + (q.val 1 ^ 2 + (q.val 2 ^ 2 + q.val 3 ^ 2)) at h
    linarith
  have hm := congrArg (fun r : ℝ ↦ r * (v 2) ^ 2) hq
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  norm_num [Fin.sum_univ_succ, deformation_apply]
  change v 1 ^ 2 + ((q.val 3 * v 2) ^ 2 + ((q.val 1 * v 2) ^ 2 +
    ((q.val 2 * v 2) ^ 2 + (q.val 0 * v 2) ^ 2))) = v 1 ^ 2 + v 2 ^ 2
  nlinarith

theorem continuous_deformation_sphere (s : ℝ) :
    Continuous (fun q : Sphere 3 ↦ deformation s q.val) := by
  have hc : Continuous (fun q : Sphere 3 ↦ (s, q.val)) :=
    continuous_const.prodMk continuous_subtype_val
  apply continuous_clm_apply.mpr
  intro v
  have h := (contDiff_deformation_apply v).continuous.comp hc
  simpa only [Function.comp_def] using h

theorem continuous_deformation_cylinder :
    Continuous (fun z : unitInterval × Sphere 3 ↦ deformation (z.1 : ℝ) z.2.val) := by
  have hc : Continuous (fun z : unitInterval × Sphere 3 ↦ ((z.1 : ℝ), z.2.val)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  apply continuous_clm_apply.mpr
  intro v
  have h := (contDiff_deformation_apply v).continuous.comp hc
  simpa only [Function.comp_def] using h

def simpleFrameMap : C(Sphere 3, Space 6 3) where
  toFun q := ⟨deformation 0 q.val, norm_deformation_zero q⟩
  continuous_toFun :=
    (continuous_deformation_sphere 0).subtype_mk _

def gaussMap : C(Sphere 3, Space 6 3) :=
  Orthonormalization.map (fun q : Sphere 3 ↦ deformation 1 q.val)
    (fun q ↦ injective_deformation 1 zero_le_one q.val (ne_zero_of_mem_unit_sphere q))
    (continuous_deformation_sphere 1)

theorem gaussMap_operator (q : Sphere 3) :
    (gaussMap q).val = Orthonormalization.operator
      (fun p : Vector 4 ↦ fderiv ℝ (map (p 0)) (source p)) q.val := by
  change Orthonormalization.operator (fun p : Vector 4 ↦ deformation 1 p) q.val = _
  have he : (fun p : Vector 4 ↦ deformation 1 p) =
      fun p ↦ fderiv ℝ (map (p 0)) (source p) := funext deformation_one
  rw [he]

def normalizedDeformation : C(unitInterval × Sphere 3, Space 6 3) :=
  Orthonormalization.map
    (fun z : unitInterval × Sphere 3 ↦ deformation (z.1 : ℝ) z.2.val)
    (fun z ↦ injective_deformation z.1 z.1.property.1 z.2.val
      (ne_zero_of_mem_unit_sphere z.2)) continuous_deformation_cylinder

theorem normalizedDeformation_zero (q : Sphere 3) :
    normalizedDeformation (0, q) = simpleFrameMap q := by
  apply Subtype.ext
  exact Orthonormalization.operator_eq_self
    (fun z : unitInterval × Sphere 3 ↦ deformation (z.1 : ℝ) z.2.val) (0, q)
    (norm_deformation_zero q)

theorem normalizedDeformation_one (q : Sphere 3) :
    normalizedDeformation (1, q) = gaussMap q := by
  rfl

def frameHomotopy : simpleFrameMap.Homotopy gaussMap where
  toFun := normalizedDeformation
  continuous_toFun := normalizedDeformation.continuous
  map_zero_left := normalizedDeformation_zero
  map_one_left := normalizedDeformation_one

theorem gauss_parity_eq_simple :
    sphereThirdObstruction 1 gaussMap = sphereThirdObstruction 1 simpleFrameMap :=
  sphereThirdObstruction_homotopic 1 ⟨frameHomotopy.symm⟩

end NoExoticSixSphere.WhitneyCusp
