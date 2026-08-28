import Wikipedia.NoExoticSixSphere.SemicircleSuspensionCoordinates
import Wikipedia.NoExoticSixSphere.SphereSuspensionHomotopyMap

/-!
# Descending actual fixed-endpoint path families to sphere maps

An explicit inverse to the cosine time change identifies the meridian
parameterization with the original suspension quotient. A family of paths
with fixed endpoints descends continuously, and so does a whole homotopy
of such families. Both formulas retain the original sphere maps.
-/

noncomputable section

open Set
open scoped unitInterval

namespace NoExoticSixSphere.SemicircleSuspension

open Wikipedia.HopfProblem.CuspCentralHomology
open Wikipedia.HopfProblem.SphereHomology

def inverseTime : C(I, I) where
  toFun t := ⟨Real.arccos (1 - 2 * (t : ℝ)) / Real.pi, by
    constructor
    · exact div_nonneg (Real.arccos_nonneg _) Real.pi_pos.le
    · exact (div_le_one Real.pi_pos).mpr (Real.arccos_le_pi _)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (Real.continuous_arccos.comp
      (continuous_const.sub (continuous_const.mul continuous_subtype_val))).div_const _

theorem time_inverseTime (t : I) : time (inverseTime t) = t := by
  apply Subtype.ext
  change (1 - Real.cos (Real.pi * (Real.arccos (1 - 2 * (t : ℝ)) / Real.pi))) / 2 = t
  rw [mul_div_cancel₀ _ Real.pi_ne_zero]
  rw [Real.cos_arccos (by linarith [t.property.2]) (by linarith [t.property.1])]
  ring

theorem inverseTime_time (t : I) : inverseTime (time t) = t := by
  apply Subtype.ext
  change Real.arccos (1 - 2 * ((1 - Real.cos (Real.pi * (t : ℝ))) / 2)) / Real.pi = t
  rw [show 1 - 2 * ((1 - Real.cos (Real.pi * (t : ℝ))) / 2) =
    Real.cos (Real.pi * (t : ℝ)) by ring]
  rw [Real.arccos_cos (mul_nonneg Real.pi_pos.le t.property.1)
    (by nlinarith [t.property.2, Real.pi_pos])]
  exact mul_div_cancel_left₀ (t : ℝ) Real.pi_ne_zero

theorem inverseTime_zero : inverseTime 0 = 0 := by
  simpa only [time_zero] using inverseTime_time 0

theorem inverseTime_one : inverseTime 1 = 1 := by
  simpa only [time_one] using inverseTime_time 1

theorem meridianMap_surjective (m : ℕ) : Function.Surjective (meridianMap m) := by
  intro y
  obtain ⟨⟨t, x⟩, hx⟩ := Latitude.point_surjective m y
  refine ⟨(inverseTime t, x), ?_⟩
  change Latitude.point m (time (inverseTime t)) x = y
  rw [time_inverseTime]
  exact hx

variable {m : ℕ} {Y : Type*} [TopologicalSpace Y] {a b : Y}

def quotientPathMap (P : C(Sphere m, Path a b)) : C(Suspension (Sphere m), Y) where
  toFun := Quotient.lift (fun z : I × Sphere m ↦ P z.2 (inverseTime z.1)) (by
    rintro ⟨t, x⟩ ⟨s, y⟩ ⟨ht, h0 | h1 | hxy⟩
    · change t = s at ht
      subst s
      change t = 0 at h0
      subst t
      rw [inverseTime_zero, Path.source, Path.source]
    · change t = s at ht
      subst s
      change t = 1 at h1
      subst t
      rw [inverseTime_one, Path.target, Path.target]
    · change t = s at ht
      change x = y at hxy
      subst s
      subst y
      rfl)
  continuous_toFun := by
    apply Suspension.isQuotientMap_mk.continuous_iff.mpr
    exact (PathFamilies.uncurry P).continuous.comp
      ((inverseTime.continuous.comp continuous_fst).prodMk continuous_snd)

def descend (P : C(Sphere m, Path a b)) : C(Sphere (m + 1), Y) :=
  (quotientPathMap P).comp ((suspensionSphereHomeomorph m).symm : C(_, _))

theorem descend_latitude (P : C(Sphere m, Path a b)) (t : I) (x : Sphere m) :
    descend P (Latitude.point m t x) = P x (inverseTime t) := by
  change quotientPathMap P ((suspensionSphereHomeomorph m).symm (Latitude.point m t x)) = _
  rw [← suspensionSphereHomeomorph_mk, Homeomorph.symm_apply_apply]
  rfl

theorem descend_meridian (P : C(Sphere m, Path a b)) (t : I) (x : Sphere m) :
    descend P (meridianMap m (t, x)) = P x t := by
  change descend P (Latitude.point m (time t) x) = _
  rw [descend_latitude, inverseTime_time]

def pathSlice {P Q : C(Sphere m, Path a b)} (H : P.Homotopy Q) (t : I) :
    C(Sphere m, Path a b) :=
  H.toContinuousMap.comp ⟨fun x ↦ (t, x), continuous_const.prodMk continuous_id⟩

def descendHomotopy {P Q : C(Sphere m, Path a b)} (H : P.Homotopy Q) :
    (descend P).Homotopy (descend Q) where
  toFun z := descend (pathSlice H z.1) z.2
  continuous_toFun := by
    apply (SphereMapSuspension.isQuotientMap_timeLatitude m).continuous_iff.mpr
    have hc := (PathFamilies.uncurry H.toContinuousMap).continuous.comp
      (((inverseTime.continuous.comp continuous_fst).comp continuous_snd).prodMk
        (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
    convert hc using 1
    funext z
    exact descend_latitude (pathSlice H z.1) z.2.1 z.2.2
  map_zero_left y := by
    have he : pathSlice H 0 = P := by
      apply ContinuousMap.ext
      exact H.apply_zero
    change descend (pathSlice H 0) y = _
    rw [he]
  map_one_left y := by
    have he : pathSlice H 1 = Q := by
      apply ContinuousMap.ext
      exact H.apply_one
    change descend (pathSlice H 1) y = _
    rw [he]

theorem descend_pathMap {n : ℕ} (f : C(Sphere m, Sphere n)) :
    descend (pathMap f) = SphereMapSuspension.map f := by
  apply ContinuousMap.ext
  intro y
  obtain ⟨⟨t, x⟩, rfl⟩ := meridianMap_surjective m y
  rw [descend_meridian, pathMap_apply]

def spherePathMap (f : C(Sphere (m + 1), Y)) (ha : f (south m) = a) (hb : f (north m) = b) :
    C(Sphere m, Path a b) :=
  PathFamilies.curry (f.comp (meridianMap m))
    (fun x ↦ (congrArg f (meridianMap_zero m x)).trans ha)
    (fun x ↦ (congrArg f (meridianMap_one m x)).trans hb)

theorem descend_spherePathMap (f : C(Sphere (m + 1), Y))
    (ha : f (south m) = a) (hb : f (north m) = b) : descend (spherePathMap f ha hb) = f := by
  apply ContinuousMap.ext
  intro y
  obtain ⟨⟨t, x⟩, rfl⟩ := meridianMap_surjective m y
  rw [descend_meridian]
  rfl

end NoExoticSixSphere.SemicircleSuspension
