import Wikipedia.NoExoticSixSphere.SphereCoordinateEquator
import Wikipedia.NoExoticSixSphere.SphereMapSuspension
import Wikipedia.HopfProblem.OrbitPairSphereMinimumPathSpace

/-!
# The minimum semicircles are literal suspension latitudes

The direction homeomorphism uses the actual zero-head equator, rather than
an arbitrarily chosen orthonormal basis. The cosine change of time then
identifies its minimum paths pointwise with the existing latitude maps.
-/

noncomputable section

open Set
open scoped unitInterval

namespace NoExoticSixSphere.SemicircleSuspension

open GLOrthonormalization SphereCylinder
open Wikipedia.HopfProblem.SphereHomology
open Wikipedia.HopfProblem.OrbitPair SphereSemicircle SpherePolygonEnergy

def south (n : ℕ) : Sphere (n + 1) := antipode (spherePole (n + 1))

def north (n : ℕ) : Sphere (n + 1) := spherePole (n + 1)

theorem north_eq_neg_south (n : ℕ) : (north n).val = -(south n).val := by
  change (spherePole (n + 1)).val = -(-(spherePole (n + 1)).val)
  rw [neg_neg]

def equatorialDirection (n : ℕ) : Sphere n ≃ₜ Direction (south n) :=
  (zeroEquatorHomeomorph n).trans (directionEquatorHomeomorph (south n)).symm

theorem direction_head (n : ℕ) (x : Sphere n) : (equatorialDirection n x).val 0 = 0 := by
  change (point n (0, x)).val 0 = 0
  rw [point_head]
  exact mul_zero _

theorem norm_vector_zero (n : ℕ) (x : Sphere n) : ‖vector n (0, x)‖ = 1 := by
  have h := norm_join_sq n 0 x.val
  change ‖vector n (0, x)‖ ^ 2 = 0 ^ 2 + ‖x.val‖ ^ 2 at h
  rw [ClosedHemisphere.unit_norm] at h
  nlinarith [norm_nonneg (vector n (0, x))]

theorem direction_tail (n : ℕ) (x : Sphere n) (i : Fin (n + 1)) :
    (equatorialDirection n x).val i.succ = x.val i := by
  change ‖vector n (0, x)‖⁻¹ * x.val i = x.val i
  rw [norm_vector_zero, inv_one, one_mul]

def time : C(I, I) where
  toFun t := ⟨(1 - Real.cos (Real.pi * (t : ℝ))) / 2, by
    constructor
    · linarith [Real.cos_le_one (Real.pi * (t : ℝ))]
    · linarith [Real.neg_one_le_cos (Real.pi * (t : ℝ))]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop

theorem time_zero : time 0 = 0 := by
  apply Subtype.ext
  change (1 - Real.cos (Real.pi * 0)) / 2 = 0
  norm_num

theorem time_one : time 1 = 1 := by
  apply Subtype.ext
  change (1 - Real.cos (Real.pi * 1)) / 2 = 1
  norm_num

theorem height_time (t : I) : Latitude.height (time t) = -Real.cos (Real.pi * (t : ℝ)) := by
  change 2 * ((1 - Real.cos (Real.pi * (t : ℝ))) / 2) - 1 = _
  ring

theorem radius_time (t : I) : Latitude.radius (time t) = Real.sin (Real.pi * (t : ℝ)) := by
  have hs : 0 ≤ Real.sin (Real.pi * (t : ℝ)) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg Real.pi_pos.le t.property.1)
      (by nlinarith [t.property.2, Real.pi_pos])
  have he : 1 - Real.cos (Real.pi * (t : ℝ)) ^ 2 = Real.sin (Real.pi * (t : ℝ)) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * (t : ℝ))]
  rw [Latitude.radius, height_time, neg_sq, he, Real.sqrt_sq hs]

theorem minimumPath_eq_latitude (n : ℕ) (x : Sphere n) (t : I) :
    minimumPathMap (south n) (north n) (north_eq_neg_south n) (equatorialDirection n x) t =
      Latitude.point n (time t) x := by
  apply Subtype.ext
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · change Real.cos (Real.pi * (t : ℝ)) * (south n).val 0 +
      Real.sin (Real.pi * (t : ℝ)) * (equatorialDirection n x).val 0 = Latitude.height (time t)
    have ha : (south n).val 0 = -1 := by simp [south, antipode, spherePole]
    rw [ha, direction_head, height_time]
    ring
  · change Real.cos (Real.pi * (t : ℝ)) * (south n).val j.succ +
      Real.sin (Real.pi * (t : ℝ)) * (equatorialDirection n x).val j.succ =
        Latitude.radius (time t) * x.val j
    have ha : (south n).val j.succ = 0 := by simp [south, antipode, spherePole]
    rw [ha, direction_tail, radius_time]
    ring

def meridianMap (n : ℕ) : C(I × Sphere n, Sphere (n + 1)) :=
  ⟨fun z ↦ Latitude.point n (time z.1) z.2,
    (Latitude.point_continuous n).comp
      ((time.continuous.comp continuous_fst).prodMk continuous_snd)⟩

def pathMap {m n : ℕ} (f : C(Sphere m, Sphere n)) :
    C(Sphere m, Path (south n) (north n)) :=
  (minimumPathMap (south n) (north n) (north_eq_neg_south n)).comp
    ((equatorialDirection n : C(_, _)).comp f)

theorem pathMap_apply {m n : ℕ} (f : C(Sphere m, Sphere n)) (x : Sphere m) (t : I) :
    pathMap f x t = SphereMapSuspension.map f (meridianMap m (t, x)) := by
  change minimumPathMap (south n) (north n) (north_eq_neg_south n)
    (equatorialDirection n (f x)) t = SphereMapSuspension.map f (Latitude.point m (time t) x)
  rw [minimumPath_eq_latitude, SphereMapSuspension.map_point]

theorem meridianMap_zero (n : ℕ) (x : Sphere n) : meridianMap n (0, x) = south n :=
  (minimumPath_eq_latitude n x 0).symm.trans
    (minimumPathMap (south n) (north n) (north_eq_neg_south n) (equatorialDirection n x)).source

theorem meridianMap_one (n : ℕ) (x : Sphere n) : meridianMap n (1, x) = north n :=
  (minimumPath_eq_latitude n x 1).symm.trans
    (minimumPathMap (south n) (north n) (north_eq_neg_south n) (equatorialDirection n x)).target

theorem suspension_south {m n : ℕ} (f : C(Sphere m, Sphere n)) :
    SphereMapSuspension.map f (south m) = south n := by
  have h := pathMap_apply f (spherePole m) 0
  rw [meridianMap_zero] at h
  exact h.symm.trans (pathMap f (spherePole m)).source

theorem suspension_north {m n : ℕ} (f : C(Sphere m, Sphere n)) :
    SphereMapSuspension.map f (north m) = north n := by
  have h := pathMap_apply f (spherePole m) 1
  rw [meridianMap_one] at h
  exact h.symm.trans (pathMap f (spherePole m)).target

end NoExoticSixSphere.SemicircleSuspension
