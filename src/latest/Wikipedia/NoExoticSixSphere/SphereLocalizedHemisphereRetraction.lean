import Wikipedia.NoExoticSixSphere.SphereHemisphereRetraction
import Wikipedia.NoExoticSixSphere.SphereSumSourceCover

/-!
# A hemisphere retraction constant on a whole opposite cap

The northern hemisphere is fixed pointwise. Below height minus one half,
the map is the northern pole. Between those regions the original hemisphere
contraction interpolates the folded point to the pole. This permits local
coordinate changes that do not modify the opposite cap.
-/

noncomputable section

open Set Function

namespace NoExoticSixSphere.LocalizedHemisphereRetraction

open SphereHemisphereRetraction SphereSumNeck

def time (x : Sphere 3) : unitInterval :=
  ⟨max 0 (min 1 (-2 * x.val 0)), le_max_left _ _,
    max_le (by norm_num) (min_le_left _ _)⟩

theorem continuous_time : Continuous time :=
  (continuous_const.max
    (continuous_const.min (continuous_const.mul continuous_sourceHead))).subtype_mk _

theorem time_north (x : Sphere 3) (hx : 0 ≤ x.val 0) : time x = 0 := by
  apply Subtype.ext
  change max 0 (min 1 (-2 * x.val 0)) = 0
  apply max_eq_left
  exact (min_le_right _ _).trans (by linarith)

theorem time_south (x : Sphere 3) (hx : x.val 0 ≤ -(1 / 2 : ℝ)) : time x = 1 := by
  apply Subtype.ext
  change max 0 (min 1 (-2 * x.val 0)) = 1
  rw [min_eq_left (by linarith)]
  norm_num

def retraction : C(Sphere 3, North) :=
  (ClosedHemisphere.contraction (spherePole 3)).toContinuousMap.comp
    ⟨fun x ↦ (time x, SphereHemisphereRetraction.retraction x),
      continuous_time.prodMk SphereHemisphereRetraction.retraction.continuous⟩

theorem retraction_north (x : North) : retraction x.val = x := by
  change ClosedHemisphere.contract (spherePole 3) (time x.val)
    (SphereHemisphereRetraction.retraction x.val) = x
  rw [time_north x.val ((mem_north_iff x.val).mp x.property),
    SphereHemisphereRetraction.retraction_north, ClosedHemisphere.contract_zero]

theorem retraction_south (x : Sphere 3) (hx : x.val 0 ≤ -(1 / 2 : ℝ)) :
    retraction x = ClosedHemisphere.center (spherePole 3) := by
  change ClosedHemisphere.contract (spherePole 3) (time x)
    (SphereHemisphereRetraction.retraction x) = _
  rw [time_south x hx, ClosedHemisphere.contract_one]

def contraction : retraction.Homotopy
    (ContinuousMap.const _ (ClosedHemisphere.center (spherePole 3))) :=
  (ClosedHemisphere.contraction (spherePole 3)).compContinuousMap retraction

end NoExoticSixSphere.LocalizedHemisphereRetraction
