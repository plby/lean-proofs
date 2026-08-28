import Wikipedia.NoExoticSixSphere.SphereHemisphereCutPaste
import Wikipedia.NoExoticSixSphere.SphereHeadReflection
import Wikipedia.NoExoticSixSphere.SphereCoordinateEquator

/-!
# A genuine hemisphere retraction for extending local coordinate families

Fold the southern hemisphere across the equator and retain the northern
hemisphere pointwise. The known hemisphere contraction then contracts this
whole-sphere retraction to its pole. This is not a disk extension of the
quaternionic tangent framing.
-/

noncomputable section

open Set Function Topology

namespace NoExoticSixSphere.SphereHemisphereRetraction

open GLOrthonormalization SphereSumNeck

abbrev North := ClosedHemisphere (spherePole 3)

theorem mem_north_iff (x : Sphere 3) : x ∈ closedHemisphere (spherePole 3) ↔ 0 ≤ x.val 0 := by
  change 0 ≤ inner ℝ (spherePole 3).val x.val ↔ _
  rw [SphereCylinder.pole_inner]

theorem reflectHead_eq_self {x : Sphere 3} (hx : x.val 0 = 0) : reflectHead x = x := by
  apply Subtype.ext
  ext i
  refine Fin.cases ?_ (fun _ ↦ rfl) i
  change -x.val 0 = x.val 0
  rw [hx, neg_zero]

def reflectionMap : C(Sphere 3, Sphere 3) := ⟨reflectHead, contMDiff_reflectHead.continuous⟩

def fold : C(Sphere 3, Sphere 3) :=
  HemisphereExchange.gluedMap (ContinuousMap.id _) reflectionMap
    (fun _ hx ↦ (reflectHead_eq_self hx).symm)

theorem fold_north (x : Sphere 3) (hx : 0 ≤ x.val 0) : fold x = x :=
  HemisphereExchange.gluedMap_north _ _ _ x hx

theorem fold_south (x : Sphere 3) (hx : x.val 0 ≤ 0) : fold x = reflectHead x :=
  HemisphereExchange.gluedMap_south _ _ _ x hx

theorem fold_mem_north (x : Sphere 3) : fold x ∈ closedHemisphere (spherePole 3) := by
  rw [mem_north_iff]
  by_cases hx : 0 ≤ x.val 0
  · rwa [fold_north x hx]
  · rw [fold_south x (le_of_not_ge hx), reflectHead_head]
    exact neg_nonneg.mpr (le_of_not_ge hx)

def retraction : C(Sphere 3, North) :=
  ⟨fun x ↦ ⟨fold x, fold_mem_north x⟩, fold.continuous.subtype_mk _⟩

theorem retraction_north (x : North) : retraction x.val = x :=
  Subtype.ext (fold_north x.val ((mem_north_iff x.val).mp x.property))

def contraction : retraction.Homotopy (ContinuousMap.const _
    (ClosedHemisphere.center (spherePole 3))) :=
  (ClosedHemisphere.contraction (spherePole 3)).compContinuousMap retraction

def contracted (t : unitInterval) (x : Sphere 3) : North := contraction (t, x)

theorem contracted_apply (t : unitInterval) (x : Sphere 3) :
    contracted t x = ClosedHemisphere.contract (spherePole 3) t (retraction x) := rfl

theorem continuous_contracted :
    Continuous (fun p : unitInterval × Sphere 3 ↦ contracted p.1 p.2) := contraction.continuous

theorem contracted_zero (x : Sphere 3) : contracted 0 x = retraction x := contraction.apply_zero x

theorem contracted_one (x : Sphere 3) : contracted 1 x = ClosedHemisphere.center (spherePole 3) :=
  contraction.apply_one x

end NoExoticSixSphere.SphereHemisphereRetraction
