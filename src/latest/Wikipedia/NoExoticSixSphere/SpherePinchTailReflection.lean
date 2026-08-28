import Wikipedia.NoExoticSixSphere.SphereCapPinchCoordinates
import Wikipedia.NoExoticSixSphere.SphereHeadReflection

/-!
# The explicit reflection in the southern pinch parametrization

The neck uses the same radial direction on its two ends, whereas the
polynomial sphere fold reverses that direction between hemispheres.
The reflection fixing the first coordinate and negating the tail records
this difference exactly. It fixes the collapsed pole.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

def tailReflection (x : Sphere 3) : Sphere 3 := antipode (reflectHead x)

theorem tailReflection_head (x : Sphere 3) : (tailReflection x).val 0 = x.val 0 := by
  change - -x.val 0 = x.val 0
  exact neg_neg _

theorem tailReflection_succ (x : Sphere 3) (i : Fin 3) :
    (tailReflection x).val i.succ = -x.val i.succ := rfl

theorem tailReflection_involutive : Involutive tailReflection := by
  intro x
  apply Subtype.ext
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rw [tailReflection_head, tailReflection_head]
  · rw [tailReflection_succ, tailReflection_succ, neg_neg]

theorem contMDiff_tailReflection : ContMDiff (𝓡 3) (𝓡 3) ∞ tailReflection := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  exact (SphereFold.contMDiff_antipode (n := 3)).comp contMDiff_reflectHead

def tailReflectionHomeomorph : Sphere 3 ≃ₜ Sphere 3 where
  toFun := tailReflection
  invFun := tailReflection
  left_inv := tailReflection_involutive
  right_inv := tailReflection_involutive
  continuous_toFun := contMDiff_tailReflection.continuous
  continuous_invFun := contMDiff_tailReflection.continuous

theorem tailReflection_pole : tailReflection pinchPole = pinchPole := by
  apply Subtype.ext
  ext i
  refine Fin.cases (tailReflection_head pinchPole) (fun j ↦ ?_) i
  rw [tailReflection_succ]
  simp [pinchPole, spherePole]

theorem tailReflection_antipode (x : Sphere 3) :
    tailReflection (antipode x) = antipode (tailReflection x) := by
  apply Subtype.ext
  ext i
  exact Fin.cases rfl (fun _ ↦ rfl) i

theorem tailReflection_base : tailReflection (antipode pinchPole) = antipode pinchPole := by
  rw [tailReflection_antipode, tailReflection_pole]

theorem fold_reflectHead (x : Sphere 3) :
    SphereFold.fold pinchPole (reflectHead x) = tailReflection (SphereFold.fold pinchPole x) := by
  apply Subtype.ext
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · change (2 * SphereFold.height pinchPole (reflectHead x)) * (-x.val 0) - pinchPole.val 0 =
      - -((2 * SphereFold.height pinchPole x) * x.val 0 - pinchPole.val 0)
    rw [pinchPole_height, reflectHead_head, pinchPole_height]
    ring
  · change (2 * SphereFold.height pinchPole (reflectHead x)) * x.val j.succ - pinchPole.val j.succ =
      -((2 * SphereFold.height pinchPole x) * x.val j.succ - pinchPole.val j.succ)
    rw [pinchPole_height, reflectHead_head, pinchPole_height]
    have hz : pinchPole.val j.succ = 0 := by
      simp [pinchPole, spherePole]
    rw [hz]
    ring

theorem capPinchComparison_fold_south (ε : ℝ) (hε : ε ≠ 0) {x : Sphere 3}
    (hx : x.val 0 < 0) :
    capPinchComparison ε hε (tailReflection (SphereFold.fold pinchPole x)) =
      sphereCap ε (reflectHead x) := by
  rw [← fold_reflectHead]
  apply capPinchComparison_fold_north
  rw [reflectHead_head]
  exact neg_pos.mpr hx

end NoExoticSixSphere.SphereSumNeck
