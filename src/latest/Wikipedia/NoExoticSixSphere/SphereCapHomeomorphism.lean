import Wikipedia.NoExoticSixSphere.SphereFoldCapExtension
import Wikipedia.NoExoticSixSphere.SphereExteriorCapEquiv
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction

/-!
# Whole-sphere homeomorphisms agreeing with the retained cap maps

Compose the checked fold extension with the actual cap-to-pinch comparison.
This gives an actual sphere homeomorphism equal to the northern cap map
on its entire retained open region. Reflection gives the southern version.
The maps are local diffeomorphisms on those regions in the original atlas;
no global smoothness across the pasted latitude is required or asserted.
-/

noncomputable section

open Set Function Filter Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

theorem half_lt_head_of_northRegion {x : Sphere 3} (hx : x ∈ northRegion) :
    (1 / 2 : ℝ) < x.val 0 := by
  have hp := northRegion_head_pos hx
  change 2 * ‖SphereCylinder.tail 2 x.val‖ < x.val 0 at hx
  by_contra hh
  have hh' : x.val 0 ≤ (1 / 2 : ℝ) := le_of_not_gt hh
  have ht : ‖SphereCylinder.tail 2 x.val‖ ≤ (1 / 4 : ℝ) := by linarith
  have hh2 := mul_self_le_mul_self hp.le hh'
  have ht2 := mul_self_le_mul_self (norm_nonneg (SphereCylinder.tail 2 x.val)) ht
  nlinarith [source_head_tail_sq x]

theorem reflectHead_mem_northRegion {x : Sphere 3} (hx : x ∈ southRegion) :
    reflectHead x ∈ northRegion := by
  change 2 * ‖SphereCylinder.tail 2 (reflectHead x).val‖ < (reflectHead x).val 0
  rw [reflectHead_tail, reflectHead_head]
  exact hx

def northCapHomeomorph (ε : ℝ) (hε : 0 < ε) : Sphere 3 ≃ₜ Sphere 3 :=
  foldCapHomeomorph.trans (capPinchComparison ε hε.ne')

theorem northCapHomeomorph_upper (ε : ℝ) (hε : 0 < ε) (x : Sphere 3)
    (hx : (1 / 2 : ℝ) ≤ x.val 0) : northCapHomeomorph ε hε x = sphereCap ε x := by
  change capPinchComparison ε hε.ne' (foldCapExtension x) = sphereCap ε x
  rw [foldCapExtension_upper x hx]
  exact capPinchComparison_fold_north ε hε.ne' (by linarith)

theorem northCapHomeomorph_north (ε : ℝ) (hε : 0 < ε) {x : Sphere 3}
    (hx : x ∈ northRegion) : northCapHomeomorph ε hε x = sphereCap ε x :=
  northCapHomeomorph_upper ε hε x (half_lt_head_of_northRegion hx).le

theorem northCapHomeomorph_exterior (ε : ℝ) (hε : 0 < ε) {x : Sphere 3}
    (hx : x ∈ northExterior) : northCapHomeomorph ε hε x = sphereCap ε x :=
  northCapHomeomorph_north ε hε (northExterior_mem_northRegion hx)

theorem northCapHomeomorph_eventuallyEq (ε : ℝ) (hε : 0 < ε) {x : Sphere 3}
    (hx : x ∈ northRegion) :
    (northCapHomeomorph ε hε : Sphere 3 → Sphere 3) =ᶠ[𝓝 x] sphereCap ε := by
  filter_upwards [isOpen_northRegion.mem_nhds hx] with y hy
  exact northCapHomeomorph_north ε hε hy

theorem isLocalDiffeomorphAt_northCapHomeomorph (ε : ℝ) (hε : 0 < ε) {x : Sphere 3}
    (hx : (1 / 2 : ℝ) < x.val 0) :
    IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (northCapHomeomorph ε hε) x := by
  let U : Set (Sphere 3) := {y | (1 / 2 : ℝ) < y.val 0}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_sourceHead
  let C := Wikipedia.SmoothSixDPoincare.PartialChart.restrictSource
    (sphereCapCoordinates ε hε.ne') hU
  refine ⟨C, ?_, ?_⟩
  · change x ∈ (sphereCapCoordinates ε hε.ne').source ∩ U
    refine ⟨?_, hx⟩
    rw [sphereCapCoordinates_source]
    change 0 < x.val 0
    linarith
  · intro y hy
    change y ∈ (sphereCapCoordinates ε hε.ne').source ∩ U at hy
    exact northCapHomeomorph_upper ε hε y hy.2.le

def southCapHomeomorph (ε : ℝ) (hε : 0 < ε) : Sphere 3 ≃ₜ Sphere 3 :=
  reflectHeadDiffeomorph.toHomeomorph.trans (northCapHomeomorph ε hε)

theorem southCapHomeomorph_apply (ε : ℝ) (hε : 0 < ε) (x : Sphere 3) :
    southCapHomeomorph ε hε x = northCapHomeomorph ε hε (reflectHead x) := rfl

theorem southCapHomeomorph_south (ε : ℝ) (hε : 0 < ε) {x : Sphere 3}
    (hx : x ∈ southRegion) :
    southCapHomeomorph ε hε x = sphereCap ε (reflectHead x) :=
  northCapHomeomorph_north ε hε (reflectHead_mem_northRegion hx)

theorem southCapHomeomorph_exterior (ε : ℝ) (hε : 0 < ε) {x : Sphere 3}
    (hx : x ∈ southExterior) :
    southCapHomeomorph ε hε x = sphereCap ε (reflectHead x) :=
  southCapHomeomorph_south ε hε (southExterior_mem_southRegion hx)

theorem southCapHomeomorph_eventuallyEq (ε : ℝ) (hε : 0 < ε) {x : Sphere 3}
    (hx : x ∈ southRegion) :
    (southCapHomeomorph ε hε : Sphere 3 → Sphere 3) =ᶠ[𝓝 x] (sphereCap ε ∘ reflectHead) := by
  filter_upwards [isOpen_southRegion.mem_nhds hx] with y hy
  exact southCapHomeomorph_south ε hε hy

theorem isLocalDiffeomorphAt_southCapHomeomorph (ε : ℝ) (hε : 0 < ε) {x : Sphere 3}
    (hx : x ∈ southRegion) :
    IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (southCapHomeomorph ε hε) x := by
  have hr : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ reflectHead x :=
    ⟨reflectHeadDiffeomorph.toPartialDiffeomorph, mem_univ _, fun _ _ ↦ rfl⟩
  exact hr.comp (𝓡 3) (Sphere 3) (isLocalDiffeomorphAt_northCapHomeomorph ε hε
    (half_lt_head_of_northRegion (reflectHead_mem_northRegion hx)))

end NoExoticSixSphere.SphereSumNeck
