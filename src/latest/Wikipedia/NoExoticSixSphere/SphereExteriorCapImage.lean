import Wikipedia.NoExoticSixSphere.SphereCapPinchCoordinates
import Wikipedia.NoExoticSixSphere.SphereNeckCapSeparation
import Wikipedia.NoExoticSixSphere.SpherePositiveRadialCoordinates

/-!
# The exterior cap parametrizes the complement of the removed source disk

The cap chart covers the entire original sphere except its reference
center. Its part lying in the neck region maps exactly to the punctured
reference-chart ball of radius four times the cap scale. This includes
the exterior pole and retains the exact boundary radius.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

theorem sphereCapCoordinates_target (ε : ℝ) (hε : ε ≠ 0) :
    (sphereCapCoordinates ε hε).target = {sourceChart 0}ᶜ := by
  ext x
  change (x ∈ sourceComplementChart.target ∧
    (sourceComplementChart.symm x ∈ (univ : Set (Vector 3)) ∧
      (capScaling ε hε).symm (sourceComplementChart.symm x) ∈ (univ : Set (Vector 3)))) ↔ _
  rw [sourceComplementChart_target]
  simp only [mem_univ, and_true]

theorem sphereCap_ne_sourceChart_zero {ε : ℝ} (hε : ε ≠ 0) {x : Sphere 3}
    (hx : 0 < x.val 0) : sphereCap ε x ≠ sourceChart 0 := by
  have hs : x ∈ (sphereCapCoordinates ε hε).source := by rwa [sphereCapCoordinates_source]
  have ht := (sphereCapCoordinates ε hε).map_source hs
  rwa [sphereCapCoordinates_target] at ht

def removedSourceDisk (ε : ℝ) : Set (Sphere 3) := sourceChart '' ball (0 : Vector 3) (ε * 4)

theorem sourceChart_zero_mem_removed {ε : ℝ} (hε : 0 < ε) :
    sourceChart 0 ∈ removedSourceDisk ε := ⟨0, mem_ball_self (by positivity), rfl⟩

theorem sphereCap_mem_removed_iff {ε : ℝ} (hε : 0 < ε) {x : Sphere 3}
    (hx : 0 < x.val 0) : sphereCap ε x ∈ removedSourceDisk ε ↔ x ∈ neckRegion := by
  constructor
  · rintro ⟨v, hv, he⟩
    have hv0 : v ≠ 0 := by
      intro hv0
      subst v
      exact sphereCap_ne_sourceChart_zero hε.ne' hx he.symm
    let s := (positiveRadialInverse v).2
    let t := ‖v‖ / ε
    have ht : 0 < t := div_pos (norm_pos_iff.mpr hv0) hε
    have ht4 : t < 4 := by
      apply (div_lt_iff₀ hε).mpr
      simpa only [mem_ball_zero_iff, mul_comm] using hv
    have heps : ε * t = ‖v‖ := by dsimp [t]; field_simp
    have hvec : (ε * t) • s.val = v := by
      rw [heps]
      exact positiveRadialInverse_right v hv0
    exact sphereCap_ray_implies_neckRegion hε ht ht4 s hx
      (he.symm.trans (congrArg sourceChart hvec.symm))
  · intro hn
    let q := SphereCylinder.inverse 2 x
    have hband := neckRegion_mem_band hn
    have ht : 0 < q.1 := div_pos hx (norm_pos_iff.mpr hband)
    have ht4 := (neckRegion_time hn).2
    refine ⟨(ε * q.1) • q.2.val, ?_, ?_⟩
    · rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hε ht),
        ClosedHemisphere.unit_norm, mul_one]
      exact mul_lt_mul_of_pos_left ht4 hε
    · have hc := sphereCap_cylinder hε q.1 q.2 ht
      rw [SphereCylinder.point_inverse 2 x hband] at hc
      exact hc.symm

end NoExoticSixSphere.SphereSumNeck
