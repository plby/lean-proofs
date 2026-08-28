import Wikipedia.HopfProblem.StandardSixSphereCircleModelTubeHomeomorph
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# The frontier of the original equatorial tube

For `0 < r < 1`, the closure of the open normal-radius tube is the closed
tube, its interior is the open tube, and both frontiers are the literal
radius-`r` level in the standard six-sphere.  All closure, interior, and
frontier operations use the original sphere topology.

The explicit radius-one tube chart makes its normal projection an open
map.  The conclusions follow from the corresponding Euclidean ball
identities, without a recognition or collar hypothesis.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.StandardSixSphereCircleModel.Tube

theorem continuous_normal_on_openTube (r : ℝ) :
    Continuous (fun p : ↥(openTube r) => normal p.val.val) :=
  continuous_normal.comp (continuous_subtype_val.comp continuous_subtype_val)

/-- The normal projection is open on the actual tube, by its explicit product chart. -/
theorem isOpenMap_normal_on_openTube (r : ℝ) (hr1 : r ≤ 1) :
    IsOpenMap (fun p : ↥(openTube r) => normal p.val.val) := by
  have h : IsOpenMap (fun p : ↥(openTube r) =>
      ((openHomeomorph r hr1).symm p).2.val) :=
    (normalBall r).isOpen.isOpenMap_subtype_val.comp
      (isOpenMap_snd.comp (openHomeomorph r hr1).symm.isOpenMap)
  simpa only [openHomeomorph_symm_snd_val] using h

/-- Closure is taken in the original standard six-sphere. -/
theorem closure_openTube (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    closure (openTube r : Set Sphere) = closedTube r := by
  apply Subset.antisymm
  · apply closure_minimal
    · intro p hp
      exact show ‖normal p.val‖ ≤ r from le_of_lt hp
    · exact isClosed_closedTube r
  · intro p hp
    change ‖normal p.val‖ ≤ r at hp
    let q : ↥(openTube 1) := ⟨p, lt_of_le_of_lt hp hr1⟩
    have hpre : (Subtype.val : ↥(openTube 1) → Sphere) ⁻¹' (openTube r : Set Sphere) =
        (fun z : ↥(openTube 1) => normal z.val.val) ⁻¹' Metric.ball (0 : Normal) r := by
      ext z
      change ‖normal z.val.val‖ < r ↔ dist (normal z.val.val) 0 < r
      rw [dist_zero_right]
    have hq : q ∈ closure
        ((fun z : ↥(openTube 1) => normal z.val.val) ⁻¹' Metric.ball (0 : Normal) r) := by
      rw [← (isOpenMap_normal_on_openTube 1 le_rfl).preimage_closure_eq_closure_preimage
        (continuous_normal_on_openTube 1), closure_ball (0 : Normal) hr.ne']
      simpa only [mem_preimage, Metric.mem_closedBall, dist_zero_right] using hp
    have hi : (Subtype.val : ↥(openTube 1) → Sphere) ⁻¹'
        closure (openTube r : Set Sphere) =
        closure ((Subtype.val : ↥(openTube 1) → Sphere) ⁻¹' (openTube r : Set Sphere)) :=
      (openTube 1).isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
        continuous_subtype_val _
    rw [← hpre, ← hi] at hq
    exact hq

/-- The closed tube has precisely the original open tube as its interior. -/
theorem interior_closedTube (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    interior (closedTube r) = (openTube r : Set Sphere) := by
  apply Subset.antisymm
  · intro p hp
    have hpmem : p ∈ closedTube r := interior_subset hp
    change ‖normal p.val‖ ≤ r at hpmem
    let q : ↥(openTube 1) := ⟨p, lt_of_le_of_lt hpmem hr1⟩
    have hq : q ∈ (Subtype.val : ↥(openTube 1) → Sphere) ⁻¹'
        interior (closedTube r) := hp
    have hi : (Subtype.val : ↥(openTube 1) → Sphere) ⁻¹'
        interior (closedTube r) =
        interior ((Subtype.val : ↥(openTube 1) → Sphere) ⁻¹' closedTube r) :=
      (openTube 1).isOpen.isOpenMap_subtype_val.preimage_interior_eq_interior_preimage
        continuous_subtype_val _
    rw [hi] at hq
    have hpre : (Subtype.val : ↥(openTube 1) → Sphere) ⁻¹' closedTube r =
        (fun z : ↥(openTube 1) => normal z.val.val) ⁻¹' Metric.closedBall (0 : Normal) r := by
      ext z
      change ‖normal z.val.val‖ ≤ r ↔ dist (normal z.val.val) 0 ≤ r
      rw [dist_zero_right]
    rw [hpre, ← (isOpenMap_normal_on_openTube 1 le_rfl).preimage_interior_eq_interior_preimage
      (continuous_normal_on_openTube 1), interior_closedBall (0 : Normal) hr.ne'] at hq
    change ‖normal p.val‖ < r
    simpa only [mem_preimage, Metric.mem_ball, dist_zero_right] using hq
  · apply interior_maximal
    · intro p hp
      exact show ‖normal p.val‖ ≤ r from le_of_lt hp
    · exact (openTube r).isOpen

/-- The closed tube's frontier is its literal normal-radius level set. -/
theorem frontier_closedTube (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    frontier (closedTube r) = {p : Sphere | ‖normal p.val‖ = r} := by
  rw [frontier, (isClosed_closedTube r).closure_eq, interior_closedTube r hr hr1]
  ext p
  change (‖normal p.val‖ ≤ r ∧ ¬ ‖normal p.val‖ < r) ↔ ‖normal p.val‖ = r
  simp only [not_lt, le_antisymm_iff]

/-- The original open tube has the same frontier as the closed tube. -/
theorem frontier_openTube (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    frontier (openTube r : Set Sphere) = {p : Sphere | ‖normal p.val‖ = r} := by
  rw [frontier, closure_openTube r hr hr1, (openTube r).isOpen.interior_eq]
  ext p
  change (‖normal p.val‖ ≤ r ∧ ¬ ‖normal p.val‖ < r) ↔ ‖normal p.val‖ = r
  simp only [not_lt, le_antisymm_iff]

end Wikipedia.HopfProblem.StandardSixSphereCircleModel.Tube
