import StackExchange.Puzzling139335.SegmentCrossing.Defs
import StackExchange.Puzzling139335.SegmentCrossing.Algebra

/-! Two local interior half-balls overlap if their strict sides share a direction. -/

open Set

namespace Puzzling139335.SegmentCrossing

noncomputable section

/-- The determinant with a fixed first argument, as a continuous linear functional. -/
def detForm (u : Plane) : Plane →L[ℝ] ℝ :=
  u 0 • EuclideanSpace.proj 1 - u 1 • EuclideanSpace.proj 0

@[simp] theorem detForm_apply (u w : Plane) : detForm u w = det u w := rfl

@[simp] theorem detForm_neg (u : Plane) : detForm (-u) = -detForm u := by
  ext w
  simp only [detForm_apply, neg_apply, det, PiLp.neg_apply]
  ring

/-- Independent determinant functionals can take any prescribed pair of values. -/
theorem exists_detForm_eq_pair {u v : Plane} (h : det u v ≠ 0) (a b : ℝ) :
    ∃ w : Plane, detForm u w = a ∧ detForm v w = b := by
  refine ⟨(det u v)⁻¹ • (a • v - b • u), ?_, ?_⟩
  · simp only [detForm_apply, det_smul_right, det_sub_right, det_self]
    field_simp
    ring
  · simp only [detForm_apply, det_smul_right, det_sub_right, det_self, det_swap u v]
    field_simp
    ring

/-- A nonzero determinant certifies that the first determinant form is onto. -/
theorem detForm_surjective_of_det_ne_zero {u v : Plane} (h : det u v ≠ 0) :
    Function.Surjective (detForm u) := by
  intro a
  obtain ⟨w, hw, _⟩ := exists_detForm_eq_pair h a 0
  exact ⟨w, hw⟩

/-- Move a sufficiently small positive distance in a direction entering both collars. -/
theorem HasInteriorHalfBall.inter_nonempty
    {P Q : Set Plane} {x : Plane} {f g : Plane →L[ℝ] ℝ}
    (hP : HasInteriorHalfBall P x f) (hQ : HasInteriorHalfBall Q x g)
    (hdir : ∃ w : Plane, 0 < f w ∧ 0 < g w) :
    (interior P ∩ interior Q).Nonempty := by
  obtain ⟨r, hr, hPr⟩ := hP
  obtain ⟨s, hs, hQs⟩ := hQ
  obtain ⟨w, hfw, hgw⟩ := hdir
  let t : ℝ := min r s / (‖w‖ + 1)
  have hden : 0 < ‖w‖ + 1 := by positivity
  have ht : 0 < t := div_pos (lt_min hr hs) hden
  have hsmall : ‖t • w‖ < min r s := by
    calc
      ‖t • w‖ = t * ‖w‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      _ < t * (‖w‖ + 1) := mul_lt_mul_of_pos_left (lt_add_one _) ht
      _ = min r s := div_mul_cancel₀ _ (ne_of_gt hden)
  have hdist : dist (x + t • w) x < min r s := by
    simpa only [dist_eq_norm, add_sub_cancel_left] using hsmall
  have hf : f x < f (x + t • w) := by
    simp only [map_add, map_smul, smul_eq_mul]
    exact lt_add_of_pos_right _ (mul_pos ht hfw)
  have hg : g x < g (x + t • w) := by
    simp only [map_add, map_smul, smul_eq_mul]
    exact lt_add_of_pos_right _ (mul_pos ht hgw)
  exact ⟨x + t • w,
    hPr ⟨lt_of_lt_of_le hdist (min_le_left _ _), hf⟩,
    hQs ⟨lt_of_lt_of_le hdist (min_le_right _ _), hg⟩⟩

/-- Disjoint tile interiors cannot have half-ball collars entering a common direction. -/
theorem not_disjoint_interiors_of_halfBalls
    {P Q : Set Plane} {x : Plane} {f g : Plane →L[ℝ] ℝ}
    (hP : HasInteriorHalfBall P x f) (hQ : HasInteriorHalfBall Q x g)
    (hdir : ∃ w : Plane, 0 < f w ∧ 0 < g w) :
    ¬ Disjoint (interior P) (interior Q) :=
  (hP.inter_nonempty hQ hdir).not_disjoint

end

end Puzzling139335.SegmentCrossing
