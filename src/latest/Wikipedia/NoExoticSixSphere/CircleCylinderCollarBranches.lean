import Wikipedia.NoExoticSixSphere.CircleCylinderSeam

/-!
# Literal height-coordinate branches near the two circle poles

The two branches are `(±sqrt(1-s²), s)`, with seam time exactly `s`.
They are continuous on every closed interval of radius less than one,
have opposite nonzero first coordinates, and recover any circle point
in that time band according to the sign of its first coordinate.
-/

noncomputable section

open Set Function

namespace NoExoticSixSphere.CircleCylinder

def branchRadius (s : ℝ) : ℝ := Real.sqrt (1 - s ^ 2)

def branchVector (left : Bool) (s : ℝ) : V :=
  WithLp.toLp 2 (Fin.cons (if left then branchRadius s else -branchRadius s)
    (fun _ : Fin 1 ↦ s))

theorem continuous_branchRadius : Continuous branchRadius :=
  (continuous_const.sub (continuous_id.pow 2)).sqrt

theorem continuous_branchVector (left : Bool) : Continuous (branchVector left) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · cases left
    · exact continuous_branchRadius.neg
    · exact continuous_branchRadius
  · exact continuous_id

theorem interval_sq_lt_one {ε : ℝ} (hε : ε < 1) (s : Icc (-ε) ε) : s.val ^ 2 < 1 := by
  have hlo : 0 < 1 + s.val := by have h := s.property.1; linarith
  have hhi : 0 < 1 - s.val := by have h := s.property.2; linarith
  nlinarith [mul_pos hlo hhi]

theorem branchRadius_pos {ε : ℝ} (hε : ε < 1) (s : Icc (-ε) ε) :
    0 < branchRadius s.val := Real.sqrt_pos.mpr (sub_pos.mpr (interval_sq_lt_one hε s))

theorem norm_branchVector {ε : ℝ} (hε : ε < 1) (left : Bool) (s : Icc (-ε) ε) :
    ‖branchVector left s.val‖ = 1 := by
  have hs := Real.sq_sqrt (le_of_lt (sub_pos.mpr (interval_sq_lt_one hε s)))
  have hn : ‖branchVector left s.val‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
    simp only [branchVector, Fin.cons_zero, Fin.cons_succ, Fin.sum_univ_succ,
      Fin.sum_univ_zero, add_zero]
    cases left <;> simp only [Bool.false_eq_true, ↓reduceIte, neg_sq]
    · exact by change (Real.sqrt (1 - s.val ^ 2)) ^ 2 + s.val ^ 2 = 1; linarith
    · exact by change (Real.sqrt (1 - s.val ^ 2)) ^ 2 + s.val ^ 2 = 1; linarith
  nlinarith [norm_nonneg (branchVector left s.val)]

def collarBranch {ε : ℝ} (hε : ε < 1) (left : Bool) (s : Icc (-ε) ε) : Sphere 1 :=
  ⟨branchVector left s.val, by
    rw [Metric.mem_sphere, dist_zero_right]
    exact norm_branchVector hε left s⟩

theorem continuous_collarBranch {ε : ℝ} (hε : ε < 1) (left : Bool) :
    Continuous (collarBranch hε left) :=
  ((continuous_branchVector left).comp continuous_subtype_val).subtype_mk _

theorem collarBranch_head {ε : ℝ} (hε : ε < 1) (left : Bool) (s : Icc (-ε) ε) :
    (collarBranch hε left s).val 0 = if left then branchRadius s.val else -branchRadius s.val := rfl

theorem seam_collarBranch {ε : ℝ} (hε : ε < 1) (left : Bool) (s : Icc (-ε) ε) :
    seam (collarBranch hε left s) = s.val := rfl

def branchClock (left : Bool) (s : ℝ) : ℝ :=
  (1 - (if left then branchRadius s else -branchRadius s)) / 2

theorem continuous_branchClock (left : Bool) : Continuous (branchClock left) := by
  cases left
  · exact (continuous_const.sub continuous_branchRadius.neg).div_const 2
  · exact (continuous_const.sub continuous_branchRadius).div_const 2

theorem clock_collarBranch {ε : ℝ} (hε : ε < 1) (left : Bool) (s : Icc (-ε) ε) :
    clock (collarBranch hε left s) = branchClock left s.val := by
  rw [clock_apply]
  rfl

theorem branchClock_zero (left : Bool) : branchClock left 0 = if left then 0 else 1 := by
  cases left <;> norm_num [branchClock, branchRadius]

theorem collarBranch_zero {ε : ℝ} (hε : ε < 1) (h0 : 0 ∈ Icc (-ε) ε) (left : Bool) :
    collarBranch hε left ⟨0, h0⟩ = SphereCylinder.endPole 0 left := by
  apply Subtype.ext
  ext i
  fin_cases i
  · change (if left then branchRadius 0 else -branchRadius 0) = if left then 1 else -1
    norm_num [branchRadius]
  · rfl

theorem head_sq_add_seam_sq (c : Sphere 1) : c.val 0 ^ 2 + seam c ^ 2 = 1 := by
  have h : ‖c.val‖ ^ 2 = 1 := by rw [ClosedHemisphere.unit_norm]; norm_num
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  exact h

theorem collarBranch_left_inverse {ε : ℝ} (hε : ε < 1) (c : Sphere 1)
    (hc : seam c ∈ Icc (-ε) ε) (hh : 0 ≤ c.val 0) :
    collarBranch hε true ⟨seam c, hc⟩ = c := by
  have hs : 1 - seam c ^ 2 = c.val 0 ^ 2 := by linarith [head_sq_add_seam_sq c]
  apply Subtype.ext
  ext i
  fin_cases i
  · change Real.sqrt (1 - seam c ^ 2) = c.val 0
    rw [hs, Real.sqrt_sq hh]
  · rfl

theorem collarBranch_right_inverse {ε : ℝ} (hε : ε < 1) (c : Sphere 1)
    (hc : seam c ∈ Icc (-ε) ε) (hh : c.val 0 ≤ 0) :
    collarBranch hε false ⟨seam c, hc⟩ = c := by
  have hs : 1 - seam c ^ 2 = (-c.val 0) ^ 2 := by nlinarith [head_sq_add_seam_sq c]
  apply Subtype.ext
  ext i
  fin_cases i
  · change -Real.sqrt (1 - seam c ^ 2) = c.val 0
    rw [hs, Real.sqrt_sq (neg_nonneg.mpr hh), neg_neg]
  · rfl

theorem collarBranch_left_ne_right {ε : ℝ} (hε : ε < 1) (s t : Icc (-ε) ε) :
    collarBranch hε true s ≠ collarBranch hε false t := by
  intro h
  have he := congrArg (fun c : Sphere 1 ↦ c.val 0) h
  change branchRadius s.val = -branchRadius t.val at he
  linarith [branchRadius_pos hε s, branchRadius_pos hε t]

end NoExoticSixSphere.CircleCylinder
