import Wikipedia.NoExoticSixSphere.SphereCylinderPoles

/-!
# The actual open caps outside the closed time cylinder

The lower cap is the negative-head hemisphere; the upper cap is the region
where the head exceeds the tail norm. In the genuine cylinder coordinates
these are exactly times below zero and above one, respectively.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereCylinder

def lowerCap (n : ℕ) : Set (Sphere (n + 1)) := {y | y.val 0 < 0}

def upperCap (n : ℕ) : Set (Sphere (n + 1)) := {y | ‖tail n y.val‖ < y.val 0}

def capRegion (n : ℕ) (b : Bool) : Set (Sphere (n + 1)) :=
  if b then upperCap n else lowerCap n

theorem isOpen_lowerCap (n : ℕ) : IsOpen (lowerCap n) := by
  have hh : Continuous (fun y : Sphere (n + 1) ↦ y.val 0) :=
    ((join n).symm.continuous.comp continuous_subtype_val).fst
  exact isOpen_lt hh continuous_const

theorem isOpen_upperCap (n : ℕ) : IsOpen (upperCap n) := by
  have hh : Continuous (fun y : Sphere (n + 1) ↦ y.val 0) :=
    ((join n).symm.continuous.comp continuous_subtype_val).fst
  exact isOpen_lt (((tail n).continuous.comp continuous_subtype_val).norm) hh

theorem isOpen_capRegion (n : ℕ) (b : Bool) : IsOpen (capRegion n b) := by
  cases b
  · exact isOpen_lowerCap n
  · exact isOpen_upperCap n

theorem endPole_mem_capRegion (n : ℕ) (b : Bool) : endPole n b ∈ capRegion n b := by
  cases b
  · change (endPole n false).val 0 < 0
    norm_num [endPole_head]
  · change ‖tail n (endPole n true).val‖ < (endPole n true).val 0
    norm_num [tail_endPole, endPole_head]

theorem point_mem_lowerCap_iff (n : ℕ) (p : ℝ × Sphere n) :
    point n p ∈ lowerCap n ↔ p.1 < 0 := by
  change (point n p).val 0 < 0 ↔ p.1 < 0
  rw [point_head]
  have hp := inv_pos.mpr (norm_pos_iff.mpr (vector_ne_zero n p))
  simpa only [mul_zero] using
    (mul_lt_mul_iff_right₀ hp : ‖vector n p‖⁻¹ * p.1 < ‖vector n p‖⁻¹ * 0 ↔ p.1 < 0)

theorem point_mem_upperCap_iff (n : ℕ) (p : ℝ × Sphere n) :
    point n p ∈ upperCap n ↔ 1 < p.1 := by
  change ‖tail n (point n p).val‖ < (point n p).val 0 ↔ 1 < p.1
  rw [norm_tail_point, point_head]
  have hp := inv_pos.mpr (norm_pos_iff.mpr (vector_ne_zero n p))
  simpa only [mul_one] using
    (mul_lt_mul_iff_right₀ hp : ‖vector n p‖⁻¹ * 1 < ‖vector n p‖⁻¹ * p.1 ↔ 1 < p.1)

theorem disjoint_caps (n : ℕ) : Disjoint (lowerCap n) (upperCap n) := by
  apply disjoint_left.mpr
  intro y hl hu
  exact not_lt_of_ge (norm_nonneg (tail n y.val)) (lt_trans hu hl)

theorem pairwise_disjoint_capRegion (n : ℕ) : Pairwise (Disjoint on (capRegion n)) := by
  intro a b hne
  cases a <;> cases b
  · exact False.elim (hne rfl)
  · exact disjoint_caps n
  · exact (disjoint_caps n).symm
  · exact False.elim (hne rfl)

theorem capRegion_disjoint_middle (n : ℕ) (b : Bool) :
    Disjoint (capRegion n b)
      (point n '' (Icc (0 : ℝ) 1 ×ˢ (univ : Set (Sphere n)))) := by
  apply disjoint_left.mpr
  rintro y hy ⟨p, hp, rfl⟩
  cases b
  · exact not_lt_of_ge hp.1.1 ((point_mem_lowerCap_iff n p).mp hy)
  · exact not_lt_of_ge hp.1.2 ((point_mem_upperCap_iff n p).mp hy)

end NoExoticSixSphere.SphereCylinder
