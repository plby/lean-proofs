import Mathlib

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Pushing a cube coefficient to a forward face
-/

namespace Erdos394

/-- Maximum nonnegative time allowed by one coordinate `x + t*a`, capped by
an external time `z` in the stationary case. -/
noncomputable def forwardCap (x a z : ℝ) : ℝ :=
  if 0 < a then (1 - x) / a else if a < 0 then x / (-a) else z

lemma forwardCap_nonneg {x a z : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hz : 0 ≤ z) :
    0 ≤ forwardCap x a z := by
  unfold forwardCap
  split_ifs with ha ha
  · exact div_nonneg (sub_nonneg.mpr hx1) ha.le
  · exact div_nonneg hx0 (neg_nonneg.mpr ha.le)
  · exact hz

lemma add_mul_mem_Icc_of_le_forwardCap {x a z t : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hz : 0 ≤ z)
    (ht0 : 0 ≤ t) (ht : t ≤ forwardCap x a z) :
    0 ≤ x + t * a ∧ x + t * a ≤ 1 := by
  unfold forwardCap at ht
  split_ifs at ht with ha ha
  · constructor
    · positivity
    · apply (le_div_iff₀ ha).mp at ht
      nlinarith
  · have hneg : a < 0 := ha
    constructor
    · have hpos : 0 < -a := neg_pos.mpr hneg
      apply (le_div_iff₀ hpos).mp at ht
      nlinarith
    · have hta : t * a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 hneg.le
      linarith
  · have ha0 : a = 0 := by linarith
    simp [ha0, hx0, hx1]

lemma add_forwardCap_mul_eq_boundary_or_stationary {x a z : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x + forwardCap x a z * a = 0 ∨
      x + forwardCap x a z * a = 1 ∨
      (a = 0 ∧ forwardCap x a z = z) := by
  unfold forwardCap
  split_ifs with ha ha
  · right; left
    field_simp [ne_of_gt ha]
    ring
  · left
    field_simp [ne_of_lt ha]
    ring
  · right; right
    have ha0 : a = 0 := by linarith
    exact ⟨ha0, rfl⟩

/-- Starting from `(x,y,z)∈[0,1]³`, move in direction `(a,b,-1)` until either
the last coordinate reaches zero or one of the first two reaches a cube face. -/
theorem exists_forward_face {x y z a b : ℝ}
    (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1)
    (hz : 0 ≤ z ∧ z ≤ 1) :
    ∃ t : ℝ,
      0 ≤ t ∧ t ≤ z ∧
      (0 ≤ x + t * a ∧ x + t * a ≤ 1) ∧
      (0 ≤ y + t * b ∧ y + t * b ≤ 1) ∧
      (t = z ∨ x + t * a = 0 ∨ x + t * a = 1 ∨
        y + t * b = 0 ∨ y + t * b = 1) := by
  let ca := forwardCap x a z
  let cb := forwardCap y b z
  let t := min z (min ca cb)
  have hca0 : 0 ≤ ca := forwardCap_nonneg hx.1 hx.2 hz.1
  have hcb0 : 0 ≤ cb := forwardCap_nonneg hy.1 hy.2 hz.1
  have ht0 : 0 ≤ t := by exact le_min hz.1 (le_min hca0 hcb0)
  have htz : t ≤ z := min_le_left _ _
  have htca : t ≤ ca := (min_le_right _ _).trans (min_le_left _ _)
  have htcb : t ≤ cb := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨t, ht0, htz,
    add_mul_mem_Icc_of_le_forwardCap hx.1 hx.2 hz.1 ht0 htca,
    add_mul_mem_Icc_of_le_forwardCap hy.1 hy.2 hz.1 ht0 htcb, ?_⟩
  rcases min_choice z (min ca cb) with ht | ht
  · exact Or.inl ht
  · rcases min_choice ca cb with hca | hcb
    · have htcaeq : t = ca := ht.trans hca
      rcases add_forwardCap_mul_eq_boundary_or_stationary (z := z) hx.1 hx.2 with h0 | h1 | ⟨ha0, hcaz⟩
      · exact Or.inr (Or.inl (by simpa [htcaeq] using h0))
      · exact Or.inr (Or.inr (Or.inl (by simpa [htcaeq] using h1)))
      · exact Or.inl (htcaeq.trans hcaz)
    · have htcbeq : t = cb := ht.trans hcb
      rcases add_forwardCap_mul_eq_boundary_or_stationary (z := z) hy.1 hy.2 with h0 | h1 | ⟨hb0, hcbz⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa [htcbeq] using h0))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (by simpa [htcbeq] using h1))))
      · exact Or.inl (htcbeq.trans hcbz)

end Erdos394
