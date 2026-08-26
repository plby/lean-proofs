import ErdosProblems.Erdos633.DirectedCrossing

/-!
# The crossing number of an oriented triangle

The algebraic crossing formula is proved by the signs of the three vertex
heights and the three determinants. This supplies the triangle indicator
without an imported Jordan-curve or winding-number theorem.
-/

namespace Erdos633

theorem planeDet_neg_neg (a b : ℂ) : planeDet (-a) (-b) = planeDet a b := by
  simp [planeDet]

theorem planeDet_swap (a b : ℂ) : planeDet b a = -planeDet a b := by
  unfold planeDet
  ring

theorem planeDet_weighted_im (a b c : ℂ) :
    planeDet b c * a.im + planeDet c a * b.im + planeDet a b * c.im = 0 := by
  unfold planeDet
  ring

theorem positiveStep_of_pos {r : ℝ} (hr : 0 < r) : positiveStep r = 1 := if_pos hr

theorem positiveStep_of_nonpos {r : ℝ} (hr : r ≤ 0) : positiveStep r = 0 :=
  if_neg (not_lt_of_ge hr)

theorem positiveStep_neg {r : ℝ} (hr : r ≠ 0) :
    positiveStep (-r) = 1 - positiveStep r := by
  rcases lt_or_gt_of_ne hr with h | h
  · rw [positiveStep_of_pos (neg_pos.mpr h), positiveStep_of_nonpos h.le]
    norm_num
  · rw [positiveStep_of_nonpos (neg_nonpos.mpr h.le), positiveStep_of_pos h]
    norm_num

theorem rayEdgeCrossing_of_below {a b : ℂ} (ha : a.im ≤ 0) (hb : b.im ≤ 0) :
    rayEdgeCrossing a b = 0 := by
  rw [rayEdgeCrossing, positiveStep_of_nonpos ha, positiveStep_of_nonpos hb]
  ring

theorem rayEdgeCrossing_of_above {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im) :
    rayEdgeCrossing a b = 0 := by
  rw [rayEdgeCrossing, positiveStep_of_pos ha, positiveStep_of_pos hb]
  ring

theorem rayEdgeCrossing_of_up {a b : ℂ} (ha : a.im ≤ 0) (hb : 0 < b.im) :
    rayEdgeCrossing a b = positiveStep (planeDet a b) := by
  have h : 0 < b.im - a.im := by linarith
  rw [rayEdgeCrossing, positiveStep_of_nonpos ha, positiveStep_of_pos hb,
    mul_comm (planeDet a b), positiveStep_pos_mul _ _ h]
  ring

theorem rayEdgeCrossing_of_down {a b : ℂ} (ha : 0 < a.im) (hb : b.im ≤ 0) :
    rayEdgeCrossing a b = -positiveStep (-planeDet a b) := by
  rw [rayEdgeCrossing_reverse, rayEdgeCrossing_of_up hb ha, planeDet_swap]

theorem rayEdgeCrossing_neg (a b : ℂ) (ha : a.im ≠ 0) (hb : b.im ≠ 0)
    (hd : planeDet a b ≠ 0) :
    rayEdgeCrossing (-a) (-b) =
      rayEdgeCrossing a b - (positiveStep b.im - positiveStep a.im) := by
  by_cases he : b.im = a.im
  · simp [rayEdgeCrossing, he]
  · have hp : planeDet a b * (b.im - a.im) ≠ 0 := mul_ne_zero hd (sub_ne_zero.mpr he)
    have hprod : planeDet (-a) (-b) * ((-b).im - (-a).im) =
        -(planeDet a b * (b.im - a.im)) := by
      rw [planeDet_neg_neg]
      simp only [Complex.neg_im]
      ring
    rw [rayEdgeCrossing, rayEdgeCrossing, hprod, positiveStep_neg hp]
    simp only [Complex.neg_im, positiveStep_neg ha, positiveStep_neg hb]
    ring

noncomputable def rayTriangleCrossing (a b c : ℂ) : ℤ :=
  rayEdgeCrossing a b + rayEdgeCrossing b c + rayEdgeCrossing c a

noncomputable def triangleDetSign (a b c : ℂ) : ℤ :=
  if 0 < planeDet a b ∧ 0 < planeDet b c ∧ 0 < planeDet c a then 1
  else if planeDet a b < 0 ∧ planeDet b c < 0 ∧ planeDet c a < 0 then -1 else 0

theorem rayTriangleCrossing_rotate (a b c : ℂ) :
    rayTriangleCrossing b c a = rayTriangleCrossing a b c := by
  unfold rayTriangleCrossing
  ring

theorem triangleDetSign_rotate (a b c : ℂ) :
    triangleDetSign b c a = triangleDetSign a b c := by
  have hp : (0 < planeDet b c ∧ 0 < planeDet c a ∧ 0 < planeDet a b) ↔
      (0 < planeDet a b ∧ 0 < planeDet b c ∧ 0 < planeDet c a) := by tauto
  have hn : (planeDet b c < 0 ∧ planeDet c a < 0 ∧ planeDet a b < 0) ↔
      (planeDet a b < 0 ∧ planeDet b c < 0 ∧ planeDet c a < 0) := by tauto
  simp only [triangleDetSign, hp, hn]

theorem rayTriangleCrossing_neg (a b c : ℂ)
    (ha : a.im ≠ 0) (hb : b.im ≠ 0) (hc : c.im ≠ 0)
    (hab : planeDet a b ≠ 0) (hbc : planeDet b c ≠ 0) (hca : planeDet c a ≠ 0) :
    rayTriangleCrossing (-a) (-b) (-c) = rayTriangleCrossing a b c := by
  simp only [rayTriangleCrossing, rayEdgeCrossing_neg a b ha hb hab,
    rayEdgeCrossing_neg b c hb hc hbc, rayEdgeCrossing_neg c a hc ha hca]
  ring

theorem triangleDetSign_neg (a b c : ℂ) :
    triangleDetSign (-a) (-b) (-c) = triangleDetSign a b c := by
  simp only [triangleDetSign, planeDet_neg_neg]

theorem rayTriangleCrossing_eq_detSign_one_above {a b c : ℂ}
    (ha : a.im < 0) (hb : b.im < 0) (hc : 0 < c.im)
    (hbc : planeDet b c ≠ 0) (hca : planeDet c a ≠ 0) :
    rayTriangleCrossing a b c = triangleDetSign a b c := by
  have hw := planeDet_weighted_im a b c
  rw [rayTriangleCrossing, rayEdgeCrossing_of_below ha.le hb.le,
    rayEdgeCrossing_of_up hb.le hc, rayEdgeCrossing_of_down hc ha.le, zero_add]
  by_cases hp : 0 < planeDet b c
  · by_cases hq : 0 < planeDet c a
    · have hab : 0 < planeDet a b := by
        have h1 := mul_neg_of_pos_of_neg hp ha
        have h2 := mul_neg_of_pos_of_neg hq hb
        have h3 : 0 < planeDet a b * c.im := by linarith
        exact pos_of_mul_pos_left h3 hc.le
      simp [triangleDetSign, positiveStep, hp, hq, hab, not_lt_of_gt hq]
    · have hq' : planeDet c a < 0 := lt_of_le_of_ne (le_of_not_gt hq) hca
      simp [triangleDetSign, positiveStep, hp, hq, hq', not_lt_of_gt hp]
  · have hp' : planeDet b c < 0 := lt_of_le_of_ne (le_of_not_gt hp) hbc
    by_cases hq : 0 < planeDet c a
    · simp [triangleDetSign, positiveStep, hp, hp', hq, not_lt_of_gt hq]
    · have hq' : planeDet c a < 0 := lt_of_le_of_ne (le_of_not_gt hq) hca
      have hab : planeDet a b < 0 := by
        have h1 := mul_pos_of_neg_of_neg hp' ha
        have h2 := mul_pos_of_neg_of_neg hq' hb
        have h3 : planeDet a b * c.im < 0 := by linarith
        exact neg_of_mul_neg_left h3 hc.le
      simp [triangleDetSign, positiveStep, hp, hp', hq, hq', hab, not_lt_of_gt hab]

theorem rayTriangleCrossing_eq_detSign_all_above {a b c : ℂ}
    (ha : 0 < a.im) (hb : 0 < b.im) (hc : 0 < c.im) :
    rayTriangleCrossing a b c = triangleDetSign a b c := by
  have hw := planeDet_weighted_im a b c
  have hp : ¬(0 < planeDet a b ∧ 0 < planeDet b c ∧ 0 < planeDet c a) := by
    rintro ⟨hab, hbc, hca⟩
    have h1 := mul_pos hbc ha
    have h2 := mul_pos hca hb
    have h3 := mul_pos hab hc
    linarith
  have hn : ¬(planeDet a b < 0 ∧ planeDet b c < 0 ∧ planeDet c a < 0) := by
    rintro ⟨hab, hbc, hca⟩
    have h1 := mul_neg_of_neg_of_pos hbc ha
    have h2 := mul_neg_of_neg_of_pos hca hb
    have h3 := mul_neg_of_neg_of_pos hab hc
    linarith
  rw [rayTriangleCrossing, rayEdgeCrossing_of_above ha hb,
    rayEdgeCrossing_of_above hb hc, rayEdgeCrossing_of_above hc ha,
    triangleDetSign, if_neg hp, if_neg hn]
  norm_num

theorem rayTriangleCrossing_eq_detSign_all_below {a b c : ℂ}
    (ha : a.im < 0) (hb : b.im < 0) (hc : c.im < 0)
    (hab : planeDet a b ≠ 0) (hbc : planeDet b c ≠ 0) (hca : planeDet c a ≠ 0) :
    rayTriangleCrossing a b c = triangleDetSign a b c := by
  have h := rayTriangleCrossing_eq_detSign_all_above
    (show 0 < (-a).im from neg_pos.mpr ha)
    (show 0 < (-b).im from neg_pos.mpr hb)
    (show 0 < (-c).im from neg_pos.mpr hc)
  rwa [rayTriangleCrossing_neg a b c (ne_of_lt ha) (ne_of_lt hb) (ne_of_lt hc)
    hab hbc hca, triangleDetSign_neg] at h

theorem rayTriangleCrossing_eq_detSign_one_below {a b c : ℂ}
    (ha : 0 < a.im) (hb : 0 < b.im) (hc : c.im < 0)
    (hab : planeDet a b ≠ 0) (hbc : planeDet b c ≠ 0) (hca : planeDet c a ≠ 0) :
    rayTriangleCrossing a b c = triangleDetSign a b c := by
  have h := rayTriangleCrossing_eq_detSign_one_above
    (show (-a).im < 0 from neg_neg_of_pos ha)
    (show (-b).im < 0 from neg_neg_of_pos hb)
    (show 0 < (-c).im from neg_pos.mpr hc)
    (by simpa only [planeDet_neg_neg] using hbc)
    (by simpa only [planeDet_neg_neg] using hca)
  rwa [rayTriangleCrossing_neg a b c (ne_of_gt ha) (ne_of_gt hb) (ne_of_lt hc)
    hab hbc hca, triangleDetSign_neg] at h

/-- The generic horizontal-ray crossing number equals the common determinant
sign, and is zero when the determinants have mixed signs. -/
theorem rayTriangleCrossing_eq_detSign (a b c : ℂ)
    (ha : a.im ≠ 0) (hb : b.im ≠ 0) (hc : c.im ≠ 0)
    (hab : planeDet a b ≠ 0) (hbc : planeDet b c ≠ 0) (hca : planeDet c a ≠ 0) :
    rayTriangleCrossing a b c = triangleDetSign a b c := by
  rcases lt_or_gt_of_ne ha with ha | ha
  · rcases lt_or_gt_of_ne hb with hb | hb
    · rcases lt_or_gt_of_ne hc with hc | hc
      · exact rayTriangleCrossing_eq_detSign_all_below ha hb hc hab hbc hca
      · exact rayTriangleCrossing_eq_detSign_one_above ha hb hc hbc hca
    · rcases lt_or_gt_of_ne hc with hc | hc
      · calc
          _ = rayTriangleCrossing c a b := rayTriangleCrossing_rotate c a b
          _ = triangleDetSign c a b :=
            rayTriangleCrossing_eq_detSign_one_above hc ha hb hab hbc
          _ = _ := (triangleDetSign_rotate c a b).symm
      · calc
          _ = rayTriangleCrossing b c a := (rayTriangleCrossing_rotate a b c).symm
          _ = triangleDetSign b c a :=
            rayTriangleCrossing_eq_detSign_one_below hb hc ha hbc hca hab
          _ = _ := triangleDetSign_rotate a b c
  · rcases lt_or_gt_of_ne hb with hb | hb
    · rcases lt_or_gt_of_ne hc with hc | hc
      · calc
          _ = rayTriangleCrossing b c a := (rayTriangleCrossing_rotate a b c).symm
          _ = triangleDetSign b c a :=
            rayTriangleCrossing_eq_detSign_one_above hb hc ha hca hab
          _ = _ := triangleDetSign_rotate a b c
      · calc
          _ = rayTriangleCrossing c a b := rayTriangleCrossing_rotate c a b
          _ = triangleDetSign c a b :=
            rayTriangleCrossing_eq_detSign_one_below hc ha hb hca hab hbc
          _ = _ := (triangleDetSign_rotate c a b).symm
    · rcases lt_or_gt_of_ne hc with hc | hc
      · exact rayTriangleCrossing_eq_detSign_one_below ha hb hc hab hbc hca
      · exact rayTriangleCrossing_eq_detSign_all_above ha hb hc

end Erdos633
