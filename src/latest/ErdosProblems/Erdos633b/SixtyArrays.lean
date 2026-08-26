import ErdosProblems.Erdos633b.BasicTrapezoid
import ErdosProblems.Erdos633b.PlanarMotions

/-! Exact parallelogram arrays in the two orientations needed by the group-2 layers. -/

namespace Erdos633b.Sixty

noncomputable def strip (d : ℝ) (hd : 0 < d) (z x y : ℝ) : Set Plane :=
  {p | 0 ≤ (frame d hd).coord 2 p ∧ (frame d hd).coord 2 p ≤ y ∧
    z ≤ (frame d hd).coord 1 p + (frame d hd).coord 2 p ∧
    (frame d hd).coord 1 p + (frame d hd).coord 2 p ≤ z + x}

theorem point_affine_rectangle (d z x y u v : ℝ) :
    point d z 0 + u • point d x 0 + v • point d (-y) y =
      point d (z + u * x - v * y) (v * y) := by
  ext i
  fin_cases i <;> simp [point] <;> ring

theorem parallelogram_strip (d : ℝ) (hd : 0 < d) (z x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    parallelogram (point d z 0) (point d x 0) (point d (-y) y) = strip d hd z x y := by
  ext p
  constructor
  · rintro ⟨u, v, hu, hu1, hv, hv1, rfl⟩
    change 0 ≤ (frame d hd).coord 2 _ ∧ (frame d hd).coord 2 _ ≤ y ∧
      z ≤ (frame d hd).coord 1 _ + (frame d hd).coord 2 _ ∧
      (frame d hd).coord 1 _ + (frame d hd).coord 2 _ ≤ z + x
    rw [point_affine_rectangle, (frame_coords d hd _ _).1, (frame_coords d hd _ _).2]
    exact ⟨mul_nonneg hv hy.le, by nlinarith, by nlinarith [mul_nonneg hu hx.le],
      by nlinarith⟩
  · rintro ⟨ht, hty, hsum, hsumx⟩
    let s := (frame d hd).coord 1 p
    let t := (frame d hd).coord 2 p
    refine ⟨(s + t - z) / x, t / y, div_nonneg (by linarith) hx.le,
      (div_le_one hx).mpr (by linarith), div_nonneg ht hy.le, (div_le_one hy).mpr hty, ?_⟩
    rw [point_affine_rectangle]
    apply (frame d hd).ext_coords
    · rw [(frame_coords d hd _ _).1]
      change s = z + ((s + t - z) / x) * x - (t / y) * y
      rw [div_mul_cancel₀ _ hx.ne', div_mul_cancel₀ _ hy.ne']
      ring
    · rw [(frame_coords d hd _ _).2]
      exact (div_mul_cancel₀ t hy.ne').symm

theorem parallelogram_swap (Q U V : Plane) : parallelogram Q U V = parallelogram Q V U := by
  ext p
  constructor <;> rintro ⟨u, v, hu, hu1, hv, hv1, hp⟩ <;>
    refine ⟨v, u, hv, hv1, hu, hu1, ?_⟩ <;> rw [hp] <;> abel

noncomputable def axisSwap (d : ℝ) (he : d ^ 2 = 3) : Plane ≃ₗᵢ[ℝ] Plane :=
  reflection (-1 / 2) (d / 2) (by nlinarith)

theorem axisSwap_point (d : ℝ) (he : d ^ 2 = 3) (s t : ℝ) :
    axisSwap d he (point d s t) = point d (-s) (s + t) := by
  change reflectionMap (-1 / 2) (d / 2) (point d s t) = _
  ext i
  fin_cases i
  · simp [reflectionMap, point]
    linear_combination (t / 4) * he
  · simp [reflectionMap, point]
    ring

noncomputable def aligned_array_patch (d : ℝ) (hd : 0 < d) (a b z : ℝ)
    (ha : 0 < a) (hb : 0 < b) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Patch (groupTwoReference d hd a b ha hb) (strip d hd z ((m : ℝ) * b) ((n : ℝ) * a))
      (2 * m * n) := by
  let R := groupTwoReference d hd a b ha hb
  let Q := point d z 0
  let g := AffineIsometryEquiv.constVAdd ℝ Plane Q
  have hQ : g (R.points 0) = Q := by
    change Q + point d 0 0 = Q
    rw [point_zero, add_zero]
  have hU : (m : ℝ) • (g (R.points 1) - g (R.points 0)) = point d ((m : ℝ) * b) 0 := by
    change (m : ℝ) • ((Q + point d b 0) - (Q + point d 0 0)) = _
    rw [point_zero, add_zero, add_sub_cancel_left]
    simpa only [mul_zero] using (point_smul d m b 0).symm
  have hV : (n : ℝ) • (g (R.points 2) - g (R.points 0)) =
      point d (-((n : ℝ) * a)) ((n : ℝ) * a) := by
    change (n : ℝ) • ((Q + point d (-a) a) - (Q + point d 0 0)) = _
    rw [point_zero, add_zero, add_sub_cancel_left]
    simpa only [mul_neg] using (point_smul d n (-a) a).symm
  have result := parallelogram_patch R g m n hm hn
  rw [hU, hV, hQ, parallelogram_strip d hd z ((m : ℝ) * b) ((n : ℝ) * a)
    (mul_pos (by exact_mod_cast hm) hb) (mul_pos (by exact_mod_cast hn) ha)] at result
  exact result

noncomputable def swapped_array_patch (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3) (a b z : ℝ)
    (ha : 0 < a) (hb : 0 < b) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Patch (groupTwoReference d hd a b ha hb) (strip d hd z ((n : ℝ) * a) ((m : ℝ) * b))
      (2 * m * n) := by
  let R := groupTwoReference d hd a b ha hb
  let Q := point d z 0
  let g := (axisSwap d he).toAffineIsometryEquiv.trans (AffineIsometryEquiv.constVAdd ℝ Plane Q)
  have hg (s t : ℝ) : g (point d s t) = Q + point d (-s) (s + t) := by
    change Q + axisSwap d he (point d s t) = _
    rw [axisSwap_point]
  have hQ : g (R.points 0) = Q := by
    change g (point d 0 0) = Q
    rw [hg]
    simp only [neg_zero, add_zero, point_zero]
  have hU : (m : ℝ) • (g (R.points 1) - g (R.points 0)) =
      point d (-((m : ℝ) * b)) ((m : ℝ) * b) := by
    change (m : ℝ) • (g (point d b 0) - g (point d 0 0)) = _
    rw [hg, hg]
    simp only [neg_zero, add_zero, point_zero, add_sub_cancel_left]
    simpa only [mul_neg] using (point_smul d m (-b) b).symm
  have hV : (n : ℝ) • (g (R.points 2) - g (R.points 0)) = point d ((n : ℝ) * a) 0 := by
    change (n : ℝ) • (g (point d (-a) a) - g (point d 0 0)) = _
    rw [hg, hg]
    simp only [neg_neg, neg_add_cancel, neg_zero, add_zero, point_zero, add_sub_cancel_left]
    simpa only [mul_zero] using (point_smul d n a 0).symm
  have result := parallelogram_patch R g m n hm hn
  rw [hU, hV, hQ, parallelogram_swap Q] at result
  rw [parallelogram_strip d hd z ((n : ℝ) * a) ((m : ℝ) * b)
    (mul_pos (by exact_mod_cast hn) ha) (mul_pos (by exact_mod_cast hm) hb)] at result
  exact result

end Erdos633b.Sixty
