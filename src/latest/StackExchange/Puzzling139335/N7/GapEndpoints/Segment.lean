import StackExchange.Puzzling139335.N7.CornerGap

/-!
# Coordinates of the open gap segment

The segment between `gapLeft c s` and `gapRight c s` lies near the top-right
corner and strictly between the two supporting lines whenever `0 < s < c ≤ 1`.
These are purely affine inequalities; no unit-circle relation is required.
-/

open Set

namespace Puzzling139335.N7

/-- The whole open gap segment lies inside the square and strictly between
the two gap-supporting lines. -/
theorem gap_openSegment_properties {c s : ℝ} {p : Plane}
    (hs : 0 < s) (hsc : s < c) (hc : c ≤ 1)
    (hp : p ∈ openSegment ℝ (gapLeft c s) (gapRight c s)) :
    p ∈ unitSquare ∧ (3 / 4 : ℝ) ≤ p 0 ∧ (3 / 4 : ℝ) ≤ p 1 ∧
      s * (1 - p 0) < c * (1 - p 1) ∧
      s * (1 - p 1) < c * (1 - p 0) := by
  obtain ⟨a, b, ha, hb, hab, heq⟩ := hp
  have hcpos : 0 < c := hs.trans hsc
  have hsone : s ≤ 1 := hsc.le.trans hc
  have hx : p 0 = 1 - (a * c + b * s) / 4 := by
    rw [← heq]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, gapLeft, gapRight,
      Matrix.cons_val_zero]
    linear_combination hab
  have hy : p 1 = 1 - (a * s + b * c) / 4 := by
    rw [← heq]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, gapLeft, gapRight,
      Matrix.cons_val_one, Matrix.cons_val_zero]
    linear_combination hab
  have hxnonneg : 0 ≤ a * c + b * s :=
    add_nonneg (mul_nonneg ha.le hcpos.le) (mul_nonneg hb.le hs.le)
  have hynonneg : 0 ≤ a * s + b * c :=
    add_nonneg (mul_nonneg ha.le hs.le) (mul_nonneg hb.le hcpos.le)
  have hxle : a * c + b * s ≤ 1 := by
    calc
      a * c + b * s ≤ a * 1 + b * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hc ha.le)
          (mul_le_mul_of_nonneg_left hsone hb.le)
      _ = 1 := by simpa only [mul_one] using hab
  have hyle : a * s + b * c ≤ 1 := by
    calc
      a * s + b * c ≤ a * 1 + b * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hsone ha.le)
          (mul_le_mul_of_nonneg_left hc hb.le)
      _ = 1 := by simpa only [mul_one] using hab
  have hxlower : (3 / 4 : ℝ) ≤ p 0 := by linarith only [hx, hxle]
  have hylower : (3 / 4 : ℝ) ≤ p 1 := by linarith only [hy, hyle]
  have hxupper : p 0 ≤ 1 := by linarith only [hx, hxnonneg]
  have hyupper : p 1 ≤ 1 := by linarith only [hy, hynonneg]
  have hdiff : 0 < c ^ 2 - s ^ 2 :=
    sub_pos.mpr ((sq_lt_sq₀ hs.le hcpos.le).mpr hsc)
  refine ⟨?_, hxlower, hylower, ?_, ?_⟩
  · exact ⟨⟨by linarith only [hxlower], hxupper⟩,
      ⟨by linarith only [hylower], hyupper⟩⟩
  · apply sub_pos.mp
    have hgap : c * (1 - p 1) - s * (1 - p 0) = b * (c ^ 2 - s ^ 2) / 4 := by
      rw [hx, hy]
      ring
    rw [hgap]
    exact div_pos (mul_pos hb hdiff) (by norm_num)
  · apply sub_pos.mp
    have hgap : c * (1 - p 0) - s * (1 - p 1) = a * (c ^ 2 - s ^ 2) / 4 := by
      rw [hx, hy]
      ring
    rw [hgap]
    exact div_pos (mul_pos ha hdiff) (by norm_num)

end Puzzling139335.N7
