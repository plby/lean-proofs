import ErdosProblems.Erdos633b.SixtyTranslations
import ErdosProblems.Erdos633b.GroupTwoDimensions

/-! Stack the explicitly tileable layers into the large trapezoid used three times. -/

namespace Erdos633b.Sixty

open GroupTwoDimensions

noncomputable def layer_patch_at (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c i : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    Patch (groupTwoReference d hd a b (by exact_mod_cast ha) (by exact_mod_cast hb))
      (TrapezoidPartition.trapezoidSet (frame d hd)
        (((scale a b + i : ℕ) : ℝ) * ((a : ℝ) * b)) ((a : ℝ) * b)) (rowCount a b i) := by
  have hrelR : (c : ℝ) ^ 2 = (a : ℝ) ^ 2 + (a : ℝ) * b + (b : ℝ) ^ 2 := by
    exact_mod_cast hrel
  have result := wide_layer_patch d hd he a b c (rowU a b i) (rowV a b) ha hb hc
    (rowU_pos a b i hb) (rowV_pos a b ha) hrelR
  have hwidth : (((scale a b + i : ℕ) : ℝ) * ((a : ℝ) * b)) =
      (a : ℝ) ^ 2 + (b : ℝ) ^ 2 + ((rowU a b i : ℝ) * a + (rowV a b : ℝ) * b) := by
    exact_mod_cast width_identity a b i ha hb
  rw [← hwidth, row_count_identity a b c i ha hb hrel] at result
  exact result

noncomputable def stacked_layers_patch (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) (n : ℕ) :
    ∀ i : ℕ, Patch (groupTwoReference d hd a b (by exact_mod_cast ha) (by exact_mod_cast hb))
      (TrapezoidPartition.trapezoidSet (frame d hd)
        (((scale a b + i : ℕ) : ℝ) * ((a : ℝ) * b))
        (((n + 1 : ℕ) : ℝ) * ((a : ℝ) * b)))
      ((n + 1) * (2 * (scale a b + i) + (n + 1)) * (a * b)) := by
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have hy : (0 : ℝ) < (a : ℝ) * b := mul_pos har hbr
  let R := groupTwoReference d hd a b har hbr
  induction n with
  | zero =>
    intro i
    have result := layer_patch_at d hd he a b c i ha hb hc hrel
    simpa only [Nat.zero_add, Nat.cast_one, one_mul, rowCount] using result
  | succ n ih =>
    intro i
    let x := (((scale a b + i : ℕ) : ℝ) * ((a : ℝ) * b))
    let r := (((n + 1 : ℕ) : ℝ) * ((a : ℝ) * b))
    have lower := ih (i + 1)
    have hwidth : (((scale a b + (i + 1) : ℕ) : ℝ) * ((a : ℝ) * b)) = x + (a : ℝ) * b := by
      dsimp only [x]
      push_cast
      ring
    rw [hwidth] at lower
    have upper := layer_patch_at d hd he a b c i ha hb hc hrel
    have result := stack_patch_step d hd R x ((a : ℝ) * b) r hy.le
      (mul_pos (by exact_mod_cast Nat.succ_pos n) hy).le _ _ lower upper
    have hheight : r + (a : ℝ) * b = (((n + 1 + 1 : ℕ) : ℝ) * ((a : ℝ) * b)) := by
      dsimp only [r]
      push_cast
      ring
    have hcount :
        (n + 1) * (2 * (scale a b + (i + 1)) + (n + 1)) * (a * b) + rowCount a b i =
        (n + 1 + 1) * (2 * (scale a b + i) + (n + 1 + 1)) * (a * b) := by
      unfold rowCount
      ring
    rw [hheight, hcount] at result
    exact result

noncomputable def large_trapezoid_patch (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    Patch (groupTwoReference d hd a b (by exact_mod_cast ha) (by exact_mod_cast hb))
      (TrapezoidPartition.trapezoidSet (frame d hd)
        ((scale a b : ℝ) * ((a : ℝ) * b)) ((scale a b : ℝ) * ((a : ℝ) * b)))
      (3 * scale a b ^ 2 * (a * b)) := by
  have result := stacked_layers_patch d hd he a b c ha hb hc hrel (scale a b - 1) 0
  have hscale : scale a b - 1 + 1 = scale a b :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr (scale_pos a b))
  rw [hscale, Nat.add_zero] at result
  have hcount : scale a b * (2 * scale a b + scale a b) * (a * b) =
      3 * scale a b ^ 2 * (a * b) := by ring
  rwa [hcount] at result

end Erdos633b.Sixty
