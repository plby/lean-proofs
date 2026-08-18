/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.GAP

/-!
# Lower volume bounds for dilated generalized arithmetic progressions

The definition of `GAP.dilate` gives the new width
`k * (w - 1) + 1` in a coordinate of old width `w`.  If `w >= 2`, this is
at least `k * w / 2`; if `w >= 3`, it is at least `2 * k * w / 3`.

This file records integral coordinatewise and product forms of these
estimates, together with their real-valued division forms.  No properness is
needed: `GAP.volume` is the displayed coefficient-box volume.
-/

namespace Erdos186.GAP

open scoped BigOperators

variable {d r : ℕ}

/-! ## Widths at least two -/

/-- One coordinate of a dilated GAP loses at most a factor two compared to
the heuristic scaling by `k`. -/
theorem mul_width_le_two_mul_dilate_width (P : GAP d r)
    (hwidth : ∀ i, 2 ≤ P.widths i) (k : ℕ) (i : Fin r) :
    k * P.widths i ≤ 2 * (P.dilate k).widths i := by
  change k * P.widths i ≤ 2 * (k * (P.widths i - 1) + 1)
  have hi := hwidth i
  have hw : (P.widths i - 1) + 1 = P.widths i :=
    Nat.sub_add_cancel (by omega : 1 ≤ P.widths i)
  have hk : k ≤ k * (P.widths i - 1) :=
    Nat.le_mul_of_pos_right k (by omega)
  calc
    k * P.widths i = k * ((P.widths i - 1) + 1) :=
      congrArg (fun w ↦ k * w) hw.symm
    _ = k * (P.widths i - 1) + k := by rw [Nat.mul_add, Nat.mul_one]
    _ ≤ 2 * (k * (P.widths i - 1) + 1) := by omega

/-- Product form of `mul_width_le_two_mul_dilate_width`.  This is the exact
natural-number version of
`volume (k P) >= (k / 2)^rank * volume P`. -/
theorem pow_mul_volume_le_pow_two_mul_volume_dilate
    (P : GAP d r) (hwidth : ∀ i, 2 ≤ P.widths i) (k : ℕ) :
    k ^ r * P.volume ≤ 2 ^ r * (P.dilate k).volume := by
  rw [volume, volume_dilate]
  calc
    k ^ r * ∏ i, P.widths i = ∏ i, k * P.widths i := by
      rw [Finset.prod_mul_distrib]
      simp
    _ ≤ ∏ i, 2 * (k * (P.widths i - 1) + 1) :=
      Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
        (fun i _ ↦ mul_width_le_two_mul_dilate_width P hwidth k i)
    _ = 2 ^ r * ∏ i, (k * (P.widths i - 1) + 1) := by
      rw [Finset.prod_mul_distrib]
      simp

/-- Real-cast product form of the width-at-least-two volume estimate. -/
theorem pow_mul_volume_cast_le_pow_two_mul_volume_dilate_cast
    (P : GAP d r) (hwidth : ∀ i, 2 ≤ P.widths i) (k : ℕ) :
    (k : ℝ) ^ r * (P.volume : ℝ) ≤
      (2 : ℝ) ^ r * ((P.dilate k).volume : ℝ) := by
  exact_mod_cast pow_mul_volume_le_pow_two_mul_volume_dilate P hwidth k

/-- Division form of the real width-at-least-two estimate. -/
theorem half_pow_mul_volume_cast_le_volume_dilate_cast
    (P : GAP d r) (hwidth : ∀ i, 2 ≤ P.widths i) (k : ℕ) :
    ((k : ℝ) / 2) ^ r * (P.volume : ℝ) ≤
      ((P.dilate k).volume : ℝ) := by
  have h := pow_mul_volume_cast_le_pow_two_mul_volume_dilate_cast P hwidth k
  rw [div_pow]
  calc
    (k : ℝ) ^ r / 2 ^ r * (P.volume : ℝ) =
        ((k : ℝ) ^ r * (P.volume : ℝ)) / 2 ^ r := by ring
    _ ≤ ((2 : ℝ) ^ r * ((P.dilate k).volume : ℝ)) / 2 ^ r :=
      div_le_div_of_nonneg_right h (by positivity)
    _ = ((P.dilate k).volume : ℝ) := by
      field_simp

/-! ## Widths at least three -/

/-- With width at least three, one keeps two thirds of the heuristic
coordinate scaling. -/
theorem two_mul_mul_width_le_three_mul_dilate_width (P : GAP d r)
    (hwidth : ∀ i, 3 ≤ P.widths i) (k : ℕ) (i : Fin r) :
    (2 * k) * P.widths i ≤ 3 * (P.dilate k).widths i := by
  change (2 * k) * P.widths i ≤ 3 * (k * (P.widths i - 1) + 1)
  have hi := hwidth i
  have hw : (P.widths i - 1) + 1 = P.widths i :=
    Nat.sub_add_cancel (by omega : 1 ≤ P.widths i)
  have htwo : 2 * k ≤ k * (P.widths i - 1) := by
    have h : 2 ≤ P.widths i - 1 := by omega
    simpa [mul_comm] using Nat.mul_le_mul_left k h
  calc
    (2 * k) * P.widths i =
        (2 * k) * ((P.widths i - 1) + 1) :=
      congrArg (fun w ↦ (2 * k) * w) hw.symm
    _ = 2 * (k * (P.widths i - 1) + k) := by ring
    _ ≤ 3 * (k * (P.widths i - 1) + 1) := by omega

/-- Product form of the sharper width-at-least-three estimate. -/
theorem two_mul_pow_mul_volume_le_pow_three_mul_volume_dilate
    (P : GAP d r) (hwidth : ∀ i, 3 ≤ P.widths i) (k : ℕ) :
    (2 * k) ^ r * P.volume ≤ 3 ^ r * (P.dilate k).volume := by
  rw [volume, volume_dilate]
  calc
    (2 * k) ^ r * ∏ i, P.widths i = ∏ i, (2 * k) * P.widths i := by
      rw [Finset.prod_mul_distrib]
      simp
    _ ≤ ∏ i, 3 * (k * (P.widths i - 1) + 1) :=
      Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
        (fun i _ ↦ two_mul_mul_width_le_three_mul_dilate_width P hwidth k i)
    _ = 3 ^ r * ∏ i, (k * (P.widths i - 1) + 1) := by
      rw [Finset.prod_mul_distrib]
      simp

/-- Real-cast product form of the width-at-least-three volume estimate. -/
theorem two_mul_pow_mul_volume_cast_le_pow_three_mul_volume_dilate_cast
    (P : GAP d r) (hwidth : ∀ i, 3 ≤ P.widths i) (k : ℕ) :
    ((2 * k : ℕ) : ℝ) ^ r * (P.volume : ℝ) ≤
      (3 : ℝ) ^ r * ((P.dilate k).volume : ℝ) := by
  exact_mod_cast two_mul_pow_mul_volume_le_pow_three_mul_volume_dilate P hwidth k

/-- Division form of the sharper real width-at-least-three estimate. -/
theorem two_thirds_pow_mul_volume_cast_le_volume_dilate_cast
    (P : GAP d r) (hwidth : ∀ i, 3 ≤ P.widths i) (k : ℕ) :
    ((2 * (k : ℝ)) / 3) ^ r * (P.volume : ℝ) ≤
      ((P.dilate k).volume : ℝ) := by
  have h :=
    two_mul_pow_mul_volume_cast_le_pow_three_mul_volume_dilate_cast P hwidth k
  have hscalar : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by norm_num
  rw [hscalar] at h
  rw [div_pow]
  calc
    (2 * (k : ℝ)) ^ r / 3 ^ r * (P.volume : ℝ) =
        ((2 * (k : ℝ)) ^ r * (P.volume : ℝ)) / 3 ^ r := by ring
    _ ≤ ((3 : ℝ) ^ r * ((P.dilate k).volume : ℝ)) / 3 ^ r :=
      div_le_div_of_nonneg_right h (by positivity)
    _ = ((P.dilate k).volume : ℝ) := by
      field_simp

end Erdos186.GAP
