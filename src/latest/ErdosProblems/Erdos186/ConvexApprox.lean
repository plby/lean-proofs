/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib

/-!
# A local affine approximation lemma for bounded convex functions

This file formalizes the one-dimensional base case of the local affine
approximation argument in Pham--Zakharov's convex-density lemma.  If a convex
function taking values in `[0, 1]` is defined with a margin `c` around the unit
interval, then among any prescribed nonempty collection of `m` grid cells one
cell has secant-line error at most

`2 / (c * m * number_of_prescribed_cells)`.

The proof is completely discrete.  Consecutive secant slopes are monotone by
convexity, their jumps telescope, and the outer margin bounds the total slope
variation.  This is stronger (in base dimension one) than the constant in the
published multidimensional lemma and does not use differentiability or
smoothing.
-/

open scoped BigOperators

namespace Erdos186.ConvexApprox

set_option autoImplicit false

noncomputable section

/-- The grid point `k / m`. -/
def gridPoint (m k : ℕ) : ℝ := (k : ℝ) / (m : ℝ)

/-- The slope on the grid interval immediately to the left of `k / m`.

Thus `gridSlope f m (k + 1)` is the slope on the `k`-th cell.  The
normalization by `m` is legitimate in all the results below, where `m > 0`.
-/
def gridSlope (f : ℝ → ℝ) (m k : ℕ) : ℝ :=
  (m : ℝ) * (f (gridPoint m k) - f (gridPoint m k - (m : ℝ)⁻¹))

/-- The secant line of `f` on the `k`-th grid cell. -/
def cellSecant (f : ℝ → ℝ) (m k : ℕ) (x : ℝ) : ℝ :=
  f (gridPoint m k) +
    gridSlope f m (k + 1) * (x - gridPoint m k)

lemma gridPoint_succ {m k : ℕ} (hm : 0 < m) :
    gridPoint m (k + 1) = gridPoint m k + (m : ℝ)⁻¹ := by
  unfold gridPoint
  push_cast
  field_simp

lemma gridSlope_eq_secant {f : ℝ → ℝ} {m k : ℕ} (hm : 0 < m) :
    gridSlope f m k =
      (f (gridPoint m k) - f (gridPoint m k - (m : ℝ)⁻¹)) /
        (gridPoint m k - (gridPoint m k - (m : ℝ)⁻¹)) := by
  have hden : gridPoint m k - (gridPoint m k - (m : ℝ)⁻¹) = (m : ℝ)⁻¹ := by
    ring
  rw [hden]
  simp only [gridSlope]
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  field_simp

lemma gridSlope_succ {f : ℝ → ℝ} {m k : ℕ} (hm : 0 < m) :
    gridSlope f m (k + 1) =
      (f (gridPoint m (k + 1)) - f (gridPoint m k)) /
        (gridPoint m (k + 1) - gridPoint m k) := by
  rw [gridSlope_eq_secant hm]
  have hleft : gridPoint m (k + 1) - (m : ℝ)⁻¹ = gridPoint m k := by
    rw [gridPoint_succ hm]
    ring
  rw [hleft]

lemma gridSlope_zero {f : ℝ → ℝ} {m : ℕ} (hm : 0 < m) :
    gridSlope f m 0 =
      (f 0 - f (-(m : ℝ)⁻¹)) / (0 - (-(m : ℝ)⁻¹)) := by
  simp only [gridSlope, gridPoint, Nat.cast_zero, zero_div, zero_sub]
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  field_simp

/-- Convexity makes the normalized secant slopes on adjacent grid cells
monotone. -/
lemma gridSlope_mono_step {f : ℝ → ℝ} {c : ℝ} {m k : ℕ}
    (hm : 0 < m) (hmargin : (m : ℝ)⁻¹ < c) (hk : k < m)
    (hconv : ConvexOn ℝ (Set.Icc (-c) (1 + c)) f) :
    gridSlope f m k ≤ gridSlope f m (k + 1) := by
  have hc : 0 < c := lt_of_le_of_lt (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ m)) hmargin
  have hpos : 0 < (m : ℝ)⁻¹ := by positivity
  have hmk : (0 : ℝ) ≤ gridPoint m k := by
    exact div_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg m)
  have hk_one : gridPoint m k + (m : ℝ)⁻¹ ≤ 1 := by
    rw [← gridPoint_succ hm]
    unfold gridPoint
    rw [div_le_one (by positivity : (0 : ℝ) < m)]
    exact_mod_cast Nat.succ_le_iff.mpr hk
  have hx : gridPoint m k - (m : ℝ)⁻¹ ∈ Set.Icc (-c) (1 + c) := by
    constructor
    · linarith
    · calc
        gridPoint m k - (m : ℝ)⁻¹ ≤ gridPoint m k + (m : ℝ)⁻¹ := by linarith
        _ ≤ 1 := hk_one
        _ ≤ 1 + c := by linarith
  have hz : gridPoint m k + (m : ℝ)⁻¹ ∈ Set.Icc (-c) (1 + c) := by
    constructor
    · linarith
    · exact hk_one.trans (by linarith)
  have hs := hconv.slope_mono_adjacent hx hz (by linarith :
      gridPoint m k - (m : ℝ)⁻¹ < gridPoint m k) (by linarith :
      gridPoint m k < gridPoint m k + (m : ℝ)⁻¹)
  rw [← gridPoint_succ hm] at hs
  rw [← gridSlope_succ hm] at hs
  rw [← gridSlope_eq_secant hm] at hs
  exact hs

/-- The sum of all grid-slope jumps telescopes. -/
lemma sum_gridSlope_jumps (f : ℝ → ℝ) (m : ℕ) :
    ∑ k ∈ Finset.range m, (gridSlope f m (k + 1) - gridSlope f m k) =
      gridSlope f m m - gridSlope f m 0 := by
  exact Finset.sum_range_sub (gridSlope f m) m

/-- The margin and the range `[0,1]` bound the total variation of the grid
slopes by `2/c`. -/
lemma gridSlope_total_variation_le {f : ℝ → ℝ} {c : ℝ} {m : ℕ}
    (hm : 0 < m) (hmargin : (m : ℝ)⁻¹ < c)
    (hconv : ConvexOn ℝ (Set.Icc (-c) (1 + c)) f)
    (hrange : ∀ x ∈ Set.Icc (-c) (1 + c), 0 ≤ f x ∧ f x ≤ 1) :
    gridSlope f m m - gridSlope f m 0 ≤ 2 / c := by
  have hc : 0 < c := lt_of_le_of_lt (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ m)) hmargin
  have hinv : 0 < (m : ℝ)⁻¹ := by positivity
  have hleft_order : -c < -(m : ℝ)⁻¹ := by linarith
  have hright_order : 1 - (m : ℝ)⁻¹ < 1 := by linarith
  have hmem_negc : -c ∈ Set.Icc (-c) (1 + c) := by constructor <;> linarith
  have hmem_zero : (0 : ℝ) ∈ Set.Icc (-c) (1 + c) := by constructor <;> linarith
  have hmem_one : (1 : ℝ) ∈ Set.Icc (-c) (1 + c) := by constructor <;> linarith
  have hmem_right : 1 + c ∈ Set.Icc (-c) (1 + c) := by constructor <;> linarith
  have hmem_leftGrid : -(m : ℝ)⁻¹ ∈ Set.Icc (-c) (1 + c) := by
    constructor <;> linarith
  have hmem_rightGrid : 1 - (m : ℝ)⁻¹ ∈ Set.Icc (-c) (1 + c) := by
    constructor <;> linarith
  have hq0_lower : -1 / c ≤ gridSlope f m 0 := by
    have hs := hconv.secant_mono_aux3 hmem_negc hmem_zero hleft_order
      (by linarith : -(m : ℝ)⁻¹ < 0)
    rw [← gridSlope_zero hm] at hs
    have h0 := hrange 0 hmem_zero
    have hnegc := hrange (-c) hmem_negc
    have hlong : -1 / c ≤ (f 0 - f (-c)) / (0 - (-c)) := by
      rw [show 0 - (-c) = c by ring]
      rw [le_div_iff₀ hc, div_mul_cancel₀ (-1) hc.ne']
      nlinarith
    exact hlong.trans hs
  have hqm_upper : gridSlope f m m ≤ 1 / c := by
    have hgm : gridPoint m m = 1 := by
      simp [gridPoint, ne_of_gt hm]
    have hs := hconv.slope_mono_adjacent hmem_rightGrid hmem_right hright_order
      (by linarith : 1 < 1 + c)
    have h1 := hrange 1 hmem_one
    have hright := hrange (1 + c) hmem_right
    have hshort : gridSlope f m m ≤ (f (1 + c) - f 1) / ((1 + c) - 1) := by
      rw [gridSlope_eq_secant hm, hgm]
      exact hs
    have hlong : (f (1 + c) - f 1) / ((1 + c) - 1) ≤ 1 / c := by
      rw [show (1 + c) - 1 = c by ring]
      rw [div_le_iff₀ hc, div_mul_cancel₀ 1 hc.ne']
      nlinarith
    exact hshort.trans hlong
  calc
    gridSlope f m m - gridSlope f m 0 ≤ 1 / c - (-1 / c) :=
      sub_le_sub hqm_upper hq0_lower
    _ = 2 / c := by ring

/-- On a grid cell, the secant line lies above a convex function and its
excess is controlled by the jump from the preceding secant slope. -/
lemma cellSecant_error_le_slope_jump {f : ℝ → ℝ} {c : ℝ} {m k : ℕ}
    (hm : 0 < m) (hmargin : (m : ℝ)⁻¹ < c) (hk : k < m)
    (hconv : ConvexOn ℝ (Set.Icc (-c) (1 + c)) f)
    {x : ℝ} (hx : x ∈ Set.Icc (gridPoint m k) (gridPoint m (k + 1))) :
    0 ≤ cellSecant f m k x - f x ∧
      cellSecant f m k x - f x ≤
        (gridSlope f m (k + 1) - gridSlope f m k) * (m : ℝ)⁻¹ := by
  have hc : 0 < c := lt_of_le_of_lt (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ m)) hmargin
  have hinv : 0 < (m : ℝ)⁻¹ := by positivity
  have ha0 : 0 ≤ gridPoint m k := by
    exact div_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg m)
  have hb1 : gridPoint m (k + 1) ≤ 1 := by
    unfold gridPoint
    rw [div_le_one (by positivity : (0 : ℝ) < m)]
    exact_mod_cast Nat.succ_le_iff.mpr hk
  have hab : gridPoint m k < gridPoint m (k + 1) := by
    rw [gridPoint_succ hm]
    linarith
  have ha : gridPoint m k ∈ Set.Icc (-c) (1 + c) := by
    constructor
    · linarith
    · linarith
  have hb : gridPoint m (k + 1) ∈ Set.Icc (-c) (1 + c) := by
    constructor
    · linarith
    · exact hb1.trans (by linarith)
  have hprev : gridPoint m k - (m : ℝ)⁻¹ ∈ Set.Icc (-c) (1 + c) := by
    constructor
    · linarith
    · calc
        gridPoint m k - (m : ℝ)⁻¹ ≤ gridPoint m k := by linarith
        _ ≤ gridPoint m (k + 1) := hx.1.trans hx.2
        _ ≤ 1 + c := hb.2
  have hxin : x ∈ Set.Icc (-c) (1 + c) := by
    constructor
    · exact ha.1.trans hx.1
    · exact hx.2.trans hb.2
  have hupper : f x ≤ cellSecant f m k x := by
    rcases hx.1.eq_or_lt with rfl | hax
    · simp [cellSecant]
    rcases hx.2.eq_or_lt with rfl | hxb
    · unfold cellSecant
      rw [gridSlope_succ hm]
      have hne : gridPoint m (k + 1) - gridPoint m k ≠ 0 := ne_of_gt (sub_pos.mpr hab)
      field_simp
      linarith
    · have hs := hconv.secant_mono_aux1 ha hb hax hxb
      have hline : cellSecant f m k x =
          ((gridPoint m (k + 1) - x) * f (gridPoint m k) +
            (x - gridPoint m k) * f (gridPoint m (k + 1))) /
              (gridPoint m (k + 1) - gridPoint m k) := by
        unfold cellSecant
        rw [gridSlope_succ hm]
        have hne : gridPoint m (k + 1) - gridPoint m k ≠ 0 :=
          ne_of_gt (sub_pos.mpr hab)
        field_simp [hne]
        ring
      rw [hline]
      rw [le_div_iff₀ (sub_pos.mpr hab)]
      nlinarith
  have hlower :
      f (gridPoint m k) + gridSlope f m k * (x - gridPoint m k) ≤ f x := by
    rcases hx.1.eq_or_lt with rfl | hax
    · simp
    · have hs := hconv.slope_mono_adjacent hprev hxin
          (by linarith : gridPoint m k - (m : ℝ)⁻¹ < gridPoint m k) hax
      rw [← gridSlope_eq_secant hm] at hs
      have hs' := (le_div_iff₀ (sub_pos.mpr hax)).mp hs
      nlinarith
  constructor
  · exact sub_nonneg.mpr hupper
  · have hxwidth : x - gridPoint m k ≤ (m : ℝ)⁻¹ := by
      have hs := gridPoint_succ (m := m) (k := k) hm
      linarith [hx.2]
    have hjump := gridSlope_mono_step hm hmargin hk hconv
    unfold cellSecant
    nlinarith

/-- **Prescribed-cell affine approximation (one-dimensional PZ lemma).**

Let `I` be any nonempty collection of cells in the `m`-grid of `[0,1]`.
For a convex `f : [-c,1+c] → [0,1]`, one of the prescribed cells has a
secant line whose uniform error is at most `2 / (c*m*I.card)`.

Unlike the smooth intermediate claim in Pham--Zakharov, this statement needs
no differentiability: it follows directly from Mathlib's secant-slope API.
-/
theorem exists_cell_affine_approximation {f : ℝ → ℝ} {c : ℝ} {m : ℕ}
    (hm : 0 < m) (hmargin : (m : ℝ)⁻¹ < c)
    (hconv : ConvexOn ℝ (Set.Icc (-c) (1 + c)) f)
    (hrange : ∀ x ∈ Set.Icc (-c) (1 + c), 0 ≤ f x ∧ f x ≤ 1)
    (I : Finset ℕ) (hI : I.Nonempty) (hIgrid : I ⊆ Finset.range m) :
    ∃ k ∈ I, ∀ x ∈ Set.Icc (gridPoint m k) (gridPoint m (k + 1)),
      |f x - cellSecant f m k x| ≤ 2 / (c * (m : ℝ) * (I.card : ℝ)) := by
  let jump : ℕ → ℝ := fun k ↦ gridSlope f m (k + 1) - gridSlope f m k
  have hjump_nonneg : ∀ k ∈ Finset.range m, 0 ≤ jump k := by
    intro k hk
    exact sub_nonneg.mpr (gridSlope_mono_step hm hmargin (Finset.mem_range.mp hk) hconv)
  have hsum_range : ∑ k ∈ Finset.range m, jump k ≤ 2 / c := by
    rw [show (∑ k ∈ Finset.range m, jump k) =
        gridSlope f m m - gridSlope f m 0 by
      simpa [jump] using sum_gridSlope_jumps f m]
    exact gridSlope_total_variation_le hm hmargin hconv hrange
  have hsum_I : ∑ k ∈ I, jump k ≤ 2 / c := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg hIgrid
      (fun k hk _ ↦ hjump_nonneg k hk)).trans hsum_range
  have hc : 0 < c := lt_of_le_of_lt (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ m)) hmargin
  have hcard : 0 < (I.card : ℝ) := by exact_mod_cast hI.card_pos
  have hconst : ∑ _k ∈ I, (2 / (c * (I.card : ℝ)) : ℝ) = 2 / c := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    field_simp
  have havg : ∑ k ∈ I, jump k ≤ ∑ _k ∈ I, (2 / (c * (I.card : ℝ)) : ℝ) := by
    rw [hconst]
    exact hsum_I
  obtain ⟨k, hkI, hk⟩ := Finset.exists_le_of_sum_le hI havg
  refine ⟨k, hkI, fun x hx ↦ ?_⟩
  have hklt : k < m := Finset.mem_range.mp (hIgrid hkI)
  have herr := cellSecant_error_le_slope_jump hm hmargin hklt hconv hx
  have hinv : 0 < (m : ℝ)⁻¹ := by positivity
  have hscaled :
      (cellSecant f m k x - f x) ≤
        (2 / (c * (I.card : ℝ))) * (m : ℝ)⁻¹ := by
    exact herr.2.trans (mul_le_mul_of_nonneg_right hk (le_of_lt hinv))
  rw [abs_sub_comm, abs_of_nonneg herr.1]
  calc
    cellSecant f m k x - f x
        ≤ (2 / (c * (I.card : ℝ))) * (m : ℝ)⁻¹ := hscaled
    _ = 2 / (c * (m : ℝ) * (I.card : ℝ)) := by
      field_simp

end

end Erdos186.ConvexApprox
