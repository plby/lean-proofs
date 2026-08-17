/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ErdosProblems.Erdos230.Angular
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Finite circle grids for Erdős Problem 230

The random coefficient correction is first controlled on a finite grid.
These elementary estimates pass from that grid to the whole circle without
using Bernstein's inequality.
-/

namespace Erdos230

noncomputable section

theorem norm_unitPoint_sub_le (theta phi : ℝ) :
    ‖unitPoint theta - unitPoint phi‖ ≤ |theta - phi| := by
  have hfactor : unitPoint theta - unitPoint phi =
      unitPoint phi * (unitPoint (theta - phi) - 1) := by
    rw [unitPoint, unitPoint, unitPoint]
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hfactor, norm_mul, norm_unitPoint, one_mul, unitPoint]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := theta - phi)
  simpa [mul_comm, Real.norm_eq_abs] using h

theorem norm_periodicPoint_sub_le (theta phi : ℝ) :
    ‖periodicPoint theta - periodicPoint phi‖ ≤
      2 * Real.pi * |theta - phi| := by
  rw [periodicPoint, periodicPoint]
  refine (norm_unitPoint_sub_le _ _).trans ?_
  rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]

theorem norm_pow_sub_pow_le_of_norm_eq_one (z w : ℂ)
    (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) (k : ℕ) :
    ‖z ^ k - w ^ k‖ ≤ k * ‖z - w‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, pow_succ]
      have hid : z ^ k * z - w ^ k * w =
          z ^ k * (z - w) + (z ^ k - w ^ k) * w := by ring
      rw [hid]
      calc
        ‖z ^ k * (z - w) + (z ^ k - w ^ k) * w‖ ≤
            ‖z ^ k * (z - w)‖ + ‖(z ^ k - w ^ k) * w‖ := norm_add_le _ _
        _ = ‖z - w‖ + ‖z ^ k - w ^ k‖ := by
          simp [norm_pow, hz, hw]
        _ ≤ ‖z - w‖ + k * ‖z - w‖ := by gcongr
        _ = ((k + 1 : ℕ) : ℝ) * ‖z - w‖ := by
          norm_num
          ring

/-- Every real phase has a representative within `1 / G` of a point on the
period-one grid indexed by `Fin G`. -/
theorem exists_gridIndex (G : ℕ) (hG : 0 < G) (theta : ℝ) :
    ∃ j : Fin G,
      0 ≤ Int.fract theta - (j : ℕ) / (G : ℝ) ∧
      Int.fract theta - (j : ℕ) / (G : ℝ) < 1 / (G : ℝ) := by
  let j0 : ℕ := ⌊(G : ℝ) * Int.fract theta⌋₊
  have hnonneg : 0 ≤ (G : ℝ) * Int.fract theta :=
    mul_nonneg (by positivity) (Int.fract_nonneg theta)
  have hjlt : j0 < G := by
    apply (Nat.floor_lt hnonneg).2
    have hGreal : (0 : ℝ) < G := by exact_mod_cast hG
    simpa using (mul_lt_mul_of_pos_left (Int.fract_lt_one theta) hGreal)
  let j : Fin G := ⟨j0, hjlt⟩
  refine ⟨j, ?_, ?_⟩
  · have hfloor : (j0 : ℝ) ≤ (G : ℝ) * Int.fract theta :=
      Nat.floor_le hnonneg
    have hGreal : (0 : ℝ) < G := by exact_mod_cast hG
    apply sub_nonneg.mpr
    rw [div_le_iff₀ hGreal]
    simpa [j, j0, mul_comm, add_comm] using hfloor
  · have hfloor : (G : ℝ) * Int.fract theta < (j0 : ℝ) + 1 :=
      Nat.lt_floor_add_one ((G : ℝ) * Int.fract theta)
    have hGreal : (0 : ℝ) < G := by exact_mod_cast hG
    rw [sub_lt_iff_lt_add, ← add_div]
    apply (lt_div_iff₀ hGreal).2
    simpa [j, j0, mul_comm, add_comm] using hfloor

/-- Direct coefficientwise Lipschitz bound for a degree-`n` Fourier sum
whose coefficients have norm at most one. -/
theorem norm_normalizedZerothValue_sub_le_of_norm_le {n : ℕ}
    (c : Fin (n + 1) → ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hc : ∀ k, ‖c k‖ ≤ L) (theta phi : ℝ) :
    ‖normalizedZerothValue c theta - normalizedZerothValue c phi‖ ≤
      L * (2 * Real.pi * |theta - phi| * (n + 1) * n) := by
  classical
  rw [normalizedZerothValue, normalizedZerothValue, ← Finset.sum_sub_distrib]
  calc
    ‖∑ k : Fin (n + 1),
        (c k * periodicPoint theta ^ k.1 - c k * periodicPoint phi ^ k.1)‖ ≤
        ∑ k : Fin (n + 1),
          ‖c k * periodicPoint theta ^ k.1 - c k * periodicPoint phi ^ k.1‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _k : Fin (n + 1),
        (L * (2 * Real.pi * |theta - phi| * n)) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [← mul_sub, norm_mul]
      calc
        ‖c k‖ * ‖periodicPoint theta ^ k.1 - periodicPoint phi ^ k.1‖ ≤
            L * ‖periodicPoint theta ^ k.1 - periodicPoint phi ^ k.1‖ := by
          gcongr
          exact hc k
        _ ≤ L * (k.1 * ‖periodicPoint theta - periodicPoint phi‖) := by
          gcongr
          simpa using norm_pow_sub_pow_le_of_norm_eq_one
            (periodicPoint theta) (periodicPoint phi)
            (norm_periodicPoint theta) (norm_periodicPoint phi) k.1
        _ ≤ L * (k.1 * (2 * Real.pi * |theta - phi|)) := by
          gcongr
          exact norm_periodicPoint_sub_le theta phi
        _ ≤ L * (n * (2 * Real.pi * |theta - phi|)) := by
          gcongr
          exact_mod_cast (show k.1 ≤ n by omega)
        _ = L * (2 * Real.pi * |theta - phi| * n) := by ring
    _ = L * (2 * Real.pi * |theta - phi| * (n + 1) * n) := by
      simp
      ring

theorem norm_normalizedZerothValue_sub_le {n : ℕ}
    (c : Fin (n + 1) → ℂ) (hc : ∀ k, ‖c k‖ ≤ 1) (theta phi : ℝ) :
    ‖normalizedZerothValue c theta - normalizedZerothValue c phi‖ ≤
      2 * Real.pi * |theta - phi| * (n + 1) * n := by
  simpa using
    norm_normalizedZerothValue_sub_le_of_norm_le c 1 zero_le_one hc theta phi

theorem normalizedZerothValue_fract {n : ℕ}
    (c : Fin (n + 1) → ℂ) (theta : ℝ) :
    normalizedZerothValue c (Int.fract theta) = normalizedZerothValue c theta := by
  classical
  rw [normalizedZerothValue, normalizedZerothValue]
  apply Finset.sum_congr rfl
  intro k hk
  rw [periodicPoint_fract]

/-- A strict bound on a period-one grid gives a whole-circle bound with an
explicit coefficientwise interpolation loss. -/
theorem norm_normalizedZerothValue_lt_of_grid {n G : ℕ}
    (c : Fin (n + 1) → ℂ) (hc : ∀ k, ‖c k‖ ≤ 2)
    (hG : 0 < G) (R : ℝ)
    (hgrid : ∀ j : Fin G,
      ‖normalizedZerothValue c ((j : ℕ) / (G : ℝ))‖ < R)
    (theta : ℝ) :
    ‖normalizedZerothValue c theta‖ <
      4 * Real.pi * (n + 1) * n / G + R := by
  obtain ⟨j, hj0, hj1⟩ := exists_gridIndex G hG theta
  let x := Int.fract theta
  let y : ℝ := (j : ℕ) / (G : ℝ)
  have hxy : |x - y| ≤ 1 / (G : ℝ) := by
    rw [abs_of_nonneg]
    · exact hj1.le
    · exact hj0
  have hinterp := norm_normalizedZerothValue_sub_le_of_norm_le
    c 2 (by norm_num) hc x y
  have hinterp' :
      ‖normalizedZerothValue c x - normalizedZerothValue c y‖ ≤
        4 * Real.pi * (n + 1) * n / G := by
    calc
      ‖normalizedZerothValue c x - normalizedZerothValue c y‖ ≤
          2 * (2 * Real.pi * |x - y| * (n + 1) * n) := hinterp
      _ ≤ 2 * (2 * Real.pi * (1 / (G : ℝ)) * (n + 1) * n) := by
        gcongr
      _ = 4 * Real.pi * (n + 1) * n / G := by ring
  rw [← normalizedZerothValue_fract c theta]
  calc
    ‖normalizedZerothValue c x‖ =
        ‖(normalizedZerothValue c x - normalizedZerothValue c y) +
          normalizedZerothValue c y‖ := by ring_nf
    _ ≤ ‖normalizedZerothValue c x - normalizedZerothValue c y‖ +
        ‖normalizedZerothValue c y‖ := norm_add_le _ _
    _ < 4 * Real.pi * (n + 1) * n / G + R :=
      add_lt_add_of_le_of_lt hinterp' (hgrid j)

end

end Erdos230
