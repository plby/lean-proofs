import ErdosProblems.Erdos633b.TilingResidueCondition
import Mathlib.Tactic.NormNum.GCD

/-! Exact coprime residue witnesses exclude the listed rational phases
for one group-2 outer shape. All weights and residues are checked in Lean. -/

namespace Erdos633b.Tiling

theorem groupTwo_residue_exclusion_7_1_4 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = 2 * d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 1 / 7 := by
  intro hα
  let w : Fin 3 → ℕ := ![6, 1, 14]
  let a : Fin 3 → ℕ := ![12, 2, 7]
  have hw (i : Fin 3) : d.tile.angle i = (w i : ℝ) * (Real.pi / 21) := by
    fin_cases i
    · change d.tile.angle 0 = ((6 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 1 = ((1 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 2 = ((14 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have ha (i : Fin 3) : T.angle i = (a i : ℝ) * (Real.pi / 21) := by
    fin_cases i
    · change T.angle 0 = ((12 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((2 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((7 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have hh := d.coprime_angle_residue_sum_eq 21 (by decide) w a hw ha
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by decide) (by decide) 5 (by norm_num [Nat.Coprime])
  exact (by decide : angleResidueSum 21 5 w ≠ angleResidueSum 21 5 a) hh

theorem groupTwo_residue_exclusion_8_1_4 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = 2 * d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 1 / 8 := by
  intro hα
  let w : Fin 3 → ℕ := ![3, 1, 8]
  let a : Fin 3 → ℕ := ![6, 2, 4]
  have hw (i : Fin 3) : d.tile.angle i = (w i : ℝ) * (Real.pi / 12) := by
    fin_cases i
    · change d.tile.angle 0 = ((3 : ℕ) : ℝ) * (Real.pi / 12)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 1 = ((1 : ℕ) : ℝ) * (Real.pi / 12)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 2 = ((8 : ℕ) : ℝ) * (Real.pi / 12)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have ha (i : Fin 3) : T.angle i = (a i : ℝ) * (Real.pi / 12) := by
    fin_cases i
    · change T.angle 0 = ((6 : ℕ) : ℝ) * (Real.pi / 12)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((2 : ℕ) : ℝ) * (Real.pi / 12)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((4 : ℕ) : ℝ) * (Real.pi / 12)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have hh := d.coprime_angle_residue_sum_eq 12 (by decide) w a hw ha
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by decide) (by decide) 5 (by norm_num [Nat.Coprime])
  exact (by decide : angleResidueSum 12 5 w ≠ angleResidueSum 12 5 a) hh

theorem groupTwo_residue_exclusion_9_1_4 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = 2 * d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 1 / 9 := by
  intro hα
  let w : Fin 3 → ℕ := ![2, 1, 6]
  let a : Fin 3 → ℕ := ![4, 2, 3]
  have hw (i : Fin 3) : d.tile.angle i = (w i : ℝ) * (Real.pi / 9) := by
    fin_cases i
    · change d.tile.angle 0 = ((2 : ℕ) : ℝ) * (Real.pi / 9)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 1 = ((1 : ℕ) : ℝ) * (Real.pi / 9)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 2 = ((6 : ℕ) : ℝ) * (Real.pi / 9)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have ha (i : Fin 3) : T.angle i = (a i : ℝ) * (Real.pi / 9) := by
    fin_cases i
    · change T.angle 0 = ((4 : ℕ) : ℝ) * (Real.pi / 9)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((2 : ℕ) : ℝ) * (Real.pi / 9)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((3 : ℕ) : ℝ) * (Real.pi / 9)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have hh := d.coprime_angle_residue_sum_eq 9 (by decide) w a hw ha
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by decide) (by decide) 7 (by norm_num [Nat.Coprime])
  exact (by decide : angleResidueSum 9 7 w ≠ angleResidueSum 9 7 a) hh

theorem groupTwo_residue_exclusion_10_1_4 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = 2 * d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 1 / 10 := by
  intro hα
  let w : Fin 3 → ℕ := ![3, 2, 10]
  let a : Fin 3 → ℕ := ![6, 4, 5]
  have hw (i : Fin 3) : d.tile.angle i = (w i : ℝ) * (Real.pi / 15) := by
    fin_cases i
    · change d.tile.angle 0 = ((3 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 1 = ((2 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 2 = ((10 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have ha (i : Fin 3) : T.angle i = (a i : ℝ) * (Real.pi / 15) := by
    fin_cases i
    · change T.angle 0 = ((6 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((4 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((5 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have hh := d.coprime_angle_residue_sum_eq 15 (by decide) w a hw ha
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by decide) (by decide) 11 (by norm_num [Nat.Coprime])
  exact (by decide : angleResidueSum 15 11 w ≠ angleResidueSum 15 11 a) hh

theorem groupTwo_residue_exclusion_11_1_4 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = 2 * d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 1 / 11 := by
  intro hα
  let w : Fin 3 → ℕ := ![6, 5, 22]
  let a : Fin 3 → ℕ := ![12, 10, 11]
  have hw (i : Fin 3) : d.tile.angle i = (w i : ℝ) * (Real.pi / 33) := by
    fin_cases i
    · change d.tile.angle 0 = ((6 : ℕ) : ℝ) * (Real.pi / 33)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 1 = ((5 : ℕ) : ℝ) * (Real.pi / 33)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 2 = ((22 : ℕ) : ℝ) * (Real.pi / 33)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have ha (i : Fin 3) : T.angle i = (a i : ℝ) * (Real.pi / 33) := by
    fin_cases i
    · change T.angle 0 = ((12 : ℕ) : ℝ) * (Real.pi / 33)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((10 : ℕ) : ℝ) * (Real.pi / 33)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((11 : ℕ) : ℝ) * (Real.pi / 33)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have hh := d.coprime_angle_residue_sum_eq 33 (by decide) w a hw ha
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by decide) (by decide) 23 (by norm_num [Nat.Coprime])
  exact (by decide : angleResidueSum 33 23 w ≠ angleResidueSum 33 23 a) hh

theorem groupTwo_residue_exclusion_13_1_4 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = 2 * d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 1 / 13 := by
  intro hα
  let w : Fin 3 → ℕ := ![6, 7, 26]
  let a : Fin 3 → ℕ := ![12, 14, 13]
  have hw (i : Fin 3) : d.tile.angle i = (w i : ℝ) * (Real.pi / 39) := by
    fin_cases i
    · change d.tile.angle 0 = ((6 : ℕ) : ℝ) * (Real.pi / 39)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 1 = ((7 : ℕ) : ℝ) * (Real.pi / 39)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 2 = ((26 : ℕ) : ℝ) * (Real.pi / 39)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have ha (i : Fin 3) : T.angle i = (a i : ℝ) * (Real.pi / 39) := by
    fin_cases i
    · change T.angle 0 = ((12 : ℕ) : ℝ) * (Real.pi / 39)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((14 : ℕ) : ℝ) * (Real.pi / 39)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((13 : ℕ) : ℝ) * (Real.pi / 39)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have hh := d.coprime_angle_residue_sum_eq 39 (by decide) w a hw ha
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by decide) (by decide) 29 (by norm_num [Nat.Coprime])
  exact (by decide : angleResidueSum 39 29 w ≠ angleResidueSum 39 29 a) hh

theorem groupTwo_residue_exclusion_13_2_4 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = 2 * d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 2 / 13 := by
  intro hα
  let w : Fin 3 → ℕ := ![12, 1, 26]
  let a : Fin 3 → ℕ := ![24, 2, 13]
  have hw (i : Fin 3) : d.tile.angle i = (w i : ℝ) * (Real.pi / 39) := by
    fin_cases i
    · change d.tile.angle 0 = ((12 : ℕ) : ℝ) * (Real.pi / 39)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 1 = ((1 : ℕ) : ℝ) * (Real.pi / 39)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 2 = ((26 : ℕ) : ℝ) * (Real.pi / 39)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have ha (i : Fin 3) : T.angle i = (a i : ℝ) * (Real.pi / 39) := by
    fin_cases i
    · change T.angle 0 = ((24 : ℕ) : ℝ) * (Real.pi / 39)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((2 : ℕ) : ℝ) * (Real.pi / 39)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((13 : ℕ) : ℝ) * (Real.pi / 39)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have hh := d.coprime_angle_residue_sum_eq 39 (by decide) w a hw ha
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by decide) (by decide) 11 (by norm_num [Nat.Coprime])
  exact (by decide : angleResidueSum 39 11 w ≠ angleResidueSum 39 11 a) hh

theorem groupTwo_residue_exclusion_14_1_4 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = 2 * d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 1 / 14 := by
  intro hα
  let w : Fin 3 → ℕ := ![3, 4, 14]
  let a : Fin 3 → ℕ := ![6, 8, 7]
  have hw (i : Fin 3) : d.tile.angle i = (w i : ℝ) * (Real.pi / 21) := by
    fin_cases i
    · change d.tile.angle 0 = ((3 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 1 = ((4 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 2 = ((14 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have ha (i : Fin 3) : T.angle i = (a i : ℝ) * (Real.pi / 21) := by
    fin_cases i
    · change T.angle 0 = ((6 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((8 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((7 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have hh := d.coprime_angle_residue_sum_eq 21 (by decide) w a hw ha
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by decide) (by decide) 17 (by norm_num [Nat.Coprime])
  exact (by decide : angleResidueSum 21 17 w ≠ angleResidueSum 21 17 a) hh

theorem groupTwo_residue_exclusion_15_1_4 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = 2 * d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 1 / 15 := by
  intro hα
  let w : Fin 3 → ℕ := ![2, 3, 10]
  let a : Fin 3 → ℕ := ![4, 6, 5]
  have hw (i : Fin 3) : d.tile.angle i = (w i : ℝ) * (Real.pi / 15) := by
    fin_cases i
    · change d.tile.angle 0 = ((2 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 1 = ((3 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 2 = ((10 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have ha (i : Fin 3) : T.angle i = (a i : ℝ) * (Real.pi / 15) := by
    fin_cases i
    · change T.angle 0 = ((4 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((6 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((5 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have hh := d.coprime_angle_residue_sum_eq 15 (by decide) w a hw ha
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by decide) (by decide) 11 (by norm_num [Nat.Coprime])
  exact (by decide : angleResidueSum 15 11 w ≠ angleResidueSum 15 11 a) hh

theorem groupTwo_residue_exclusion_16_1_4 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = 2 * d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 1 / 16 := by
  intro hα
  let w : Fin 3 → ℕ := ![3, 5, 16]
  let a : Fin 3 → ℕ := ![6, 10, 8]
  have hw (i : Fin 3) : d.tile.angle i = (w i : ℝ) * (Real.pi / 24) := by
    fin_cases i
    · change d.tile.angle 0 = ((3 : ℕ) : ℝ) * (Real.pi / 24)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 1 = ((5 : ℕ) : ℝ) * (Real.pi / 24)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 2 = ((16 : ℕ) : ℝ) * (Real.pi / 24)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have ha (i : Fin 3) : T.angle i = (a i : ℝ) * (Real.pi / 24) := by
    fin_cases i
    · change T.angle 0 = ((6 : ℕ) : ℝ) * (Real.pi / 24)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((10 : ℕ) : ℝ) * (Real.pi / 24)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((8 : ℕ) : ℝ) * (Real.pi / 24)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have hh := d.coprime_angle_residue_sum_eq 24 (by decide) w a hw ha
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by decide) (by decide) 11 (by norm_num [Nat.Coprime])
  exact (by decide : angleResidueSum 24 11 w ≠ angleResidueSum 24 11 a) hh

theorem groupTwo_residue_exclusion_18_1_4 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = 2 * d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 1 / 18 := by
  intro hα
  let w : Fin 3 → ℕ := ![1, 2, 6]
  let a : Fin 3 → ℕ := ![2, 4, 3]
  have hw (i : Fin 3) : d.tile.angle i = (w i : ℝ) * (Real.pi / 9) := by
    fin_cases i
    · change d.tile.angle 0 = ((1 : ℕ) : ℝ) * (Real.pi / 9)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 1 = ((2 : ℕ) : ℝ) * (Real.pi / 9)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 2 = ((6 : ℕ) : ℝ) * (Real.pi / 9)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have ha (i : Fin 3) : T.angle i = (a i : ℝ) * (Real.pi / 9) := by
    fin_cases i
    · change T.angle 0 = ((2 : ℕ) : ℝ) * (Real.pi / 9)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((4 : ℕ) : ℝ) * (Real.pi / 9)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((3 : ℕ) : ℝ) * (Real.pi / 9)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have hh := d.coprime_angle_residue_sum_eq 9 (by decide) w a hw ha
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by decide) (by decide) 7 (by norm_num [Nat.Coprime])
  exact (by decide : angleResidueSum 9 7 w ≠ angleResidueSum 9 7 a) hh

theorem groupTwo_residue_exclusion_20_1_4 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = 2 * d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 1 / 20 := by
  intro hα
  let w : Fin 3 → ℕ := ![3, 7, 20]
  let a : Fin 3 → ℕ := ![6, 14, 10]
  have hw (i : Fin 3) : d.tile.angle i = (w i : ℝ) * (Real.pi / 30) := by
    fin_cases i
    · change d.tile.angle 0 = ((3 : ℕ) : ℝ) * (Real.pi / 30)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 1 = ((7 : ℕ) : ℝ) * (Real.pi / 30)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 2 = ((20 : ℕ) : ℝ) * (Real.pi / 30)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have ha (i : Fin 3) : T.angle i = (a i : ℝ) * (Real.pi / 30) := by
    fin_cases i
    · change T.angle 0 = ((6 : ℕ) : ℝ) * (Real.pi / 30)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((14 : ℕ) : ℝ) * (Real.pi / 30)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((10 : ℕ) : ℝ) * (Real.pi / 30)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have hh := d.coprime_angle_residue_sum_eq 30 (by decide) w a hw ha
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by decide) (by decide) 7 (by norm_num [Nat.Coprime])
  exact (by decide : angleResidueSum 30 7 w ≠ angleResidueSum 30 7 a) hh

theorem groupTwo_residue_exclusion_20_3_4 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = 2 * d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 3 / 20 := by
  intro hα
  let w : Fin 3 → ℕ := ![9, 1, 20]
  let a : Fin 3 → ℕ := ![18, 2, 10]
  have hw (i : Fin 3) : d.tile.angle i = (w i : ℝ) * (Real.pi / 30) := by
    fin_cases i
    · change d.tile.angle 0 = ((9 : ℕ) : ℝ) * (Real.pi / 30)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 1 = ((1 : ℕ) : ℝ) * (Real.pi / 30)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 2 = ((20 : ℕ) : ℝ) * (Real.pi / 30)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have ha (i : Fin 3) : T.angle i = (a i : ℝ) * (Real.pi / 30) := by
    fin_cases i
    · change T.angle 0 = ((18 : ℕ) : ℝ) * (Real.pi / 30)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((2 : ℕ) : ℝ) * (Real.pi / 30)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((10 : ℕ) : ℝ) * (Real.pi / 30)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have hh := d.coprime_angle_residue_sum_eq 30 (by decide) w a hw ha
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by decide) (by decide) 11 (by norm_num [Nat.Coprime])
  exact (by decide : angleResidueSum 30 11 w ≠ angleResidueSum 30 11 a) hh

theorem groupTwo_residue_exclusion_21_1_4 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = 2 * d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 1 / 21 := by
  intro hα
  let w : Fin 3 → ℕ := ![2, 5, 14]
  let a : Fin 3 → ℕ := ![4, 10, 7]
  have hw (i : Fin 3) : d.tile.angle i = (w i : ℝ) * (Real.pi / 21) := by
    fin_cases i
    · change d.tile.angle 0 = ((2 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 1 = ((5 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 2 = ((14 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have ha (i : Fin 3) : T.angle i = (a i : ℝ) * (Real.pi / 21) := by
    fin_cases i
    · change T.angle 0 = ((4 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((10 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((7 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have hh := d.coprime_angle_residue_sum_eq 21 (by decide) w a hw ha
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by decide) (by decide) 5 (by norm_num [Nat.Coprime])
  exact (by decide : angleResidueSum 21 5 w ≠ angleResidueSum 21 5 a) hh

theorem groupTwo_residue_exclusion_21_2_4 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = 2 * d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 2 / 21 := by
  intro hα
  let w : Fin 3 → ℕ := ![4, 3, 14]
  let a : Fin 3 → ℕ := ![8, 6, 7]
  have hw (i : Fin 3) : d.tile.angle i = (w i : ℝ) * (Real.pi / 21) := by
    fin_cases i
    · change d.tile.angle 0 = ((4 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 1 = ((3 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 2 = ((14 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have ha (i : Fin 3) : T.angle i = (a i : ℝ) * (Real.pi / 21) := by
    fin_cases i
    · change T.angle 0 = ((8 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((6 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((7 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have hh := d.coprime_angle_residue_sum_eq 21 (by decide) w a hw ha
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by decide) (by decide) 17 (by norm_num [Nat.Coprime])
  exact (by decide : angleResidueSum 21 17 w ≠ angleResidueSum 21 17 a) hh

theorem groupTwo_residue_exclusion_22_1_4 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = 2 * d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 1 / 22 := by
  intro hα
  let w : Fin 3 → ℕ := ![3, 8, 22]
  let a : Fin 3 → ℕ := ![6, 16, 11]
  have hw (i : Fin 3) : d.tile.angle i = (w i : ℝ) * (Real.pi / 33) := by
    fin_cases i
    · change d.tile.angle 0 = ((3 : ℕ) : ℝ) * (Real.pi / 33)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 1 = ((8 : ℕ) : ℝ) * (Real.pi / 33)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 2 = ((22 : ℕ) : ℝ) * (Real.pi / 33)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have ha (i : Fin 3) : T.angle i = (a i : ℝ) * (Real.pi / 33) := by
    fin_cases i
    · change T.angle 0 = ((6 : ℕ) : ℝ) * (Real.pi / 33)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((16 : ℕ) : ℝ) * (Real.pi / 33)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((11 : ℕ) : ℝ) * (Real.pi / 33)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have hh := d.coprime_angle_residue_sum_eq 33 (by decide) w a hw ha
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by decide) (by decide) 5 (by norm_num [Nat.Coprime])
  exact (by decide : angleResidueSum 33 5 w ≠ angleResidueSum 33 5 a) hh

theorem groupTwo_residue_exclusion_22_3_4 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = 2 * d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 3 / 22 := by
  intro hα
  let w : Fin 3 → ℕ := ![9, 2, 22]
  let a : Fin 3 → ℕ := ![18, 4, 11]
  have hw (i : Fin 3) : d.tile.angle i = (w i : ℝ) * (Real.pi / 33) := by
    fin_cases i
    · change d.tile.angle 0 = ((9 : ℕ) : ℝ) * (Real.pi / 33)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 1 = ((2 : ℕ) : ℝ) * (Real.pi / 33)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 2 = ((22 : ℕ) : ℝ) * (Real.pi / 33)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have ha (i : Fin 3) : T.angle i = (a i : ℝ) * (Real.pi / 33) := by
    fin_cases i
    · change T.angle 0 = ((18 : ℕ) : ℝ) * (Real.pi / 33)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((4 : ℕ) : ℝ) * (Real.pi / 33)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((11 : ℕ) : ℝ) * (Real.pi / 33)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have hh := d.coprime_angle_residue_sum_eq 33 (by decide) w a hw ha
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by decide) (by decide) 5 (by norm_num [Nat.Coprime])
  exact (by decide : angleResidueSum 33 5 w ≠ angleResidueSum 33 5 a) hh

theorem groupTwo_residue_exclusion_24_1_4 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = 2 * d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 1 / 24 := by
  intro hα
  let w : Fin 3 → ℕ := ![1, 3, 8]
  let a : Fin 3 → ℕ := ![2, 6, 4]
  have hw (i : Fin 3) : d.tile.angle i = (w i : ℝ) * (Real.pi / 12) := by
    fin_cases i
    · change d.tile.angle 0 = ((1 : ℕ) : ℝ) * (Real.pi / 12)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 1 = ((3 : ℕ) : ℝ) * (Real.pi / 12)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 2 = ((8 : ℕ) : ℝ) * (Real.pi / 12)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have ha (i : Fin 3) : T.angle i = (a i : ℝ) * (Real.pi / 12) := by
    fin_cases i
    · change T.angle 0 = ((2 : ℕ) : ℝ) * (Real.pi / 12)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((6 : ℕ) : ℝ) * (Real.pi / 12)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((4 : ℕ) : ℝ) * (Real.pi / 12)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have hh := d.coprime_angle_residue_sum_eq 12 (by decide) w a hw ha
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by decide) (by decide) 5 (by norm_num [Nat.Coprime])
  exact (by decide : angleResidueSum 12 5 w ≠ angleResidueSum 12 5 a) hh

theorem groupTwo_residue_exclusion_26_1_4 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = 2 * d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 1 / 26 := by
  intro hα
  let w : Fin 3 → ℕ := ![3, 10, 26]
  let a : Fin 3 → ℕ := ![6, 20, 13]
  have hw (i : Fin 3) : d.tile.angle i = (w i : ℝ) * (Real.pi / 39) := by
    fin_cases i
    · change d.tile.angle 0 = ((3 : ℕ) : ℝ) * (Real.pi / 39)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 1 = ((10 : ℕ) : ℝ) * (Real.pi / 39)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 2 = ((26 : ℕ) : ℝ) * (Real.pi / 39)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have ha (i : Fin 3) : T.angle i = (a i : ℝ) * (Real.pi / 39) := by
    fin_cases i
    · change T.angle 0 = ((6 : ℕ) : ℝ) * (Real.pi / 39)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((20 : ℕ) : ℝ) * (Real.pi / 39)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((13 : ℕ) : ℝ) * (Real.pi / 39)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have hh := d.coprime_angle_residue_sum_eq 39 (by decide) w a hw ha
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by decide) (by decide) 5 (by norm_num [Nat.Coprime])
  exact (by decide : angleResidueSum 39 5 w ≠ angleResidueSum 39 5 a) hh

theorem groupTwo_residue_exclusion_26_3_4 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = 2 * d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 3 / 26 := by
  intro hα
  let w : Fin 3 → ℕ := ![9, 4, 26]
  let a : Fin 3 → ℕ := ![18, 8, 13]
  have hw (i : Fin 3) : d.tile.angle i = (w i : ℝ) * (Real.pi / 39) := by
    fin_cases i
    · change d.tile.angle 0 = ((9 : ℕ) : ℝ) * (Real.pi / 39)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 1 = ((4 : ℕ) : ℝ) * (Real.pi / 39)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 2 = ((26 : ℕ) : ℝ) * (Real.pi / 39)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have ha (i : Fin 3) : T.angle i = (a i : ℝ) * (Real.pi / 39) := by
    fin_cases i
    · change T.angle 0 = ((18 : ℕ) : ℝ) * (Real.pi / 39)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((8 : ℕ) : ℝ) * (Real.pi / 39)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((13 : ℕ) : ℝ) * (Real.pi / 39)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have hh := d.coprime_angle_residue_sum_eq 39 (by decide) w a hw ha
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by decide) (by decide) 7 (by norm_num [Nat.Coprime])
  exact (by decide : angleResidueSum 39 7 w ≠ angleResidueSum 39 7 a) hh

theorem groupTwo_residue_exclusion_28_1_4 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = 2 * d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 1 / 28 := by
  intro hα
  let w : Fin 3 → ℕ := ![3, 11, 28]
  let a : Fin 3 → ℕ := ![6, 22, 14]
  have hw (i : Fin 3) : d.tile.angle i = (w i : ℝ) * (Real.pi / 42) := by
    fin_cases i
    · change d.tile.angle 0 = ((3 : ℕ) : ℝ) * (Real.pi / 42)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 1 = ((11 : ℕ) : ℝ) * (Real.pi / 42)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 2 = ((28 : ℕ) : ℝ) * (Real.pi / 42)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have ha (i : Fin 3) : T.angle i = (a i : ℝ) * (Real.pi / 42) := by
    fin_cases i
    · change T.angle 0 = ((6 : ℕ) : ℝ) * (Real.pi / 42)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((22 : ℕ) : ℝ) * (Real.pi / 42)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((14 : ℕ) : ℝ) * (Real.pi / 42)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have hh := d.coprime_angle_residue_sum_eq 42 (by decide) w a hw ha
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by decide) (by decide) 5 (by norm_num [Nat.Coprime])
  exact (by decide : angleResidueSum 42 5 w ≠ angleResidueSum 42 5 a) hh

theorem groupTwo_residue_exclusion_28_3_4 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = 2 * d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 3 / 28 := by
  intro hα
  let w : Fin 3 → ℕ := ![9, 5, 28]
  let a : Fin 3 → ℕ := ![18, 10, 14]
  have hw (i : Fin 3) : d.tile.angle i = (w i : ℝ) * (Real.pi / 42) := by
    fin_cases i
    · change d.tile.angle 0 = ((9 : ℕ) : ℝ) * (Real.pi / 42)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 1 = ((5 : ℕ) : ℝ) * (Real.pi / 42)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 2 = ((28 : ℕ) : ℝ) * (Real.pi / 42)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have ha (i : Fin 3) : T.angle i = (a i : ℝ) * (Real.pi / 42) := by
    fin_cases i
    · change T.angle 0 = ((18 : ℕ) : ℝ) * (Real.pi / 42)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((10 : ℕ) : ℝ) * (Real.pi / 42)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((14 : ℕ) : ℝ) * (Real.pi / 42)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have hh := d.coprime_angle_residue_sum_eq 42 (by decide) w a hw ha
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by decide) (by decide) 11 (by norm_num [Nat.Coprime])
  exact (by decide : angleResidueSum 42 11 w ≠ angleResidueSum 42 11 a) hh

theorem groupTwo_residue_exclusion_36_1_4 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = 2 * d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 1 / 36 := by
  intro hα
  let w : Fin 3 → ℕ := ![1, 5, 12]
  let a : Fin 3 → ℕ := ![2, 10, 6]
  have hw (i : Fin 3) : d.tile.angle i = (w i : ℝ) * (Real.pi / 18) := by
    fin_cases i
    · change d.tile.angle 0 = ((1 : ℕ) : ℝ) * (Real.pi / 18)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 1 = ((5 : ℕ) : ℝ) * (Real.pi / 18)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 2 = ((12 : ℕ) : ℝ) * (Real.pi / 18)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have ha (i : Fin 3) : T.angle i = (a i : ℝ) * (Real.pi / 18) := by
    fin_cases i
    · change T.angle 0 = ((2 : ℕ) : ℝ) * (Real.pi / 18)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((10 : ℕ) : ℝ) * (Real.pi / 18)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((6 : ℕ) : ℝ) * (Real.pi / 18)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have hh := d.coprime_angle_residue_sum_eq 18 (by decide) w a hw ha
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by decide) (by decide) 5 (by norm_num [Nat.Coprime])
  exact (by decide : angleResidueSum 18 5 w ≠ angleResidueSum 18 5 a) hh

theorem groupTwo_residue_exclusion_36_5_4 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = 2 * d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 5 / 36 := by
  intro hα
  let w : Fin 3 → ℕ := ![5, 1, 12]
  let a : Fin 3 → ℕ := ![10, 2, 6]
  have hw (i : Fin 3) : d.tile.angle i = (w i : ℝ) * (Real.pi / 18) := by
    fin_cases i
    · change d.tile.angle 0 = ((5 : ℕ) : ℝ) * (Real.pi / 18)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 1 = ((1 : ℕ) : ℝ) * (Real.pi / 18)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 2 = ((12 : ℕ) : ℝ) * (Real.pi / 18)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have ha (i : Fin 3) : T.angle i = (a i : ℝ) * (Real.pi / 18) := by
    fin_cases i
    · change T.angle 0 = ((10 : ℕ) : ℝ) * (Real.pi / 18)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((2 : ℕ) : ℝ) * (Real.pi / 18)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((6 : ℕ) : ℝ) * (Real.pi / 18)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have hh := d.coprime_angle_residue_sum_eq 18 (by decide) w a hw ha
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by decide) (by decide) 5 (by norm_num [Nat.Coprime])
  exact (by decide : angleResidueSum 18 5 w ≠ angleResidueSum 18 5 a) hh

theorem groupTwo_residue_exclusion_42_1_4 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = 2 * d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 1 / 42 := by
  intro hα
  let w : Fin 3 → ℕ := ![1, 6, 14]
  let a : Fin 3 → ℕ := ![2, 12, 7]
  have hw (i : Fin 3) : d.tile.angle i = (w i : ℝ) * (Real.pi / 21) := by
    fin_cases i
    · change d.tile.angle 0 = ((1 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 1 = ((6 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 2 = ((14 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have ha (i : Fin 3) : T.angle i = (a i : ℝ) * (Real.pi / 21) := by
    fin_cases i
    · change T.angle 0 = ((2 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((12 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((7 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have hh := d.coprime_angle_residue_sum_eq 21 (by decide) w a hw ha
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by decide) (by decide) 5 (by norm_num [Nat.Coprime])
  exact (by decide : angleResidueSum 21 5 w ≠ angleResidueSum 21 5 a) hh

theorem groupTwo_residue_exclusion_42_5_4 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = 2 * d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 5 / 42 := by
  intro hα
  let w : Fin 3 → ℕ := ![5, 2, 14]
  let a : Fin 3 → ℕ := ![10, 4, 7]
  have hw (i : Fin 3) : d.tile.angle i = (w i : ℝ) * (Real.pi / 21) := by
    fin_cases i
    · change d.tile.angle 0 = ((5 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 1 = ((2 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 2 = ((14 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have ha (i : Fin 3) : T.angle i = (a i : ℝ) * (Real.pi / 21) := by
    fin_cases i
    · change T.angle 0 = ((10 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((4 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((7 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have hh := d.coprime_angle_residue_sum_eq 21 (by decide) w a hw ha
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by decide) (by decide) 5 (by norm_num [Nat.Coprime])
  exact (by decide : angleResidueSum 21 5 w ≠ angleResidueSum 21 5 a) hh

end Erdos633b.Tiling
