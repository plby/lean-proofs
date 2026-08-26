import ErdosProblems.Erdos633b.TilingResidueCondition
import Mathlib.Tactic.NormNum.GCD

/-! Exact coprime residue witnesses exclude the listed rational phases
for one group-2 outer shape. All weights and residues are checked in Lean. -/

namespace Erdos633b.Tiling

theorem groupTwo_residue_exclusion_7_1_2 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = 2 * d.tile.angle 0 + d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 1 / 7 := by
  intro hα
  let w : Fin 3 → ℕ := ![6, 1, 14]
  let a : Fin 3 → ℕ := ![6, 2, 13]
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
    · change T.angle 0 = ((6 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((2 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((13 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have hh := d.coprime_angle_residue_sum_eq 21 (by decide) w a hw ha
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by decide) (by decide) 13 (by norm_num [Nat.Coprime])
  exact (by decide : angleResidueSum 21 13 w ≠ angleResidueSum 21 13 a) hh

theorem groupTwo_residue_exclusion_8_1_2 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = 2 * d.tile.angle 0 + d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 1 / 8 := by
  intro hα
  let w : Fin 3 → ℕ := ![3, 1, 8]
  let a : Fin 3 → ℕ := ![3, 2, 7]
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
    · change T.angle 0 = ((3 : ℕ) : ℝ) * (Real.pi / 12)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((2 : ℕ) : ℝ) * (Real.pi / 12)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((7 : ℕ) : ℝ) * (Real.pi / 12)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have hh := d.coprime_angle_residue_sum_eq 12 (by decide) w a hw ha
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by decide) (by decide) 5 (by norm_num [Nat.Coprime])
  exact (by decide : angleResidueSum 12 5 w ≠ angleResidueSum 12 5 a) hh

theorem groupTwo_residue_exclusion_10_1_2 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = 2 * d.tile.angle 0 + d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 1 / 10 := by
  intro hα
  let w : Fin 3 → ℕ := ![3, 2, 10]
  let a : Fin 3 → ℕ := ![3, 4, 8]
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
    · change T.angle 0 = ((3 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((4 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((8 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have hh := d.coprime_angle_residue_sum_eq 15 (by decide) w a hw ha
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by decide) (by decide) 11 (by norm_num [Nat.Coprime])
  exact (by decide : angleResidueSum 15 11 w ≠ angleResidueSum 15 11 a) hh

theorem groupTwo_residue_exclusion_14_1_2 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = 2 * d.tile.angle 0 + d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 1 / 14 := by
  intro hα
  let w : Fin 3 → ℕ := ![3, 4, 14]
  let a : Fin 3 → ℕ := ![3, 8, 10]
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
    · change T.angle 0 = ((3 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((8 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((10 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have hh := d.coprime_angle_residue_sum_eq 21 (by decide) w a hw ha
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by decide) (by decide) 19 (by norm_num [Nat.Coprime])
  exact (by decide : angleResidueSum 21 19 w ≠ angleResidueSum 21 19 a) hh

theorem groupTwo_residue_exclusion_15_1_2 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = 2 * d.tile.angle 0 + d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 1 / 15 := by
  intro hα
  let w : Fin 3 → ℕ := ![2, 3, 10]
  let a : Fin 3 → ℕ := ![2, 6, 7]
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
    · change T.angle 0 = ((2 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((6 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((7 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have hh := d.coprime_angle_residue_sum_eq 15 (by decide) w a hw ha
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by decide) (by decide) 13 (by norm_num [Nat.Coprime])
  exact (by decide : angleResidueSum 15 13 w ≠ angleResidueSum 15 13 a) hh

theorem groupTwo_residue_exclusion_20_1_2 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = 2 * d.tile.angle 0 + d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 1 / 20 := by
  intro hα
  let w : Fin 3 → ℕ := ![3, 7, 20]
  let a : Fin 3 → ℕ := ![3, 14, 13]
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
    · change T.angle 0 = ((3 : ℕ) : ℝ) * (Real.pi / 30)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((14 : ℕ) : ℝ) * (Real.pi / 30)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((13 : ℕ) : ℝ) * (Real.pi / 30)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have hh := d.coprime_angle_residue_sum_eq 30 (by decide) w a hw ha
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by decide) (by decide) 7 (by norm_num [Nat.Coprime])
  exact (by decide : angleResidueSum 30 7 w ≠ angleResidueSum 30 7 a) hh

theorem groupTwo_residue_exclusion_20_3_2 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = 2 * d.tile.angle 0 + d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 3 / 20 := by
  intro hα
  let w : Fin 3 → ℕ := ![9, 1, 20]
  let a : Fin 3 → ℕ := ![9, 2, 19]
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
    · change T.angle 0 = ((9 : ℕ) : ℝ) * (Real.pi / 30)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((2 : ℕ) : ℝ) * (Real.pi / 30)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((19 : ℕ) : ℝ) * (Real.pi / 30)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have hh := d.coprime_angle_residue_sum_eq 30 (by decide) w a hw ha
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by decide) (by decide) 11 (by norm_num [Nat.Coprime])
  exact (by decide : angleResidueSum 30 11 w ≠ angleResidueSum 30 11 a) hh

end Erdos633b.Tiling
