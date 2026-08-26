import ErdosProblems.Erdos633b.TilingResidueCondition
import Mathlib.Tactic.NormNum.GCD

/-! Exact coprime residue witnesses exclude the listed rational phases
for one group-2 outer shape. All weights and residues are checked in Lean. -/

namespace Erdos633b.Tiling

theorem groupTwo_residue_exclusion_7_1_1 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 0)
    (h2 : T.angle 2 = 3 * d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 1 / 7 := by
  intro hα
  let w : Fin 3 → ℕ := ![6, 1, 14]
  let a : Fin 3 → ℕ := ![6, 12, 3]
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
    · change T.angle 1 = ((12 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((3 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have hh := d.coprime_angle_residue_sum_eq 21 (by decide) w a hw ha
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by decide) (by decide) 5 (by norm_num [Nat.Coprime])
  exact (by decide : angleResidueSum 21 5 w ≠ angleResidueSum 21 5 a) hh

theorem groupTwo_residue_exclusion_9_1_1 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 0)
    (h2 : T.angle 2 = 3 * d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 1 / 9 := by
  intro hα
  let w : Fin 3 → ℕ := ![2, 1, 6]
  let a : Fin 3 → ℕ := ![2, 4, 3]
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

theorem groupTwo_residue_exclusion_14_1_1 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 0)
    (h2 : T.angle 2 = 3 * d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 1 / 14 := by
  intro hα
  let w : Fin 3 → ℕ := ![3, 4, 14]
  let a : Fin 3 → ℕ := ![3, 6, 12]
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
    · change T.angle 1 = ((6 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((12 : ℕ) : ℝ) * (Real.pi / 21)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have hh := d.coprime_angle_residue_sum_eq 21 (by decide) w a hw ha
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by decide) (by decide) 17 (by norm_num [Nat.Coprime])
  exact (by decide : angleResidueSum 21 17 w ≠ angleResidueSum 21 17 a) hh

theorem groupTwo_residue_exclusion_15_1_1 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 0)
    (h2 : T.angle 2 = 3 * d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 1 / 15 := by
  intro hα
  let w : Fin 3 → ℕ := ![2, 3, 10]
  let a : Fin 3 → ℕ := ![2, 4, 9]
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
    · change T.angle 1 = ((4 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((9 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have hh := d.coprime_angle_residue_sum_eq 15 (by decide) w a hw ha
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by decide) (by decide) 11 (by norm_num [Nat.Coprime])
  exact (by decide : angleResidueSum 15 11 w ≠ angleResidueSum 15 11 a) hh

theorem groupTwo_residue_exclusion_16_1_1 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 0)
    (h2 : T.angle 2 = 3 * d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 1 / 16 := by
  intro hα
  let w : Fin 3 → ℕ := ![3, 5, 16]
  let a : Fin 3 → ℕ := ![3, 6, 15]
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
    · change T.angle 0 = ((3 : ℕ) : ℝ) * (Real.pi / 24)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((6 : ℕ) : ℝ) * (Real.pi / 24)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((15 : ℕ) : ℝ) * (Real.pi / 24)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have hh := d.coprime_angle_residue_sum_eq 24 (by decide) w a hw ha
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by decide) (by decide) 11 (by norm_num [Nat.Coprime])
  exact (by decide : angleResidueSum 24 11 w ≠ angleResidueSum 24 11 a) hh

theorem groupTwo_residue_exclusion_24_1_1 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 0)
    (h2 : T.angle 2 = 3 * d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 1 / 24 := by
  intro hα
  let w : Fin 3 → ℕ := ![1, 3, 8]
  let a : Fin 3 → ℕ := ![1, 2, 9]
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
    · change T.angle 0 = ((1 : ℕ) : ℝ) * (Real.pi / 12)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((2 : ℕ) : ℝ) * (Real.pi / 12)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((9 : ℕ) : ℝ) * (Real.pi / 12)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  have hh := d.coprime_angle_residue_sum_eq 12 (by decide) w a hw ha
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by decide) (by decide) 5 (by norm_num [Nat.Coprime])
  exact (by decide : angleResidueSum 12 5 w ≠ angleResidueSum 12 5 a) hh

end Erdos633b.Tiling
