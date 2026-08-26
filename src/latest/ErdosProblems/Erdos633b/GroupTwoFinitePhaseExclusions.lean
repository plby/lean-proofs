import ErdosProblems.Erdos633b.GroupTwoThirdOrder8
import ErdosProblems.Erdos633b.GroupTwoFirstOrder15
import ErdosProblems.Erdos633b.GroupTwoSecondOrder15
import ErdosProblems.Erdos633b.GroupTwoThirdOrder20One
import ErdosProblems.Erdos633b.GroupTwoThirdOrder20Three
import ErdosProblems.Erdos633b.GroupTwoFirstOrder20One
import ErdosProblems.Erdos633b.GroupTwoFirstOrder20Three
import ErdosProblems.Erdos633b.GroupTwoSecondOrder24
import ErdosProblems.Erdos633b.GroupTwoFirstOrder30
import ErdosProblems.Erdos633b.GroupTwoSecondOrder30
import ErdosProblems.Erdos633b.Boundary48Exclusion

/-! Transport the checked exact-weight boundary and area obstructions
to the remaining primitive phase descriptions of the three group-2 shapes. -/

namespace Erdos633b.Tiling

theorem groupTwo_phase_exclusion_8_1_3 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = d.tile.angle 0)
    (h1 : T.angle 1 = d.tile.angle 0 + d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + 2 * d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 1 / 8 := by
  intro hα
  apply d.groupTwo_finite_8_1_3_impossible
  · intro i
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
  · intro i
    fin_cases i
    · change T.angle 0 = ((3 : ℕ) : ℝ) * (Real.pi / 12)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((4 : ℕ) : ℝ) * (Real.pi / 12)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((5 : ℕ) : ℝ) * (Real.pi / 12)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]

theorem groupTwo_phase_exclusion_15_2_1 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 0)
    (h2 : T.angle 2 = 3 * d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 2 / 15 := by
  intro hα
  apply d.groupTwo_finite_15_2_1_impossible
  · intro i
    fin_cases i
    · change d.tile.angle 0 = ((4 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 1 = ((1 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 2 = ((10 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  · intro i
    fin_cases i
    · change T.angle 0 = ((4 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((8 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((3 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]

theorem groupTwo_phase_exclusion_15_2_2 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = 2 * d.tile.angle 0 + d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 2 / 15 := by
  intro hα
  apply d.groupTwo_finite_15_2_2_impossible
  · intro i
    fin_cases i
    · change d.tile.angle 0 = ((4 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 1 = ((1 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 2 = ((10 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  · intro i
    fin_cases i
    · change T.angle 0 = ((4 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((2 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((9 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]

theorem groupTwo_phase_exclusion_16_1_2 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = 2 * d.tile.angle 0 + d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 1 / 16 := by
  intro hα
  apply d.boundary48_impossible
  · intro i
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
  · intro i
    fin_cases i
    · change T.angle 0 = ((3 : ℕ) : ℝ) * (Real.pi / 24)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((10 : ℕ) : ℝ) * (Real.pi / 24)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((11 : ℕ) : ℝ) * (Real.pi / 24)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]

theorem groupTwo_phase_exclusion_20_1_1 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 0)
    (h2 : T.angle 2 = 3 * d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 1 / 20 := by
  intro hα
  apply d.groupTwo_finite_20_1_1_impossible
  · intro i
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
  · intro i
    fin_cases i
    · change T.angle 0 = ((3 : ℕ) : ℝ) * (Real.pi / 30)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((6 : ℕ) : ℝ) * (Real.pi / 30)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((21 : ℕ) : ℝ) * (Real.pi / 30)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]

theorem groupTwo_phase_exclusion_20_1_3 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = d.tile.angle 0)
    (h1 : T.angle 1 = d.tile.angle 0 + d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + 2 * d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 1 / 20 := by
  intro hα
  apply d.groupTwo_finite_20_1_3_impossible
  · intro i
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
  · intro i
    fin_cases i
    · change T.angle 0 = ((3 : ℕ) : ℝ) * (Real.pi / 30)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((10 : ℕ) : ℝ) * (Real.pi / 30)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((17 : ℕ) : ℝ) * (Real.pi / 30)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]

theorem groupTwo_phase_exclusion_20_3_1 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 0)
    (h2 : T.angle 2 = 3 * d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 3 / 20 := by
  intro hα
  apply d.groupTwo_finite_20_3_1_impossible
  · intro i
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
  · intro i
    fin_cases i
    · change T.angle 0 = ((9 : ℕ) : ℝ) * (Real.pi / 30)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((18 : ℕ) : ℝ) * (Real.pi / 30)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((3 : ℕ) : ℝ) * (Real.pi / 30)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]

theorem groupTwo_phase_exclusion_20_3_3 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = d.tile.angle 0)
    (h1 : T.angle 1 = d.tile.angle 0 + d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + 2 * d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 3 / 20 := by
  intro hα
  apply d.groupTwo_finite_20_3_3_impossible
  · intro i
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
  · intro i
    fin_cases i
    · change T.angle 0 = ((9 : ℕ) : ℝ) * (Real.pi / 30)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((10 : ℕ) : ℝ) * (Real.pi / 30)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((11 : ℕ) : ℝ) * (Real.pi / 30)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]

theorem groupTwo_phase_exclusion_24_1_2 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = 2 * d.tile.angle 0 + d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 1 / 24 := by
  intro hα
  apply d.groupTwo_finite_24_1_2_impossible
  · intro i
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
  · intro i
    fin_cases i
    · change T.angle 0 = ((1 : ℕ) : ℝ) * (Real.pi / 12)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((6 : ℕ) : ℝ) * (Real.pi / 12)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((5 : ℕ) : ℝ) * (Real.pi / 12)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]

theorem groupTwo_phase_exclusion_30_1_1 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 0)
    (h2 : T.angle 2 = 3 * d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 1 / 30 := by
  intro hα
  apply d.groupTwo_finite_30_1_1_impossible
  · intro i
    fin_cases i
    · change d.tile.angle 0 = ((1 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 1 = ((4 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 2 = ((10 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  · intro i
    fin_cases i
    · change T.angle 0 = ((1 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((2 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((12 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]

theorem groupTwo_phase_exclusion_30_1_2 {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = 2 * d.tile.angle 0 + d.tile.angle 1) :
    d.tile.angle 0 ≠ 2 * Real.pi * 1 / 30 := by
  intro hα
  apply d.groupTwo_finite_30_1_2_impossible
  · intro i
    fin_cases i
    · change d.tile.angle 0 = ((1 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 1 = ((4 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change d.tile.angle 2 = ((10 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
  · intro i
    fin_cases i
    · change T.angle 0 = ((1 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 1 = ((8 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]
    · change T.angle 2 = ((6 : ℕ) : ℝ) * (Real.pi / 15)
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      linarith [d.tile.angle_sum]

end Erdos633b.Tiling
