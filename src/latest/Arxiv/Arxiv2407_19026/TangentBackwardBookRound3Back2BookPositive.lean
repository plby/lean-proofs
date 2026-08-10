import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2BookCells3

/-! Positivity of the Round 3 Back2 book numerator from the 16 exact Horner cells. -/

namespace Arxiv2407_19026
namespace BackwardBookRound3Back2Certificate

noncomputable section

lemma book_power_positive {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    0 < evalIntegerPower bookPowerCoeffs u := by
  by_cases h1 : u ≤ (1 / 16 : ℝ)
  · have hmem :
        u ∈
          ({ lo := 0 / 16, hi := 1 / 16,
              le := by norm_num } :
            LeanCert.Core.IntervalRat) := by
      rw [LeanCert.Core.IntervalRat.mem_def]
      norm_num
      constructor <;> nlinarith [hu.1, hu.2]
    exact eval_integer_power_pos_of_interval bookPowerCoeffs
      ({ lo := 0 / 16, hi := 1 / 16,
          le := by norm_num } :
        LeanCert.Core.IntervalRat)
      hmem book_cell_0_horner
  by_cases h2 : u ≤ (2 / 16 : ℝ)
  · have hmem :
        u ∈
          ({ lo := 1 / 16, hi := 2 / 16,
              le := by norm_num } :
            LeanCert.Core.IntervalRat) := by
      rw [LeanCert.Core.IntervalRat.mem_def]
      norm_num
      constructor <;> nlinarith [hu.1, hu.2]
    exact eval_integer_power_pos_of_interval bookPowerCoeffs
      ({ lo := 1 / 16, hi := 2 / 16,
          le := by norm_num } :
        LeanCert.Core.IntervalRat)
      hmem book_cell_1_horner
  by_cases h3 : u ≤ (3 / 16 : ℝ)
  · have hmem :
        u ∈
          ({ lo := 2 / 16, hi := 3 / 16,
              le := by norm_num } :
            LeanCert.Core.IntervalRat) := by
      rw [LeanCert.Core.IntervalRat.mem_def]
      norm_num
      constructor <;> nlinarith [hu.1, hu.2]
    exact eval_integer_power_pos_of_interval bookPowerCoeffs
      ({ lo := 2 / 16, hi := 3 / 16,
          le := by norm_num } :
        LeanCert.Core.IntervalRat)
      hmem book_cell_2_horner
  by_cases h4 : u ≤ (4 / 16 : ℝ)
  · have hmem :
        u ∈
          ({ lo := 3 / 16, hi := 4 / 16,
              le := by norm_num } :
            LeanCert.Core.IntervalRat) := by
      rw [LeanCert.Core.IntervalRat.mem_def]
      norm_num
      constructor <;> nlinarith [hu.1, hu.2]
    exact eval_integer_power_pos_of_interval bookPowerCoeffs
      ({ lo := 3 / 16, hi := 4 / 16,
          le := by norm_num } :
        LeanCert.Core.IntervalRat)
      hmem book_cell_3_horner
  by_cases h5 : u ≤ (5 / 16 : ℝ)
  · have hmem :
        u ∈
          ({ lo := 4 / 16, hi := 5 / 16,
              le := by norm_num } :
            LeanCert.Core.IntervalRat) := by
      rw [LeanCert.Core.IntervalRat.mem_def]
      norm_num
      constructor <;> nlinarith [hu.1, hu.2]
    exact eval_integer_power_pos_of_interval bookPowerCoeffs
      ({ lo := 4 / 16, hi := 5 / 16,
          le := by norm_num } :
        LeanCert.Core.IntervalRat)
      hmem book_cell_4_horner
  by_cases h6 : u ≤ (6 / 16 : ℝ)
  · have hmem :
        u ∈
          ({ lo := 5 / 16, hi := 6 / 16,
              le := by norm_num } :
            LeanCert.Core.IntervalRat) := by
      rw [LeanCert.Core.IntervalRat.mem_def]
      norm_num
      constructor <;> nlinarith [hu.1, hu.2]
    exact eval_integer_power_pos_of_interval bookPowerCoeffs
      ({ lo := 5 / 16, hi := 6 / 16,
          le := by norm_num } :
        LeanCert.Core.IntervalRat)
      hmem book_cell_5_horner
  by_cases h7 : u ≤ (7 / 16 : ℝ)
  · have hmem :
        u ∈
          ({ lo := 6 / 16, hi := 7 / 16,
              le := by norm_num } :
            LeanCert.Core.IntervalRat) := by
      rw [LeanCert.Core.IntervalRat.mem_def]
      norm_num
      constructor <;> nlinarith [hu.1, hu.2]
    exact eval_integer_power_pos_of_interval bookPowerCoeffs
      ({ lo := 6 / 16, hi := 7 / 16,
          le := by norm_num } :
        LeanCert.Core.IntervalRat)
      hmem book_cell_6_horner
  by_cases h8 : u ≤ (8 / 16 : ℝ)
  · have hmem :
        u ∈
          ({ lo := 7 / 16, hi := 8 / 16,
              le := by norm_num } :
            LeanCert.Core.IntervalRat) := by
      rw [LeanCert.Core.IntervalRat.mem_def]
      norm_num
      constructor <;> nlinarith [hu.1, hu.2]
    exact eval_integer_power_pos_of_interval bookPowerCoeffs
      ({ lo := 7 / 16, hi := 8 / 16,
          le := by norm_num } :
        LeanCert.Core.IntervalRat)
      hmem book_cell_7_horner
  by_cases h9 : u ≤ (9 / 16 : ℝ)
  · have hmem :
        u ∈
          ({ lo := 8 / 16, hi := 9 / 16,
              le := by norm_num } :
            LeanCert.Core.IntervalRat) := by
      rw [LeanCert.Core.IntervalRat.mem_def]
      norm_num
      constructor <;> nlinarith [hu.1, hu.2]
    exact eval_integer_power_pos_of_interval bookPowerCoeffs
      ({ lo := 8 / 16, hi := 9 / 16,
          le := by norm_num } :
        LeanCert.Core.IntervalRat)
      hmem book_cell_8_horner
  by_cases h10 : u ≤ (10 / 16 : ℝ)
  · have hmem :
        u ∈
          ({ lo := 9 / 16, hi := 10 / 16,
              le := by norm_num } :
            LeanCert.Core.IntervalRat) := by
      rw [LeanCert.Core.IntervalRat.mem_def]
      norm_num
      constructor <;> nlinarith [hu.1, hu.2]
    exact eval_integer_power_pos_of_interval bookPowerCoeffs
      ({ lo := 9 / 16, hi := 10 / 16,
          le := by norm_num } :
        LeanCert.Core.IntervalRat)
      hmem book_cell_9_horner
  by_cases h11 : u ≤ (11 / 16 : ℝ)
  · have hmem :
        u ∈
          ({ lo := 10 / 16, hi := 11 / 16,
              le := by norm_num } :
            LeanCert.Core.IntervalRat) := by
      rw [LeanCert.Core.IntervalRat.mem_def]
      norm_num
      constructor <;> nlinarith [hu.1, hu.2]
    exact eval_integer_power_pos_of_interval bookPowerCoeffs
      ({ lo := 10 / 16, hi := 11 / 16,
          le := by norm_num } :
        LeanCert.Core.IntervalRat)
      hmem book_cell_10_horner
  by_cases h12 : u ≤ (12 / 16 : ℝ)
  · have hmem :
        u ∈
          ({ lo := 11 / 16, hi := 12 / 16,
              le := by norm_num } :
            LeanCert.Core.IntervalRat) := by
      rw [LeanCert.Core.IntervalRat.mem_def]
      norm_num
      constructor <;> nlinarith [hu.1, hu.2]
    exact eval_integer_power_pos_of_interval bookPowerCoeffs
      ({ lo := 11 / 16, hi := 12 / 16,
          le := by norm_num } :
        LeanCert.Core.IntervalRat)
      hmem book_cell_11_horner
  by_cases h13 : u ≤ (13 / 16 : ℝ)
  · have hmem :
        u ∈
          ({ lo := 12 / 16, hi := 13 / 16,
              le := by norm_num } :
            LeanCert.Core.IntervalRat) := by
      rw [LeanCert.Core.IntervalRat.mem_def]
      norm_num
      constructor <;> nlinarith [hu.1, hu.2]
    exact eval_integer_power_pos_of_interval bookPowerCoeffs
      ({ lo := 12 / 16, hi := 13 / 16,
          le := by norm_num } :
        LeanCert.Core.IntervalRat)
      hmem book_cell_12_horner
  by_cases h14 : u ≤ (14 / 16 : ℝ)
  · have hmem :
        u ∈
          ({ lo := 13 / 16, hi := 14 / 16,
              le := by norm_num } :
            LeanCert.Core.IntervalRat) := by
      rw [LeanCert.Core.IntervalRat.mem_def]
      norm_num
      constructor <;> nlinarith [hu.1, hu.2]
    exact eval_integer_power_pos_of_interval bookPowerCoeffs
      ({ lo := 13 / 16, hi := 14 / 16,
          le := by norm_num } :
        LeanCert.Core.IntervalRat)
      hmem book_cell_13_horner
  by_cases h15 : u ≤ (15 / 16 : ℝ)
  · have hmem :
        u ∈
          ({ lo := 14 / 16, hi := 15 / 16,
              le := by norm_num } :
            LeanCert.Core.IntervalRat) := by
      rw [LeanCert.Core.IntervalRat.mem_def]
      norm_num
      constructor <;> nlinarith [hu.1, hu.2]
    exact eval_integer_power_pos_of_interval bookPowerCoeffs
      ({ lo := 14 / 16, hi := 15 / 16,
          le := by norm_num } :
        LeanCert.Core.IntervalRat)
      hmem book_cell_14_horner
  have hmem :
        u ∈
          ({ lo := 15 / 16, hi := 16 / 16,
              le := by norm_num } :
            LeanCert.Core.IntervalRat) := by
      rw [LeanCert.Core.IntervalRat.mem_def]
      norm_num
      constructor <;> nlinarith [hu.1, hu.2]
  exact eval_integer_power_pos_of_interval bookPowerCoeffs
      ({ lo := 15 / 16, hi := 16 / 16,
          le := by norm_num } :
        LeanCert.Core.IntervalRat)
      hmem book_cell_15_horner

end

end BackwardBookRound3Back2Certificate
end Arxiv2407_19026
