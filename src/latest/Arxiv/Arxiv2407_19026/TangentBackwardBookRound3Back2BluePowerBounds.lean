import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2BlueLocalCertificate

/-!
# Certified blue numerator positivity on the third-round second backward interval

The 32 exact local Horner certificates are combined into a continuous cover
of `[3 / 5, 1]`.
-/

namespace Arxiv2407_19026
namespace BackwardBookRound3Back2Bounds

noncomputable section

open BackwardBookRound3Back2Certificate

lemma evalPower_eq_evalIntegerPower
    (coefficients : List ℤ) (x : ℝ) :
    evalPower coefficients x = evalIntegerPower coefficients x := by
  induction coefficients with
  | nil => rfl
  | cons coefficient coefficients ih =>
      simp only [evalPower, evalIntegerPower]
      rw [ih]

lemma blue_power_positive_on_cell
    (left : ℤ) (localCoefficients : List ℤ)
    (hcoefficients :
      integerPowerAffine 80 left 1 bluePowerCoeffs =
        localCoefficients)
    (hlower :
      0 <
        (integerHornerInterval localCoefficients
          ({ lo := 0, hi := 1, le := by norm_num } :
            LeanCert.Core.IntervalRat)).lo)
    {z : ℝ}
    (hz : z ∈ Set.Icc (left / 80 : ℝ) ((left + 1) / 80)) :
    0 < evalPower bluePowerCoeffs z := by
  let u : ℝ := 80 * z - left
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have huInterval :
      u ∈
        ({ lo := 0, hi := 1, le := by norm_num } :
          LeanCert.Core.IntervalRat) := by
    simpa [LeanCert.Core.IntervalRat.mem_def] using hu
  have hlocal : 0 < evalIntegerPower localCoefficients u :=
    eval_integer_power_pos_of_interval localCoefficients
      ({ lo := 0, hi := 1, le := by norm_num } :
        LeanCert.Core.IntervalRat)
      huInterval hlower
  have haffine :=
    evalIntegerPower_affine
      80 left 1 bluePowerCoeffs u (by norm_num)
  rw [hcoefficients] at haffine
  norm_num only [Nat.cast_ofNat, Int.cast_one] at haffine
  have hpoint :
      (((left : ℝ) + (1 : ℝ) * u) / 80) = z := by
    dsimp [u]
    ring
  rw [hpoint] at haffine
  have horiginal : 0 < evalIntegerPower bluePowerCoeffs z := by
    have hproduct :
        0 < evalIntegerPower localCoefficients u * 80 :=
      mul_pos hlocal (by norm_num)
    rw [haffine] at hproduct
    rcases mul_pos_iff.mp hproduct with hpositive | hnegative
    · exact hpositive.2
    · exact (not_lt_of_ge (by positivity) hnegative.1).elim
  rw [evalPower_eq_evalIntegerPower]
  exact horiginal

set_option maxHeartbeats 1000000 in
-- Combining the 32 exact local cells and normalizing their rational endpoints exceeds the default budget.
lemma blue_power_positive {z : ℝ}
    (hz : z ∈ Set.Icc (3 / 5 : ℝ) 1) :
    0 < evalPower bluePowerCoeffs z := by
  by_cases h49 : z ≤ (49 / 80 : ℝ)
  · apply blue_power_positive_on_cell 48
      blueCell48Coeffs blue_cell_48_coefficients
      blue_cell_48_horner
    constructor <;> norm_num at hz h49 ⊢ <;> linarith
  by_cases h50 : z ≤ (50 / 80 : ℝ)
  · apply blue_power_positive_on_cell 49
      blueCell49Coeffs blue_cell_49_coefficients
      blue_cell_49_horner
    constructor <;> norm_num at hz h49 h50 ⊢ <;> linarith
  by_cases h51 : z ≤ (51 / 80 : ℝ)
  · apply blue_power_positive_on_cell 50
      blueCell50Coeffs blue_cell_50_coefficients
      blue_cell_50_horner
    constructor <;> norm_num at hz h50 h51 ⊢ <;> linarith
  by_cases h52 : z ≤ (52 / 80 : ℝ)
  · apply blue_power_positive_on_cell 51
      blueCell51Coeffs blue_cell_51_coefficients
      blue_cell_51_horner
    constructor <;> norm_num at hz h51 h52 ⊢ <;> linarith
  by_cases h53 : z ≤ (53 / 80 : ℝ)
  · apply blue_power_positive_on_cell 52
      blueCell52Coeffs blue_cell_52_coefficients
      blue_cell_52_horner
    constructor <;> norm_num at hz h52 h53 ⊢ <;> linarith
  by_cases h54 : z ≤ (54 / 80 : ℝ)
  · apply blue_power_positive_on_cell 53
      blueCell53Coeffs blue_cell_53_coefficients
      blue_cell_53_horner
    constructor <;> norm_num at hz h53 h54 ⊢ <;> linarith
  by_cases h55 : z ≤ (55 / 80 : ℝ)
  · apply blue_power_positive_on_cell 54
      blueCell54Coeffs blue_cell_54_coefficients
      blue_cell_54_horner
    constructor <;> norm_num at hz h54 h55 ⊢ <;> linarith
  by_cases h56 : z ≤ (56 / 80 : ℝ)
  · apply blue_power_positive_on_cell 55
      blueCell55Coeffs blue_cell_55_coefficients
      blue_cell_55_horner
    constructor <;> norm_num at hz h55 h56 ⊢ <;> linarith
  by_cases h57 : z ≤ (57 / 80 : ℝ)
  · apply blue_power_positive_on_cell 56
      blueCell56Coeffs blue_cell_56_coefficients
      blue_cell_56_horner
    constructor <;> norm_num at hz h56 h57 ⊢ <;> linarith
  by_cases h58 : z ≤ (58 / 80 : ℝ)
  · apply blue_power_positive_on_cell 57
      blueCell57Coeffs blue_cell_57_coefficients
      blue_cell_57_horner
    constructor <;> norm_num at hz h57 h58 ⊢ <;> linarith
  by_cases h59 : z ≤ (59 / 80 : ℝ)
  · apply blue_power_positive_on_cell 58
      blueCell58Coeffs blue_cell_58_coefficients
      blue_cell_58_horner
    constructor <;> norm_num at hz h58 h59 ⊢ <;> linarith
  by_cases h60 : z ≤ (60 / 80 : ℝ)
  · apply blue_power_positive_on_cell 59
      blueCell59Coeffs blue_cell_59_coefficients
      blue_cell_59_horner
    constructor <;> norm_num at hz h59 h60 ⊢ <;> linarith
  by_cases h61 : z ≤ (61 / 80 : ℝ)
  · apply blue_power_positive_on_cell 60
      blueCell60Coeffs blue_cell_60_coefficients
      blue_cell_60_horner
    constructor <;> norm_num at hz h60 h61 ⊢ <;> linarith
  by_cases h62 : z ≤ (62 / 80 : ℝ)
  · apply blue_power_positive_on_cell 61
      blueCell61Coeffs blue_cell_61_coefficients
      blue_cell_61_horner
    constructor <;> norm_num at hz h61 h62 ⊢ <;> linarith
  by_cases h63 : z ≤ (63 / 80 : ℝ)
  · apply blue_power_positive_on_cell 62
      blueCell62Coeffs blue_cell_62_coefficients
      blue_cell_62_horner
    constructor <;> norm_num at hz h62 h63 ⊢ <;> linarith
  by_cases h64 : z ≤ (64 / 80 : ℝ)
  · apply blue_power_positive_on_cell 63
      blueCell63Coeffs blue_cell_63_coefficients
      blue_cell_63_horner
    constructor <;> norm_num at hz h63 h64 ⊢ <;> linarith
  by_cases h65 : z ≤ (65 / 80 : ℝ)
  · apply blue_power_positive_on_cell 64
      blueCell64Coeffs blue_cell_64_coefficients
      blue_cell_64_horner
    constructor <;> norm_num at hz h64 h65 ⊢ <;> linarith
  by_cases h66 : z ≤ (66 / 80 : ℝ)
  · apply blue_power_positive_on_cell 65
      blueCell65Coeffs blue_cell_65_coefficients
      blue_cell_65_horner
    constructor <;> norm_num at hz h65 h66 ⊢ <;> linarith
  by_cases h67 : z ≤ (67 / 80 : ℝ)
  · apply blue_power_positive_on_cell 66
      blueCell66Coeffs blue_cell_66_coefficients
      blue_cell_66_horner
    constructor <;> norm_num at hz h66 h67 ⊢ <;> linarith
  by_cases h68 : z ≤ (68 / 80 : ℝ)
  · apply blue_power_positive_on_cell 67
      blueCell67Coeffs blue_cell_67_coefficients
      blue_cell_67_horner
    constructor <;> norm_num at hz h67 h68 ⊢ <;> linarith
  by_cases h69 : z ≤ (69 / 80 : ℝ)
  · apply blue_power_positive_on_cell 68
      blueCell68Coeffs blue_cell_68_coefficients
      blue_cell_68_horner
    constructor <;> norm_num at hz h68 h69 ⊢ <;> linarith
  by_cases h70 : z ≤ (70 / 80 : ℝ)
  · apply blue_power_positive_on_cell 69
      blueCell69Coeffs blue_cell_69_coefficients
      blue_cell_69_horner
    constructor <;> norm_num at hz h69 h70 ⊢ <;> linarith
  by_cases h71 : z ≤ (71 / 80 : ℝ)
  · apply blue_power_positive_on_cell 70
      blueCell70Coeffs blue_cell_70_coefficients
      blue_cell_70_horner
    constructor <;> norm_num at hz h70 h71 ⊢ <;> linarith
  by_cases h72 : z ≤ (72 / 80 : ℝ)
  · apply blue_power_positive_on_cell 71
      blueCell71Coeffs blue_cell_71_coefficients
      blue_cell_71_horner
    constructor <;> norm_num at hz h71 h72 ⊢ <;> linarith
  by_cases h73 : z ≤ (73 / 80 : ℝ)
  · apply blue_power_positive_on_cell 72
      blueCell72Coeffs blue_cell_72_coefficients
      blue_cell_72_horner
    constructor <;> norm_num at hz h72 h73 ⊢ <;> linarith
  by_cases h74 : z ≤ (74 / 80 : ℝ)
  · apply blue_power_positive_on_cell 73
      blueCell73Coeffs blue_cell_73_coefficients
      blue_cell_73_horner
    constructor <;> norm_num at hz h73 h74 ⊢ <;> linarith
  by_cases h75 : z ≤ (75 / 80 : ℝ)
  · apply blue_power_positive_on_cell 74
      blueCell74Coeffs blue_cell_74_coefficients
      blue_cell_74_horner
    constructor <;> norm_num at hz h74 h75 ⊢ <;> linarith
  by_cases h76 : z ≤ (76 / 80 : ℝ)
  · apply blue_power_positive_on_cell 75
      blueCell75Coeffs blue_cell_75_coefficients
      blue_cell_75_horner
    constructor <;> norm_num at hz h75 h76 ⊢ <;> linarith
  by_cases h77 : z ≤ (77 / 80 : ℝ)
  · apply blue_power_positive_on_cell 76
      blueCell76Coeffs blue_cell_76_coefficients
      blue_cell_76_horner
    constructor <;> norm_num at hz h76 h77 ⊢ <;> linarith
  by_cases h78 : z ≤ (78 / 80 : ℝ)
  · apply blue_power_positive_on_cell 77
      blueCell77Coeffs blue_cell_77_coefficients
      blue_cell_77_horner
    constructor <;> norm_num at hz h77 h78 ⊢ <;> linarith
  by_cases h79 : z ≤ (79 / 80 : ℝ)
  · apply blue_power_positive_on_cell 78
      blueCell78Coeffs blue_cell_78_coefficients
      blue_cell_78_horner
    constructor <;> norm_num at hz h78 h79 ⊢ <;> linarith
  apply blue_power_positive_on_cell 79
    blueCell79Coeffs blue_cell_79_coefficients
    blue_cell_79_horner
  constructor <;> norm_num at hz h79 ⊢ <;> linarith

end

end BackwardBookRound3Back2Bounds
end Arxiv2407_19026
