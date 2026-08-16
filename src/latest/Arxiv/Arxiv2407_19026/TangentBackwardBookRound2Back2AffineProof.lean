import Arxiv.Arxiv2407_19026.TangentBackwardBookRound2Back2NumeratorData
import Arxiv.Arxiv2407_19026.TangentBackwardBookRound2Back2AffineData
import Arxiv.Arxiv2407_19026.TangentBackwardBookRound2Back2AffineStagesData

/-! Exact affine transport for the round-2 second backward-book certificate. -/

namespace Arxiv2407_19026
namespace BackwardBookRound2Back2Certificate

noncomputable section

def bookPowerScale : ℕ :=
  bookNumeratorScale * 1000 ^ 140

private def affinePrefix (denominator : ℕ) (left width : ℤ)
    (tailLength : ℕ) (tailAffine : List ℤ) : List ℤ → List ℤ
  | [] => tailAffine
  | coefficient :: coefficients =>
      integerPowerAdd
        [coefficient * denominator ^ (coefficients.length + tailLength)]
        (integerPowerLinear left width
          (affinePrefix denominator left width
            tailLength tailAffine coefficients))

private lemma integerPowerAffine_append (denominator : ℕ) (left width : ℤ)
    (front suffix : List ℤ) :
    integerPowerAffine denominator left width (front ++ suffix) =
      affinePrefix denominator left width suffix.length
        (integerPowerAffine denominator left width suffix) front := by
  induction front with
  | nil =>
      rfl
  | cons coefficient coefficients ih =>
      simp only [List.cons_append, integerPowerAffine,
        affinePrefix, List.length_append]
      rw [ih]

private lemma book_affine_tail140 :
    integerPowerAffine 1000 600 400 bookNumeratorTail140 =
      bookAffineTail140 := by
  rfl

private lemma book_affine_tail120 :
    integerPowerAffine 1000 600 400 bookNumeratorTail120 =
      bookAffineTail120 := by
  rw [bookNumeratorTail120, bookNumeratorTail130,
    ← List.append_assoc, integerPowerAffine_append,
    book_affine_tail140]
  rfl

private lemma book_affine_tail100 :
    integerPowerAffine 1000 600 400 bookNumeratorTail100 =
      bookAffineTail100 := by
  rw [bookNumeratorTail100, bookNumeratorTail110,
    ← List.append_assoc, integerPowerAffine_append,
    book_affine_tail120]
  rfl

private lemma book_affine_tail80 :
    integerPowerAffine 1000 600 400 bookNumeratorTail80 =
      bookAffineTail80 := by
  rw [bookNumeratorTail80, bookNumeratorTail90,
    ← List.append_assoc, integerPowerAffine_append,
    book_affine_tail100]
  rfl

private lemma book_affine_tail60 :
    integerPowerAffine 1000 600 400 bookNumeratorTail60 =
      bookAffineTail60 := by
  rw [bookNumeratorTail60, bookNumeratorTail70,
    ← List.append_assoc, integerPowerAffine_append,
    book_affine_tail80]
  rfl

set_option maxRecDepth 100000 in
-- Reducing a 20-coefficient affine stage over a long exact tail exceeds the default depth.
private lemma book_affine_tail40 :
    integerPowerAffine 1000 600 400 bookNumeratorTail40 =
      bookAffineTail40 := by
  rw [bookNumeratorTail40, bookNumeratorTail50,
    ← List.append_assoc, integerPowerAffine_append,
    book_affine_tail60]
  rfl

set_option maxRecDepth 100000 in
-- Reducing a 20-coefficient affine stage over a long exact tail exceeds the default depth.
private lemma book_affine_tail20 :
    integerPowerAffine 1000 600 400 bookNumeratorTail20 =
      bookAffineTail20 := by
  rw [bookNumeratorTail20, bookNumeratorTail25,
    bookNumeratorTail30, bookNumeratorTail35,
    ← List.append_assoc, ← List.append_assoc,
    ← List.append_assoc, integerPowerAffine_append,
    book_affine_tail40]
  rfl

set_option maxRecDepth 100000 in
-- Reducing the final 20-coefficient affine stage exceeds the default depth.
lemma book_affine_tail0 :
    integerPowerAffine 1000 600 400 bookNumeratorTail0 =
      bookAffineTail0 := by
  rw [bookNumeratorTail0, bookNumeratorTail5,
    bookNumeratorTail10, bookNumeratorTail15,
    ← List.append_assoc, ← List.append_assoc,
    ← List.append_assoc, integerPowerAffine_append,
    book_affine_tail20]
  rfl

lemma book_power_coeffs_affine :
    integerPowerAffine 1000 600 400 bookNumeratorCoeffs =
      bookPowerCoeffs := by
  simpa [bookNumeratorCoeffs, bookPowerCoeffs] using
    book_affine_tail0

set_option maxRecDepth 100000 in
-- Specializing the affine evaluator to 141 coefficients exceeds the default recursion depth.
lemma book_affine_eval (u : ℝ) :
    evalIntegerPower bookPowerCoeffs u * 1000 =
      1000 ^ 141 *
        evalIntegerPower bookNumeratorCoeffs
          (((600 : ℝ) + (400 : ℝ) * u) / 1000) := by
  rw [← book_power_coeffs_affine]
  have haffine :=
    evalIntegerPower_affine
      1000 600 400 bookNumeratorCoeffs u (by norm_num)
  rw [bookNumeratorCoeffs,
    bookNumeratorTail0_length] at haffine
  exact haffine

end

end BackwardBookRound2Back2Certificate
end Arxiv2407_19026
