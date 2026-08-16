import Arxiv.Arxiv2407_19026.TangentBackwardBookRound2Back1RightAffineStagesData

/-! Reflected-coordinate affine identity for round 2, first backward-book interval. -/

namespace Arxiv2407_19026
namespace BackwardBookRound2Back1Certificate

noncomputable section

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

private lemma book_reflected_affine_tail100 :
    integerPowerAffine 1 1 (-1) (bookPowerCoeffs.drop 100) =
      bookReflectedAffineTail100 := by
  rfl

private lemma book_reflected_affine_tail80 :
    integerPowerAffine 1 1 (-1) (bookPowerCoeffs.drop 80) =
      bookReflectedAffineTail80 := by
  rw [show bookPowerCoeffs.drop 80 =
      (bookPowerCoeffs.drop 80).take 20 ++ bookPowerCoeffs.drop 100 by
        rfl,
    integerPowerAffine_append, book_reflected_affine_tail100]
  rfl

private lemma book_reflected_affine_tail60 :
    integerPowerAffine 1 1 (-1) (bookPowerCoeffs.drop 60) =
      bookReflectedAffineTail60 := by
  rw [show bookPowerCoeffs.drop 60 =
      (bookPowerCoeffs.drop 60).take 20 ++ bookPowerCoeffs.drop 80 by
        rfl,
    integerPowerAffine_append, book_reflected_affine_tail80]
  rfl

set_option maxRecDepth 100000 in
private lemma book_reflected_affine_tail40 :
    integerPowerAffine 1 1 (-1) (bookPowerCoeffs.drop 40) =
      bookReflectedAffineTail40 := by
  rw [show bookPowerCoeffs.drop 40 =
      (bookPowerCoeffs.drop 40).take 20 ++ bookPowerCoeffs.drop 60 by
        rfl,
    integerPowerAffine_append, book_reflected_affine_tail60]
  rfl

set_option maxRecDepth 100000 in
private lemma book_reflected_affine_tail20 :
    integerPowerAffine 1 1 (-1) (bookPowerCoeffs.drop 20) =
      bookReflectedAffineTail20 := by
  rw [show bookPowerCoeffs.drop 20 =
      (bookPowerCoeffs.drop 20).take 20 ++ bookPowerCoeffs.drop 40 by
        rfl,
    integerPowerAffine_append, book_reflected_affine_tail40]
  rfl

set_option maxRecDepth 100000 in
private lemma book_reflected_affine :
    integerPowerAffine 1 1 (-1) bookPowerCoeffs =
      bookReflectedCoeffs := by
  rw [← List.take_append_drop 20 bookPowerCoeffs,
    integerPowerAffine_append, book_reflected_affine_tail20]
  rfl

lemma book_reflected_coeffs :
    bookReflectedCoeffs =
      integerPowerAffine 1 1 (-1) bookPowerCoeffs := by
  exact book_reflected_affine.symm

lemma book_reflected_eval (v : ℝ) :
    evalIntegerPower bookReflectedCoeffs v =
      evalIntegerPower bookPowerCoeffs (1 - v) := by
  rw [book_reflected_coeffs]
  have haffine :=
    evalIntegerPower_affine
      1 1 (-1) bookPowerCoeffs v (by norm_num)
  calc
    _ = evalIntegerPower bookPowerCoeffs
        (((1 : ℝ) + (-1 : ℝ) * v) / 1) := by
      simpa only [Nat.cast_one, Int.cast_one, Int.cast_neg,
        Int.cast_ofNat, mul_one, one_mul, one_pow] using haffine
    _ = _ :=
      congrArg (evalIntegerPower bookPowerCoeffs) (by ring)

end

end BackwardBookRound2Back1Certificate
end Arxiv2407_19026
