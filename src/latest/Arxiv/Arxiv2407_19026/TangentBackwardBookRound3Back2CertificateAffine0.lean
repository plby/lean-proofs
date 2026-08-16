import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2CertificateData

/-! Batched affine certificate for the round-3 second backward-book interval. -/

namespace Arxiv2407_19026
namespace BackwardBookRound3Back2Certificate

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

private lemma book_affine_tail170 :
    integerPowerAffine 5 3 2 bookNumeratorTail170 =
      bookAffineTail170 := by
  rfl

private lemma book_affine_tail150 :
    integerPowerAffine 5 3 2 bookNumeratorTail150 =
      bookAffineTail150 := by
  rw [bookNumeratorTail150, bookNumeratorTail160,
    ← List.append_assoc, integerPowerAffine_append,
    book_affine_tail170]
  rfl

private lemma book_affine_tail130 :
    integerPowerAffine 5 3 2 bookNumeratorTail130 =
      bookAffineTail130 := by
  rw [bookNumeratorTail130, bookNumeratorTail140,
    ← List.append_assoc, integerPowerAffine_append,
    book_affine_tail150]
  rfl

private lemma book_affine_tail110 :
    integerPowerAffine 5 3 2 bookNumeratorTail110 =
      bookAffineTail110 := by
  rw [bookNumeratorTail110, bookNumeratorTail120,
    ← List.append_assoc, integerPowerAffine_append,
    book_affine_tail130]
  rfl

private lemma book_affine_tail90 :
    integerPowerAffine 5 3 2 bookNumeratorTail90 =
      bookAffineTail90 := by
  rw [bookNumeratorTail90, bookNumeratorTail100,
    ← List.append_assoc, integerPowerAffine_append,
    book_affine_tail110]
  rfl

private lemma book_affine_tail70 :
    integerPowerAffine 5 3 2 bookNumeratorTail70 =
      bookAffineTail70 := by
  rw [bookNumeratorTail70, bookNumeratorTail80,
    ← List.append_assoc, integerPowerAffine_append,
    book_affine_tail90]
  rfl

set_option maxRecDepth 100000 in
-- Reducing a 20-coefficient affine stage over a long exact tail exceeds the default depth.
private lemma book_affine_tail50 :
    integerPowerAffine 5 3 2 bookNumeratorTail50 =
      bookAffineTail50 := by
  rw [bookNumeratorTail50, bookNumeratorTail60,
    ← List.append_assoc, integerPowerAffine_append,
    book_affine_tail70]
  rfl

set_option maxRecDepth 100000 in
-- Reducing a 20-coefficient affine stage over a long exact tail exceeds the default depth.
private lemma book_affine_tail30 :
    integerPowerAffine 5 3 2 bookNumeratorTail30 =
      bookAffineTail30 := by
  rw [bookNumeratorTail30, bookNumeratorTail35,
    bookNumeratorTail40, ← List.append_assoc,
    ← List.append_assoc, integerPowerAffine_append,
    book_affine_tail50]
  rfl

set_option maxRecDepth 100000 in
-- Reducing a 20-coefficient affine stage over a long exact tail exceeds the default depth.
private lemma book_affine_tail10 :
    integerPowerAffine 5 3 2 bookNumeratorTail10 =
      bookAffineTail10 := by
  rw [bookNumeratorTail10, bookNumeratorTail15,
    bookNumeratorTail20, bookNumeratorTail25,
    ← List.append_assoc, ← List.append_assoc,
    ← List.append_assoc, integerPowerAffine_append,
    book_affine_tail30]
  rfl

set_option maxRecDepth 100000 in
-- Reducing the final ten-coefficient affine stage exceeds the default depth.
lemma book_affine_tail0 :
    integerPowerAffine 5 3 2 bookNumeratorTail0 =
      bookAffineTail0 := by
  rw [bookNumeratorTail0, bookNumeratorTail5,
    ← List.append_assoc, integerPowerAffine_append,
    book_affine_tail10]
  rfl

end

end BackwardBookRound3Back2Certificate
end Arxiv2407_19026
