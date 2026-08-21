import ErdosProblems.Erdos239.External.Erdos67.MRGSA9GeneralizedMangoldt

/-!
# Finite coefficient identities behind the GS A.10 contour formula

This module extracts the purely finite part of the many-convolutions
argument.  In particular, it removes the `m = 1` endpoint from
`Λ_a * a = a·log`; after division by `log n` this is the coefficient
identity used in GS Lemma 2.1.  No convergence or contour interchange is
used here.
-/

open scoped BigOperators

namespace Erdos67.MRHalaszBands

noncomputable section

private theorem filter_divisorsAntidiagonal_second_ne_one
    {n : ℕ} (hn : n ≠ 0) :
    n.divisorsAntidiagonal.filter (fun xy ↦ xy.2 ≠ 1) =
      n.divisorsAntidiagonal.erase (n, 1) := by
  ext xy
  rcases xy with ⟨x, y⟩
  simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal,
    Finset.mem_erase]
  constructor
  · rintro ⟨⟨hxy, _⟩, hy⟩
    refine ⟨?_, ⟨hxy, hn⟩⟩
    rintro hpair
    have hy1 : y = 1 := congrArg Prod.snd hpair
    exact hy hy1
  · rintro ⟨hne, ⟨hxy, _⟩⟩
    refine ⟨⟨hxy, hn⟩, ?_⟩
    intro hy
    apply hne
    apply Prod.ext
    · simpa [hy] using hxy
    · simpa using hy

/-- Removing the `m = 1` endpoint from `Λ_a * a = a·log` gives the
finite numerator in the first many-convolutions identity. -/
theorem sum_gsGeneralizedMangoldt_mul_self_second_ne_one
    (a : ArithmeticFunction ℂ) (ha : Invertible (a 1))
    (ha1 : a 1 = 1) {n : ℕ} (hn : n ≠ 0) :
    ∑ xy ∈ n.divisorsAntidiagonal with xy.2 ≠ 1,
        gsGeneralizedMangoldt a ha xy.1 * a xy.2 =
      a n * (Real.log n : ℂ) - gsGeneralizedMangoldt a ha n := by
  let b : ℕ × ℕ → ℂ := fun xy ↦
    gsGeneralizedMangoldt a ha xy.1 * a xy.2
  have hmem : (n, 1) ∈ n.divisorsAntidiagonal := by
    exact Nat.mem_divisorsAntidiagonal.mpr ⟨by simp, hn⟩
  have herase := Finset.sum_erase_add n.divisorsAntidiagonal b hmem
  have hfull := sum_gsGeneralizedMangoldt_mul_self a ha n
  rw [filter_divisorsAntidiagonal_second_ne_one hn]
  change ∑ xy ∈ n.divisorsAntidiagonal.erase (n, 1), b xy = _
  change (∑ xy ∈ n.divisorsAntidiagonal.erase (n, 1), b xy) +
      b (n, 1) =
    ∑ xy ∈ n.divisorsAntidiagonal, b xy at herase
  have hb : b (n, 1) = gsGeneralizedMangoldt a ha n := by
    simp [b, ha1]
  have hfull' :
      (∑ xy ∈ n.divisorsAntidiagonal, b xy) =
        a n * (Real.log n : ℂ) := by
    simpa only [b] using hfull
  rw [hb, hfull'] at herase
  linear_combination herase

/-- Divided form of the finite coefficient identity.  It is stated only for
`n ≥ 2`, so the logarithmic denominator is nonzero. -/
theorem sum_gsGeneralizedMangoldt_mul_self_div_log
    (a : ArithmeticFunction ℂ) (ha : Invertible (a 1))
    (ha1 : a 1 = 1) {n : ℕ} (hn : 2 ≤ n) :
    (∑ xy ∈ n.divisorsAntidiagonal with xy.2 ≠ 1,
        gsGeneralizedMangoldt a ha xy.1 * a xy.2) /
          (Real.log n : ℂ) =
      a n - gsGeneralizedMangoldt a ha n / (Real.log n : ℂ) := by
  rw [sum_gsGeneralizedMangoldt_mul_self_second_ne_one a ha ha1
    (by omega)]
  have hlog : (Real.log n : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos (by exact_mod_cast hn)).ne'
  field_simp

/-- The preceding identity specialized to the common high-prime factor in
the A.9 decomposition. -/
theorem sum_gsA9HighGeneralizedMangoldt_mul_high_div_log
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    (∑ xy ∈ n.divisorsAntidiagonal with xy.2 ≠ 1,
        gsA9HighGeneralizedMangoldt hmul y xy.1 *
          gsA9HighArithmetic f y xy.2) /
          (Real.log n : ℂ) =
      gsA9HighArithmetic f y n -
        gsA9HighGeneralizedMangoldt hmul y n / (Real.log n : ℂ) := by
  exact sum_gsGeneralizedMangoldt_mul_self_div_log
    (gsA9HighArithmetic f y) (gsA9HighArithmeticInvertible hmul y)
      (gsA9HighArithmetic_one hmul y) hn

end

end Erdos67.MRHalaszBands
