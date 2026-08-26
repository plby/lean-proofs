import ErdosProblems.Erdos67b.Pretentious

/-!
# Pretentious symmetry for real-valued coefficients

For a real-valued one-bounded function, proximity to the Archimedean
twist `n^(it)` forces the two opposite twists `n^(it)` and `n^(-it)` to
be close.  This is the deterministic reduction used in the real-valued
Matomäki--Radziwiłł argument away from the central frequency.
-/

open scoped BigOperators ComplexConjugate

namespace Erdos67b

noncomputable section

theorem archimedeanTwist_neg (t : ℝ) (n : ℕ) :
    archimedeanTwist (-t) n = conj (archimedeanTwist t n) := by
  rw [conj_archimedeanTwist, archimedeanTwist]
  congr 1
  push_cast
  ring

/-- Pointwise real symmetry.  The constant `4` is uniform over the whole
closed unit disk on the real axis. -/
theorem pretentiousTerm_twist_neg_le_four_mul_of_real
    {f : ℕ → ℂ} {p : ℕ} (hp : p.Prime)
    (hreal : conj (f p) = f p) (hbound : ‖f p‖ ≤ 1) (t : ℝ) :
    pretentiousTerm (archimedeanTwist t) (archimedeanTwist (-t)) p ≤
      4 * pretentiousTerm f (archimedeanTwist t) p := by
  let a : ℂ := archimedeanTwist t p
  have ha : ‖a‖ = 1 := norm_archimedeanTwist hp.pos t
  have haf : a.re ^ 2 + a.im ^ 2 = 1 := by
    have hsq : Complex.normSq a = 1 := by
      rw [Complex.normSq_eq_norm_sq, ha]
      norm_num
    simpa [Complex.normSq_apply, pow_two] using hsq
  have hfim : (f p).im = 0 := by
    have him := congrArg Complex.im hreal
    simp only [Complex.conj_im] at him
    linarith
  have hfre : |(f p).re| ≤ 1 :=
    (Complex.abs_re_le_norm (f p)).trans hbound
  have hfreSq : (f p).re ^ 2 ≤ 1 := by
    rw [abs_le] at hfre
    nlinarith [sq_nonneg ((f p).re - 1), sq_nonneg ((f p).re + 1)]
  have hscalar :
      1 - (a * a).re ≤ 4 * (1 - (f p * conj a).re) := by
    rw [Complex.mul_re, Complex.mul_re]
    simp only [Complex.conj_re, Complex.conj_im, hfim, zero_mul, sub_zero]
    nlinarith [sq_nonneg (a.re - (f p).re)]
  unfold pretentiousTerm
  rw [archimedeanTwist_neg]
  change
    (1 - (a * conj (conj a)).re) / (p : ℝ) ≤
      4 * ((1 - (f p * conj a).re) / (p : ℝ))
  simp only [starRingEnd_apply, star_star]
  have hp0 : (0 : ℝ) ≤ p := by positivity
  calc
    (1 - (a * a).re) / (p : ℝ) ≤
        (4 * (1 - (f p * conj a).re)) / (p : ℝ) :=
      div_le_div_of_nonneg_right hscalar hp0
    _ = 4 * ((1 - (f p * conj a).re) / (p : ℝ)) := by ring

/-- Finite-prime version of real pretentious symmetry.  Thus any lower
bound for separation of the opposite Archimedean twists gives one quarter
of that lower bound for a real-valued one-bounded function. -/
theorem pretentiousDistSq_twist_neg_le_four_mul_of_real
    {f : ℕ → ℂ} (hreal : ∀ n, 0 < n → conj (f n) = f n)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) (t : ℝ) (X : ℕ) :
    pretentiousDistSq (archimedeanTwist t) (archimedeanTwist (-t)) X ≤
      4 * pretentiousDistSq f (archimedeanTwist t) X := by
  unfold pretentiousDistSq
  calc
    (∑ p ∈ primesUpTo X,
        pretentiousTerm (archimedeanTwist t) (archimedeanTwist (-t)) p) ≤
        ∑ p ∈ primesUpTo X,
          4 * pretentiousTerm f (archimedeanTwist t) p := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' := (mem_primesUpTo.mp hp).1
      exact pretentiousTerm_twist_neg_le_four_mul_of_real hp'
        (hreal p hp'.pos) (hbound p hp'.pos) t
    _ = 4 * ∑ p ∈ primesUpTo X,
        pretentiousTerm f (archimedeanTwist t) p := by
      rw [Finset.mul_sum]

/-- Consumer form: a twist-separation lower bound immediately supplies
the nonpretentious lower bound needed at a real frequency. -/
theorem one_fourth_mul_le_pretentiousDistSq_of_real_of_twist_separation
    {f : ℕ → ℂ} (hreal : ∀ n, 0 < n → conj (f n) = f n)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {t A : ℝ} {X : ℕ}
    (hsep : A ≤
      pretentiousDistSq (archimedeanTwist t) (archimedeanTwist (-t)) X) :
    A / 4 ≤ pretentiousDistSq f (archimedeanTwist t) X := by
  have hsym := pretentiousDistSq_twist_neg_le_four_mul_of_real
    hreal hbound t X
  linarith

end

end Erdos67b
