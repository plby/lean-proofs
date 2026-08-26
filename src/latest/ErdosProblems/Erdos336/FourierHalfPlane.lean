import ErdosProblems.Erdos336.FourierFourFifths

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped BigOperators ComplexConjugate

variable {N : ℕ} [NeZero N]

noncomputable def fourierPositiveHalf
    (A : Finset (ZMod N)) (k : ZMod N) : Finset (ZMod N) :=
  A.filter fun x => 0 <
    (conj (cyclicFinsetFourier A k) * ZMod.stdAddChar (-(x * k))).re

/-- The open half-plane in the direction of a Fourier sum contains at least
as many terms as the norm of that sum. -/
theorem norm_fourier_le_card_positiveHalf
    (A : Finset (ZMod N)) (k : ZMod N) :
    ‖cyclicFinsetFourier A k‖ ≤ (fourierPositiveHalf A k).card := by
  let F := cyclicFinsetFourier A k
  let z : ZMod N → ℂ := fun x => ZMod.stdAddChar (-(x * k))
  let B := fourierPositiveHalf A k
  have hzNorm (x : ZMod N) : ‖z x‖ = 1 := by
    simp [z]
  have hpoint (x : ZMod N) (hx : x ∈ A) :
      (conj F * z x).re ≤
        if 0 < (conj F * z x).re then ‖F‖ else 0 := by
    by_cases hp : 0 < (conj F * z x).re
    · simp only [hp, if_true]
      apply le_trans (Complex.re_le_norm _)
      rw [norm_mul, Complex.norm_conj, hzNorm, mul_one]
    · simp only [hp, if_false]
      linarith
  have hsum := Finset.sum_le_sum fun x hx => hpoint x hx
  have hleft : (∑ x ∈ A, (conj F * z x).re) = ‖F‖ ^ 2 := by
    calc
      (∑ x ∈ A, (conj F * z x).re) =
          (conj F * ∑ x ∈ A, z x).re := by
            rw [Finset.mul_sum]
            simp
      _ = (conj F * F).re := by
            simp [F, z, cyclicFinsetFourier]
      _ = ‖F‖ ^ 2 := by
            rw [show conj F * F = F * conj F by ring, Complex.mul_conj]
            rw [Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hright : (∑ x ∈ A,
      if 0 < (conj F * z x).re then ‖F‖ else 0) = B.card * ‖F‖ := by
    change (∑ x ∈ A,
      if 0 < (conj F * z x).re then ‖F‖ else 0) =
      ((A.filter fun x => 0 < (conj F * z x).re).card : ℝ) * ‖F‖
    rw [← Finset.sum_filter]
    simp
  rw [hleft, hright] at hsum
  by_cases hF : ‖F‖ = 0
  · change ‖F‖ ≤ (B.card : ℝ)
    rw [hF]
    positivity
  · have hFpos : 0 < ‖F‖ := lt_of_le_of_ne (norm_nonneg F) (Ne.symm hF)
    nlinarith

/-- A coefficient larger than four fifths produces an open semicircle
containing more than four fifths of the set. -/
theorem four_mul_card_lt_five_mul_positiveHalf
    (A : Finset (ZMod N)) (k : ZMod N)
    (hk : 16 * (A.card : ℝ) ^ 2 <
      25 * ‖cyclicFinsetFourier A k‖ ^ 2) :
    4 * A.card < 5 * (fourierPositiveHalf A k).card := by
  have hnorm : 4 * (A.card : ℝ) <
      5 * ‖cyclicFinsetFourier A k‖ := by
    have hn := norm_nonneg (cyclicFinsetFourier A k)
    have ha : 0 ≤ (A.card : ℝ) := by positivity
    nlinarith
  have hle := norm_fourier_le_card_positiveHalf A k
  exact_mod_cast (show (4 : ℝ) * A.card <
    5 * (fourierPositiveHalf A k).card by nlinarith)

end Erdos336
