/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.RationalWeilWeight

/-!
# A coefficient-cancellation probe for the rational Artin polynomial

For a selected supported pole `r`, multiply the common simple-pole
denominator by the product of all its factors except `X - r`.  The resulting
polynomial has a simple zero at `r` and a double zero at every other pole.
Its derivative therefore vanishes at all other poles and is nonzero at `r`.

Adding a scalar multiple of this probe to a polynomial does not change its
values at the poles, but changes its logarithmic-derivative phase in one
nonzero affine direction.  This is the cancellation mechanism which makes
the rational Artin polynomial have degree less than twice the number of
poles.
-/

namespace Erdos387

open Polynomial

namespace RationalWeil

/-- The product of all supported linear pole factors except the selected
one. -/
noncomputable def poleComplementPolynomial
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p) (r : ZMod p) :
    (ZMod p)[X] :=
  ∏ s ∈ (InverseRational.poleSupport coeff).erase r, (X - C s)

/-- A polynomial with a simple zero at the selected pole and double zeros at
all other supported poles. -/
noncomputable def derivativeProbe
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p) (r : ZMod p) :
    (ZMod p)[X] :=
  InverseRational.simplePoleDenominatorPolynomial coeff *
    poleComplementPolynomial coeff r

theorem monic_poleComplementPolynomial
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p) (r : ZMod p) :
    (poleComplementPolynomial coeff r).Monic := by
  exact monic_prod_X_sub_C (fun s : ZMod p => s)
    ((InverseRational.poleSupport coeff).erase r)

theorem monic_derivativeProbe
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p) (r : ZMod p) :
    (derivativeProbe coeff r).Monic := by
  exact (InverseRational.monic_simplePoleDenominatorPolynomial coeff).mul
    (monic_poleComplementPolynomial coeff r)

/-- At a supported selected pole, the probe is `(X-r)` times the square of
the complementary product. -/
theorem derivativeProbe_eq_linear_mul_complement_sq
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p)
    {r : ZMod p} (hr : r ∈ InverseRational.poleSupport coeff) :
    derivativeProbe coeff r =
      (X - C r) * (poleComplementPolynomial coeff r) ^ 2 := by
  rw [derivativeProbe,
    InverseRational.simplePoleDenominatorPolynomial_eq_mul_erase coeff hr]
  unfold poleComplementPolynomial
  ring

/-- The probe vanishes at every supported pole. -/
theorem eval_derivativeProbe_eq_zero
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) (r : ZMod p)
    {s : ZMod p} (hs : s ∈ InverseRational.poleSupport coeff) :
    eval s (derivativeProbe coeff r) = 0 := by
  rw [derivativeProbe, eval_mul]
  have hden :
      eval s (InverseRational.simplePoleDenominatorPolynomial coeff) = 0 := by
    rw [InverseRational.simplePoleDenominatorPolynomial_eq_mul_erase coeff hs,
      eval_mul]
    simp
  rw [hden, zero_mul]

/-- At the selected pole, the derivative of the probe is the square of the
nonzero complementary value. -/
theorem eval_derivative_derivativeProbe_at_selected
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) {r : ZMod p}
    (hr : r ∈ InverseRational.poleSupport coeff) :
    eval r (derivativeProbe coeff r).derivative =
      eval r (poleComplementPolynomial coeff r) ^ 2 := by
  rw [derivativeProbe_eq_linear_mul_complement_sq coeff hr,
    derivative_mul, eval_add, eval_mul, eval_mul]
  simp

/-- Hence the selected derivative value is nonzero. -/
theorem eval_derivative_derivativeProbe_at_selected_ne_zero
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) {r : ZMod p}
    (hr : r ∈ InverseRational.poleSupport coeff) :
    eval r (derivativeProbe coeff r).derivative ≠ 0 := by
  rw [eval_derivative_derivativeProbe_at_selected coeff hr]
  exact pow_ne_zero 2
    (InverseRational.eval_simplePoleComplement_ne_zero coeff hr)

/-- At every other supported pole, the probe has a double zero and its
derivative vanishes. -/
theorem eval_derivative_derivativeProbe_at_other
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) {r s : ZMod p}
    (hr : r ∈ InverseRational.poleSupport coeff)
    (hs : s ∈ InverseRational.poleSupport coeff) (hsr : s ≠ r) :
    eval s (derivativeProbe coeff r).derivative = 0 := by
  rw [derivativeProbe_eq_linear_mul_complement_sq coeff hr,
    derivative_mul, eval_add, eval_mul, eval_mul]
  have hscomp : s ∈ (InverseRational.poleSupport coeff).erase r :=
    Finset.mem_erase.mpr ⟨hsr, hs⟩
  have hcomp : eval s (poleComplementPolynomial coeff r) = 0 := by
    rw [poleComplementPolynomial, eval_prod]
    exact Finset.prod_eq_zero hscomp (by simp)
  simp [derivative_pow, eval_pow, eval_mul, hcomp]

/-- Adding any scalar multiple of the probe preserves every value at a
supported pole. -/
theorem eval_add_C_mul_derivativeProbe
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) (r t : ZMod p) (F : (ZMod p)[X])
    {s : ZMod p} (hs : s ∈ InverseRational.poleSupport coeff) :
    eval s (F + C t * derivativeProbe coeff r) = eval s F := by
  rw [eval_add, eval_mul, eval_C, eval_derivativeProbe_eq_zero coeff r hs,
    mul_zero, add_zero]

/-- Avoiding the pole support is invariant under translation by the probe. -/
theorem avoidsPoleSupport_add_C_mul_derivativeProbe_iff
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) (r t : ZMod p) (F : (ZMod p)[X]) :
    AvoidsPoleSupport coeff (F + C t * derivativeProbe coeff r) ↔
      AvoidsPoleSupport coeff F := by
  simp only [AvoidsPoleSupport]
  constructor <;> intro h s hs
  · simpa only [eval_add_C_mul_derivativeProbe coeff r t F hs] using h s hs
  · simpa only [eval_add_C_mul_derivativeProbe coeff r t F hs] using h s hs

/-- The probe has the exact degree `2 * |support| - 1` when the selected
pole belongs to the support. -/
theorem natDegree_derivativeProbe
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) {r : ZMod p}
    (hr : r ∈ InverseRational.poleSupport coeff) :
    (derivativeProbe coeff r).natDegree =
      2 * (InverseRational.poleSupport coeff).card - 1 := by
  rw [derivativeProbe, Polynomial.Monic.natDegree_mul
    (InverseRational.monic_simplePoleDenominatorPolynomial coeff)
    (monic_poleComplementPolynomial coeff r),
    InverseRational.natDegree_simplePoleDenominatorPolynomial,
    show (poleComplementPolynomial coeff r).natDegree =
        ((InverseRational.poleSupport coeff).erase r).card by
      exact natDegree_finsetProd_X_sub_C_eq_card
        ((InverseRational.poleSupport coeff).erase r)
        (fun s : ZMod p => s),
    Finset.card_erase_of_mem hr]
  omega

end RationalWeil

end Erdos387
