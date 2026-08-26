import ErdosProblems.Erdos67b.MRGSA10Perron

/-!
# Coefficientwise reconstruction of the two-block A.10 input

The low/high split used in the Granville--Soundararajan contour argument is
needed coefficientwise, not merely after applying `LSeries`.  This file
packages the alternating low factor as one arithmetic function and proves
that its single convolution with the common high factor is exactly the
two-block typical coefficient.  Thus all four deletion terms remain inside
one broad coefficient before Perron is applied.
-/

namespace Erdos67b.MRHalaszBands

noncomputable section

/-- The low factor before either of the two prime-block deletions. -/
def gsA9LowArithmetic (f : ℕ → ℂ) (y : ℕ) : ArithmeticFunction ℂ :=
  toArithmeticFunction (gsA9Low f y)

/-- A low factor with one prime predicate deleted. -/
def gsA9LowDeletionArithmetic
    (f : ℕ → ℂ) (Q : ℕ → Prop) [DecidablePred Q] (y : ℕ) :
    ArithmeticFunction ℂ :=
  toArithmeticFunction (gsA9LowDeletion f Q y)

/-- The four-term low factor in the two-block inclusion--exclusion. -/
def gsA10TwoBlockAlternatingLow
    (f : ℕ → ℂ) (P₁ P₂ : ℕ → Prop)
    [DecidablePred P₁] [DecidablePred P₂] (y : ℕ) :
    ArithmeticFunction ℂ :=
  gsA9LowArithmetic f y -
    gsA9LowDeletionArithmetic f (fun p ↦ ¬ P₁ p ∧ P₂ p) y -
    gsA9LowDeletionArithmetic f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) y +
    gsA9LowDeletionArithmetic f
      (fun p ↦ (¬ P₁ p ∧ P₂ p) ∨ (¬ P₁ p ∧ ¬ P₂ p)) y

private theorem gsA9LowDeletionArithmetic_mul_high
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (Q : ℕ → Prop) [DecidablePred Q] (y : ℕ)
    (hQ : ∀ p, Q p → p ≤ y) :
    gsA9LowDeletionArithmetic f Q y * gsA9HighArithmetic f y =
      toArithmeticFunction (gsDeletePrimeBand f Q) := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp
  have hconv := congrFun
    (convolution_gsA9LowDeletion_gsA9High hmul Q y hQ) n
  have hwrap := congrFun (LSeries.convolution_congr
    (f := gsA9LowDeletionArithmetic f Q y)
    (f' := gsA9LowDeletion f Q y)
    (g := gsA9HighArithmetic f y) (g' := gsA9High f y)
    (fun {m} hm ↦ by simp [gsA9LowDeletionArithmetic, toArithmeticFunction, hm])
    (fun {m} hm ↦ gsA9HighArithmetic_apply_of_ne_zero f y hm)) n
  have hmulEq := congrFun (ArithmeticFunction.coe_mul
    (gsA9LowDeletionArithmetic f Q y) (gsA9HighArithmetic f y)) n
  calc
    (gsA9LowDeletionArithmetic f Q y * gsA9HighArithmetic f y) n =
        LSeries.convolution (gsA9LowDeletionArithmetic f Q y)
          (gsA9HighArithmetic f y) n := hmulEq.symm
    _ = LSeries.convolution (gsA9LowDeletion f Q y) (gsA9High f y) n := hwrap
    _ = gsDeletePrimeBand f Q n := hconv
    _ = toArithmeticFunction (gsDeletePrimeBand f Q) n := by
      simp [toArithmeticFunction, hn]

private theorem gsA9LowArithmetic_mul_high
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f) (y : ℕ) :
    gsA9LowArithmetic f y * gsA9HighArithmetic f y =
      toArithmeticFunction f := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp
  have hconv := primeBandCoefficient_convolution_compl_of_multiplicative
    hmul (fun p ↦ p ≤ y) n (Nat.pos_of_ne_zero hn)
  have hwrap := congrFun (LSeries.convolution_congr
    (f := gsA9LowArithmetic f y) (f' := gsA9Low f y)
    (g := gsA9HighArithmetic f y) (g' := gsA9High f y)
    (fun {m} hm ↦ by simp [gsA9LowArithmetic, toArithmeticFunction, hm])
    (fun {m} hm ↦ gsA9HighArithmetic_apply_of_ne_zero f y hm)) n
  have hmulEq := congrFun (ArithmeticFunction.coe_mul
    (gsA9LowArithmetic f y) (gsA9HighArithmetic f y)) n
  calc
    (gsA9LowArithmetic f y * gsA9HighArithmetic f y) n =
        LSeries.convolution (gsA9LowArithmetic f y)
          (gsA9HighArithmetic f y) n := hmulEq.symm
    _ = LSeries.convolution (gsA9Low f y) (gsA9High f y) n := hwrap
    _ = f n := hconv
    _ = toArithmeticFunction f n := by simp [toArithmeticFunction, hn]

/-- Coefficientwise whole-block reconstruction.  The alternating low factor
is convolved with the common high factor only once, so no deletion-block
triangle inequality or Cauchy loss is introduced. -/
theorem gsA10TwoBlockAlternatingLow_mul_high_eq_typical
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y : ℕ)
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y) :
    gsA10TwoBlockAlternatingLow f P₁ P₂ y * gsA9HighArithmetic f y =
      toArithmeticFunction (finiteHalaszTypicalCoefficient f P₁ P₂) := by
  let Q₂ : ℕ → Prop := fun p ↦ ¬ P₁ p ∧ P₂ p
  let Q₃ : ℕ → Prop := fun p ↦ ¬ P₁ p ∧ ¬ P₂ p
  calc
    gsA10TwoBlockAlternatingLow f P₁ P₂ y * gsA9HighArithmetic f y =
        gsA9LowArithmetic f y * gsA9HighArithmetic f y -
          gsA9LowDeletionArithmetic f Q₂ y * gsA9HighArithmetic f y -
          gsA9LowDeletionArithmetic f Q₃ y * gsA9HighArithmetic f y +
          gsA9LowDeletionArithmetic f (fun p ↦ Q₂ p ∨ Q₃ p) y *
            gsA9HighArithmetic f y := by
      unfold gsA10TwoBlockAlternatingLow Q₂ Q₃
      ring
    _ = toArithmeticFunction f -
          toArithmeticFunction (gsDeletePrimeBand f Q₂) -
          toArithmeticFunction (gsDeletePrimeBand f Q₃) +
          toArithmeticFunction (gsDeletePrimeBand f (fun p ↦ Q₂ p ∨ Q₃ p)) := by
      rw [gsA9LowArithmetic_mul_high hmul y,
        gsA9LowDeletionArithmetic_mul_high hmul Q₂ y hQ₂,
        gsA9LowDeletionArithmetic_mul_high hmul Q₃ y hQ₃,
        gsA9LowDeletionArithmetic_mul_high hmul (fun p ↦ Q₂ p ∨ Q₃ p) y
          (fun p hp ↦ hp.elim (hQ₂ p) (hQ₃ p))]
    _ = toArithmeticFunction (finiteHalaszTypicalCoefficient f P₁ P₂) := by
      ext n
      by_cases hn : n = 0
      · subst n
        simp
      change (if n = 0 then 0 else f n) -
          (if n = 0 then 0 else gsDeletePrimeBand f Q₂ n) -
          (if n = 0 then 0 else gsDeletePrimeBand f Q₃ n) +
          (if n = 0 then 0 else
            gsDeletePrimeBand f (fun p ↦ Q₂ p ∨ Q₃ p) n) =
        (if n = 0 then 0 else finiteHalaszTypicalCoefficient f P₁ P₂ n)
      simp only [if_neg hn]
      exact (finiteHalaszTypicalCoefficient_eq_twoBlock_inclusionExclusion
        f P₁ P₂ (Nat.pos_of_ne_zero hn)).symm

end

end Erdos67b.MRHalaszBands
