/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Witness

/-!
# The exact integration target for the CFP structure theorem

This module records the integer-scale form of Conlon--Fox--Pham, Theorem 1.5,
that the rest of the Erdős 186 development must prove and consume.  Unlike the
older `HasCFPStructure` abbreviation, the statement below fixes the scale and
loss constants *before* quantifying over the input set.  Consequently it cannot
be inhabited by choosing a zero dilation or by discarding the whole set.

The analytic hypotheses use the paper's base-two logarithm.  The rational
constant `scaleNum / scaleDen` is a uniform positive lower bound for the
integer dilation factor.  Replacing the paper's real dilation by this smaller
integer dilation is the standard floor-and-shrink corollary.

`IntegerTheorem15` is a proposition, not an assumed theorem.  It is
kept as the explicit end-to-end target while its combinatorial dependencies
are proved in the sibling modules.
-/

namespace Erdos186.CFP

/-- The canonical embedding of an integer in the one-dimensional integer
lattice used by `GAP`. -/
def integerPoint (a : ℤ) : LatticePoint 1 :=
  fun _ ↦ a

/-- Pointwise embedding of a finite set of integers. -/
def integerPoints (A : Finset ℤ) : Finset (LatticePoint 1) :=
  A.image integerPoint

@[simp]
theorem integerPoint_apply (a : ℤ) (i : Fin 1) : integerPoint a i = a :=
  rfl

theorem integerPoint_injective : Function.Injective integerPoint := by
  intro a b hab
  have h := congrFun hab 0
  simpa using h

@[simp]
theorem mem_integerPoints_iff {A : Finset ℤ} {a : ℤ} :
    integerPoint a ∈ integerPoints A ↔ a ∈ A := by
  classical
  simp [integerPoints, integerPoint_injective.eq_iff]

@[simp]
theorem card_integerPoints (A : Finset ℤ) :
    (integerPoints A).card = A.card := by
  classical
  exact Finset.card_image_of_injective A integerPoint_injective

/-- The exact, nonvacuous integer-scale target corresponding to CFP Theorem
1.5.  The loss inequality has an additive `1` solely to absorb integer
rounding. -/
def IntegerTheorem15 : Prop :=
  ∀ β η : ℝ, 1 < β → 0 < η → η < 1 →
    ∃ scaleNum scaleDen D lossConstant : ℕ,
      0 < scaleNum ∧ 0 < scaleDen ∧ 0 < lossConstant ∧
      ∀ (n : ℕ) (A : Finset ℤ) (s : ℕ),
        A ⊆ Finset.Icc 1 (n : ℤ) →
        (n : ℝ) ≤ Real.rpow (A.card : ℝ) β →
        Real.rpow (A.card : ℝ) η ≤ (s : ℝ) →
        (scaleDen : ℝ) * (s : ℝ) *
              Real.logb 2 (A.card : ℝ) ≤
            (scaleNum : ℝ) * (A.card : ℝ) →
        ∃ k loss : ℕ,
          Nonempty
              (FixedScaleWitness (integerPoints A) s D k loss
                scaleNum scaleDen) ∧
          (loss : ℝ) ≤
            (lossConstant : ℝ) * (s : ℝ) *
                Real.logb 2 (A.card : ℝ) + 1

/-- The source-correct nonempty form of `IntegerTheorem15`.  The paper only
applies the structure theorem to a set of positive cardinality.  Recording
that hypothesis explicitly also rules out the degenerate `s = 0` instance,
since the scale lower bound then has positive left-hand side. -/
def NonemptyIntegerTheorem15 : Prop :=
  ∀ β η : ℝ, 1 < β → 0 < η → η < 1 →
    ∃ scaleNum scaleDen D lossConstant : ℕ,
      0 < scaleNum ∧ 0 < scaleDen ∧ 0 < lossConstant ∧
      ∀ (n : ℕ) (A : Finset ℤ) (s : ℕ),
        A.Nonempty →
        A ⊆ Finset.Icc 1 (n : ℤ) →
        (n : ℝ) ≤ Real.rpow (A.card : ℝ) β →
        Real.rpow (A.card : ℝ) η ≤ (s : ℝ) →
        (scaleDen : ℝ) * (s : ℝ) *
              Real.logb 2 (A.card : ℝ) ≤
            (scaleNum : ℝ) * (A.card : ℝ) →
        ∃ k loss : ℕ,
          Nonempty
              (FixedScaleWitness (integerPoints A) s D k loss
                scaleNum scaleDen) ∧
          (loss : ℝ) ≤
            (lossConstant : ℝ) * (s : ℝ) *
                Real.logb 2 (A.card : ℝ) + 1

/-- The legacy all-input proposition implies its source-correct nonempty
restriction with the same uniform constants. -/
theorem nonemptyIntegerTheorem15_of_integerTheorem15
    (h : IntegerTheorem15) : NonemptyIntegerTheorem15 := by
  intro β η hβ hη hη1
  obtain ⟨scaleNum, scaleDen, D, lossConstant, hnum, hden, hloss, hout⟩ :=
    h β η hβ hη hη1
  exact ⟨scaleNum, scaleDen, D, lossConstant, hnum, hden, hloss,
    fun n A s _hA ↦ hout n A s⟩

/-- The bounded-dimensional form used after passing to GAP coordinates in
the Pham--Zakharov iteration.  The ambient dimension is fixed before the
uniform constants are chosen, and box cardinality replaces the one-
dimensional endpoint `n`.  This is the precise target of the bounded
no-carry encoding and witness-transport argument.

The quantifier order is essential: `D`, the dilation scale, and the loss
constant may depend on `ambient`, `β`, and `η`, but not on the box or on
`A`. -/
def HigherDimensionalCorollary5 : Prop :=
  ∀ (ambient : ℕ) (β η : ℝ), 1 < β → 0 < η → η < 1 →
    ∃ scaleNum scaleDen D lossConstant : ℕ,
      0 < scaleNum ∧ 0 < scaleDen ∧ 0 < lossConstant ∧
      ∀ (B : IntegerBox ambient) (A : Finset (LatticePoint ambient))
          (s : ℕ),
        A ⊆ B.carrier →
        (B.carrier.card : ℝ) ≤ Real.rpow (A.card : ℝ) β →
        Real.rpow (A.card : ℝ) η ≤ (s : ℝ) →
        (scaleDen : ℝ) * (s : ℝ) *
              Real.logb 2 (A.card : ℝ) ≤
            (scaleNum : ℝ) * (A.card : ℝ) →
        ∃ k loss : ℕ,
          Nonempty
              (FixedScaleWitness A s D k loss scaleNum scaleDen) ∧
          (loss : ℝ) ≤
            (lossConstant : ℝ) * (s : ℝ) *
                Real.logb 2 (A.card : ℝ) + 1

/-- The source-correct form of CFP Corollary 5 used by the Pham--Zakharov
iteration.  Every actual PZ input is nonempty; making that premise explicit
removes the false empty-set/zero-scale instance from the legacy proposition
without changing the conclusion or any quantitative hypothesis. -/
def NonemptyHigherDimensionalCorollary5 : Prop :=
  ∀ (ambient : ℕ) (β η : ℝ), 1 < β → 0 < η → η < 1 →
    ∃ scaleNum scaleDen D lossConstant : ℕ,
      0 < scaleNum ∧ 0 < scaleDen ∧ 0 < lossConstant ∧
      ∀ (B : IntegerBox ambient) (A : Finset (LatticePoint ambient))
          (s : ℕ),
        A.Nonempty →
        A ⊆ B.carrier →
        (B.carrier.card : ℝ) ≤ Real.rpow (A.card : ℝ) β →
        Real.rpow (A.card : ℝ) η ≤ (s : ℝ) →
        (scaleDen : ℝ) * (s : ℝ) *
              Real.logb 2 (A.card : ℝ) ≤
            (scaleNum : ℝ) * (A.card : ℝ) →
        ∃ k loss : ℕ,
          Nonempty
              (FixedScaleWitness A s D k loss scaleNum scaleDen) ∧
          (loss : ℝ) ≤
            (lossConstant : ℝ) * (s : ℝ) *
                Real.logb 2 (A.card : ℝ) + 1

/-- The legacy all-input corollary implies the source-correct nonempty
corollary with the same uniform constants. -/
theorem nonemptyHigherDimensionalCorollary5_of_higherDimensionalCorollary5
    (h : HigherDimensionalCorollary5) :
    NonemptyHigherDimensionalCorollary5 := by
  intro ambient β η hβ hη hη1
  obtain ⟨scaleNum, scaleDen, D, lossConstant, hnum, hden, hloss, hout⟩ :=
    h ambient β η hβ hη hη1
  exact ⟨scaleNum, scaleDen, D, lossConstant, hnum, hden, hloss,
    fun B A s _hA ↦ hout B A s⟩

end Erdos186.CFP
