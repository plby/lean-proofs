/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerCoprimeMomentBounds
import ErdosProblems.Erdos240.BakerCoprimeProductRatio
import ErdosProblems.Erdos240.BakerSourceBudgetInequalities

/-!
# The p. 52 coprime-node Hermite polynomial at a missing node

This file combines the exact arbitrary-node Hermite basis, the factorial
product-ratio estimate, the predecessor `/9` moment cancellation, and the
`3/4 + 1/4` budget split.  Its final estimate leaves only the explicit
parameter-only Hermite loss as an input; that loss is discharged in the
numerical parameter module.
-/

open scoped BigOperators

noncomputable section

namespace Erdos240.BakerCoprimeHermiteTarget

open Complex Finset Metric Polynomial
open BakerCoprimeInterpolation
open BakerCoprimeMomentBounds
open BakerCoprimeProductRatio
open BakerInduction
open BakerLemma3Concrete
open BakerLemma3Instantiation
open BakerLemma4Concrete
open BakerSourceAlgebraicMajorant
open BakerSourceAlgebraicMomentBounds
open BakerSourceMomentCancellation
open BakerSourceOversizedConstantNumerics
open BakerSourceState
open CoprimeHermiteBasis
open HermiteInterpolation

@[simp] theorem finiteRepeatedNodes_coprimeNodeIndices
    (q R T : ℕ) :
    finiteRepeatedNodes (coprimeNodeIndices q R) T =
      coprimeNodes q R T := rfl

theorem coprimeNodeIndices_nonempty {q R : ℕ}
    (hR : 0 < R) : (coprimeNodeIndices q R).Nonempty := by
  refine ⟨0, ?_⟩
  simp [mem_coprimeNodeIndices, hR]

/-- Uniform estimate for the actual Newton--Hermite polynomial on the
coprime nodes.  The hypothesis `hloss` is completely parameter-only and is
the exact finite-sum factor exposed by `CoprimeHermiteBasis`.
-/
theorem norm_coprimeHermitePolynomial_eval_le_exp_neg_half
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (state : LevelState P (J + 1)) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0) (hJ : P.LevelOK J)
    (hseed : CoprimeDescentAtLevel P (g state b bLast) J)
    {C₀ : ℝ} (hstruct : 4 * P.C ≤ C₀)
    (hjet : jetAbsorptionConstant P ≤ C₀)
    (hE : 8 ≤ sourceExponent P (C₀ * Real.log P.OmegaOld))
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm
          P.old P.newPrime b bLast| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ))))
    (l : ℕ) (hl : 1 ≤ l) (hlR : l ≤ P.R (J + 1))
    (hlq : ¬l.Coprime P.q)
    (hgrowth : ∀ r ∈ coprimeNodeIndices P.q (P.R (J + 1)),
      ∀ m', VDPLMultiIndex.weight m' ≤ P.Sstep J →
        (scaledStateAlgebraicExponentialMajorant P state b bLast
          (((r + 1 : ℕ) : ℂ)) m').growth ≤
            Real.exp
              (sourceExponent P (P.C * Real.log P.OmegaOld) / 4))
    (hamplification : ∀ r ∈ coprimeNodeIndices P.q (P.R (J + 1)),
      ∀ m', VDPLMultiIndex.weight m' ≤ P.Sstep J →
        (stateSourceMajorants P state b bLast
          (((r + 1 : ℕ) : ℂ)) m').amplificationMajorant ≤
            Real.exp
              (sourceExponent P (P.C * Real.log P.OmegaOld) / 4))
    (m : VDPLMultiIndex P.rank)
    (hm : VDPLMultiIndex.weight m ≤ P.Slevel (J + 1))
    (hloss :
      ((coprimeNodeIndices P.q (P.R (J + 1))).card : ℝ) *
          ((P.Sstep J / 4 : ℕ) : ℝ) *
          ((P.Sstep J / 4 : ℕ) : ℝ) *
        (((P.q : ℝ) * (2 : ℝ) ^ (3 * P.R (J + 1))) ^
            (P.Sstep J / 4) *
          (2 : ℝ) ^
            ((coprimeNodeIndices P.q (P.R (J + 1))).card *
                (P.Sstep J / 4) + (P.Sstep J / 4))) ≤
        Real.exp
          (sourceExponent P (C₀ * Real.log P.OmegaOld) / 6)) :
    ‖(polynomial (fun w ↦ f state b bLast w m)
        (coprimeNodes P.q (P.R (J + 1)) (P.Sstep J / 4))).eval
          (l : ℂ)‖ ≤
      Real.exp
        (-sourceExponent P (C₀ * Real.log P.OmegaOld) / 2) := by
  let s := coprimeNodeIndices P.q (P.R (J + 1))
  let T := P.Sstep J / 4
  let K : ℝ := (P.q : ℝ) * (2 : ℝ) ^ (3 * P.R (J + 1))
  let E : ℝ := sourceExponent P (C₀ * Real.log P.OmegaOld)
  let delta : ℝ := Real.exp (-2 * E / 3)
  have hs : s.Nonempty :=
    coprimeNodeIndices_nonempty (P.R_pos (J + 1))
  have hT : 0 < T := by
    exact P.Sstep_div_four_pos_of_LevelOK hJ
  have hK : 0 ≤ K := by positivity
  have hdelta : 0 ≤ delta := (Real.exp_pos _).le
  have hdiff : Differentiable ℂ (fun w ↦ f state b bLast w m) :=
    differentiable_sourceState_f state b bLast m
  have hdistinct : ∀ r ∈ s, l ≠ r + 1 := by
    intro r hr hrl
    apply hlq
    subst l
    exact (mem_coprimeNodeIndices.mp hr).2
  have hratio : ∀ r ∈ s,
      ‖(finiteNodePolynomial s).eval (l : ℂ)‖ ≤
        K * finiteSpacingProduct s r := by
    intro r hr
    exact norm_finiteNodePolynomial_eval_le P.q_prime (P.q_dvd_R_succ J)
      hl hlR hlq hr
  have hsmallJets : ∀ r ∈ s, ∀ j < T,
      ‖iteratedDeriv j (fun w ↦ f state b bLast w m)
          (((r + 1 : ℕ) : ℂ)) / (j.factorial : ℂ)‖ ≤ delta := by
    intro r hr j hj
    have hrmem := mem_coprimeNodeIndices.mp hr
    apply norm_normalizedIteratedDeriv_f_le_exp_neg_two_thirds_of_coprimeDescent
      state b hbLast hseed hstruct hjet hE hsmall (r + 1) j
      (by omega) (by omega) hrmem.2 (hgrowth r hr) (hamplification r hr) m
    have hbudget := P.Slevel_succ_add_Sstep_div_four_le_of_LevelOK hJ
    exact (Nat.add_le_add_left (Nat.le_of_lt hj) _).trans
      ((Nat.add_le_add_right hm T).trans hbudget)
  have hpoly := norm_polynomial_finiteRepeatedNodes_eval_le_uniform
    hdiff hs hT hK hdelta hdistinct hratio hsmallJets
  rw [finiteRepeatedNodes_coprimeNodeIndices] at hpoly
  have hloss' :
      (s.card : ℝ) * T * T *
          (K ^ T * (2 : ℝ) ^ (s.card * T + T)) ≤ Real.exp (E / 6) := by
    simpa only [s, T, K, E] using hloss
  calc
    ‖(polynomial (fun w ↦ f state b bLast w m)
        (coprimeNodes P.q (P.R (J + 1)) (P.Sstep J / 4))).eval
          (l : ℂ)‖ ≤
        delta * ((s.card : ℝ) * T * T *
          (K ^ T * (2 : ℝ) ^ (s.card * T + T))) := by
            simpa only [s, T, K] using hpoly
    _ ≤ Real.exp (-2 * E / 3) * Real.exp (E / 6) := by
      exact mul_le_mul_of_nonneg_left hloss' hdelta
    _ = Real.exp (-E / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring

#print axioms norm_coprimeHermitePolynomial_eval_le_exp_neg_half

end Erdos240.BakerCoprimeHermiteTarget
