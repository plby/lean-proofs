/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerSourceAssemblyIndependent
import ErdosProblems.Erdos240.BakerSourceNumericalAssemblyIndependent
import ErdosProblems.Erdos240.BakerSourceOversizedConstantNumerics

/-!
# A uniform oversized source constant for a fixed old prime family

This file makes the uniformity of the numerical slack explicit.  Given any
additional fixed-family requirement `A`, one constant is chosen before the
varying prime and coefficient cutoff.  It simultaneously dominates `A`, four
times the source's structural constant, and the equation-(7) jet-absorption
constant.  Its normalized exponent is at least eight at every specialization.

Later local-circle, Lemma-5, or coprime-completion estimates can therefore be
added to the single input `A` once their fixed-family exponent coefficients
have been isolated.
-/

noncomputable section

namespace Erdos240.BakerSourceOversizedConstantUniform

open Erdos240
open BakerLemma3Concrete
open BakerLemma3Instantiation
open BakerSourceAssemblyIndependent
open BakerSourceNumericalAssemblyIndependent
open BakerSourceOversizedConstantNumerics
open BakerSourceState

/-- For a fixed old family, an arbitrarily prescribed fixed lower bound can
be imposed together with all source-row and normalized-jet requirements.
The choice is uniform in the varying prime, cutoff, and induction level. -/
theorem exists_uniform_oversizedConstant_ge {oldRank : ℕ}
    [Nonempty (Fin oldRank)]
    (old : Fin oldRank → ℕ) (oldPrime : ∀ i, (old i).Prime)
    (oldInjective : Function.Injective old) (A : ℝ) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ A ≤ C₀ ∧
      ∀ (newPrime : ℕ) (newPrimePrime : newPrime.Prime)
        (newFresh : ∀ i, old i ≠ newPrime)
        (N : ℕ) (Nlarge : Real.exp 2 ≤ (N : ℝ)),
        let P := sourceParameters old oldPrime oldInjective newPrime
          newPrimePrime newFresh N Nlarge
        4 * P.C ≤ C₀ ∧
          jetAbsorptionConstant P ≤ C₀ ∧
          8 ≤ sourceExponent P (C₀ * Real.log P.OmegaOld) := by
  classical
  let oldMax : ℕ := Finset.univ.sup old
  obtain ⟨referencePrime, hreferencePrime, referencePrime_prime⟩ :=
    Nat.exists_infinite_primes (oldMax + 1)
  have referencePrime_fresh : ∀ i, old i ≠ referencePrime := by
    intro i
    have holdMax : old i ≤ oldMax := by
      exact Finset.le_sup (f := old) (Finset.mem_univ i)
    have holdLt : old i < referencePrime := by omega
    exact ne_of_lt holdLt
  let referenceBound : ℕ := ⌈Real.exp 2⌉₊
  have referenceBound_large : Real.exp 2 ≤ (referenceBound : ℝ) := by
    exact Nat.le_ceil (Real.exp 2)
  let P₀ := sourceParameters old oldPrime oldInjective referencePrime
    referencePrime_prime referencePrime_fresh referenceBound
      referenceBound_large
  let C₀ : ℝ := max A (max (4 * P₀.C) (jetAbsorptionConstant P₀)) + 1
  have hP₀C : 0 < P₀.C := P₀.C_pos
  have hC₀ : 0 < C₀ := by
    dsimp only [C₀]
    have hmax : 4 * P₀.C ≤
        max A (max (4 * P₀.C) (jetAbsorptionConstant P₀)) :=
      (le_max_left (4 * P₀.C) (jetAbsorptionConstant P₀)).trans
        (le_max_right A (max (4 * P₀.C) (jetAbsorptionConstant P₀)))
    linarith
  refine ⟨C₀, hC₀, ?_, ?_⟩
  · exact (le_max_left A _).trans (le_add_of_nonneg_right (by norm_num))
  · intro newPrime newPrimePrime newFresh N Nlarge
    let P := sourceParameters old oldPrime oldInjective newPrime
      newPrimePrime newFresh N Nlarge
    have hk : P.k = P₀.k := by
      exact sourceParameters_k_eq old oldPrime oldInjective newPrime
        newPrimePrime newFresh N Nlarge old oldPrime oldInjective
        referencePrime referencePrime_prime referencePrime_fresh referenceBound
        referenceBound_large
    have hCeq : P.C = P₀.C := by
      exact sourceParameters_C_eq old oldPrime oldInjective newPrime
        newPrimePrime newFresh N Nlarge old oldPrime oldInjective
        referencePrime referencePrime_prime referencePrime_fresh referenceBound
        referenceBound_large
    have hold : P.old = old := rfl
    have hold₀ : P₀.old = old := rfl
    have hjet : jetAbsorptionConstant P = jetAbsorptionConstant P₀ := by
      unfold jetAbsorptionConstant oldJetFactor BakerSourceState.oldLog
      rw [hk, hold, hold₀]
    have hstruct0 : 4 * P₀.C ≤ C₀ := by
      dsimp only [C₀]
      exact (le_max_left (4 * P₀.C) (jetAbsorptionConstant P₀)).trans
        ((le_max_right A (max (4 * P₀.C)
          (jetAbsorptionConstant P₀))).trans
            (le_add_of_nonneg_right (by norm_num)))
    have hjet0 : jetAbsorptionConstant P₀ ≤ C₀ := by
      dsimp only [C₀]
      exact (le_max_right (4 * P₀.C) (jetAbsorptionConstant P₀)).trans
        ((le_max_right A (max (4 * P₀.C)
          (jetAbsorptionConstant P₀))).trans
            (le_add_of_nonneg_right (by norm_num)))
    have hstruct : 4 * P.C ≤ C₀ := by simpa only [hCeq] using hstruct0
    have hjetP : jetAbsorptionConstant P ≤ C₀ := by
      simpa only [hjet] using hjet0
    refine ⟨hstruct, hjetP, ?_⟩
    have hmono := sourceExponent_mono_normalized P hstruct
    rw [sourceExponent_four_mul] at hmono
    linarith [four_le_normalizedSourceExponent P]

/-! ## Direct entry into the rational-grid lower-bound interface -/

/-- A product upper bound is the multiplicative form of the exact rational
Liouville comparison.  It avoids taking logarithms of the automatically
constructed conjugate bound and common Delta denominator. -/
theorem exp_neg_three_quarters_le_stateRationalLiouvilleThreshold
    {oldRank : ℕ} (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (l : ℕ) (m : VDPLMultiIndex (oldRank + 1)) (E : ℝ)
    (hproduct :
      2 *
          (rationalTargetConjugateBound P (coordinatesForState state)
              state.support state.coeff P.h P.LzeroPlusOne b bLast J l m ^
            (13 ^ (oldRank + 1) - 1)) *
          ‖(commonDeltaDenominator P.h P.LzeroPlusOne
            (P.q ^ (J + 1)) m : ℂ)‖ ≤
        Real.exp (3 * E / 4)) :
    Real.exp (-3 * E / 4) ≤
      stateRationalLiouvilleThreshold P J state b bLast l m := by
  let H : ℝ := rationalTargetConjugateBound P (coordinatesForState state)
    state.support state.coeff P.h P.LzeroPlusOne b bLast J l m
  let D : ℝ := ‖(commonDeltaDenominator P.h P.LzeroPlusOne
    (P.q ^ (J + 1)) m : ℂ)‖
  let d : ℕ := 13 ^ (oldRank + 1) - 1
  have hH : 0 < H := by
    dsimp only [H]
    exact rationalTargetConjugateBound_pos P (coordinatesForState state)
      state.support state.coeff P.h P.LzeroPlusOne b bLast J l m
  have hHpow : 0 < H ^ d := pow_pos hH d
  have hq : P.q ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt P.one_lt_q)
  have hD : 0 < D := by
    dsimp only [D]
    rw [norm_pos_iff]
    exact_mod_cast commonDeltaDenominator_ne_zero P.h P.LzeroPlusOne
      (P.q ^ (J + 1)) (pow_ne_zero (J + 1) hq) m
  have hden : 0 < 2 * H ^ d * D := by positivity
  have hinv : 1 / Real.exp (3 * E / 4) ≤ 1 / (2 * H ^ d * D) :=
    one_div_le_one_div_of_le hden (by simpa only [H, D, d] using hproduct)
  change Real.exp (-3 * E / 4) ≤ (H ^ d)⁻¹ / D / 2
  calc
    Real.exp (-3 * E / 4) = 1 / Real.exp (3 * E / 4) := by
      rw [one_div, ← Real.exp_neg]
      congr 1
      ring
    _ ≤ 1 / (2 * H ^ d * D) := hinv
    _ = (H ^ d)⁻¹ / D / 2 := by
      field_simp

/-- Build all rational-grid Lemma-3 inputs from quarter-scale estimates at
the literal source constant `P.C` after replacing it by one oversized
constant `C₀`.  The comparison error then has the stronger envelope
`exp (-3 E / 4)`, where `E` is the enlarged source exponent.

This formulation is useful because the growth and amplification estimates
do not have to be reproved at the larger constant: monotonicity supplies the
needed sixteenth-scale bounds.  Thus the only arithmetic comparison left in
`henvelope` is the strong exponential envelope against the exact Liouville
threshold. -/
def rationalLowerInputsOfOversized {oldRank : ℕ}
    [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (C₀ : ℝ)
    (hstruct : 4 * P.C ≤ C₀)
    (hE : 8 ≤ sourceExponent P (C₀ * Real.log P.OmegaOld))
    (hbLast : bLast ≠ 0)
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm P.old P.newPrime b bLast| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ))))
    (hgrowth : ∀ l, 1 ≤ l → l ≤ P.R (J + 1) →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep J →
        (stateSourceMajorants P state b bLast ((l : ℂ) / (P.q : ℂ))
          (toSourceMultiIndex P m)).growth ≤
          Real.exp
            (sourceExponent P (P.C * Real.log P.OmegaOld) / 4))
    (hamplification : ∀ l, 1 ≤ l → l ≤ P.R (J + 1) →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep J →
        (stateSourceMajorants P state b bLast ((l : ℂ) / (P.q : ℂ))
          (toSourceMultiIndex P m)).amplificationMajorant ≤
          Real.exp
            (sourceExponent P (P.C * Real.log P.OmegaOld) / 4))
    (henvelope : ∀ l, 1 ≤ l → l ≤ P.R (J + 1) →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep J →
        Real.exp
            (-3 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 4) ≤
          stateRationalLiouvilleThreshold P J state b bLast l
            (toSourceMultiIndex P m)) :
    RationalLowerInputs P state b bLast := by
  have hC₀ : 0 < C₀ :=
    lt_of_lt_of_le (mul_pos (by norm_num) P.C_pos) hstruct
  exact RationalLowerInputs.ofNormalizedDirectError C₀ hC₀ hbLast hsmall
    (fun l hl hlR m hm ↦
      (error_le_exp_neg_three_quarters_of_oversized
        (stateSourceMajorants P state b bLast ((l : ℂ) / (P.q : ℂ))
          (toSourceMultiIndex P m)) hstruct hE
        (hgrowth l hl hlR m hm) (hamplification l hl hlR m hm)).trans
          (henvelope l hl hlR m hm))

/-- Product-bound specialization of `rationalLowerInputsOfOversized`.
The final hypothesis is an upper bound for exactly the two positive factors
that occur in the rational Liouville certificate. -/
def rationalLowerInputsOfOversizedProduct {oldRank : ℕ}
    [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (C₀ : ℝ)
    (hstruct : 4 * P.C ≤ C₀)
    (hE : 8 ≤ sourceExponent P (C₀ * Real.log P.OmegaOld))
    (hbLast : bLast ≠ 0)
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm P.old P.newPrime b bLast| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ))))
    (hgrowth : ∀ l, 1 ≤ l → l ≤ P.R (J + 1) →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep J →
        (stateSourceMajorants P state b bLast ((l : ℂ) / (P.q : ℂ))
          (toSourceMultiIndex P m)).growth ≤
          Real.exp
            (sourceExponent P (P.C * Real.log P.OmegaOld) / 4))
    (hamplification : ∀ l, 1 ≤ l → l ≤ P.R (J + 1) →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep J →
        (stateSourceMajorants P state b bLast ((l : ℂ) / (P.q : ℂ))
          (toSourceMultiIndex P m)).amplificationMajorant ≤
          Real.exp
            (sourceExponent P (P.C * Real.log P.OmegaOld) / 4))
    (hproduct : ∀ l, 1 ≤ l → l ≤ P.R (J + 1) →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep J →
        2 *
            (rationalTargetConjugateBound P (coordinatesForState state)
                state.support state.coeff P.h P.LzeroPlusOne b bLast J l
                  (toSourceMultiIndex P m) ^
              (13 ^ (oldRank + 1) - 1)) *
            ‖(commonDeltaDenominator P.h P.LzeroPlusOne
              (P.q ^ (J + 1)) (toSourceMultiIndex P m) : ℂ)‖ ≤
          Real.exp
            (3 * sourceExponent P
              (C₀ * Real.log P.OmegaOld) / 4)) :
    RationalLowerInputs P state b bLast :=
  rationalLowerInputsOfOversized state b bLast C₀ hstruct hE hbLast hsmall
    hgrowth hamplification fun l hl hlR m hm ↦
      exp_neg_three_quarters_le_stateRationalLiouvilleThreshold
        P state b bLast l (toSourceMultiIndex P m)
        (sourceExponent P (C₀ * Real.log P.OmegaOld))
        (hproduct l hl hlR m hm)

end Erdos240.BakerSourceOversizedConstantUniform

#print axioms Erdos240.BakerSourceOversizedConstantUniform.exists_uniform_oversizedConstant_ge
#print axioms Erdos240.BakerSourceOversizedConstantUniform.rationalLowerInputsOfOversized
#print axioms Erdos240.BakerSourceOversizedConstantUniform.exp_neg_three_quarters_le_stateRationalLiouvilleThreshold
#print axioms Erdos240.BakerSourceOversizedConstantUniform.rationalLowerInputsOfOversizedProduct
