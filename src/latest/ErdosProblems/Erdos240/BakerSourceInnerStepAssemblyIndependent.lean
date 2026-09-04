/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerLemma4InnerInduction
import ErdosProblems.Erdos240.BakerLemma4LocalResidues
import ErdosProblems.Erdos240.BakerSourceBudgetInequalities
import ErdosProblems.Erdos240.BakerSourceAlgebraicMomentBounds
import ErdosProblems.Erdos240.BakerSourceMomentCancellation
import ErdosProblems.Erdos240.BakerSourceOversizedConstantNumerics

/-!
# Exact source Lemma-4 stage assembly

This module contains only the logical and radius bookkeeping needed to turn
the pointwise local-circle conclusion at one inner stage into the bounded
`InnerStepCallback` consumed by the source continuation.  In particular, it
does not use the obsolete global Hasse-matrix estimate: the analytic input is
the pointwise conclusion which the factorial-cancelled local-circle argument
must prove.
-/

noncomputable section

namespace Erdos240.BakerSourceInnerStepAssemblyIndependent

open Erdos240
open Erdos240.BakerInduction
open Erdos240.BakerLemma4InnerInduction
open Erdos240.BakerLemma3
open Erdos240.BakerLemma3Concrete
open Erdos240.BakerLemma3Instantiation
open Erdos240.BakerLemma4Concrete
open Erdos240.BakerSourceLogFormNormalization
open Erdos240.BakerSourceAlgebraicMomentBounds
open Erdos240.BakerSourceMomentCancellation
open Erdos240.BakerSourceOversizedConstantNumerics
open Erdos240.BakerSourceState
open Erdos240.HermiteInterpolation
open Erdos240.InterpolationProducts

variable {ι : Type*} [Fintype ι]

/-- The real radii in source Lemma 4 are nondecreasing in the inner stage. -/
theorem lemmaFourRadiusScale_mono (P : VDPLParameters ι) (N : ℕ)
    {s t : ℕ} (hst : s ≤ t) :
    P.lemmaFourRadiusScale N s ≤ P.lemmaFourRadiusScale N t := by
  have hexponent : P.epsilon * (s : ℝ) ≤ P.epsilon * (t : ℝ) := by
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hst) P.epsilon_pos.le
  have hrpow : P.k ^ (P.epsilon * (s : ℝ)) ≤
      P.k ^ (P.epsilon * (t : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le P.one_le_k hexponent
  unfold VDPLParameters.lemmaFourRadiusScale
  gcongr

/-- Successive real radii differ by the literal source factor
`k ^ epsilon`. -/
theorem lemmaFourRadiusScale_succ (P : VDPLParameters ι) (N t : ℕ) :
    P.lemmaFourRadiusScale N (t + 1) =
      P.lemmaFourRadiusScale N t * P.k ^ P.epsilon := by
  unfold VDPLParameters.lemmaFourRadiusScale
  have hexponent : P.epsilon * ((t + 1 : ℕ) : ℝ) =
      P.epsilon * (t : ℝ) + P.epsilon := by
    push_cast
    ring
  rw [hexponent, Real.rpow_add P.k_pos]
  ring

/-- Flooring preserves the monotonicity of the source radii. -/
theorem lemmaFourRadius_mono (P : VDPLParameters ι) (N : ℕ)
    {s t : ℕ} (hst : s ≤ t) :
    P.lemmaFourRadius N s ≤ P.lemmaFourRadius N t := by
  unfold VDPLParameters.lemmaFourRadius
  exact Nat.floor_mono (lemmaFourRadiusScale_mono P N hst)

/-- Every integral radius occurring in source Lemma 4 is nonzero. -/
theorem lemmaFourRadius_pos [Nonempty ι]
    (P : VDPLParameters ι) (N t : ℕ) :
    0 < P.lemmaFourRadius N t := by
  have hbase : P.R N ≤ P.lemmaFourRadius N t := by
    simpa only [P.lemmaFourRadius_zero] using
      lemmaFourRadius_mono P N (Nat.zero_le t)
  exact (P.R_pos N).trans_le hbase

/-- The source radii grow strictly at every inner step.  This is the exact
separation needed when the local-circle proof splits old nodes from newly
added targets. -/
theorem lemmaFourRadius_lt_succ [Nonempty ι]
    (P : VDPLParameters ι) (N t : ℕ) :
    P.lemmaFourRadius N t < P.lemmaFourRadius N (t + 1) := by
  let x := P.lemmaFourRadiusScale N t
  let y := P.lemmaFourRadiusScale N (t + 1)
  have hx16 : (16 : ℝ) ≤ x := by
    dsimp only [x, VDPLParameters.lemmaFourRadiusScale]
    have hqpow : (1 : ℝ) ≤ (P.q ^ N : ℕ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (pow_ne_zero N (Nat.ne_of_gt (Nat.zero_lt_of_lt P.one_lt_q)))
    have hh : (1 : ℝ) ≤ P.h := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr P.h_pos.ne')
    have hrpow : (1 : ℝ) ≤ P.k ^ (P.epsilon * (t : ℝ)) := by
      exact Real.one_le_rpow P.one_le_k
        (mul_nonneg P.epsilon_pos.le (Nat.cast_nonneg t))
    calc
      (16 : ℝ) = 16 * 1 * 1 * 1 := by norm_num
      _ ≤ 16 * (P.q ^ N : ℕ) * P.h *
          P.k ^ (P.epsilon * (t : ℝ)) := by gcongr
  have hfactor : (13 : ℝ) < P.k ^ P.epsilon := by
    have h := P.q_lt_k_rpow_epsilon
    norm_num [VDPLParameters.q] at h ⊢
    exact h
  have hy : y = x * P.k ^ P.epsilon := by
    exact lemmaFourRadiusScale_succ P N t
  have hgap : x + 1 < y := by
    rw [hy]
    nlinarith [mul_lt_mul_of_pos_left hfactor (by positivity : 0 < x)]
  apply Nat.lt_iff_add_one_le.mpr
  unfold VDPLParameters.lemmaFourRadius
  apply Nat.le_floor
  have hfloor : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x :=
    Nat.floor_le (P.lemmaFourRadiusScale_pos N t).le
  have hcast : ((⌊x⌋₊ : ℕ) : ℝ) + 1 ≤ y := by
    linarith
  simpa only [Nat.cast_add, Nat.cast_one] using hcast

/-- Equations (7)--(8) at an arbitrary current inner rectangle.  Unlike the
level-seed specialization, this theorem can be applied after every local
circle step, because its radius and budget are the current invariant's
literal values. -/
theorem norm_normalizedIteratedDeriv_f_le_sourceError_of_currentInvariant
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {N R S : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0)
    (hseed : VanishesOn (g state b bLast) 1 R S)
    (C₀ : ℝ)
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm
          P.old P.newPrime b bLast| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ))))
    {l j : ℕ} (hl : 1 ≤ l) (hlR : l ≤ R)
    (m : VDPLMultiIndex P.rank)
    (hmj : VDPLMultiIndex.weight m + j ≤ S) :
    ‖iteratedDeriv j (fun w ↦ f state b bLast w m) (l : ℂ) /
        (j.factorial : ℂ)‖ ≤
      jetErrorIterate P N bLast j
          (sourceRowError P state b bLast (l : ℂ)
            (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)))
          (toSourceMultiIndex P m) /
        ‖(j.factorial : ℂ)‖ := by
  apply norm_normalizedIteratedDeriv_f_le_jetErrorIterate_of_vanishesOn
    state b hbLast hseed
    (sourceRowError P state b bLast (l : ℂ)
      (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)))
  · intro m'
    exact sourceRowError_nonneg P state b bLast (l : ℂ)
      (by unfold smallLinearFormBound; positivity) m'
  · exact hl
  · exact hlR
  · intro m' _hm'
    have hform := norm_logForm_le_smallLinearFormBound_of_normalized
      P C₀ b bLast hsmall
    have hcomparison :=
      (stateSourceMajorants P state b bLast (l : ℂ) m').norm_vdplG_sub_vdplF_le_error
        (lastLog P) hbLast (by unfold smallLinearFormBound; positivity) hform
    change
      ‖gSource state b bLast (l : ℂ) m' -
          fSource state b bLast (l : ℂ) m'‖ ≤
        sourceRowError P state b bLast (l : ℂ)
          (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)) m'
      at hcomparison
    simpa only [norm_sub_rev] using hcomparison
  · exact hmj

/-- The sharp equations-(7)--(8) endpoint at an arbitrary current inner
rectangle.  The comparison rows are assumed at the full level seed budget,
as required by the source recurrence; factorial cancellation and absorption
then turn the pointwise `exp (-3E/4)` error into the normalized
`exp (-2E/3)` jet bound used by the local-circle step. -/
theorem norm_normalizedIteratedDeriv_f_le_exp_neg_two_thirds_of_currentInvariant
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {N R S : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0)
    (hseed : VanishesOn (g state b bLast) 1 R S)
    (C₀ : ℝ)
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm
          P.old P.newPrime b bLast| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ))))
    (hC : jetAbsorptionConstant P ≤ C₀)
    {l j : ℕ} (hl : 1 ≤ l) (hlR : l ≤ R)
    (hrow : ∀ m' : VDPLMultiIndex (oldRank + 1),
      VDPLMultiIndex.weight m' ≤ P.Slevel N →
        sourceRowError P state b bLast (l : ℂ)
            (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)) m' ≤
          Real.exp
            (-3 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 4))
    (m : VDPLMultiIndex P.rank)
    (hmj : VDPLMultiIndex.weight m + j ≤ S)
    (hS : S ≤ P.Slevel N) :
    ‖iteratedDeriv j (fun w ↦ f state b bLast w m) (l : ℂ) /
        (j.factorial : ℂ)‖ ≤
      Real.exp
        (-2 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 3) := by
  have hjet :=
    norm_normalizedIteratedDeriv_f_le_sourceError_of_currentInvariant
      state b hbLast hseed C₀ hsmall hl hlR m hmj
  refine hjet.trans ?_
  apply jetErrorIterate_div_factorial_le_exp_neg_two_thirds
    P N bLast hbLast j
      (sourceRowError P state b bLast (l : ℂ)
        (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)))
  · intro m'
    exact sourceRowError_nonneg P state b bLast (l : ℂ)
      (by unfold smallLinearFormBound; positivity) m'
  · exact hC
  · exact hrow
  · simpa only [weight_toSourceMultiIndex] using hmj.trans hS

/-- The current-rectangle jet estimate with the source-faithful algebraic
base function.  This is the no-coefficient-dominance version of equations
(7)--(8): the comparison error is measured relative to `g`, so large ratios
between the logarithmic-form coefficients never enter the growth term. -/
theorem norm_normalizedIteratedDeriv_f_le_algebraicError_of_currentInvariant
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {N R S : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0)
    (hseed : VanishesOn (g state b bLast) 1 R S)
    (C₀ : ℝ)
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm
          P.old P.newPrime b bLast| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ))))
    {l j : ℕ} (hl : 1 ≤ l) (hlR : l ≤ R)
    (m : VDPLMultiIndex P.rank)
    (hmj : VDPLMultiIndex.weight m + j ≤ S) :
    ‖iteratedDeriv j (fun w ↦ f state b bLast w m) (l : ℂ) /
        (j.factorial : ℂ)‖ ≤
      jetErrorIterate P N bLast j
          (levelAlgebraicSourceRowError P state b bLast (l : ℂ)
            (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)))
          (toSourceMultiIndex P m) /
        ‖(j.factorial : ℂ)‖ := by
  apply norm_normalizedIteratedDeriv_f_le_jetErrorIterate_of_vanishesOn
    state b hbLast hseed
    (levelAlgebraicSourceRowError P state b bLast (l : ℂ)
      (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)))
  · intro m'
    exact levelAlgebraicSourceRowError_nonneg P state b bLast (l : ℂ)
      (by unfold smallLinearFormBound; positivity) m'
  · exact hl
  · exact hlR
  · intro m' _hm'
    have hform := norm_logForm_le_smallLinearFormBound_of_normalized
      P C₀ b bLast hsmall
    have hcomparison :=
      norm_gSource_sub_fSource_le_levelAlgebraicSourceRowError
        P state b hbLast (l : ℂ) m'
          (by unfold smallLinearFormBound; positivity) hform
    simpa only [norm_sub_rev] using hcomparison
  · exact hmj

/-- After the fixed-family jet mass is absorbed, a pointwise algebraic
comparison error of size `exp (-3E/4)` gives the normalized `exp (-2E/3)`
jet bound at every current Lemma-4 rectangle. -/
theorem norm_normalizedIteratedDeriv_f_le_exp_neg_two_thirds_algebraic_of_currentInvariant
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {N R S : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0)
    (hseed : VanishesOn (g state b bLast) 1 R S)
    (C₀ : ℝ)
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm
          P.old P.newPrime b bLast| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ))))
    (hC : jetAbsorptionConstant P ≤ C₀)
    {l j : ℕ} (hl : 1 ≤ l) (hlR : l ≤ R)
    (hrow : ∀ m' : VDPLMultiIndex (oldRank + 1),
      VDPLMultiIndex.weight m' ≤ P.Slevel N →
        levelAlgebraicSourceRowError P state b bLast (l : ℂ)
            (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)) m' ≤
          Real.exp
            (-3 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 4))
    (m : VDPLMultiIndex P.rank)
    (hmj : VDPLMultiIndex.weight m + j ≤ S)
    (hS : S ≤ P.Slevel N) :
    ‖iteratedDeriv j (fun w ↦ f state b bLast w m) (l : ℂ) /
        (j.factorial : ℂ)‖ ≤
      Real.exp
        (-2 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 3) := by
  have hjet :=
    norm_normalizedIteratedDeriv_f_le_algebraicError_of_currentInvariant
      state b hbLast hseed C₀ hsmall hl hlR m hmj
  refine hjet.trans ?_
  apply jetErrorIterate_div_factorial_le_exp_neg_two_thirds
    P N bLast hbLast j
      (levelAlgebraicSourceRowError P state b bLast (l : ℂ)
        (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)))
  · intro m'
    exact levelAlgebraicSourceRowError_nonneg P state b bLast (l : ℂ)
      (by unfold smallLinearFormBound; positivity) m'
  · exact hC
  · exact hrow
  · simpa only [weight_toSourceMultiIndex] using hmj.trans hS

/-- The exact source equation-(9) bound for the Hermite polynomial attached
to an arbitrary current inner rectangle.  The interpolation multiplicity
`T` is explicit; in the source application it is the lost budget plus one.
The only contour input is the literal power-of-two estimate proved by the
separate parameter-budget calculation. -/
theorem norm_sourceHermitePolynomial_eval_le_exp_neg_half_of_currentInvariant
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {N R S T l : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0)
    (hseed : VanishesOn (g state b bLast) 1 R S)
    (C₀ : ℝ)
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm
          P.old P.newPrime b bLast| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ))))
    (hC : jetAbsorptionConstant P ≤ C₀)
    (hR : 1 ≤ R) (hT : 1 ≤ T) (hRl : R < l)
    (hcontour :
      (2 : ℝ) ^ (((3 * R + l) * T) + R * T) ≤
        Real.exp
          (sourceExponent P (C₀ * Real.log P.OmegaOld) / 6))
    (hrow : ∀ (i : Fin R) (m' : VDPLMultiIndex (oldRank + 1)),
      VDPLMultiIndex.weight m' ≤ P.Slevel N →
        sourceRowError P state b bLast ((i.1 + 1 : ℕ) : ℂ)
            (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)) m' ≤
          Real.exp
            (-3 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 4))
    (m : VDPLMultiIndex P.rank)
    (hmT : VDPLMultiIndex.weight m + (T - 1) ≤ S)
    (hS : S ≤ P.Slevel N) :
    ‖(polynomial (fun w ↦ f state b bLast w m)
        (integralNodes R T)).eval (l : ℂ)‖ ≤
      Real.exp
        (-sourceExponent P (C₀ * Real.log P.OmegaOld) / 2) := by
  let E := sourceExponent P (C₀ * Real.log P.OmegaOld)
  let delta := Real.exp (-2 * E / 3)
  have hjetPos : 0 < jetAbsorptionConstant P := by
    have hsum : 0 ≤ ∑ r, ‖oldLog P r‖ :=
      Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
    have hold : 0 < oldJetFactor P := by
      unfold oldJetFactor
      nlinarith
    unfold jetAbsorptionConstant
    exact mul_pos (mul_pos (by norm_num) (by nlinarith [P.k_pos])) hold
  have hC₀ : 0 < C₀ := hjetPos.trans_le hC
  have hE : 0 ≤ E := by
    dsimp only [E]
    unfold sourceExponent
    exact mul_pos
      (mul_pos
        (mul_pos (mul_pos hC₀ P.log_OmegaOld_pos) P.OmegaOld_pos)
          P.log_newHeight_pos)
      (log_Bsrc_pos P) |>.le
  have hsmallDelta : delta ≤ Real.exp (-(2 / 3) * E) := by
    dsimp only [delta]
    apply le_of_eq
    congr 1
    ring
  have hcontourE :
      (2 : ℝ) ^ (((3 * R + l) * T) + R * T) ≤
        Real.exp ((1 / 6) * E) := by
    convert hcontour using 1 <;> dsimp only [E] <;> ring_nf
  have hresult :
      ‖(polynomial (fun w ↦ f state b bLast w m)
          (integralNodes R T)).eval (l : ℂ)‖ ≤
        Real.exp (-(1 / 2) * E) := by
    apply norm_polynomial_eval_le_exp_neg_half_of_local_jets hR hT hRl
      (polynomial (fun w ↦ f state b bLast w m) (integralNodes R T))
      (polynomial_integralNodes_mem_degreeLT
        (fun w ↦ f state b bLast w m) R T)
      hE (Real.exp_pos _).le hsmallDelta hcontourE
    intro i k
    rw [hasseDeriv_eval_eq_iteratedDeriv_div_factorial]
    obtain ⟨after, hsplit⟩ :=
      integralNodes_eq_append_replicate_append (S := T) i
    rw [hsplit]
    rw [iteratedDeriv_eval_polynomial_eq_of_replicate_block
      (differentiable_sourceState_f state b bLast m)
      (integralNodes i.1 T) after ((i.1 + 1 : ℕ) : ℂ) T k.1 k.2]
    apply norm_normalizedIteratedDeriv_f_le_exp_neg_two_thirds_of_currentInvariant
      state b hbLast hseed C₀ hsmall hC
      (show 1 ≤ i.1 + 1 by omega) (show i.1 + 1 ≤ R by omega)
      (hrow i) m
    · have hk : k.1 ≤ T - 1 := by omega
      exact (Nat.add_le_add_left hk _).trans hmT
    · exact hS
  convert hresult using 1 <;> dsimp only [E] <;> ring_nf

/-- The Hermite-polynomial half-exponent bound at the literal `t`th source
Lemma-4 rectangle.  Radius positivity, strict separation of a genuinely new
target, the lost-budget multiplicity, and the full local-circle contour loss
are all discharged from `LevelOK` and the source parameter ledger. -/
theorem norm_sourceHermitePolynomial_eval_le_exp_neg_half_at_innerStage
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {N t : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0) (hN : P.LevelOK N)
    (ht : t < terminalStage P)
    (hcurrent : InnerInvariant P (g state b bLast) N t)
    (C₀ : ℝ)
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm
          P.old P.newPrime b bLast| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ))))
    (hjet : jetAbsorptionConstant P ≤ C₀)
    (hcontourConstant : P.lemmaFourContourAbsorptionConstant ≤ C₀)
    (hrow : ∀
      (i : Fin (P.lemmaFourRadius N t))
      (m' : VDPLMultiIndex (oldRank + 1)),
      VDPLMultiIndex.weight m' ≤ P.Slevel N →
        sourceRowError P state b bLast ((i.1 + 1 : ℕ) : ℂ)
            (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)) m' ≤
          Real.exp
            (-3 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 4))
    {l : ℕ} (hnew : P.lemmaFourRadius N t < l)
    (hl : l ≤ P.lemmaFourRadius N (t + 1))
    (m : VDPLMultiIndex P.rank)
    (hm : VDPLMultiIndex.weight m ≤ P.lemmaFourBudget N (t + 1)) :
    ‖(polynomial (fun w ↦ f state b bLast w m)
        (integralNodes (P.lemmaFourRadius N t)
          (P.lemmaFourBudget N t - P.lemmaFourBudget N (t + 1) + 1))).eval
        (l : ℂ)‖ ≤
      Real.exp
        (-sourceExponent P (C₀ * Real.log P.OmegaOld) / 2) := by
  let R := P.lemmaFourRadius N t
  let T := P.lemmaFourBudget N t - P.lemmaFourBudget N (t + 1) + 1
  have hR : 1 ≤ R := by
    exact Nat.one_le_iff_ne_zero.mpr (lemmaFourRadius_pos P N t).ne'
  have hT : 1 ≤ T := by
    dsimp only [T]
    omega
  have hC₀ : 0 < C₀ := by
    have hsum : 0 ≤ ∑ r, ‖oldLog P r‖ :=
      Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
    have hold : 0 < oldJetFactor P := by
      unfold oldJetFactor
      nlinarith
    have hjetPos : 0 < jetAbsorptionConstant P := by
      unfold jetAbsorptionConstant
      exact mul_pos (mul_pos (by norm_num) (by nlinarith [P.k_pos])) hold
    exact hjetPos.trans_le hjet
  have hconstantHeight :
      P.lemmaFourContourAbsorptionConstant * (P.h : ℝ) ≤
        C₀ * Real.log (P.Bsrc : ℝ) := by
    calc
      P.lemmaFourContourAbsorptionConstant * (P.h : ℝ) ≤
          C₀ * (P.h : ℝ) :=
        mul_le_mul_of_nonneg_right hcontourConstant (Nat.cast_nonneg P.h)
      _ ≤ C₀ * Real.log (P.Bsrc : ℝ) :=
        mul_le_mul_of_nonneg_left P.h_cast_le_log_Bsrc hC₀.le
  have habsorb :
      P.lemmaFourContourAbsorptionConstant * (P.h : ℝ) *
          P.Omega * Real.log P.OmegaOld ≤
        sourceExponent P (C₀ * Real.log P.OmegaOld) := by
    calc
      P.lemmaFourContourAbsorptionConstant * (P.h : ℝ) *
          P.Omega * Real.log P.OmegaOld ≤
        (C₀ * Real.log (P.Bsrc : ℝ)) *
          P.Omega * Real.log P.OmegaOld := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hconstantHeight P.Omega_pos.le)
              P.log_OmegaOld_pos.le
      _ = sourceExponent P (C₀ * Real.log P.OmegaOld) := by
        unfold sourceExponent VDPLParameters.Omega
        ring
  have hcontour :
      (2 : ℝ) ^ (((3 * R + l) * T) + R * T) ≤
        Real.exp
          (sourceExponent P (C₀ * Real.log P.OmegaOld) / 6) := by
    have hlocal := P.lemmaFour_localCircleFactor_le_exp_sixth hN ht hl
    have hexponent :
        (P.lemmaFourContourAbsorptionConstant * (P.h : ℝ) *
            P.Omega * Real.log P.OmegaOld) / 6 ≤
          sourceExponent P (C₀ * Real.log P.OmegaOld) / 6 := by
      linarith
    exact hlocal.trans (Real.exp_le_exp.mpr hexponent)
  apply norm_sourceHermitePolynomial_eval_le_exp_neg_half_of_currentInvariant
    state b hbLast hcurrent C₀ hsmall hjet hR hT hnew hcontour hrow m
  · have hj : T - 1 ≤
        P.lemmaFourBudget N t - P.lemmaFourBudget N (t + 1) := by
      dsimp only [T]
      omega
    exact weight_add_jet_le_currentBudget P N t m (T - 1) hm hj
  · exact P.lemmaFourBudget_le_Slevel N t

/-- Pointwise form of one exact inner source step.

The input deliberately receives the current vanishing rectangle.  Its
conclusion is only the new target value.  All local-circle estimates,
normalized-jet bounds, and the Liouville alternative belong in the proof of
this input; the present theorem performs no analytic weakening. -/
theorem innerInvariant_succ_of_pointwise
    (P : VDPLParameters ι)
    (G : ℂ → VDPLMultiIndex P.rank → ℂ) (N t : ℕ)
    (hpoint : InnerInvariant P G N t →
      ∀ l, 1 ≤ l → l ≤ P.lemmaFourRadius N (t + 1) →
        ∀ m, VDPLMultiIndex.weight m ≤ P.lemmaFourBudget N (t + 1) →
          G (l : ℂ) m = 0) :
    InnerInvariant P G N t → InnerInvariant P G N (t + 1) := by
  intro hcurrent l hl hlR m hm
  simpa only [Nat.cast_one, div_one] using
    hpoint hcurrent l hl hlR m hm

/-- Assemble the full bounded source Lemma-4 callback from its pointwise
local-circle theorem at every genuine inner stage. -/
theorem innerStepCallback_of_pointwise
    (P : VDPLParameters ι)
    (G : ℂ → VDPLMultiIndex P.rank → ℂ) (N : ℕ)
    (hpoint : ∀ t, t < terminalStage P →
      InnerInvariant P G N t →
        ∀ l, 1 ≤ l → l ≤ P.lemmaFourRadius N (t + 1) →
          ∀ m, VDPLMultiIndex.weight m ≤ P.lemmaFourBudget N (t + 1) →
            G (l : ℂ) m = 0) :
    InnerStepCallback P G N := by
  intro t ht
  exact innerInvariant_succ_of_pointwise P G N t (hpoint t ht)

end Erdos240.BakerSourceInnerStepAssemblyIndependent

#print axioms Erdos240.BakerSourceInnerStepAssemblyIndependent.lemmaFourRadius_mono
#print axioms Erdos240.BakerSourceInnerStepAssemblyIndependent.lemmaFourRadius_pos
#print axioms Erdos240.BakerSourceInnerStepAssemblyIndependent.lemmaFourRadius_lt_succ
#print axioms Erdos240.BakerSourceInnerStepAssemblyIndependent.norm_normalizedIteratedDeriv_f_le_sourceError_of_currentInvariant
#print axioms Erdos240.BakerSourceInnerStepAssemblyIndependent.norm_normalizedIteratedDeriv_f_le_exp_neg_two_thirds_of_currentInvariant
#print axioms Erdos240.BakerSourceInnerStepAssemblyIndependent.norm_normalizedIteratedDeriv_f_le_algebraicError_of_currentInvariant
#print axioms Erdos240.BakerSourceInnerStepAssemblyIndependent.norm_normalizedIteratedDeriv_f_le_exp_neg_two_thirds_algebraic_of_currentInvariant
#print axioms Erdos240.BakerSourceInnerStepAssemblyIndependent.norm_sourceHermitePolynomial_eval_le_exp_neg_half_of_currentInvariant
#print axioms Erdos240.BakerSourceInnerStepAssemblyIndependent.norm_sourceHermitePolynomial_eval_le_exp_neg_half_at_innerStage
#print axioms Erdos240.BakerSourceInnerStepAssemblyIndependent.innerStepCallback_of_pointwise
