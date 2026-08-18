/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section4SharpDecayAssembly
import ErdosProblems.Erdos186.CFP.Bilu.Section91GenericSharpProduct

/-!
# Uniform loss for the generic sharp Section 9 product

This module removes the dimension-dependent constants from the generic
sharp-product estimate.  It is deliberately independent of the geometric
construction of the final affine restriction: that construction only has to
bound its output volume by a fixed multiple of the generic product volume.
-/

namespace Erdos186.CFP.Bilu.Section4GenericSharpLoss

open MeasureTheory
open CFP.BiluFreiman
open Proposition75Data Proposition75Case1 Proposition75Construction
open Section4SharpDecayAssembly
open Section7BiasedNumerics Section8Synthesis
open Section8PresentationNormalization
open Section9NormalizedReplacement Section91InitialPresentation
open Section91InitialPresentation.InitialPresentation
open Section91GenericSharpProduct
open Section92PresentationDescent

noncomputable section

set_option autoImplicit false

/-- A real constant bounding all Proposition 7.5 constants up to the
current-presentation rank ceiling. -/
def uniformProposition75RealConstant (rankBound r : ℕ) : ℝ :=
  1 + ∑ m ∈ Finset.range (rankBound + 1),
    (proposition75SourceConstant m r).toReal

theorem proposition75SourceConstant_toReal_lt_uniform
    {m rankBound r : ℕ} (hm : m ≤ rankBound) :
    (proposition75SourceConstant m r).toReal <
      uniformProposition75RealConstant rankBound r := by
  have hterm : (proposition75SourceConstant m r).toReal ≤
      ∑ i ∈ Finset.range (rankBound + 1),
        (proposition75SourceConstant i r).toReal := by
    exact Finset.single_le_sum
      (s := Finset.range (rankBound + 1))
      (f := fun i ↦ (proposition75SourceConstant i r).toReal)
      (fun i _hi ↦ ENNReal.toReal_nonneg)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
  unfold uniformProposition75RealConstant
  linarith

theorem one_le_uniformProposition75RealConstant
    (rankBound r : ℕ) :
    1 ≤ uniformProposition75RealConstant rankBound r := by
  unfold uniformProposition75RealConstant
  have hsum : 0 ≤ ∑ m ∈ Finset.range (rankBound + 1),
      (proposition75SourceConstant m r).toReal := by
    exact Finset.sum_nonneg fun _ _ ↦ ENNReal.toReal_nonneg
  linarith

/-- All operations entering the Proposition 7.5 constant preserve
finiteness. -/
theorem proposition75SourceConstant_ne_top (m r : ℕ) :
    proposition75SourceConstant m r ≠ ⊤ := by
  have hcase1 : case1SourceConstant m r ≠ ⊤ := by
    unfold case1SourceConstant
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num)) (by simp))
      ENNReal.ofReal_ne_top
  have hcase2 : case2SourceConstant m r ≠ ⊤ := by
    apply ne_of_lt
    unfold case2SourceConstant
    rw [Finset.sup_lt_iff (by simp)]
    intro d hd
    rw [Finset.sup_lt_iff (by simp)]
    intro k hk
    unfold case2SourceFactor
    have hnorm : ((‖(2 : ℝ)⁻¹‖₊ : ENNReal) ^ (d + k)) ≠ 0 := by
      norm_num
    have hden : (d.factorial : ENNReal) *
        ENNReal.ofReal ((((m : ℝ) + 1)⁻¹) ^ k) ≠ 0 := by
      positivity
    apply ENNReal.mul_lt_top
    · apply ENNReal.mul_lt_top
      · exact (ENNReal.inv_ne_top.mpr (by norm_num)).lt_top
      · apply ENNReal.mul_lt_top
        · apply ENNReal.mul_lt_top
          · exact (ENNReal.inv_ne_top.mpr hnorm).lt_top
          · exact (ENNReal.pow_ne_top (by norm_num)).lt_top
        · apply ENNReal.mul_lt_top
          · exact (ENNReal.inv_ne_top.mpr hden).lt_top
          · simp
    · exact ENNReal.ofReal_lt_top
  unfold proposition75SourceConstant
  exact (max_lt hcase1.lt_top hcase2.lt_top).ne

/-- The rank-dilation factor `m^m` is monotone under a positive natural
rank ceiling. -/
theorem self_pow_le_self_pow_of_le
    {m rankBound : ℕ} (hrankBound : 1 ≤ rankBound)
    (hm : m ≤ rankBound) :
    (m : ℝ) ^ m ≤ (rankBound : ℝ) ^ rankBound := by
  have hbase : (m : ℝ) ≤ rankBound := by exact_mod_cast hm
  have hfirst : (m : ℝ) ^ m ≤ (rankBound : ℝ) ^ m :=
    pow_le_pow_left₀ (by positivity) hbase m
  have hceiling : (1 : ℝ) ≤ rankBound := by exact_mod_cast hrankBound
  exact hfirst.trans (pow_le_pow_right₀ hceiling hm)

/-- The ENNReal scale used by Proposition 7.5 is finite and has the
expected real value. -/
theorem proposition83Scale_ne_top
    {epsilon exponent : ℝ} (hepsilon : 0 < epsilon) :
    (ENNReal.ofReal (epsilon ^ exponent))⁻¹ ≠ ⊤ := by
  rw [ENNReal.inv_ne_top]
  exact ENNReal.ofReal_ne_zero_iff.mpr
    (Real.rpow_pos_of_pos hepsilon exponent)

theorem proposition83Scale_toReal
    {epsilon exponent : ℝ} (hepsilon : 0 < epsilon) :
    ((ENNReal.ofReal (epsilon ^ exponent))⁻¹).toReal =
      (epsilon ^ exponent)⁻¹ := by
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal]
  exact Real.rpow_nonneg hepsilon.le exponent

/-- One uniform real loss simultaneously absorbs the generic product
dimension, Proposition 7.5's dimension constant, Mahler normalization, and
the subsequent affine-section loss. -/
def genericSharpUniformLoss
    (affineLoss : ℝ) (sharpRankBound rankBound r : ℕ) : ℝ :=
  affineLoss * (2 : ℝ) ^ sharpRankBound *
    uniformProposition75RealConstant rankBound r *
      (rankBound : ℝ) ^ rankBound

theorem genericSharpUniformLoss_pos
    {affineLoss : ℝ} (haffineLoss : 0 < affineLoss)
    {sharpRankBound rankBound r : ℕ} (hrankBound : 1 ≤ rankBound) :
    0 < genericSharpUniformLoss affineLoss sharpRankBound rankBound r := by
  unfold genericSharpUniformLoss
  have huniform : 0 < uniformProposition75RealConstant rankBound r :=
    zero_lt_one.trans_le
      (one_le_uniformProposition75RealConstant rankBound r)
  have hrankReal : (0 : ℝ) < rankBound := by exact_mod_cast hrankBound
  positivity

/-- The terminal uniform estimate.  The geometric Section 9.3 adapter only
has to provide `hsection`; all remaining factors are absorbed here. -/
theorem bodyVolume_le_genericSharpUniformLoss
    {A : Finset ℤ} (X : RankedBodyPresentation A)
    {r : ℕ} {a : Fin r → EuclideanSpace ℝ (Fin X.1)}
    {D : GeometricData (normalizedEuclideanBody X) a}
    {coverConstant sigma : ℕ}
    {epsilon exponent affineLoss : ℝ}
    (N : CoveredNormalizedReplacement (D := D)
      (K := normalizedLiftSet X) (coverConstant := coverConstant)
      (proposition75SourceConstant X.1 r)
      (ENNReal.ofReal (epsilon ^ exponent))⁻¹ sigma)
    (S : GenericSharpSectionData X N)
    (hcard : 1 < A.card)
    {Z : RankedBodyPresentation A}
    {sharpRankBound rankBound : ℕ}
    (hNrank : initialRank N ≤ sharpRankBound)
    (hXrank : X.1 ≤ rankBound)
    (hrankBound : 1 ≤ rankBound)
    (hepsilon : 0 < epsilon)
    (haffineLoss : 0 ≤ affineLoss)
    (hsection : bodyVolume Z ≤ affineLoss *
      bodyVolume (rankedGenericSharpBodyPresentation X N S hcard)) :
    bodyVolume Z ≤
      genericSharpUniformLoss affineLoss sharpRankBound rankBound r *
        bodyVolume X * (epsilon ^ exponent)⁻¹ := by
  let Y := rankedGenericSharpBodyPresentation X N S hcard
  have hconstant := proposition75SourceConstant_ne_top X.1 r
  have hscale : (ENNReal.ofReal (epsilon ^ exponent))⁻¹ ≠ ⊤ :=
    proposition83Scale_ne_top (exponent := exponent) hepsilon
  have hY := bodyVolume_rankedGenericSharpBodyPresentation_le_oldBody
    X N S hcard hconstant hscale
  have htwo : (2 : ℝ) ^ initialRank N ≤ 2 ^ sharpRankBound :=
    pow_le_pow_right₀ (by norm_num) hNrank
  have hconstantReal :
      (proposition75SourceConstant X.1 r).toReal ≤
        uniformProposition75RealConstant rankBound r :=
    (proposition75SourceConstant_toReal_lt_uniform hXrank).le
  have hrankPow := self_pow_le_self_pow_of_le hrankBound hXrank
  have hscaleReal :
      ((ENNReal.ofReal (epsilon ^ exponent))⁻¹).toReal =
        (epsilon ^ exponent)⁻¹ :=
    proposition83Scale_toReal hepsilon
  rw [hscaleReal] at hY
  calc
    bodyVolume Z ≤ affineLoss * bodyVolume Y := hsection
    _ ≤ affineLoss *
        ((2 : ℝ) ^ initialRank N *
          ((proposition75SourceConstant X.1 r).toReal *
            ((X.1 : ℝ) ^ X.1 * bodyVolume X) *
              (epsilon ^ exponent)⁻¹)) := by
      exact mul_le_mul_of_nonneg_left hY haffineLoss
    _ ≤ affineLoss *
        ((2 : ℝ) ^ sharpRankBound *
          (uniformProposition75RealConstant rankBound r *
            ((rankBound : ℝ) ^ rankBound * bodyVolume X) *
              (epsilon ^ exponent)⁻¹)) := by
      have hbody : 0 ≤ bodyVolume X := (bodyVolume_pos X).le
      have hscaleNonneg : 0 ≤ (epsilon ^ exponent)⁻¹ := by
        positivity
      have huniformNonneg :
          0 ≤ uniformProposition75RealConstant rankBound r :=
        (one_le_uniformProposition75RealConstant rankBound r).trans'
          zero_le_one
      gcongr
    _ = genericSharpUniformLoss affineLoss sharpRankBound rankBound r *
        bodyVolume X * (epsilon ^ exponent)⁻¹ := by
      unfold genericSharpUniformLoss
      ring

end

end Erdos186.CFP.Bilu.Section4GenericSharpLoss

#print axioms
  Erdos186.CFP.Bilu.Section4GenericSharpLoss.proposition75SourceConstant_ne_top
#print axioms
  Erdos186.CFP.Bilu.Section4GenericSharpLoss.bodyVolume_le_genericSharpUniformLoss
