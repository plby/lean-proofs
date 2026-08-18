/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section93NormalizedAffineVolume

/-!
# A uniform loss for the normalized affine restriction

The central-section estimate has a factor depending only on the ambient
rank and the two complementary dimensions.  A finite sum supplies one
strictly positive real constant which dominates every such factor below a
fixed ambient-rank ceiling.  The same term with codimension zero also
contains the exact normalized product-volume loss.
-/

namespace Erdos186.CFP.Bilu.Section93UniformAffineLoss

open scoped ENNReal
open Set MeasureTheory Module Submodule
open CFP.BiluFreiman
open Section8PresentationNormalization Section92PresentationDescent
open Section93HomogeneousAffineSpan Section93HomogeneousProductBody
open Section93NormalizedAffineBodyPresentation
open Section93NormalizedAffineVolume

noncomputable section

set_option autoImplicit false

/-- The real loss in dimension `n`, section dimension `d`, and complementary
dimension `k`, including the normalized Mahler product-volume factor. -/
def affineRestrictionRealFactor (n d k : ℕ) : ℝ :=
  ENNReal.toReal
      ((((d.factorial : ENNReal) *
        ENNReal.ofReal ((((n : ℝ) + 1)⁻¹ ^ k)))⁻¹) *
        ((d + k).factorial : ENNReal)) *
    (2 * (n : ℝ) ^ n)

theorem affineRestrictionRealFactor_nonneg (n d k : ℕ) :
    0 ≤ affineRestrictionRealFactor n d k := by
  unfold affineRestrictionRealFactor
  positivity

/-- A single loss dominating all affine restrictions whose old rank is at
most `rankBound`. -/
def normalizedAffineUniformLoss (rankBound : ℕ) : ℝ :=
  1 + ∑ n ∈ Finset.range (rankBound + 1),
    ∑ d ∈ Finset.range (rankBound + 2),
      ∑ k ∈ Finset.range (rankBound + 2),
        affineRestrictionRealFactor n d k

theorem normalizedAffineUniformLoss_pos (rankBound : ℕ) :
    0 < normalizedAffineUniformLoss rankBound := by
  unfold normalizedAffineUniformLoss
  have hsum : 0 ≤ ∑ n ∈ Finset.range (rankBound + 1),
      ∑ d ∈ Finset.range (rankBound + 2),
        ∑ k ∈ Finset.range (rankBound + 2),
          affineRestrictionRealFactor n d k := by
    exact Finset.sum_nonneg fun n _ ↦ Finset.sum_nonneg fun d _ ↦
      Finset.sum_nonneg fun k _ ↦ affineRestrictionRealFactor_nonneg n d k
  linarith

theorem affineRestrictionRealFactor_lt_uniform
    {n d k rankBound : ℕ} (hn : n ≤ rankBound)
    (hd : d ≤ n + 1) (hk : k ≤ n + 1) :
    affineRestrictionRealFactor n d k <
      normalizedAffineUniformLoss rankBound := by
  have hnmem : n ∈ Finset.range (rankBound + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hn)
  have hdmem : d ∈ Finset.range (rankBound + 2) := by
    apply Finset.mem_range.mpr
    omega
  have hkmem : k ∈ Finset.range (rankBound + 2) := by
    apply Finset.mem_range.mpr
    omega
  have hkSum : affineRestrictionRealFactor n d k ≤
      ∑ k' ∈ Finset.range (rankBound + 2),
        affineRestrictionRealFactor n d k' := by
    exact Finset.single_le_sum
      (fun k' _ ↦ affineRestrictionRealFactor_nonneg n d k') hkmem
  have hdSum :
      (∑ k' ∈ Finset.range (rankBound + 2),
          affineRestrictionRealFactor n d k') ≤
        ∑ d' ∈ Finset.range (rankBound + 2),
          ∑ k' ∈ Finset.range (rankBound + 2),
            affineRestrictionRealFactor n d' k' := by
    exact Finset.single_le_sum
      (fun d' _ ↦ Finset.sum_nonneg fun k' _ ↦
        affineRestrictionRealFactor_nonneg n d' k') hdmem
  have hnSum :
      (∑ d' ∈ Finset.range (rankBound + 2),
          ∑ k' ∈ Finset.range (rankBound + 2),
            affineRestrictionRealFactor n d' k') ≤
        ∑ n' ∈ Finset.range (rankBound + 1),
          ∑ d' ∈ Finset.range (rankBound + 2),
            ∑ k' ∈ Finset.range (rankBound + 2),
              affineRestrictionRealFactor n' d' k' := by
    exact Finset.single_le_sum
      (fun n' _ ↦ Finset.sum_nonneg fun d' _ ↦
        Finset.sum_nonneg fun k' _ ↦
          affineRestrictionRealFactor_nonneg n' d' k') hnmem
  unfold normalizedAffineUniformLoss
  linarith

variable {A : Finset ℤ}

/-- The codimension-zero normalized product also obeys the same uniform
rank-bounded loss. -/
theorem bodyVolume_rankedNormalizedTopAffineBodyPresentation_le_uniform
    (X : RankedBodyPresentation A) {rankBound : ℕ}
    (hXrank : X.1 ≤ rankBound) :
    bodyVolume (rankedNormalizedTopAffineBodyPresentation X) ≤
      normalizedAffineUniformLoss rankBound * bodyVolume X := by
  have hfactor : affineRestrictionRealFactor X.1 (X.1 + 1) 0 =
      2 * (X.1 : ℝ) ^ X.1 := by
    unfold affineRestrictionRealFactor
    simp only [pow_zero, ENNReal.ofReal_one, mul_one]
    rw [ENNReal.inv_mul_cancel (by positivity) (by simp)]
    norm_num
  have hlt := affineRestrictionRealFactor_lt_uniform hXrank
    (d := X.1 + 1) (k := 0) le_rfl (Nat.zero_le _)
  rw [bodyVolume_rankedNormalizedTopAffineBodyPresentation]
  calc
    2 * ((X.1 : ℝ) ^ X.1 * bodyVolume X) =
        affineRestrictionRealFactor X.1 (X.1 + 1) 0 * bodyVolume X := by
      rw [hfactor]
      ring
    _ ≤ normalizedAffineUniformLoss rankBound * bodyVolume X :=
      mul_le_mul_of_nonneg_right hlt.le (bodyVolume_pos X).le

/-- The proper normalized affine restriction has uniformly bounded real
volume at every old rank below `rankBound`. -/
theorem bodyVolume_rankedNormalizedProperAffineBodyPresentation_le_uniform
    (X : RankedBodyPresentation A) (hA : A.Nonempty)
    {rankBound : ℕ} (hXrank : X.1 ≤ rankBound)
    (hproper : normalizedHomogeneousSubspace X ≠ ⊤) :
    bodyVolume
        (rankedNormalizedProperAffineBodyPresentation X hA hproper) ≤
      normalizedAffineUniformLoss rankBound * bodyVolume X := by
  let L := normalizedHomogeneousSubspace X
  let d := finrank ℝ L
  let k := finrank ℝ Lᗮ
  let c : ENNReal :=
    ((d.factorial : ENNReal) *
      ENNReal.ofReal ((((X.1 : ℝ) + 1)⁻¹) ^ k))⁻¹ *
        ((d + k).factorial : ENNReal)
  let V : ENNReal := volume (normalizedHomogeneousUnitBall X)
  have hsum : d + k = X.1 + 1 := by
    dsimp only [d, k, L]
    simpa only [finrank_euclideanSpace_fin] using
      (Submodule.finrank_add_finrank_orthogonal
        (normalizedHomogeneousSubspace X))
  have hcTop : c ≠ ⊤ := by
    dsimp only [c]
    have hden : (d.factorial : ENNReal) *
        ENNReal.ofReal ((((X.1 : ℝ) + 1)⁻¹) ^ k) ≠ 0 := by
      positivity
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hden)
      (by simp)
  have hVTop : V ≠ ⊤ := by
    dsimp only [V]
    exact (isCompact_normalizedHomogeneousUnitBall X).measure_lt_top.ne
  have hbound : volume
        {x | normalizedAffineSectionSeminorm X hproper x ≤ 1} ≤
      c * V := by
    simpa only [c, V, d, k, L] using
      (volume_normalizedProperAffine_unitBall_le X hproper)
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top hcTop hVTop) hbound
  have hVreal : V.toReal =
      2 * (X.1 : ℝ) ^ X.1 * bodyVolume X := by
    dsimp only [V]
    rw [volume_normalizedHomogeneousUnitBall]
    change bodyVolume (rankedNormalizedTopAffineBodyPresentation X) = _
    rw [bodyVolume_rankedNormalizedTopAffineBodyPresentation]
    ring
  have hproperReal : bodyVolume
        (rankedNormalizedProperAffineBodyPresentation X hA hproper) ≤
      affineRestrictionRealFactor X.1 d k * bodyVolume X := by
    change (volume
      {x | normalizedAffineSectionSeminorm X hproper x ≤ 1}).toReal ≤ _
    rw [ENNReal.toReal_mul, hVreal] at hreal
    change _ ≤ c.toReal * (2 * (X.1 : ℝ) ^ X.1) * bodyVolume X
    exact hreal.trans_eq (by
      dsimp only [affineRestrictionRealFactor, c]
      ring)
  have hd : d ≤ X.1 + 1 := by omega
  have hk : k ≤ X.1 + 1 := by omega
  have hfactor := affineRestrictionRealFactor_lt_uniform hXrank hd hk
  exact hproperReal.trans
    (mul_le_mul_of_nonneg_right hfactor.le (bodyVolume_pos X).le)

#print axioms affineRestrictionRealFactor_lt_uniform
#print axioms bodyVolume_rankedNormalizedTopAffineBodyPresentation_le_uniform
#print axioms bodyVolume_rankedNormalizedProperAffineBodyPresentation_le_uniform

end

end Erdos186.CFP.Bilu.Section93UniformAffineLoss
