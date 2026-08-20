/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos980.ElliottTail.RationalPrimeGeneratorBridge

/-!
# Elementary geometry for the odd-prime ray cells

This file records two geometric facts used when the arithmetic odd-prime
encoding is turned into finite sieve data.  A translate of the scaled ideal
lattice has finite intersection with every dilate of the bounded generator
region.  In addition, the balanced generator attached to an exceptional
prime below `x` lies in the single height region obtained by replacing its
conductor by `x`.
-/

open scoped NumberField nonZeroDivisors Pointwise

noncomputable section

namespace Erdos980.ElliottTail.OddCellGeometry

open NumberField
open NumberField.mixedEmbedding
open NumberField.mixedEmbedding.fundamentalCone
open IdealGeneratorCongruenceCount
open RationalPrimeGeneratorBridge
open RayPrincipalization

/-- A fixed ideal-lattice congruence cell has finite intersection with every
dilate of the bounded generator region. -/
theorem generatorCongruenceCell_inter_generatorNormRegion_finite
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰) (m : ℕ) [NeZero m]
    (k : index K → ZMod m) (height : ℝ) :
    Set.Finite (generatorCongruenceCell J m k ∩
      height • generatorNormRegion K) := by
  classical
  let L : Set (index K → ℝ) :=
    (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (index K))) :
      Set (index K → ℝ))
  let e : (index K → ℝ) ≃ₜ (index K → ℝ) :=
    (scaledIdealLatticeChart J m).toContinuousLinearEquiv.toHomeomorph |>.trans
      (Homeomorph.addLeft (generatorCongruenceTranslate J k))
  have hcell : generatorCongruenceCell J m k = e '' L := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨scaledIdealLatticeChart J m z, ⟨z, hz, rfl⟩, rfl⟩
  letI : DiscreteTopology
      (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (index K)))) :=
    inferInstance
  have hLdiscrete : IsDiscrete L := by
    dsimp only [L]
    exact DiscreteTopology.isDiscrete
  have hLclosed : IsClosed L := by
    change IsClosed
      ((Submodule.span ℤ (Set.range (Pi.basisFun ℝ (index K)))).toAddSubgroup :
        Set (index K → ℝ))
    exact AddSubgroup.isClosed_of_discrete
  have hcellDiscrete : IsDiscrete (generatorCongruenceCell J m k) := by
    rw [hcell]
    exact hLdiscrete.image e.isInducing
  have hcellClosed : IsClosed (generatorCongruenceCell J m k) := by
    rw [hcell]
    exact e.isClosed_image.mpr hLclosed
  have hregion : Bornology.IsBounded (generatorNormRegion K) :=
    (mixedEmbedding.stdBasis K).equivFunL.lipschitz.isBounded_image
      (isBounded_normLeOne K)
  have hscaled : Bornology.IsBounded (height • generatorNormRegion K) :=
    Bornology.IsBounded.smul₀ hregion height
  simpa only [Set.inter_comm] using
    Metric.finite_isBounded_inter_isClosed hcellDiscrete hscaled hcellClosed

/-- The generator norm region is monotone under positive scalar dilation. -/
theorem smul_generatorNormRegion_subset
    (K : Type*) [Field K] [NumberField K]
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    a • generatorNormRegion K ⊆ b • generatorNormRegion K := by
  intro x hx
  have hb : 0 < b := ha.trans_le hab
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hb.ne']
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ ha.ne'] at hx
  unfold generatorNormRegion at hx ⊢
  rcases hx with ⟨y, hy, hyx⟩
  refine ⟨(a / b) • y, ?_, ?_⟩
  · rw [mem_normLeOne] at hy ⊢
    constructor
    · exact smul_mem_of_mem hy.1 (div_ne_zero ha.ne' hb.ne')
    · rw [mixedEmbedding.norm_smul, abs_of_pos (div_pos ha hb)]
      have hab' : a / b ≤ 1 := (div_le_one hb).mpr hab
      have hpow : (a / b) ^ Module.finrank ℚ K ≤ 1 := by
        simpa using pow_le_one₀ (div_nonneg ha.le hb.le) hab'
      nlinarith [hy.2, mixedEmbedding.norm_nonneg y]
  · rw [map_smul, hyx, smul_smul]
    congr 1
    field_simp

/-- A balanced generator of conductor `p ≤ x` lies in the common height
region obtained by replacing `p` by `x`.  The exceptional-prime application
uses this with the fixed correction index of one finite tag fibre. -/
theorem boundedGenerator_mem_commonNormRegion
    (ell : ℕ) [Fact ell.Prime]
    (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {ell} ℚ K]
    {p x : ℕ} (data : BoundedGeneratorEncodingData ell K p)
    (hpx : p ≤ x) :
    (mixedEmbedding.stdBasis K).equivFunL
        (mixedEmbedding K (data.balancedGenerator : K)) ∈
      (((x * Ideal.absNorm
          (cyclotomicRayCorrection ell K data.correctionIndex) : ℕ) : ℝ) ^
        ((Module.finrank ℚ K : ℝ)⁻¹)) • generatorNormRegion K := by
  have hcorrPos : 0 < Ideal.absNorm
      (cyclotomicRayCorrection ell K data.correctionIndex) :=
    Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (cyclotomicRayCorrection_ne_bot ell K data.correctionIndex))
  have hpPos : 0 < p := by
    rw [← data.primeIdeal_absNorm]
    exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp data.primeIdeal.2))
  have hbase : p * Ideal.absNorm
        (cyclotomicRayCorrection ell K data.correctionIndex) ≤
      x * Ideal.absNorm
        (cyclotomicRayCorrection ell K data.correctionIndex) :=
    Nat.mul_le_mul_right _ hpx
  have hsmallPos : (0 : ℝ) <
      ((p * Ideal.absNorm
          (cyclotomicRayCorrection ell K data.correctionIndex) : ℕ) : ℝ) ^
        ((Module.finrank ℚ K : ℝ)⁻¹) := by
    positivity
  have hrpow :
      ((p * Ideal.absNorm
          (cyclotomicRayCorrection ell K data.correctionIndex) : ℕ) : ℝ) ^
          ((Module.finrank ℚ K : ℝ)⁻¹) ≤
        ((x * Ideal.absNorm
          (cyclotomicRayCorrection ell K data.correctionIndex) : ℕ) : ℝ) ^
          ((Module.finrank ℚ K : ℝ)⁻¹) := by
    apply Real.rpow_le_rpow
    · positivity
    · exact_mod_cast hbase
    · positivity
  apply smul_generatorNormRegion_subset K hsmallPos hrpow
  exact data.balancedGenerator_mem_region

end Erdos980.ElliottTail.OddCellGeometry
