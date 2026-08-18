/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section6DistortingHalfCell
import ErdosProblems.Erdos186.CFP.Bilu.Section6BiasedResidueCell
import ErdosProblems.Erdos186.CFP.Bilu.Proposition75Construction

/-!
# The biased residue cell in Bilu Section 7

This module repairs the quantitative interface between Lemmas 6.1/6.3
and Proposition 7.5.  The distortion-coordinate count is `r`, whereas
Freiman's affine-slice theorem is invoked at target rank `r - 1`.
The residue-cell loss is `(2 / gamma)^r`, not the crude `2^r`.
-/

namespace Erdos186.CFP.Bilu.Section7BiasedAffineSlice

open scoped RealInnerProductSpace
open DistortingMeasure Section8Synthesis SubspaceLattice
open Section7FreimanMap Section7AffineSlice
open Section5TwoN Section5RpowAffineSlice
open Section6DistortingHalfCell Section6BiasedResidueCell
open Proposition75Construction

noncomputable section

/-- Lemmas 6.1 and 6.3 produce a residue cell whose doubling loss is
`(2 / gamma)^r`.  Thus the ambient distortion count `r` is cleanly
separated from the affine-slice target `r - 1`. -/
theorem exists_biased_rpow_residueCell
    {m r : ℕ} (hr : 0 < r)
    (K : Finset (Mahler.IntegralPoint m)) (hK : K.Nonempty)
    (a : Fin r → EuclideanSpace ℝ (Fin m))
    (delta sigma targetDelta : ℝ)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hsigma : 0 < sigma)
    (ha : ∀ i, WithLp.ofLp (a i) ∈ cubeDistortingSet delta K)
    (hsum : ((sumset K).card : ℝ) ≤ sigma * K.card)
    (hrank : sigma * (2 / biasGamma delta) ^ r ≤
      Real.rpow 2 (((r - 1 : ℕ) : ℝ) + 1 - targetDelta)) :
    ∃ b : Fin r → ℝ, ∃ alpha : Fin r → Fin 2,
      (biasGamma delta / 2) ^ r * K.card <
          (residueCell a b alpha K).card ∧
        K.card ≤ 2 ^ r * (residueCell a b alpha K).card ∧
        (residueCell a b alpha K).Nonempty ∧
        ((pairSumset (residueCell a b alpha K)).card : ℝ) ≤
          Real.rpow 2 (((r - 1 : ℕ) : ℝ) + 1 - targetDelta) *
            (residueCell a b alpha K).card := by
  obtain ⟨b, hbias⟩ :=
    exists_offsets_biased_halfCells_of_mem_cubeDistortingSet
      K delta hdelta.le a ha
  obtain ⟨alpha, hlarge⟩ := exists_large_biased_residueCell
    a b K hr hdelta hdeltaOne hbias
  let S := residueCell a b alpha K
  have hgamma : 0 < biasGamma delta :=
    (Real.exp_pos _).trans (exp_half_sq_lt_biasGamma hdelta hdeltaOne)
  have hfactor : 0 < (2 / biasGamma delta) ^ r := by positivity
  have hcancel :
      (2 / biasGamma delta) ^ r * (biasGamma delta / 2) ^ r = 1 := by
    rw [← mul_pow]
    have hbase : (2 / biasGamma delta) * (biasGamma delta / 2) = 1 := by
      field_simp
    rw [hbase, one_pow]
  have hK_lt : (K.card : ℝ) <
      (2 / biasGamma delta) ^ r * S.card := by
    have hscaled := mul_lt_mul_of_pos_left hlarge hfactor
    calc
      (K.card : ℝ) =
          (2 / biasGamma delta) ^ r *
            ((biasGamma delta / 2) ^ r * K.card) := by
        rw [← mul_assoc, hcancel, one_mul]
      _ < (2 / biasGamma delta) ^ r * S.card := hscaled
  have hSnonempty : S.Nonempty := by
    rw [← Finset.card_pos]
    have hleftPos : 0 < (biasGamma delta / 2) ^ r * (K.card : ℝ) := by
      positivity
    exact_mod_cast hleftPos.trans hlarge
  have hgammaOne : 1 < biasGamma delta := by
    have honeExp : 1 ≤ Real.exp (delta ^ 2 / 2) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by positivity)
    exact honeExp.trans_lt (exp_half_sq_lt_biasGamma hdelta hdeltaOne)
  have hbase_le : 2 / biasGamma delta ≤ (2 : ℝ) := by
    rw [div_le_iff₀ hgamma]
    nlinarith
  have hfactor_le : (2 / biasGamma delta) ^ r ≤ (2 : ℝ) ^ r := by
    exact pow_le_pow_left₀ (by positivity) hbase_le r
  have hK_lt_crude : (K.card : ℝ) < (2 : ℝ) ^ r * S.card :=
    hK_lt.trans_le (mul_le_mul_of_nonneg_right hfactor_le (by positivity))
  have hcover : K.card ≤ 2 ^ r * S.card := by
    have hcast : K.card < 2 ^ r * S.card := by
      exact_mod_cast hK_lt_crude
    exact hcast.le
  have hSsub : S ⊆ K := by
    intro x hx
    exact (mem_residueCell a b alpha K x).mp hx |>.1
  have hpair_le : (pairSumset S).card ≤ (sumset K).card := by
    apply Finset.card_le_card
    rw [← pairSumset_eq_sumset K]
    exact pairSumset_mono hSsub
  have hscaledK : sigma * (K.card : ℝ) <
      (sigma * (2 / biasGamma delta) ^ r) * S.card := by
    calc
      sigma * (K.card : ℝ) <
          sigma * ((2 / biasGamma delta) ^ r * S.card) :=
        mul_lt_mul_of_pos_left hK_lt hsigma
      _ = (sigma * (2 / biasGamma delta) ^ r) * S.card := by ring
  refine ⟨b, alpha, hlarge, hcover, hSnonempty, ?_⟩
  apply le_of_lt
  calc
    ((pairSumset S).card : ℝ) ≤ (sumset K).card := by
      exact_mod_cast hpair_le
    _ ≤ sigma * K.card := hsum
    _ < (sigma * (2 / biasGamma delta) ^ r) * S.card := hscaledK
    _ ≤ Real.rpow 2 (((r - 1 : ℕ) : ℝ) + 1 - targetDelta) *
          S.card := by
      exact mul_le_mul_of_nonneg_right hrank (by positivity)

/-- The corrected Section 7 affine-slice constructor.  It consumes the
biased cell and applies the genuine exponential theorem at rank `r-1`. -/
theorem exists_sourceAffineSlice_of_distortingSystem
    {m r : ℕ} (hr : 0 < r)
    (K : Finset (Mahler.IntegralPoint m)) (hK : K.Nonempty)
    (a : Fin r → EuclideanSpace ℝ (Fin m))
    (delta sigma targetDelta : ℝ)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (htargetDelta : 0 < targetDelta) (hsigma : 0 < sigma)
    (ha : ∀ i, WithLp.ofLp (a i) ∈ cubeDistortingSet delta K)
    (hsum : ((sumset K).card : ℝ) ≤ sigma * K.card)
    (hrank : sigma * (2 / biasGamma delta) ^ r ≤
      Real.rpow 2 (((r - 1 : ℕ) : ℝ) + 1 - targetDelta)) :
    ∃ proportionConstant : ℕ, ∃ b : Fin r → ℝ,
      ∃ alpha : Fin r → Fin 2,
        (biasGamma delta / 2) ^ r * K.card <
            (residueCell a b alpha K).card ∧
          K.card ≤ 2 ^ r * (residueCell a b alpha K).card ∧
          Nonempty (SourceAffineSlice a b proportionConstant
            (residueCell a b alpha K)) := by
  obtain ⟨proportionConstant, hslice⟩ :=
    exists_rpowAffineSliceStatement (r - 1) targetDelta htargetDelta
  obtain ⟨b, alpha, hlarge, hcover, hcell, hdouble⟩ :=
    exists_biased_rpow_residueCell hr K hK a delta sigma targetDelta
      hdelta hdeltaOne hsigma ha hsum hrank
  exact ⟨proportionConstant, b, alpha, hlarge, hcover,
    Proposition75Construction.exists_sourceAffineSlice_of_rpow
      hr hslice a b alpha K hcell hdouble⟩

end

end Erdos186.CFP.Bilu.Section7BiasedAffineSlice

#print axioms
  Erdos186.CFP.Bilu.Section7BiasedAffineSlice.exists_biased_rpow_residueCell
#print axioms
  Erdos186.CFP.Bilu.Section7BiasedAffineSlice.exists_sourceAffineSlice_of_distortingSystem
