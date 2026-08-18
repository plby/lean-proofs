/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.PreprocessedWitness
import ErdosProblems.Erdos186.CFP.CenteredPreprocessingSource
import ErdosProblems.Erdos186.TrivialWitness

/-!
# Rank-zero preprocessed reserve certificate

The empty-relevant branch of retained preprocessing has a uniformly small
weak core.  It is handled without inventing a positive rank: discard the
stable core and use the rank-zero progression.
-/

namespace Erdos186.CFP

open scoped BigOperators

noncomputable section

/-- A small stable core admits the concrete rank-zero reserve certificate. -/
def discardAllPreprocessedReserveCertificate
    (stableCore : Finset ℤ) (s D extraLoss scaleNum scaleDen : ℕ)
    (hs : 0 < s) (hnum : 0 < scaleNum) (hden : 0 < scaleDen)
    (hscale : scaleNum ≤ scaleDen)
    (hcard : stableCore.card ≤ extraLoss) :
    PreprocessedReserveCertificate stableCore s D extraLoss
      scaleNum scaleDen where
  integerCore := ∅
  integerCore_subset := Finset.empty_subset _
  stableCore_large := by simpa using hcard
  ell := 0
  rank := 0
  k := s
  reserve := Fin.elim0
  progression := zeroGAP 1
  translatePoint := 0
  reserve_pairwiseDisjoint := by
    intro i
    exact Fin.elim0 i
  rank_le := Nat.zero_le D
  reserve_subset_core := by
    intro i
    exact Fin.elim0 i
  reserve_small := by simp
  core_zero_subset := by simp [Stability.integerPoints]
  homogeneous := zeroGAP_homogeneous
  covered := by
    simpa using (zeroGAP_covered_by_empty (d := 1) s)
  dilate_proper := zeroGAP_dilate_proper s
  k_pos := hs
  scaleNum_pos := hnum
  scaleDen_pos := hden
  scale_lower := Nat.mul_le_mul_right s hscale
  scale_upper := Nat.le_refl s
  progression_proper := by
    exact GAPBuilders.zeroGAP_proper
  progression_symmetric := by
    refine ⟨Fin.elim0, ?_⟩
    constructor
    · funext i
      exact Fin.elim0 i
    · funext j
      simp [zeroGAP]
  progression_nondegenerate := fun i ↦ Fin.elim0 i
  covered_translate_homogeneous := by
    refine ⟨Fin.elim0, ?_⟩
    funext j
    simp [zeroGAP]

/-- The small-core alternative retained by preprocessing fits the public
single-logarithm loss with a coefficient depending only on the rank and
preprocessing denominator. -/
theorem smallDyadicPreprocessingCore_card_le_logLoss
    {source : Finset ℤ} {s D n C0 scaleDen fold ell : ℕ}
    (data : Preprocessing.DyadicCenteredPreprocessingData source s D n C0
      1 scaleDen fold)
    (hsmall : data.weakCore.card ≤ 1 +
      (s / C0) *
        (D * Nat.log 2
          (4 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D) + 1))
    (hs : 0 < s) (hell : 0 < ell) :
    data.core.card ≤
      (D * Nat.log 2
          (4 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D) + 2) *
        s * ell := by
  let height := D * Nat.log 2
    (4 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D) + 1
  have hdiv : s / C0 ≤ s := Nat.div_le_self _ _
  have hcore : data.core.card ≤ 1 + s * height := by
    exact (Finset.card_le_card data.core_subset_weakCore).trans
      (hsmall.trans (Nat.add_le_add_left (Nat.mul_le_mul_right height hdiv) 1))
  have hone : 1 ≤ s * ell := Nat.mul_pos hs hell
  have hheight : s * height ≤ height * (s * ell) := by
    calc
      s * height = height * s := by ring
      _ ≤ height * (s * ell) := by
        gcongr
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left s hell
  calc
    data.core.card ≤ 1 + s * height := hcore
    _ ≤ s * ell + height * (s * ell) := Nat.add_le_add hone hheight
    _ = (D * Nat.log 2
          (4 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D) + 2) *
        s * ell := by
      dsimp only [height]
      ring

/-- Concrete rank-zero certificate for the retained empty-relevant branch. -/
theorem exists_discardAllPreprocessedReserveCertificate_of_smallDyadicCore
    {source : Finset ℤ}
    {s D n C0 preprocessingScaleDen fold ell finalScaleDen : ℕ}
    (data : Preprocessing.DyadicCenteredPreprocessingData source s D n C0
      1 preprocessingScaleDen fold)
    (hsmall : data.weakCore.card ≤ 1 +
      (s / C0) *
        (D * Nat.log 2
          (4 * (6 * preprocessingScaleDen) ^ D *
            (4 * preprocessingScaleDen) ^ D) + 1))
    (hs : 0 < s) (hell : 0 < ell) (hfinal : 0 < finalScaleDen) :
    Nonempty (PreprocessedReserveCertificate data.core s D
      ((D * Nat.log 2
          (4 * (6 * preprocessingScaleDen) ^ D *
            (4 * preprocessingScaleDen) ^ D) + 2) * s * ell)
      1 finalScaleDen) := by
  refine ⟨discardAllPreprocessedReserveCertificate data.core s D _ 1
    finalScaleDen hs (by omega) hfinal (by omega) ?_⟩
  exact smallDyadicPreprocessingCore_card_le_logLoss data hsmall hs hell

end

end Erdos186.CFP

#print axioms Erdos186.CFP.discardAllPreprocessedReserveCertificate
