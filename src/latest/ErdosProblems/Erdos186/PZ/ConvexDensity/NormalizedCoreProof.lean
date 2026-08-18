/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.NormalizedFirstStage
import ErdosProblems.Erdos186.PZ.ConvexDensity.NormalizedLargeBranch
import ErdosProblems.Erdos186.PZ.ConvexDensity.NormalizedLargeBranch2D

/-! # Unconditional normalized finite-hull core -/

open Set MeasureTheory

namespace Erdos186.PZ.ConvexDensity

set_option autoImplicit false
noncomputable section

/-- The normalized finite-hull core in ambient dimension `n+1`, `n ≥ 1`. -/
theorem normalized_finite_hull_core_succ
    (n : ℕ) (hn : 1 ≤ n) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilonLe : epsilon ≤ 1 / (((n + 1 : ℕ) : ℝ) + 1)) :
    ∃ deltaZero : ℝ, 0 < deltaZero ∧ deltaZero ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta < deltaZero →
        ∃ largeEnough : ℕ,
          ∀ Y : Finset (EuclideanPoint (n + 1)),
            largeEnough ≤ Y.card →
            ConvexGeometry.IsDeltaConvexPosition delta Y →
            normalizedInnerCube (n + 1) ⊆
              convexHull ℝ (Y : Set (EuclideanPoint (n + 1))) →
            convexHull ℝ (Y : Set (EuclideanPoint (n + 1))) ⊆
              normalizedOuterCube (n + 1) →
            volume (normalizedOuterCube (n + 1)) ≤
              normalizedBoxConstant (n + 1) * volume
                (convexHull ℝ (Y : Set (EuclideanPoint (n + 1))) ) →
            ConvexDensityOutput epsilon (tau epsilon) delta
              (convexHull ℝ (Y : Set (EuclideanPoint (n + 1)))) Y := by
  let outer := normalizedCommonHullOuterRadius (n + 1)
  let c := normalizedCaptureCoefficient n outer
  let C := normalizedBranchVolumeCoefficient n outer
  let c₀ := normalizedGraphWindowCoefficient (n + 1)
  have hc : 0 < c := normalizedCaptureCoefficient_pos (by omega) (by
    exact normalizedCommonHullOuterRadius_pos (by omega))
  have hC : 0 < C := normalizedBranchVolumeCoefficient_pos (by omega) (by
    exact normalizedCommonHullOuterRadius_pos (by omega))
  have hc₀ : 0 < c₀ := normalizedGraphWindowCoefficient_pos (by omega)
  obtain ⟨dSmall, hdSmall, hdSmallOne, hSmall⟩ :=
    exists_deltaZero_smallBranchCard (d := n + 1) (by omega) hepsilon
  obtain ⟨dRadius, hdRadius, hdRadiusOne, hRadius⟩ :=
    exists_deltaZero_chartFiberRadius (d := n + 1) (by omega) hepsilon hepsilonLe
  obtain ⟨dGrid, hdGrid, hdGridOne, hGrid⟩ :=
    exists_deltaZero_graphGridSize_ge (n + 1) (4 * ((n : ℝ) + 1) + 1)
  obtain ⟨dBranch, hdBranch, hdBranchOne, hBranch⟩ :=
    exists_deltaZero_branchClosuresAtScales (d := n + 1) (epsilon := epsilon)
      (by omega) hepsilon hepsilonLe hc hC (by norm_num : (0 : ℝ) < 1 / 2) hc₀
  let deltaZero := min (initialGridDeltaZero (n + 1))
    (min dSmall (min dRadius (min dGrid dBranch)))
  refine ⟨deltaZero, by
    dsimp only [deltaZero]
    exact lt_min (initialGridDeltaZero_pos (n + 1))
      (lt_min hdSmall (lt_min hdRadius (lt_min hdGrid hdBranch))), ?_, ?_⟩
  · exact (min_le_right _ _).trans
      ((min_le_left _ _).trans hdSmallOne.le)
  · intro delta hdelta hdeltaCut
    have hinitial : delta < initialGridDeltaZero (n + 1) :=
      hdeltaCut.trans_le (min_le_left _ _)
    have hrest : delta < min dSmall (min dRadius (min dGrid dBranch)) :=
      hdeltaCut.trans_le (min_le_right _ _)
    have hsmallCut : delta < dSmall := hrest.trans_le (min_le_left _ _)
    have hradiusCut : delta < dRadius :=
      hrest.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hgridCut : delta < dGrid :=
      hrest.trans_le ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
    have hbranchCut : delta < dBranch :=
      hrest.trans_le ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))
    have hdeltaOne : delta ≤ 1 := hsmallCut.le.trans hdSmallOne.le
    have hmarginBase := hGrid delta hdelta hgridCut
    have hmargin : 4 * ((n : ℝ) + 1) <
        (graphGridSize (n + 1) delta : ℝ) := by linarith
    have hradius := hRadius delta hdelta hradiusCut
    have hclosure := hBranch delta hdelta hbranchCut
    refine ⟨initialLargeEnough delta, ?_⟩
    intro Y hlarge hposition hinner houterHull _hvolume
    have hYne : Y.Nonempty := by
      apply Finset.card_pos.mp
      have hpos : 0 < initialLargeEnough delta :=
        Nat.ceil_pos.mpr (by positivity)
      omega
    rcases normalized_first_stage (d := n + 1) (by omega) hepsilon hepsilonLe
        hdelta hdeltaOne hinitial (hSmall delta hdelta hsmallCut)
        Y hlarge hposition hinner houterHull with hout | hlargeStage
    · exact hout
    · obtain ⟨j, J, witness, center, hj, hJdef, hJne, hmass,
          hheavy, hpoint, _hmassLower, hmassUpper, hcenter, hball, hwitness⟩ :=
        hlargeStage
      have hcutoff : 0 < initialOccupancyCutoff delta Y.card := by
        exact Nat.ceil_pos.mpr (mul_pos (mul_pos (by norm_num) hdelta)
          (by exact_mod_cast Finset.card_pos.mpr hYne))
      have hJcells : J ⊆ GridPartition.candidateGridIndices (n + 1)
          (initialRadius (n + 1) delta) := by
        intro k hk
        rw [hJdef] at hk
        exact (RelativeDyadicCells.mem_relativeShell_iff hcutoff).mp hk |>.1
      rcases hn.eq_or_lt with rfl | hnStrict
      · apply convexDensityOutput_of_normalized_large_stage_2d
          (X := Y) (j₁ := j) (J := J) (witness := witness) (center := center)
          hepsilon hdelta hdeltaOne (by norm_num at hmargin ⊢; omega) hradius
        · intro K hK hhalf
          simpa [c, C, c₀, outer] using hclosure K hK hhalf
        · exact hYne
        · exact hposition
        · exact hinner
        · exact houterHull
        · exact hJne
        · exact hJcells
        · exact hmass
        · exact hheavy
        · intro k hk
          exact (hpoint k hk).1
        · exact hmassUpper
        · exact hcenter
        · exact hball
        · exact hwitness
      · apply convexDensityOutput_of_normalized_large_stage_nd
          (X := Y) (j₁ := j) (J := J) (witness := witness) (center := center)
          (by omega) hepsilon hdelta hdeltaOne hmargin hradius
        · intro K hK hhalf
          simpa [c, C, c₀, outer] using hclosure K hK hhalf
        · exact hYne
        · exact hposition
        · exact hinner
        · exact houterHull
        · exact hJne
        · exact hJcells
        · exact hmass
        · exact hheavy
        · intro k hk
          exact (hpoint k hk).1
        · exact hmassUpper
        · exact hcenter
        · exact hball
        · exact hwitness

/-- The ambient-dimension-at-least-three specialization of the normalized core. -/
theorem normalized_finite_hull_core_ge_three
    (n : ℕ) (hn : 2 ≤ n) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilonLe : epsilon ≤ 1 / (((n + 1 : ℕ) : ℝ) + 1)) :
    ∃ deltaZero : ℝ, 0 < deltaZero ∧ deltaZero ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta < deltaZero →
        ∃ largeEnough : ℕ,
          ∀ Y : Finset (EuclideanPoint (n + 1)),
            largeEnough ≤ Y.card →
            ConvexGeometry.IsDeltaConvexPosition delta Y →
            normalizedInnerCube (n + 1) ⊆
              convexHull ℝ (Y : Set (EuclideanPoint (n + 1))) →
            convexHull ℝ (Y : Set (EuclideanPoint (n + 1))) ⊆
              normalizedOuterCube (n + 1) →
            volume (normalizedOuterCube (n + 1)) ≤
              normalizedBoxConstant (n + 1) * volume
                (convexHull ℝ (Y : Set (EuclideanPoint (n + 1))) ) →
            ConvexDensityOutput epsilon (tau epsilon) delta
              (convexHull ℝ (Y : Set (EuclideanPoint (n + 1)))) Y :=
  normalized_finite_hull_core_succ n (by omega) epsilon hepsilon hepsilonLe

/-- The complete normalized finite-hull core in every ambient dimension at least two. -/
theorem pzNormalizedFiniteHullCore : PZNormalizedFiniteHullCore := by
  intro d hd epsilon hepsilon hepsilonLe
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, d = n + 1 := ⟨d - 1, by omega⟩
  exact normalized_finite_hull_core_succ n (by omega) epsilon hepsilon hepsilonLe

/-- The literal all-dimensional Pham--Zakharov convex-density statement. -/
theorem convexDensityStatement : PZLemmaOneStatement :=
  pzLemmaOneStatement_of_normalizedFiniteHullCore pzNormalizedFiniteHullCore

end
end Erdos186.PZ.ConvexDensity

#print axioms Erdos186.PZ.ConvexDensity.pzNormalizedFiniteHullCore
#print axioms Erdos186.PZ.ConvexDensity.convexDensityStatement
