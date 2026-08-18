/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.BranchAssembly
import ErdosProblems.Erdos186.PZ.ConvexDensity.NormalizedBranchParameters
import ErdosProblems.Erdos186.PZ.ConvexDensity.SmallBranchNumerics

/-! # Complete first stage of the normalized convex-density proof -/

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace Erdos186.PZ.ConvexDensity

set_option autoImplicit false
noncomputable section

/-- Initial regularization followed by the exact small-hull/large-hull
dichotomy.  In the large alternative this returns the common-hull frontier
witnesses and the quantitative inball used by the cap step. -/
theorem normalized_first_stage
    {d : ℕ} (hd : 2 ≤ d) {epsilon delta : ℝ}
    (hepsilon : 0 < epsilon)
    (hepsilonLe : epsilon ≤ 1 / ((d : ℝ) + 1))
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdeltaGrid : delta < initialGridDeltaZero d)
    (hsmallCard :
      2 * ((dyadicLevelCount delta : ℝ) + 1) *
        (delta ^ tau epsilon) ^ densityExponent d epsilon ≤ 1)
    (Y : Finset (EuclideanPoint d))
    (hlarge : initialLargeEnough delta ≤ Y.card)
    (hposition : ConvexGeometry.IsDeltaConvexPosition delta Y)
    (hinner : normalizedInnerCube d ⊆ convexHull ℝ (Y : Set _))
    (houter : convexHull ℝ (Y : Set _) ⊆ normalizedOuterCube d) :
    ConvexDensityOutput epsilon (tau epsilon) delta
        (convexHull ℝ (Y : Set _)) Y ∨
      ∃ (j : ℕ) (J : Finset (Fin d → ℕ))
          (witness : {k // k ∈ J} → EuclideanPoint d)
          (center : EuclideanPoint d),
        j < dyadicLevelCount delta + 1 ∧
        J = RelativeDyadicCells.relativeShell
          (GridPartition.candidateGridIndices d (initialRadius d delta))
          (DyadicCells.occupancy Y
            (GridPartition.gridIndex (initialRadius d delta)))
          (initialOccupancyCutoff delta Y.card) j ∧
        J.Nonempty ∧
        Y.card ≤ 2 * ((dyadicLevelCount delta + 1) *
          RelativeDyadicCells.shellWeight
            (GridPartition.candidateGridIndices d (initialRadius d delta))
            (DyadicCells.occupancy Y
              (GridPartition.gridIndex (initialRadius d delta)))
            (initialOccupancyCutoff delta Y.card) j) ∧
        (∀ k ∈ J,
          delta * (Y.card : ℝ) <
            DyadicCells.occupancy Y
              (GridPartition.gridIndex (initialRadius d delta)) k) ∧
        (∀ k ∈ J,
          initialOccupancyCutoff delta Y.card * 2 ^ j ≤
              DyadicCells.occupancy Y
                (GridPartition.gridIndex (initialRadius d delta)) k ∧
            DyadicCells.occupancy Y
                (GridPartition.gridIndex (initialRadius d delta)) k <
              initialOccupancyCutoff delta Y.card * 2 ^ (j + 1)) ∧
        J.card * (initialOccupancyCutoff delta Y.card * 2 ^ j) ≤
          RelativeDyadicCells.shellWeight
            (GridPartition.candidateGridIndices d (initialRadius d delta))
            (DyadicCells.occupancy Y
              (GridPartition.gridIndex (initialRadius d delta)))
            (initialOccupancyCutoff delta Y.card) j ∧
        RelativeDyadicCells.shellWeight
            (GridPartition.candidateGridIndices d (initialRadius d delta))
            (DyadicCells.occupancy Y
              (GridPartition.gridIndex (initialRadius d delta)))
            (initialOccupancyCutoff delta Y.card) j ≤
          (initialOccupancyCutoff delta Y.card * 2 ^ (j + 1)) * J.card ∧
        center ∈ commonCellHull J (fun k ↦
          (gridAssignmentFiberFinset Y (initialRadius d delta) k : Set _)) ∧
        Metric.closedBall center
            (normalizedLargeHullInradius d epsilon delta) ⊆
          commonCellHull J (fun k ↦
            (gridAssignmentFiberFinset Y (initialRadius d delta) k : Set _)) ∧
        ∀ k : {k // k ∈ J},
          witness k ∈ Metric.closedBall
              (GridPartition.gridCenter (initialRadius d delta) k.1)
              (3 * (Real.sqrt (d : ℝ) *
                (initialRadius d delta / 2))) ∧
            witness k ∈ frontier (commonCellHull J (fun i ↦
              (gridAssignmentFiberFinset Y (initialRadius d delta) i : Set _))) := by
  classical
  let mesh := initialRadius d delta
  let cutoff := initialOccupancyCutoff delta Y.card
  let L := dyadicLevelCount delta
  let cells := GridPartition.candidateGridIndices d mesh
  let weight := DyadicCells.occupancy Y (GridPartition.gridIndex mesh)
  have hYne : Y.Nonempty := by
    apply Finset.card_pos.mp
    have hlargePos : 0 < initialLargeEnough delta := by
      exact Nat.ceil_pos.mpr (by positivity)
    omega
  have hmesh : 0 < mesh := by
    simp only [mesh, initialRadius]
    positivity
  have hYcube : (Y : Set (EuclideanPoint d)) ⊆
      GridPartition.normalizedCube d := by
    intro y hy
    have hyHull : y ∈ convexHull ℝ (Y : Set _) := subset_convexHull ℝ _ hy
    simpa [GridPartition.normalizedCube, normalizedOuterCube] using houter hyHull
  have hcandidate : cells.card ≤ initialCandidateCount d delta := by
    simpa [cells, mesh, initialCandidateCount, initialAxisCount] using
      GridPartition.card_candidateGridIndices_le d mesh
  obtain ⟨_hradius, hdiscard, hheavyArithmetic, _hlevel⟩ :=
    initial_grid_arithmetic hd hdelta hdeltaGrid hcandidate hlarge
  have hcutoff : 0 < cutoff := by
    simp only [cutoff, initialOccupancyCutoff]
    exact Nat.ceil_pos.mpr (mul_pos (mul_pos (by norm_num) hdelta)
      (by exact_mod_cast Finset.card_pos.mpr hYne))
  have hupper : Y.card < cutoff * 2 ^ (L + 1) := by
    simpa [cutoff, L] using
      card_lt_initialOccupancyCutoff_mul_two_pow_dyadicLevelCount
        hdelta hdeltaOne (Finset.card_pos.mpr hYne)
  obtain ⟨j, hj, hJne, hmass, hmassTwice, hheavy, hpointwise,
      hmassLower, hmassUpper⟩ :=
    exists_initial_heavy_cell_shell Y hYne hmesh hYcube hcutoff hupper
      (by simpa [cells, cutoff] using hdiscard)
      (by
        intro occupancy hocc
        exact hheavyArithmetic occupancy (by simpa [cutoff] using hocc))
  let J := RelativeDyadicCells.relativeShell cells weight cutoff j
  have hJdef : J = RelativeDyadicCells.relativeShell
      (GridPartition.candidateGridIndices d mesh)
      (DyadicCells.occupancy Y (GridPartition.gridIndex mesh)) cutoff j := rfl
  have hJne' : J.Nonempty := by simpa [J, cells, weight] using hJne
  have hheavy' : ∀ k ∈ J,
      delta * (Y.card : ℝ) <
        DyadicCells.occupancy Y (GridPartition.gridIndex mesh) k := by
    simpa [J, cells, weight] using hheavy
  obtain ⟨witness, hwitness⟩ :=
    exists_commonGridHull_boundaryWitnesses (by omega : 0 < d)
      hmesh hdelta hYne hYcube hposition hheavy'
  let Omega := convexHull ℝ (Y : Set (EuclideanPoint d))
  let P := commonCellHull J (fun k ↦
    (gridAssignmentFiberFinset Y mesh k : Set (EuclideanPoint d)))
  have hOmega : IsConvexBody Omega :=
    isConvexBody_convexHull_of_normalizedInnerCube_subset hinner
  have hYOmega : (Y : Set (EuclideanPoint d)) ⊆ Omega :=
    subset_convexHull ℝ _
  let eta := delta ^ tau epsilon
  have hEta : eta ∈ Set.Icc delta (delta ^ tau epsilon) := by
    exact ⟨le_rpow_tau_of_epsilon_le_inv_dimension hdelta hdeltaOne
      hepsilon hepsilonLe, le_rfl⟩
  have hCard : eta ^ densityExponent d epsilon * (Y.card : ℝ) ≤
      ∑ k ∈ J, DyadicCells.occupancy Y
        (GridPartition.gridIndex mesh) k := by
    have hmassR : (Y.card : ℝ) ≤
        2 * ((L : ℝ) + 1) *
          (RelativeDyadicCells.shellWeight cells weight cutoff j : ℝ) := by
      exact_mod_cast (show Y.card ≤
        2 * (L + 1) * RelativeDyadicCells.shellWeight cells weight cutoff j by
          simpa [mul_assoc] using hmassTwice)
    have hcost : eta ^ densityExponent d epsilon * (Y.card : ℝ) ≤
        (RelativeDyadicCells.shellWeight cells weight cutoff j : ℝ) := by
      have hnonneg : 0 ≤ eta ^ densityExponent d epsilon :=
        Real.rpow_nonneg (by positivity) _
      dsimp only [eta]
      nlinarith
    exact_mod_cast (hcost.trans_eq (by
      simp [RelativeDyadicCells.shellWeight, J, cells, weight]))
  have hTne : (retainedFiberUnion J
      (gridAssignmentFiberFinset Y mesh)).Nonempty := by
    obtain ⟨k, hk⟩ := hJne'
    have hoccPos : 0 < DyadicCells.occupancy Y
        (GridPartition.gridIndex mesh) k := by
      have hYR : (0 : ℝ) < Y.card := by
        exact_mod_cast Finset.card_pos.mpr hYne
      have := hheavy' k hk
      exact_mod_cast (mul_pos hdelta hYR).trans this
    have hfiber : (gridAssignmentFiberFinset Y mesh k).Nonempty := by
      rw [← Finset.card_pos, card_gridAssignmentFiberFinset]
      exact hoccPos
    obtain ⟨y, hy⟩ := hfiber
    exact ⟨y, mem_retainedFiberUnion.mpr ⟨k, hk, hy⟩⟩
  have hPball : P ⊆ Metric.closedBall 0 (Real.sqrt d) := by
    rw [show P = retainedConvexHull
      (retainedFiberUnion J (gridAssignmentFiberFinset Y mesh)) by
        simpa [P] using commonAssignmentFiberHull_eq_retainedConvexHull Y J mesh]
    apply convexHull_min
    · intro y hy
      have hyY : y ∈ Y := retainedFiberUnion_subset
        (fun k _hk ↦ gridAssignmentFiberFinset_subset Y mesh k) hy
      exact normalizedOuterCube_subset_closedBall d
        (houter (subset_convexHull ℝ _ hyY))
    · exact convex_closedBall 0 (Real.sqrt d)
  have hbranch := relativeVolume_le_or_normalized_volume_lower (P := P) hOmega
    (show 0 ≤ eta by positivity) hinner
  have hstruct := convexDensityOutput_or_commonGridHull_inball
    (by omega : 0 < d) hEta hOmega hYOmega hTne
    (show 0 < Real.sqrt d by positivity)
    (show 0 ≤ normalizedLargeHullVolume d epsilon delta by
      exact (normalizedLargeHullVolume_pos hdelta).le)
    (by simpa [P] using hPball)
    (by simpa [P, Omega, eta, normalizedLargeHullVolume] using hbranch)
    (by simpa [mesh] using hCard)
  rcases hstruct with hout | ⟨center, hcenter, hball⟩
  · exact Or.inl (by simpa [Omega] using hout)
  · right
    refine ⟨j, J, witness, center, hj, ?_, hJne', ?_, hheavy', ?_, ?_, ?_,
      hcenter, ?_, ?_⟩
    · rfl
    · simpa [L, J, cells, weight] using hmassTwice
    · simpa [J, cells, weight, cutoff, mesh] using hpointwise
    · simpa [J, cells, weight, cutoff, mesh] using hmassLower
    · simpa [J, cells, weight, cutoff, mesh] using hmassUpper
    · simpa [P, normalizedLargeHullInradius] using hball
    · simpa [mesh, P] using hwitness

end
end Erdos186.PZ.ConvexDensity
