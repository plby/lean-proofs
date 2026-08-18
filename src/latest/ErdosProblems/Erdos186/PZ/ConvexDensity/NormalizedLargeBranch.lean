/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.NormalizedCapStage
import ErdosProblems.Erdos186.PZ.ConvexDensity.NormalizedBranchAssembly

/-! # Assembly of the normalized large-hull graph branch -/

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace Erdos186.PZ.ConvexDensity

set_option autoImplicit false
noncomputable section

/-- Complete `d ≥ 3` large-hull branch. -/
theorem convexDensityOutput_of_normalized_large_stage_nd
    {n : ℕ} (hn : 2 ≤ n) {epsilon delta : ℝ}
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hmMargin : 4 * ((n : ℝ) + 1) < (graphGridSize (n + 1) delta : ℝ))
    (hradius : normalizedChartFiberRadius (n + 1) epsilon delta ≤
      1 / (graphGridSize (n + 1) delta : ℝ) ^ (2 : ℕ))
    (hclosure : ∀ K : ℝ, 0 < K →
      (1 / 2 : ℝ) ≤ K * branchLogScale delta →
      (K ≤ realGridScale (n + 1) delta ^ alpha (n + 1) →
        etaLow (n + 1)
            (normalizedBranchVolumeCoefficient n
              (normalizedCommonHullOuterRadius (n + 1)))
            (graphWidth epsilon (normalizedGraphWindowCoefficient (n + 1)) delta)
            K (realGridScale (n + 1) delta) (branchLogScale delta) ∈
              Set.Icc delta (delta ^ tau epsilon) ∧
        etaLow (n + 1)
            (normalizedBranchVolumeCoefficient n
              (normalizedCommonHullOuterRadius (n + 1)))
            (graphWidth epsilon (normalizedGraphWindowCoefficient (n + 1)) delta)
            K (realGridScale (n + 1) delta) (branchLogScale delta) ^
              (alpha (n + 1) + epsilon) ≤
            capturedFraction (n + 1)
              (normalizedCaptureCoefficient n
                (normalizedCommonHullOuterRadius (n + 1)))
              (graphWidth epsilon (normalizedGraphWindowCoefficient (n + 1)) delta)
              K (realGridScale (n + 1) delta) (branchLogScale delta)) ∧
      (realGridScale (n + 1) delta ^ alpha (n + 1) ≤ K →
        etaHigh (n + 1)
            (normalizedBranchVolumeCoefficient n
              (normalizedCommonHullOuterRadius (n + 1)))
            (graphWidth epsilon (normalizedGraphWindowCoefficient (n + 1)) delta)
            (realGridScale (n + 1) delta) ∈
              Set.Icc delta (delta ^ tau epsilon) ∧
        etaHigh (n + 1)
            (normalizedBranchVolumeCoefficient n
              (normalizedCommonHullOuterRadius (n + 1)))
            (graphWidth epsilon (normalizedGraphWindowCoefficient (n + 1)) delta)
            (realGridScale (n + 1) delta) ^ (alpha (n + 1) + epsilon) ≤
            capturedFraction (n + 1)
              (normalizedCaptureCoefficient n
                (normalizedCommonHullOuterRadius (n + 1)))
              (graphWidth epsilon (normalizedGraphWindowCoefficient (n + 1)) delta)
              K (realGridScale (n + 1) delta) (branchLogScale delta)))
    (X : Finset (EuclideanPoint (n + 1)))
    (hXne : X.Nonempty)
    (hposition : ConvexGeometry.IsDeltaConvexPosition delta X)
    (hinner : normalizedInnerCube (n + 1) ⊆ convexHull ℝ (X : Set _))
    (houterHull : convexHull ℝ (X : Set _) ⊆ normalizedOuterCube (n + 1))
    {j₁ : ℕ} {J : Finset (Fin (n + 1) → ℕ)}
    {witness : {k // k ∈ J} → EuclideanPoint (n + 1)}
    {center : EuclideanPoint (n + 1)}
    (hJ : J.Nonempty)
    (hJcells : J ⊆ GridPartition.candidateGridIndices (n + 1)
      (initialRadius (n + 1) delta))
    (hmass₁ : X.card ≤ 2 * ((dyadicLevelCount delta + 1) *
      RelativeDyadicCells.shellWeight
        (GridPartition.candidateGridIndices (n + 1) (initialRadius (n + 1) delta))
        (DyadicCells.occupancy X
          (GridPartition.gridIndex (initialRadius (n + 1) delta)))
        (initialOccupancyCutoff delta X.card) j₁))
    (hheavy : ∀ k ∈ J, delta * (X.card : ℝ) <
      DyadicCells.occupancy X
        (GridPartition.gridIndex (initialRadius (n + 1) delta)) k)
    (hlower₁ : ∀ k ∈ J,
      initialOccupancyCutoff delta X.card * 2 ^ j₁ ≤
        DyadicCells.occupancy X
          (GridPartition.gridIndex (initialRadius (n + 1) delta)) k)
    (hupper₁ : RelativeDyadicCells.shellWeight
        (GridPartition.candidateGridIndices (n + 1) (initialRadius (n + 1) delta))
        (DyadicCells.occupancy X
          (GridPartition.gridIndex (initialRadius (n + 1) delta)))
        (initialOccupancyCutoff delta X.card) j₁ ≤
      (initialOccupancyCutoff delta X.card * 2 ^ (j₁ + 1)) * J.card)
    (hcenter : center ∈ commonCellHull J (fun k ↦
      (gridAssignmentFiberFinset X (initialRadius (n + 1) delta) k : Set _)))
    (hball : Metric.closedBall center
        (normalizedLargeHullInradius (n + 1) epsilon delta) ⊆
      commonCellHull J (fun k ↦
        (gridAssignmentFiberFinset X (initialRadius (n + 1) delta) k : Set _)))
    (hwitness : ∀ k : {k // k ∈ J},
      witness k ∈ Metric.closedBall
          (GridPartition.gridCenter (initialRadius (n + 1) delta) k.1)
          (3 * (Real.sqrt ((n + 1 : ℕ) : ℝ) *
            (initialRadius (n + 1) delta / 2))) ∧
      witness k ∈ frontier (commonCellHull J (fun i ↦
        (gridAssignmentFiberFinset X (initialRadius (n + 1) delta) i : Set _)))) :
    ConvexDensityOutput epsilon (tau epsilon) delta
      (convexHull ℝ (X : Set _)) X := by
  classical
  let P : Set (EuclideanPoint (n + 1)) := commonCellHull J (fun k ↦
    (gridAssignmentFiberFinset X (initialRadius (n + 1) delta) k :
      Set (EuclideanPoint (n + 1))))
  let q := normalizedGraphWindowRadius (n + 1) epsilon delta
  let outer := normalizedCommonHullOuterRadius (n + 1)
  let m := graphGridSize (n + 1) delta
  let s := realGridScale (n + 1) delta
  let L := dyadicLevelCount delta + 1
  let M := initialOccupancyCutoff delta X.card * 2 ^ j₁
  have hq : 0 < q := normalizedGraphWindowRadius_pos (by omega) hdelta
  have houter : 0 < outer := normalizedCommonHullOuterRadius_pos (by omega)
  have hm : 0 < m := graphGridSize_pos (n + 1) hdelta hdeltaOne
  have hs : 0 < s := realGridScale_pos (n + 1) hdelta
  have hsOne : 1 ≤ s := one_le_realGridScale (n + 1) hdelta hdeltaOne
  have hsm : s ≤ (m : ℝ) := realGridScale_le_graphGridSize_cast _ _
  have hms : (m : ℝ) ≤ 2 * s :=
    graphGridSize_cast_le_two_mul_realGridScale _ hdelta hdeltaOne
  have hqWidth : q = graphWidth epsilon
      (normalizedGraphWindowCoefficient (n + 1)) delta := by
    dsimp only [q]
    rw [normalizedGraphWindowRadius_eq (by omega : 2 ≤ n + 1) hdelta]
    rfl
  have hM : 0 < M := by
    dsimp only [M]
    exact Nat.mul_pos (Nat.ceil_pos.mpr (by
      have hcard : (0 : ℝ) < X.card := by exact_mod_cast Finset.card_pos.mpr hXne
      exact mul_pos (mul_pos (by norm_num) hdelta) hcard)) (pow_pos (by decide) _)
  have hPcompact : IsCompact P := by
    simpa [P] using isCompact_commonAssignmentFiberHull X J
      (initialRadius (n + 1) delta)
  have hPconvex : Convex ℝ P := convex_commonCellHull J _
  have hPzero : P ⊆ Metric.closedBall 0 (Real.sqrt (n + 1)) := by
    rw [show P = retainedConvexHull
      (retainedFiberUnion J
        (gridAssignmentFiberFinset X (initialRadius (n + 1) delta))) by
      simpa [P] using commonAssignmentFiberHull_eq_retainedConvexHull X J
        (initialRadius (n + 1) delta)]
    apply convexHull_min
    · intro x hx
      have hxOuter := (normalizedOuterCube_subset_closedBall (n + 1))
        (houterHull (subset_convexHull ℝ _ (retainedFiberUnion_subset
        (fun k _hk ↦ gridAssignmentFiberFinset_subset X _ k) hx
        )))
      simpa only [Nat.cast_add, Nat.cast_one] using hxOuter
    · exact convex_closedBall 0 _
  obtain ⟨C, representative, hrep, hcapCard, hchartCompact, hchartConvex,
      hchartInner, hchartOuter, hbase, hgraph⟩ :=
    exists_normalized_cap_window (by omega : 0 < n) hepsilon hdelta hdeltaOne
      hPcompact hPconvex hcenter hball hPzero hJ witness (fun k ↦ hwitness k |>.2)
  let T := AffineIsometryEquiv.constVAdd ℝ (EuclideanPoint (n + 1)) (-center)
  let w₀ : {k // k ∈ J} → EuclideanPoint (n + 1) := fun k ↦ T (witness k)
  let direction := normalizedDirection (w₀ representative)
  let R := representativeToLast direction
  let P' : Set (EuclideanPoint (n + 1)) := R '' (T '' P)
  let w' : {k // k ∈ J} → EuclideanPoint (n + 1) := fun k ↦ R (w₀ k)
  have hC : C.Nonempty := ⟨representative, hrep⟩
  have hCcard : 0 < C.card := Finset.card_pos.mpr hC
  have hXcube : (X : Set _) ⊆ GridPartition.normalizedCube (n + 1) := by
    intro x hx
    simpa [GridPartition.normalizedCube, normalizedOuterCube] using
      houterHull (subset_convexHull ℝ _ hx)
  have hJlt : J.card < 2 ^ (dyadicLevelCount delta + 1) :=
    card_lt_two_pow_dyadicLevelCount hdelta hdeltaOne
      (heavy_cell_card_lt_inv X
        (GridPartition.candidateGridIndices (n + 1) (initialRadius (n + 1) delta))
        (GridPartition.gridIndex (initialRadius (n + 1) delta)) hdelta hXne
        hJcells (fun x hx ↦ GridPartition.gridIndex_mem_candidateGridIndices
          (by simp [initialRadius]; positivity) (hXcube hx)) hheavy)
  have hClt : C.card < 2 ^ (dyadicLevelCount delta + 1) := by
    have hCJ : C.card ≤ J.card := by
      simpa using Finset.card_le_card (Finset.subset_univ C)
    exact hCJ.trans_lt hJlt
  have hbase' : ∀ k ∈ C, ‖baseCoordinates (w' k)‖ ≤ q := by
    simpa [w', w₀, R, direction, T, q] using hbase
  have hgraph' : ∀ k ∈ C, w' k = upperBoundaryPoint
      P' hchartCompact (baseCoordinates (w' k)) := by
    simpa [w', w₀, R, direction, T, P'] using hgraph
  obtain ⟨j₂, hj₂, hI, hmass₂, hpoint₂, hoccupied,
      ⟨v, hv, p, hp, hw, hWconvex, hcount, hvol⟩,
      ⟨vHigh, hvHigh, hpHigh, hwHigh, hWHighConvex, hcountHigh, hvolHigh⟩⟩ :=
    exists_relativeShell_indexed_normalizedGraphSlab_nd hn hm hmMargin
      hchartCompact hchartConvex hq
      (normalizedLargeHullInradius_pos (by omega : 0 < n + 1) hdelta).le houter
      (two_mul_normalizedGraphWindowRadius_le (by omega) hdelta)
      hchartInner hchartOuter C w' hbase' hgraph' hC
      (dyadicLevelCount delta) (by simpa using hClt)
  let z : {k // k ∈ J} → EuclideanPoint (n + 1) :=
    fun k ↦ normalizeGraphPoint q outer (w' k)
  let I := RelativeDyadicCells.relativeShell
    (Finset.univ : Finset (Fin n → Fin m))
    (fun u ↦ (unitAssignedLabels hm C z u).card) 1 j₂
  let Kabs := 2 ^ j₂
  let K := relativeGraphOccupancy n m C.card Kabs
  have hIcard : 0 < I.card := Finset.card_pos.mpr (by simpa [I, z] using hI)
  have hKabs : 0 < Kabs := pow_pos (by decide) _
  have hK : 0 < K := relativeGraphOccupancy_pos hm hCcard hKabs
  have hupper₂ : RelativeDyadicCells.shellWeight
      (Finset.univ : Finset (Fin n → Fin m))
      (fun u ↦ (unitAssignedLabels hm C z u).card) 1 j₂ ≤
      2 * Kabs * I.card := by
    simpa [I, Kabs, pow_succ, mul_assoc, mul_left_comm, mul_comm] using
      RelativeDyadicCells.shell_weight_le_upper_mul_card
        (Finset.univ : Finset (Fin n → Fin m))
        (fun u ↦ (unitAssignedLabels hm C z u).card) 1 j₂ (by decide)
  have hsecond : C.card ≤ 2 * L * Kabs * I.card := by
    apply second_shell_uniform_mass (L := L)
    · simpa [L, I, z] using hmass₂
    · exact hupper₂
  have hhalf : (1 / 2 : ℝ) ≤ K * branchLogScale delta := by
    have hIuniv : I.card ≤ m ^ n := by
      calc
        I.card ≤ (Finset.univ : Finset (Fin n → Fin m)).card := by
          exact Finset.card_le_card (by simp [I, RelativeDyadicCells.relativeShell])
        _ = m ^ n := by simp
    simpa [K, L, branchLogScale] using
      half_le_relativeGraphOccupancy_mul hm hCcard hKabs (by simp [L])
        hIuniv hsecond
  obtain ⟨hlowClosure, hhighClosure⟩ := hclosure K hK hhalf
  have hRadius0 : 0 ≤ normalizedChartFiberRadius (n + 1) epsilon delta := by
    rw [normalizedChartFiberRadius]
    have hi : 0 ≤ initialRadius (n + 1) delta := by
      simp only [initialRadius]
      positivity
    have hqinv : 0 ≤ (2 * normalizedGraphWindowRadius (n + 1) epsilon delta)⁻¹ :=
      inv_nonneg.mpr (by positivity)
    have hoinv : 0 ≤ (normalizedCommonHullOuterRadius (n + 1))⁻¹ :=
      inv_nonneg.mpr houter.le
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (mul_nonneg (Real.sqrt_nonneg _) (div_nonneg hi (by norm_num))))
      (add_nonneg hqinv hoinv)
  have hRadiusCell : normalizedChartFiberRadius (n + 1) epsilon delta ≤
      1 / (m : ℝ) := by
    calc
      _ ≤ 1 / (m : ℝ) ^ (2 : ℕ) := by simpa [m] using hradius
      _ ≤ 1 / (m : ℝ) := by
        rw [div_le_div_iff_of_pos_left zero_lt_one
          (pow_pos (by exact_mod_cast hm : (0 : ℝ) < m) 2)
          (by exact_mod_cast hm : (0 : ℝ) < m)]
        have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast hm
        nlinarith
  have hfirstUpper : RelativeDyadicCells.shellWeight
      (GridPartition.candidateGridIndices (n + 1) (initialRadius (n + 1) delta))
      (DyadicCells.occupancy X (GridPartition.gridIndex (initialRadius (n + 1) delta)))
      (initialOccupancyCutoff delta X.card) j₁ ≤ 2 * M * J.card := by
    simpa [M, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hupper₁
  have hfirst : X.card ≤ 4 * L * M * J.card :=
    first_shell_uniform_mass hmass₁ hfirstUpper
  have hcap : capFractionCoefficient n outer * q ^ n * J.card ≤ C.card := by
    rw [← roundedCapFractionLower_eq (by omega : 0 < n) hq houter]
    simpa [q, outer] using hcapCard
  have hcaptured : capturedFraction (n + 1)
      (normalizedCaptureCoefficient n outer) q K s (branchLogScale delta) *
        (X.card : ℝ) ≤ (Kabs * M : ℕ) := by
    have hrnd := capturedFraction_realScale_le_integral (by omega : 0 < n)
      houter hq hK hs (branchLogScale_pos delta) (by exact_mod_cast hm) hms
    calc
      _ ≤ ((capFractionCoefficient n outer / 4) * q ^ n * K /
          ((m : ℝ) ^ n * branchLogScale delta)) * X.card := by
        exact mul_le_mul_of_nonneg_right hrnd (Nat.cast_nonneg _)
      _ ≤ (Kabs * M : ℕ) := by
        simpa [K, L, branchLogScale] using capturedFraction_le_selected_mass
          (N := X.card) (M := M) (labels := J.card) (capCard := C.card)
          (Kabs := Kabs) (n := n) (m := m) (c := capFractionCoefficient n outer)
          (q := q) (L := L) (Finset.card_pos.mpr hXne) (by simp [L]) hm
          (Finset.card_pos.mpr hJ) hCcard hKabs
          (capFractionCoefficient_pos (by omega) houter).le hq.le hfirst hcap
  by_cases hKsmall : K ≤ s ^ alpha (n + 1)
  · obtain ⟨hEta, hDensity⟩ := hlowClosure (by simpa [s] using hKsmall)
    rw [← hqWidth] at hEta hDensity
    let eta := etaLow (n + 1)
      (normalizedBranchVolumeCoefficient n outer)
      q K s (branchLogScale delta)
    let epsGraph := 4 * ((n : ℝ) + 1) ^ 4 * (m : ℝ) ^ (n - 2) /
      ((1 / 2 : ℝ) * (I.card : ℝ))
    let affine := reflectedTangentAffine
      (fun x ↦ 1 - normalizedUpperRoof P' hchartCompact q outer x)
      (Subgradient.pzFinGridPoint v) p
    let W := affineGraphSlab (graphBaseCellND v) affine epsGraph
    let S := indexedLabelsOverCellND C z v
    have heps : epsGraph ≤ 32 * ((n : ℝ) + 1) ^ 4 * K *
        branchLogScale delta / s ^ (2 : ℕ) := by
      calc
        epsGraph ≤ 32 * ((n : ℝ) + 1) ^ 4 * K * L /
            (m : ℝ) ^ (2 : ℕ) := by
          simpa [epsGraph, K, L, I, z] using
            lowGraphEpsilon_le hn hm hCcard hKabs (by simp [L]) hIcard hsecond
        _ ≤ 32 * ((n : ℝ) + 1) ^ 4 * K * L / s ^ (2 : ℕ) := by
          gcongr
        _ = _ := by simp [L, branchLogScale]
    have heps0 : 0 ≤ epsGraph := by
      dsimp only [epsGraph]
      exact div_nonneg (by positivity) (by positivity)
    have hcost := graphThickeningCost_le_etaLow
      (epsilon := epsGraph)
      (r := normalizedChartFiberRadius (n + 1) epsilon delta)
      (slope := 4) (m := (m : ℝ))
      (by omega : 0 < n) hq houter
      hs hsm hK (branchLogScale_pos delta) hhalf heps0 heps
      hRadius0 (by
        calc
          normalizedChartFiberRadius (n + 1) epsilon delta ≤
              1 / (m : ℝ) ^ (2 : ℕ) := by simpa [m] using hradius
          _ ≤ 1 / s ^ (2 : ℕ) := by
            rw [div_le_div_iff_of_pos_left zero_lt_one
              (pow_pos (by exact_mod_cast hm : (0 : ℝ) < m) 2)
              (pow_pos hs 2)]
            exact pow_le_pow_left₀ hs.le hsm 2)
      (by norm_num) (by norm_num)
    have hnorm : volume (minkowskiClosedBall W
        (normalizedChartFiberRadius (n + 1) epsilon delta)) *
          ENNReal.ofReal ((2 * q) ^ n * outer) ≤
        ENNReal.ofReal eta * ENNReal.ofReal (normalizedBranchInnerVolume n) := by
      calc
        _ ≤ ENNReal.ofReal (graphThickeningCost n q outer m epsGraph
            (normalizedChartFiberRadius (n + 1) epsilon delta) 4) := by
          simpa only [W, graphBaseCellND] using
            volume_graphCell_thickening_mul_reference_le hq.le houter.le
              (by exact_mod_cast hm) heps0 hRadius0 (by norm_num)
              hRadiusCell
              (Subgradient.pzFinGridPoint v) affine
              (by
                intro i
                have hi := hp i
                simpa [affine, affineCoordinateCoefficient,
                  reflectedTangentAffine, coordinate] using hi)
        _ ≤ ENNReal.ofReal
            (eta * normalizedBranchInnerVolume n) := by
          apply ENNReal.ofReal_le_ofReal
          simpa [eta, outer, q, s, branchLogScale,
            etaLow_branch_mul_inner] using hcost
        _ = _ := by
          apply ENNReal.ofReal_mul
          exact hdelta.le.trans (by simpa [eta, q, outer, s] using hEta.1)
    have hsum : (Kabs * M : ℕ) ≤
        ∑ i ∈ S, (gridAssignmentFiberFinset X (initialRadius (n + 1) delta) i.1).card := by
      calc
        Kabs * M ≤ S.card * M := Nat.mul_le_mul_right M hcount
        _ = ∑ _i ∈ S, M := by simp [mul_comm]
        _ ≤ ∑ i ∈ S,
            (gridAssignmentFiberFinset X (initialRadius (n + 1) delta) i.1).card := by
          apply Finset.sum_le_sum
          intro i hi
          simpa [card_gridAssignmentFiberFinset] using hlower₁ i.1 i.2
    apply convexDensityOutput_of_normalizedGraphSlab
      (S := S) (W := W)
      (mesh := initialRadius (n + 1) delta)
      (rho := Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (initialRadius (n + 1) delta / 2))
      (r := normalizedChartFiberRadius (n + 1) epsilon delta)
      (by omega : 0 < n) hq houter
      center direction
      (by simpa [eta, q, outer, s] using hEta)
      (hdelta.le.trans (by simpa [eta, q, outer, s] using hEta.1))
      (isConvexBody_convexHull_of_normalizedInnerCube_subset hinner)
      (subset_convexHull ℝ _) hinner hWconvex
    · intro i hi
      have hwi : lastCoordinateCLE n (z i) ∈ W := by
        exact hw i (by simpa only [S] using hi)
      rw [show centeredGraphWindowAffineEquiv center direction q outer
          hq.ne' houter.ne' (witness i) = z i by
        simp [z, w', w₀, R, direction, T,
          centeredGraphWindowAffineEquiv, centeredHouseholderEquiv,
          graphWindowAffineEquiv_apply, sub_eq_add_neg]]
      exact hwi
    · intro i hi x hx
      exact dist_gridAssignmentFiberFinset_witness_le
        (by simp [initialRadius]; positivity) hXcube le_rfl hx (hwitness i).1
    · simpa [q, outer, normalizedChartFiberRadius] using le_rfl
    · exact hnorm
    · calc
        eta ^ densityExponent (n + 1) epsilon * X.card ≤
            capturedFraction (n + 1) (normalizedCaptureCoefficient n outer)
              q K s (branchLogScale delta) * X.card := by
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
          exact hDensity
        _ ≤ (Kabs * M : ℕ) := hcaptured
        _ ≤ _ := Nat.cast_le.mpr hsum
  · have hKlarge : s ^ alpha (n + 1) ≤ K := le_of_not_ge hKsmall
    obtain ⟨hEta, hDensity⟩ := hhighClosure (by simpa [s] using hKlarge)
    rw [← hqWidth] at hEta hDensity
    let eta := etaHigh (n + 1)
      (normalizedBranchVolumeCoefficient n outer) q s
    have heta0 : 0 ≤ eta := hdelta.le.trans hEta.1
    let epsGraph := (n : ℝ) / ((1 / 2 : ℝ) * (m : ℝ))
    let affine := AffineMap.const ℝ (EuclideanPoint n)
      (normalizedUpperRoof P' hchartCompact q outer
        (Subgradient.pzFinGridPoint vHigh))
    let W := affineGraphSlab (graphBaseCellND vHigh) affine epsGraph
    let S := indexedLabelsOverCellND C z vHigh
    have heps0 : 0 ≤ epsGraph := by
      dsimp only [epsGraph]
      exact div_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
    have hrS : normalizedChartFiberRadius (n + 1) epsilon delta ≤
        1 / s ^ (2 : ℕ) := by
      calc
        _ ≤ 1 / (m : ℝ) ^ (2 : ℕ) := by simpa [m] using hradius
        _ ≤ 1 / s ^ (2 : ℕ) := by
          rw [div_le_div_iff_of_pos_left zero_lt_one
            (pow_pos (by exact_mod_cast hm : (0 : ℝ) < m) 2)
            (pow_pos hs 2)]
          exact pow_le_pow_left₀ hs.le hsm 2
    have hcost := graphThickeningCost_le_etaHigh
      (epsilon := epsGraph)
      (r := normalizedChartFiberRadius (n + 1) epsilon delta)
      (m := (m : ℝ)) (by omega : 0 < n) hq houter hs hsOne hsm
      heps0 (highGraphEpsilon_le (n := n) (m := m) (s := s) hm hs hsm)
      hRadius0 hrS
    have hnorm : volume (minkowskiClosedBall W
        (normalizedChartFiberRadius (n + 1) epsilon delta)) *
          ENNReal.ofReal ((2 * q) ^ n * outer) ≤
        ENNReal.ofReal eta * ENNReal.ofReal (normalizedBranchInnerVolume n) := by
      calc
        _ ≤ ENNReal.ofReal (graphThickeningCost n q outer m epsGraph
            (normalizedChartFiberRadius (n + 1) epsilon delta) 0) := by
          simpa [W, epsGraph, affine, graphBaseCellND,
            Subgradient.pzFinGridPoint] using
            volume_graphCell_thickening_mul_reference_le hq.le houter.le
              (by exact_mod_cast hm) heps0 hRadius0 (by norm_num)
              hRadiusCell
              (Subgradient.pzFinGridPoint vHigh) affine
              (by
                intro i
                simp [affine, affineCoordinateCoefficient])
        _ ≤ ENNReal.ofReal (eta * normalizedBranchInnerVolume n) := by
          apply ENNReal.ofReal_le_ofReal
          exact hcost.trans_eq (etaHigh_branch_mul_inner (n := n)
            (outer := outer) (q := q) (s := s)).symm
        _ = _ := ENNReal.ofReal_mul heta0
    have hsum : (Kabs * M : ℕ) ≤
        ∑ i ∈ S, (gridAssignmentFiberFinset X (initialRadius (n + 1) delta) i.1).card := by
      calc
        Kabs * M ≤ S.card * M := Nat.mul_le_mul_right M hcountHigh
        _ = ∑ _i ∈ S, M := by simp [mul_comm]
        _ ≤ ∑ i ∈ S,
            (gridAssignmentFiberFinset X (initialRadius (n + 1) delta) i.1).card := by
          apply Finset.sum_le_sum
          intro i hi
          simpa [card_gridAssignmentFiberFinset] using hlower₁ i.1 i.2
    apply convexDensityOutput_of_normalizedGraphSlab
      (S := S) (W := W)
      (mesh := initialRadius (n + 1) delta)
      (rho := Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (initialRadius (n + 1) delta / 2))
      (r := normalizedChartFiberRadius (n + 1) epsilon delta)
      (by omega : 0 < n) hq houter center direction
      (by simpa [eta, q, outer, s] using hEta)
      (hdelta.le.trans (by simpa [eta, q, outer, s] using hEta.1))
      (isConvexBody_convexHull_of_normalizedInnerCube_subset hinner)
      (subset_convexHull ℝ _) hinner hWHighConvex
    · intro i hi
      have hwi : lastCoordinateCLE n (z i) ∈ W := by
        exact hwHigh i (by simpa only [S] using hi)
      rw [show centeredGraphWindowAffineEquiv center direction q outer
          hq.ne' houter.ne' (witness i) = z i by
        simp [z, w', w₀, R, direction, T,
          centeredGraphWindowAffineEquiv, centeredHouseholderEquiv,
          graphWindowAffineEquiv_apply, sub_eq_add_neg]]
      exact hwi
    · intro i hi x hx
      exact dist_gridAssignmentFiberFinset_witness_le
        (by simp [initialRadius]; positivity) hXcube le_rfl hx (hwitness i).1
    · simpa [q, outer, normalizedChartFiberRadius] using le_rfl
    · exact hnorm
    · calc
        eta ^ densityExponent (n + 1) epsilon * X.card ≤
            capturedFraction (n + 1) (normalizedCaptureCoefficient n outer)
              q K s (branchLogScale delta) * X.card := by
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
          exact hDensity
        _ ≤ (Kabs * M : ℕ) := hcaptured
        _ ≤ _ := Nat.cast_le.mpr hsum

end
end Erdos186.PZ.ConvexDensity
