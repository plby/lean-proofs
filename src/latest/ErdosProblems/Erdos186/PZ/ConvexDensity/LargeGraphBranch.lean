/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.BranchAssembly
import ErdosProblems.Erdos186.PZ.ConvexDensity.CenteredBoundary
import ErdosProblems.Erdos186.PZ.ConvexDensity.GraphOscillation
import ErdosProblems.Erdos186.PZ.ConvexDensity.IndexedGraphDensity

/-! # The normalized indexed-graph middle of the large-hull branch -/

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace Erdos186.PZ.ConvexDensity

set_option autoImplicit false
noncomputable section

open Subgradient Erdos186.ConvexApprox

/-- The cap step, with an arbitrary inball centre, produces precisely the
physical upper-boundary window consumed by the normalized graph theorems
below.  The returned chart is the single centred Householder affine isometry,
so it can later be composed with `graphWindowAffineEquiv` and transported
back by `convexDensityOutput_of_affineChart_disjointFibers`. -/
theorem exists_cap_centered_upperBoundary_window
    {ι : Type*} [DecidableEq ι] {n m : ℕ}
    (hm : 0 < m) (hmLarge : 4 * Real.sqrt n ≤ m)
    {inner outer q : ℝ} (hinner : 0 < inner) (hqinner : q < inner)
    (hcapWindow : outer * (2 * Real.sqrt n / m) ≤ q)
    {P : Set (EuclideanPoint (n + 1))}
    (hPcompact : IsCompact P) (hPconvex : Convex ℝ P)
    {center : EuclideanPoint (n + 1)}
    (hinnerBall : Metric.closedBall center inner ⊆ P)
    (houterBall : P ⊆ Metric.closedBall center outer)
    (I : Finset ι) (hI : I.Nonempty)
    (witness : ι → EuclideanPoint (n + 1))
    (hfrontier : ∀ i ∈ I, witness i ∈ frontier P)
    (hannulus : ∀ i ∈ I,
      inner ≤ dist (witness i) center ∧ dist (witness i) center ≤ outer) :
    ∃ (J : Finset ι) (representative : ι),
      representative ∈ J ∧ J ⊆ I ∧
      ((((m : ℝ)⁻¹ / 3) ^ n) / (2 * (n + 1))) * I.card ≤ J.card ∧
      let T := AffineIsometryEquiv.constVAdd ℝ
        (EuclideanPoint (n + 1)) (-center)
      let w0 : ι → EuclideanPoint (n + 1) := fun i ↦ T (witness i)
      let R := representativeToLast (normalizedDirection (w0 representative))
      let P' := R '' (T '' P)
      IsCompact P' ∧ Convex ℝ P' ∧
      Metric.closedBall 0 inner ⊆ P' ∧
      P' ⊆ Metric.closedBall 0 outer ∧
      (∀ j ∈ J, ‖baseCoordinates (R (w0 j))‖ ≤ q) ∧
      ∀ j ∈ J,
        R (w0 j) = upperBoundaryPoint P'
          ((hPcompact.image T.continuous).image R.continuous)
          (baseCoordinates (R (w0 j))) := by
  let T := AffineIsometryEquiv.constVAdd ℝ (EuclideanPoint (n + 1)) (-center)
  let P0 : Set (EuclideanPoint (n + 1)) := T '' P
  let w0 : ι → EuclideanPoint (n + 1) := fun i ↦ T (witness i)
  have hP0compact : IsCompact P0 := hPcompact.image T.continuous
  have hP0convex : Convex ℝ P0 :=
    hPconvex.affine_image T.toAffineEquiv.toAffineMap
  have hP0inner : Metric.closedBall 0 inner ⊆ P0 := by
    intro y hy
    refine ⟨y + center, hinnerBall ?_, ?_⟩
    · simpa [Metric.mem_closedBall, dist_eq_norm] using hy
    · simp [T, sub_eq_add_neg, add_assoc]
  have hP0outer : P0 ⊆ Metric.closedBall 0 outer := by
    rintro y ⟨x, hx, rfl⟩
    have hxball := houterBall hx
    rw [Metric.mem_closedBall]
    calc
      dist (T x) 0 = dist (T x) (T center) := by simp [T]
      _ = dist x center := T.isometry.dist_eq x center
      _ ≤ outer := by simpa [Metric.mem_closedBall] using hxball
  have hfrontier0 : ∀ i ∈ I, w0 i ∈ frontier P0 := by
    intro i hi
    change T.toHomeomorph (witness i) ∈
      frontier (T.toHomeomorph '' P)
    rw [← T.toHomeomorph.image_frontier]
    exact ⟨witness i, hfrontier i hi, rfl⟩
  have hannulus0 : ∀ i ∈ I, w0 i ∈ boundedAnnulus inner outer := by
    intro i hi
    simpa [boundedAnnulus, w0, T, dist_eq_norm, sub_eq_add_neg,
      add_comm] using hannulus i hi
  have hsmall : outer * (2 * Real.sqrt n / m) < inner :=
    hcapWindow.trans_lt hqinner
  obtain ⟨_cap, J, representative, hrep, hJI, hcard, hcap,
      hchartCompact, hchartConvex, hchartInner, hchartGraph⟩ :=
    exists_large_indexed_cap_upperBoundary_chart hm hmLarge hinner hsmall
      hP0compact hP0convex hP0inner I hI w0 hfrontier0 hannulus0
  let R := representativeToLast (normalizedDirection (w0 representative))
  let P' : Set (EuclideanPoint (n + 1)) := R '' P0
  have hP'outer : P' ⊆ Metric.closedBall 0 outer := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hx' := hP0outer hx
    rw [Metric.mem_closedBall]
    calc
      dist (R x) 0 = dist (R x) (R 0) := by simp
      _ = dist x 0 := R.isometry.dist_eq x 0
      _ ≤ outer := by simpa [Metric.mem_closedBall] using hx'
  refine ⟨J, representative, hrep, hJI, hcard, ?_, ?_, ?_,
    hP'outer, ?_, ?_⟩
  · simpa [P', R, P0, T, w0] using hchartCompact
  · simpa [P', R, P0, T, w0] using hchartConvex
  · simpa [P', R, P0, T, w0] using hchartInner
  · intro j hj
    have hbounds := householder_annulus_base_last_bounds hm hmLarge hinner
      (hannulus0 representative (hJI hrep)) (hannulus0 j (hJI hj))
      (hcap representative hrep) (hcap j hj)
    exact hbounds.1.trans hcapWindow
  · intro j hj
    simpa [P', R, P0, T, w0] using (hchartGraph j hj).2.2.2

/-- Physical upper-boundary witnesses in a radius-`q` base window pass,
without label deduplication, through the second relative dyadic
regularization and the exact higher-dimensional graph approximation theorem.

This theorem is the complete middle of the `d ≥ 3` large-hull branch. -/
theorem exists_relativeShell_indexed_normalizedGraphSlab_nd
    {ι : Type*} [DecidableEq ι] {n m : ℕ}
    (hn : 2 ≤ n) (hm : 0 < m)
    (hmargin : 4 * ((n : ℝ) + 1) < (m : ℝ))
    {P : Set (EuclideanPoint (n + 1))}
    (hPcompact : IsCompact P) (hPconvex : Convex ℝ P)
    {inner outer q : ℝ} (hq : 0 < q) (hinner : 0 ≤ inner)
    (houter : 0 < outer)
    (hwindow : 2 * q ≤ inner / Real.sqrt (n : ℝ))
    (hinnerBall : Metric.closedBall 0 inner ⊆ P)
    (houterBall : P ⊆ Metric.closedBall 0 outer)
    (J : Finset ι) (witness : ι → EuclideanPoint (n + 1))
    (hbase : ∀ i ∈ J, ‖baseCoordinates (witness i)‖ ≤ q)
    (hgraphPhysical : ∀ i ∈ J,
      witness i = upperBoundaryPoint P hPcompact
        (baseCoordinates (witness i)))
    (hJ : J.Nonempty)
    (L : ℕ) (hupper : J.card < 2 ^ (L + 1)) :
    ∃ j < L + 1,
      let z : ι → EuclideanPoint (n + 1) :=
        fun i ↦ normalizeGraphPoint q outer (witness i)
      let I := RelativeDyadicCells.relativeShell
        (Finset.univ : Finset (Fin n → Fin m))
        (fun v ↦ (unitAssignedLabels hm J z v).card) 1 j
      I.Nonempty ∧
      J.card ≤ (L + 1) *
        RelativeDyadicCells.shellWeight
          (Finset.univ : Finset (Fin n → Fin m))
          (fun v ↦ (unitAssignedLabels hm J z v).card) 1 j ∧
      (∀ u ∈ I, (unitAssignedLabels hm J z u).card < 2 ^ (j + 1)) ∧
      (∀ u ∈ I, 2 ^ j ≤ (indexedLabelsOverCellND J z u).card) ∧
      (∃ v ∈ I, ∃ p : Fin n → ℝ,
        let epsilon :=
          4 * ((n : ℝ) + 1) ^ 4 * (m : ℝ) ^ (n - 2) /
            ((1 / 2 : ℝ) * (I.card : ℝ))
        let affine := reflectedTangentAffine
          (fun x ↦ 1 - normalizedUpperRoof P hPcompact q outer x)
          (pzFinGridPoint v) p
        let slab := affineGraphSlab (graphBaseCellND v) affine epsilon
        (∀ i, |p i| ≤ 4) ∧
          (∀ i ∈ indexedLabelsOverCellND J z v,
            lastCoordinateCLE n (z i) ∈ slab) ∧
          Convex ℝ slab ∧
          2 ^ j ≤ (indexedLabelsOverCellND J z v).card ∧
          volume slab =
            (∏ _i : Fin n, ENNReal.ofReal ((m : ℝ)⁻¹)) *
              ENNReal.ofReal (2 * epsilon)) ∧
      (∃ v ∈ I,
        let epsilon := (n : ℝ) / ((1 / 2 : ℝ) * (m : ℝ))
        let affine := AffineMap.const ℝ (EuclideanPoint n)
          (normalizedUpperRoof P hPcompact q outer (pzFinGridPoint v))
        let slab := affineGraphSlab (graphBaseCellND v) affine epsilon
        (∀ i, |affineCoordinateCoefficient affine i| ≤ 0) ∧
          (∀ i ∈ indexedLabelsOverCellND J z v,
            lastCoordinateCLE n (z i) ∈ slab) ∧
          Convex ℝ slab ∧
          2 ^ j ≤ (indexedLabelsOverCellND J z v).card ∧
          volume slab =
            (∏ _i : Fin n, ENNReal.ofReal ((m : ℝ)⁻¹)) *
              ENNReal.ofReal (2 * epsilon)) := by
  let z : ι → EuclideanPoint (n + 1) :=
    fun i ↦ normalizeGraphPoint q outer (witness i)
  have hunit : ∀ i ∈ J, ∀ k,
      coordinate (baseCoordinates (z i)) k ∈ Set.Icc (0 : ℝ) 1 := by
    intro i hi k
    have habs : |coordinate (baseCoordinates (witness i)) k| ≤ q :=
      (abs_coordinate_le_norm _ _).trans (hbase i hi)
    have hdenom : 0 < 2 * q := by positivity
    dsimp only [z]
    rw [baseCoordinates_normalizeGraphPoint]
    change (coordinate (baseCoordinates (witness i)) k + q) / (2 * q) ∈
      Set.Icc (0 : ℝ) 1
    constructor
    · exact div_nonneg (by linarith [(abs_le.mp habs).1]) hdenom.le
    · exact (div_le_one hdenom).2 (by linarith [(abs_le.mp habs).2])
  obtain ⟨j, hj, hI, hmass, hpointwise, hoccupied⟩ :=
    exists_unitGraphGrid_occupied_shell hm J z hunit L hJ hupper
  let I := RelativeDyadicCells.relativeShell
    (Finset.univ : Finset (Fin n → Fin m))
    (fun v ↦ (unitAssignedLabels hm J z v).card) 1 j
  have hroof := normalizedUpperRoof_concave_range (by omega) hPcompact hPconvex
    hq.le hinner houter hwindow hinnerBall houterBall
  have hgraph : ∀ i ∈ J,
      lastCoordinate (z i) =
        normalizedUpperRoof P hPcompact q outer
          (WithLp.ofLp (baseCoordinates (z i))) := by
    intro i hi
    exact normalizeGraphPoint_on_normalizedUpperRoof hPcompact hq houter
      (hgraphPhysical i hi)
  have hc : 2 * ((n : ℝ) + 1) / (m : ℝ) < (1 / 2 : ℝ) := by
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    rw [div_lt_iff₀ hmR]
    nlinarith
  obtain ⟨v, hvI, p, hp, hwitness, hconvex, hcount, hvolume⟩ :=
    exists_indexed_upperBoundary_affine_slab_nd hn hm hc hroof.1 hroof.2
      J z hgraph I hI hoccupied
  obtain ⟨vHigh, hvHighI, hpHigh, hwitnessHigh, hconvexHigh,
      hcountHigh, hvolumeHigh⟩ :=
    exists_indexed_upperBoundary_constant_slab_high (by omega) hm
      (c := (1 / 2 : ℝ)) (by norm_num) hroof.1 hroof.2
      J z hgraph I hI hoccupied
  refine ⟨j, hj, hI, hmass, (fun u hu ↦ (hpointwise u hu).2),
    hoccupied, ?_, ?_⟩
  · refine ⟨v, hvI, p, ?_, hwitness, hconvex, hcount, hvolume⟩
    intro i
    norm_num at hp ⊢
    exact hp i
  · exact ⟨vHigh, hvHighI, hpHigh, hwitnessHigh, hconvexHigh,
      hcountHigh, hvolumeHigh⟩

/-- Planar counterpart of
`exists_relativeShell_indexed_normalizedGraphSlab_nd`, using natural-number
cell labels throughout so that it feeds the sharp one-dimensional secant
approximation without any quotient or deduplication step. -/
theorem exists_relativeShell_indexed_normalizedGraphSlab_2d
    {ι : Type*} [DecidableEq ι] {m : ℕ}
    (hm : 0 < m) (hmargin : 2 < m)
    {P : Set (EuclideanPoint 2)}
    (hPcompact : IsCompact P) (hPconvex : Convex ℝ P)
    {inner outer q : ℝ} (hq : 0 < q) (hinner : 0 ≤ inner)
    (houter : 0 < outer)
    (hwindow : 2 * q ≤ inner / Real.sqrt (((1 : ℕ) : ℝ)))
    (hinnerBall : Metric.closedBall 0 inner ⊆ P)
    (houterBall : P ⊆ Metric.closedBall 0 outer)
    (J : Finset ι) (witness : ι → EuclideanPoint 2)
    (hbase : ∀ i ∈ J, ‖baseCoordinates (witness i)‖ ≤ q)
    (hgraphPhysical : ∀ i ∈ J,
      witness i = upperBoundaryPoint P hPcompact
        (baseCoordinates (witness i)))
    (hJ : J.Nonempty)
    (L : ℕ) (hupper : J.card < 2 ^ (L + 1)) :
    ∃ j < L + 1,
      let z : ι → EuclideanPoint 2 :=
        fun i ↦ normalizeGraphPoint q outer (witness i)
      let I := RelativeDyadicCells.relativeShell (Finset.range m)
        (fun k ↦ (unitAssignedLabels1D m hm J z k).card) 1 j
      I.Nonempty ∧ I ⊆ Finset.range m ∧
      J.card ≤ (L + 1) *
        RelativeDyadicCells.shellWeight (Finset.range m)
          (fun k ↦ (unitAssignedLabels1D m hm J z k).card) 1 j ∧
      (∀ u ∈ I, (unitAssignedLabels1D m hm J z u).card < 2 ^ (j + 1)) ∧
      (∀ u ∈ I, 2 ^ j ≤ (indexedLabelsOverCell1D J z m u).card) ∧
      (∃ k ∈ I,
        let h : ℝ → ℝ := fun t ↦ normalizedUpperRoof P hPcompact q outer
          (fun _ : Fin 1 ↦ t)
        let epsilon := 2 / ((1 / 2 : ℝ) * (m : ℝ) * (I.card : ℝ))
        let affine := graphCellSecant h m k
        let slab := affineGraphSlab (graphBaseCell m k) affine epsilon
        (∀ i, |affineCoordinateCoefficient affine i| ≤ 2) ∧
          (∀ i ∈ indexedLabelsOverCell1D J z m k,
            lastCoordinateCLE 1 (z i) ∈ slab) ∧
          Convex ℝ slab ∧
          2 ^ j ≤ (indexedLabelsOverCell1D J z m k).card ∧
          volume slab = ENNReal.ofReal ((m : ℝ)⁻¹) *
            ENNReal.ofReal
              (4 / ((1 / 2 : ℝ) * (m : ℝ) * (I.card : ℝ)))) ∧
      (∃ k ∈ I,
        let h : ℝ → ℝ := fun t ↦ normalizedUpperRoof P hPcompact q outer
          (fun _ : Fin 1 ↦ t)
        let epsilon := 1 / ((1 / 2 : ℝ) * (m : ℝ))
        let affine := AffineMap.const ℝ (EuclideanPoint 1) (h (gridPoint m k))
        let slab := affineGraphSlab (graphBaseCell m k) affine epsilon
        (∀ i, |affineCoordinateCoefficient affine i| ≤ 0) ∧
          (∀ i ∈ indexedLabelsOverCell1D J z m k,
            lastCoordinateCLE 1 (z i) ∈ slab) ∧
          Convex ℝ slab ∧
          2 ^ j ≤ (indexedLabelsOverCell1D J z m k).card ∧
          volume slab = ENNReal.ofReal ((m : ℝ)⁻¹) *
            ENNReal.ofReal (2 * epsilon)) := by
  let z : ι → EuclideanPoint 2 :=
    fun i ↦ normalizeGraphPoint q outer (witness i)
  have hunit : ∀ i ∈ J,
      coordinate (baseCoordinates (z i)) 0 ∈ Set.Icc (0 : ℝ) 1 := by
    intro i hi
    have habs : |coordinate (baseCoordinates (witness i)) 0| ≤ q :=
      (abs_coordinate_le_norm _ _).trans (hbase i hi)
    have hdenom : 0 < 2 * q := by positivity
    dsimp only [z]
    rw [baseCoordinates_normalizeGraphPoint]
    change (coordinate (baseCoordinates (witness i)) 0 + q) / (2 * q) ∈
      Set.Icc (0 : ℝ) 1
    constructor
    · exact div_nonneg (by linarith [(abs_le.mp habs).1]) hdenom.le
    · exact (div_le_one hdenom).2 (by linarith [(abs_le.mp habs).2])
  obtain ⟨j, hj, hI, hIrange, hmass, hpointwise, hoccupied⟩ :=
    exists_unitGraphGrid_occupied_shell_2d hm J z hunit L hJ hupper
  let I := RelativeDyadicCells.relativeShell (Finset.range m)
    (fun k ↦ (unitAssignedLabels1D m hm J z k).card) 1 j
  let roof := normalizedUpperRoof P hPcompact q outer
  let h : ℝ → ℝ := fun t ↦ roof (fun _ : Fin 1 ↦ t)
  have hroof := normalizedUpperRoof_concave_range (n := 1) (by omega)
    hPcompact hPconvex hq.le hinner houter hwindow hinnerBall houterBall
  have hconcave : ConcaveOn ℝ (Set.Icc (-(1 / 2 : ℝ)) (1 + 1 / 2)) h := by
    refine ⟨convex_Icc _ _, ?_⟩
    intro x hx y hy a b ha hb hab
    have hx' : (fun _ : Fin 1 ↦ x) ∈ pzExpandedBox 1 (1 / 2) := by
      exact ⟨fun _ ↦ hx.1, fun _ ↦ hx.2⟩
    have hy' : (fun _ : Fin 1 ↦ y) ∈ pzExpandedBox 1 (1 / 2) := by
      exact ⟨fun _ ↦ hy.1, fun _ ↦ hy.2⟩
    have hc := hroof.1.2 hx' hy' ha hb hab
    have heq : a • (fun _ : Fin 1 ↦ x) + b • (fun _ : Fin 1 ↦ y) =
        fun _ : Fin 1 ↦ a * x + b * y := by
      funext i
      simp [smul_eq_mul]
    rw [heq] at hc
    simpa [h, roof, smul_eq_mul] using hc
  have hrange : ∀ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 + 1 / 2),
      0 ≤ h t ∧ h t ≤ 1 := by
    intro t ht
    exact hroof.2 (fun _ : Fin 1 ↦ t)
      ⟨fun _ ↦ ht.1, fun _ ↦ ht.2⟩
  have hgraph : ∀ i ∈ J,
      lastCoordinate (z i) = h (coordinate (baseCoordinates (z i)) 0) := by
    intro i hi
    have hg := normalizeGraphPoint_on_normalizedUpperRoof hPcompact hq houter
      (hgraphPhysical i hi)
    dsimp only [z]
    rw [hg]
    dsimp only [h, roof]
    congr 1
    funext k
    rw [Subsingleton.elim k 0]
  have hc : (m : ℝ)⁻¹ < (1 / 2 : ℝ) := by
    have hmR : (2 : ℝ) < (m : ℝ) := by exact_mod_cast hmargin
    simpa [one_div] using
      (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 2) hmR)
  obtain ⟨k, hkI, hp, hwitness, hconvex, hcount, hvolume⟩ :=
    exists_indexed_upperBoundary_affine_slab_2d hm hc hconcave hrange
      J z hgraph I hI hIrange hoccupied
  obtain ⟨kHigh, hkHighI, hpHigh, hwitnessHigh, hconvexHigh,
      hcountHigh, hvolumeHigh⟩ :=
    exists_indexed_upperBoundary_constant_slab_high_2d hm
      (c := (1 / 2 : ℝ)) (by norm_num) hconcave hrange
      J z hgraph I hI hIrange hoccupied
  refine ⟨j, hj, hI, hIrange, hmass,
    (fun u hu ↦ (hpointwise u hu).2), hoccupied, ?_, ?_⟩
  · refine ⟨k, hkI, ?_, hwitness, hconvex, hcount, hvolume⟩
    intro i
    rw [Subsingleton.elim i 0]
    norm_num at hp ⊢
    exact hp
  · exact ⟨kHigh, hkHighI, hpHigh, hwitnessHigh, hconvexHigh,
      hcountHigh, hvolumeHigh⟩

end
end Erdos186.PZ.ConvexDensity
