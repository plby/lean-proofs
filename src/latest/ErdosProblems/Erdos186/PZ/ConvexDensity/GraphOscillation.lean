/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.IndexedGraphDensity
import ErdosProblems.Erdos186.PZ.ConvexDensity.Thickening

/-! # Oscillation of a bounded concave graph on one grid cell -/

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace Erdos186.PZ.ConvexDensity

set_option autoImplicit false
noncomputable section

open Subgradient Erdos186.ConvexApprox

/-- Moving a point of a unit grid cell by the full graph margin in either
coordinate direction remains in the expanded box. -/
theorem pzGridCell_full_coordinate_shifts_mem {n m : ℕ}
    (hm : 0 < m) {c : ℝ} (hc : 0 < c)
    {v : Fin n → Fin m} {x : Fin n → ℝ} (hx : x ∈ pzGridCell v)
    (i : Fin n) :
    x - c • Pi.single i 1 ∈ pzExpandedBox n c ∧
      x + c • Pi.single i 1 ∈ pzExpandedBox n c := by
  constructor
  · constructor <;> intro j
    · have hj := pzFinGridPoint_cell_le_one hm hx j
      by_cases hji : j = i
      · subst j
        simp
        linarith
      · simp [hji]
        linarith
    · have hj := pzFinGridPoint_cell_le_one hm hx j
      by_cases hji : j = i
      · subst j
        simp
        linarith
      · simp [hji]
        linarith
  · constructor <;> intro j
    · have hj := pzFinGridPoint_cell_le_one hm hx j
      by_cases hji : j = i
      · subst j
        simp
        linarith
      · simp [hji]
        linarith
    · have hj := pzFinGridPoint_cell_le_one hm hx j
      by_cases hji : j = i
      · subst j
        simp
        linarith
      · simp [hji]
        linarith

/-- Two points in the same unit grid cell differ by at most one mesh width
in every coordinate. -/
theorem abs_sub_le_inv_of_mem_same_pzGridCell {n m : ℕ}
    (hm : 0 < m) {v : Fin n → Fin m} {x y : Fin n → ℝ}
    (hx : x ∈ pzGridCell v) (hy : y ∈ pzGridCell v) (i : Fin n) :
    |y i - x i| ≤ (m : ℝ)⁻¹ := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hxlo := hx.1 i
  have hxhi := hx.2 i
  have hylo := hy.1 i
  have hyhi := hy.2 i
  change x i ≤ pzFinGridPoint v i + 1 / (m : ℝ) at hxhi
  change y i ≤ pzFinGridPoint v i + 1 / (m : ℝ) at hyhi
  rw [inv_eq_one_div]
  rw [abs_le]
  constructor <;> linarith

/-- A bounded convex function has a quantitatively bounded subgradient at
every point of a unit grid cell. -/
theorem exists_bounded_subgradient_on_pzGridCell {n m : ℕ}
    (hm : 0 < m) {c : ℝ} (hc : 0 < c)
    {f : (Fin n → ℝ) → ℝ}
    (hf : ConvexOn ℝ (pzExpandedBox n c) f)
    (hrange : ∀ z ∈ pzExpandedBox n c, f z ∈ Set.Icc (0 : ℝ) 1)
    {v : Fin n → Fin m} {x : Fin n → ℝ} (hx : x ∈ pzGridCell v) :
    ∃ p : (Fin n → ℝ) →L[ℝ] ℝ,
      (∀ z ∈ pzExpandedBox n c, f x + p (z - x) ≤ f z) ∧
      ∀ i, |p (Pi.single i 1)| ≤ 1 / c := by
  have hxint : x ∈ interior (pzExpandedBox n c) :=
    pzGridCell_subset_interior hm hc v hx
  obtain ⟨p, hp⟩ :=
    exists_continuousLinear_subgradient_of_mem_interior hf hxint
  refine ⟨p, hp, ?_⟩
  intro i
  obtain ⟨hminus, hplus⟩ :=
    pzGridCell_full_coordinate_shifts_mem hm hc hx i
  have hcoord := subgradient_coordinate_mem_Icc x p i c hc hrange
    (interior_subset hxint) hminus hplus hp
  apply abs_le.mpr
  exact ⟨by
    calc
      -(1 / c) = -1 / c := by ring
      _ ≤ p (Pi.single i 1) := hcoord.1,
    hcoord.2⟩

/-- Quantitative one-sided variation bound for a bounded concave function
between two points of one unit grid cell. -/
theorem concave_sub_le_of_mem_same_pzGridCell {n m : ℕ}
    (hm : 0 < m) {c : ℝ} (hc : 0 < c)
    {h : (Fin n → ℝ) → ℝ}
    (hh : ConcaveOn ℝ (pzExpandedBox n c) h)
    (hrange : ∀ z ∈ pzExpandedBox n c, h z ∈ Set.Icc (0 : ℝ) 1)
    {v : Fin n → Fin m} {x y : Fin n → ℝ}
    (hx : x ∈ pzGridCell v) (hy : y ∈ pzGridCell v) :
    h y - h x ≤ (n : ℝ) / (c * (m : ℝ)) := by
  let f : (Fin n → ℝ) → ℝ := fun z ↦ 1 - h z
  have hf : ConvexOn ℝ (pzExpandedBox n c) f := by
    refine ⟨hh.1, ?_⟩
    intro a ha b hb u w hu hw huw
    have hconc := hh.2 ha hb hu hw huw
    dsimp only [f]
    norm_num only [smul_eq_mul] at hconc ⊢
    nlinarith
  have hfrange : ∀ z ∈ pzExpandedBox n c,
      f z ∈ Set.Icc (0 : ℝ) 1 := by
    intro z hz
    have hr := hrange z hz
    dsimp only [f]
    exact ⟨by linarith [hr.2], by linarith [hr.1]⟩
  obtain ⟨p, hp, hpcoord⟩ :=
    exists_bounded_subgradient_on_pzGridCell hm hc hf hfrange hx
  have hyDomain : y ∈ pzExpandedBox n c :=
    interior_subset (pzGridCell_subset_interior hm hc v hy)
  have hsupport := hp y hyDomain
  have hpExpansion := continuousLinear_eq_sum_subgradientCoordinates p (y - x)
  have hpabs : |p (y - x)| ≤ (n : ℝ) / (c * (m : ℝ)) := by
    rw [hpExpansion]
    calc
      |∑ i, subgradientCoordinates p i * (y - x) i| ≤
          ∑ i, |subgradientCoordinates p i * (y - x) i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, ((1 / c) * (m : ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro i _hi
        rw [abs_mul]
        apply mul_le_mul
        · simpa [subgradientCoordinates] using hpcoord i
        · simpa [Pi.sub_apply] using
            abs_sub_le_inv_of_mem_same_pzGridCell hm hx hy i
        · exact abs_nonneg _
        · positivity
      _ = (n : ℝ) / (c * (m : ℝ)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        field_simp
  have hvariation : h y - h x ≤ -p (y - x) := by
    dsimp only [f] at hsupport
    linarith
  exact hvariation.trans ((neg_le_abs _).trans hpabs)

/-- Absolute oscillation of a bounded concave function on one unit cell. -/
theorem abs_concave_sub_le_of_mem_same_pzGridCell {n m : ℕ}
    (hm : 0 < m) {c : ℝ} (hc : 0 < c)
    {h : (Fin n → ℝ) → ℝ}
    (hh : ConcaveOn ℝ (pzExpandedBox n c) h)
    (hrange : ∀ z ∈ pzExpandedBox n c, h z ∈ Set.Icc (0 : ℝ) 1)
    {v : Fin n → Fin m} {x y : Fin n → ℝ}
    (hx : x ∈ pzGridCell v) (hy : y ∈ pzGridCell v) :
    |h x - h y| ≤ (n : ℝ) / (c * (m : ℝ)) := by
  rw [abs_le]
  have hxy := concave_sub_le_of_mem_same_pzGridCell hm hc hh hrange hx hy
  have hyx := concave_sub_le_of_mem_same_pzGridCell hm hc hh hrange hy hx
  constructor <;> linarith

/-- High-occupancy graph slab: any occupied unit cell is contained in the
constant-height slab whose half-thickness is the explicit oscillation bound.
This works in every positive base dimension, including the planar case. -/
theorem exists_indexed_upperBoundary_constant_slab_high
    {ι : Type*} [DecidableEq ι] {n m K : ℕ}
    (hn : 0 < n) (hm : 0 < m) {c : ℝ} (hc : 0 < c)
    {h : (Fin n → ℝ) → ℝ}
    (hconcave : ConcaveOn ℝ (pzExpandedBox n c) h)
    (hrange : ∀ x ∈ pzExpandedBox n c, h x ∈ Set.Icc (0 : ℝ) 1)
    (J : Finset ι) (z : ι → EuclideanPoint (n + 1))
    (hgraph : ∀ i ∈ J,
      lastCoordinate (z i) = h (WithLp.ofLp (baseCoordinates (z i))))
    (I : Finset (Fin n → Fin m)) (hI : I.Nonempty)
    (hoccupied : ∀ v ∈ I, K ≤ (indexedLabelsOverCellND J z v).card) :
    ∃ v ∈ I,
      let epsilon := (n : ℝ) / (c * (m : ℝ))
      let L := AffineMap.const ℝ (EuclideanPoint n) (h (pzFinGridPoint v))
      let slab := affineGraphSlab (graphBaseCellND v) L epsilon
      (∀ i, |affineCoordinateCoefficient L i| ≤ 0) ∧
        (∀ i ∈ indexedLabelsOverCellND J z v,
          lastCoordinateCLE n (z i) ∈ slab) ∧
        Convex ℝ slab ∧
        K ≤ (indexedLabelsOverCellND J z v).card ∧
        volume slab =
          (∏ _i : Fin n, ENNReal.ofReal ((m : ℝ)⁻¹)) *
            ENNReal.ofReal (2 * epsilon) := by
  let v := hI.choose
  have hvI : v ∈ I := hI.choose_spec
  let epsilon : ℝ := (n : ℝ) / (c * (m : ℝ))
  let L : EuclideanPoint n →ᵃ[ℝ] ℝ :=
    AffineMap.const ℝ (EuclideanPoint n) (h (pzFinGridPoint v))
  refine ⟨v, hvI, ?_, ?_, ?_, hoccupied v hvI, ?_⟩
  · intro i
    simp [L, affineCoordinateCoefficient]
  · intro i hi
    have hi' := mem_indexedLabelsOverCellND_iff.mp hi
    have hibase : WithLp.ofLp (baseCoordinates (z i)) ∈ pzGridCell v :=
      mem_graphBaseCellND_iff.mp hi'.2
    have hbase : pzFinGridPoint v ∈ pzGridCell v :=
      pzFinGridPoint_mem_cell hm v
    have hosc := abs_concave_sub_le_of_mem_same_pzGridCell
      hm hc hconcave hrange hibase hbase
    have hosc' :
        |h (WithLp.ofLp (baseCoordinates (z i))) - h (pzFinGridPoint v)| ≤
          epsilon := by simpa only [epsilon] using hosc
    rw [lastCoordinateCLE_apply]
    refine ⟨hi'.2, ?_, ?_⟩
    · change h (pzFinGridPoint v) - epsilon ≤ lastCoordinate (z i)
      rw [hgraph i hi'.1]
      linarith [(abs_le.mp hosc').1]
    · change lastCoordinate (z i) ≤ h (pzFinGridPoint v) + epsilon
      rw [hgraph i hi'.1]
      linarith [(abs_le.mp hosc').2]
  · exact convex_affineGraphSlab
      (convex_closedAxisBox (pzFinGridPoint v)
        (fun i ↦ pzFinGridPoint v i + 1 / (m : ℝ))) L epsilon
  · have hepsilon : 0 ≤ epsilon := by
      dsimp only [epsilon]
      positivity
    change volume (affineGraphSlab
      (closedAxisBox (pzFinGridPoint v)
        (fun i ↦ pzFinGridPoint v i + 1 / (m : ℝ))) L epsilon) = _
    rw [volume_affineGraphSlab_closedAxisBox
      (pzFinGridPoint v)
      (fun i ↦ pzFinGridPoint v i + 1 / (m : ℝ)) L hepsilon]
    congr 2
    funext i
    congr 1
    rw [show pzFinGridPoint v i + 1 / (m : ℝ) - pzFinGridPoint v i =
      (m : ℝ)⁻¹ by rw [one_div]; ring]

/-- Planar natural-cell-label version of the high-occupancy constant-slab
branch.  This uses the same cell family as the sharp one-dimensional secant
approximation, so the low and high alternatives can share one dyadic shell. -/
theorem exists_indexed_upperBoundary_constant_slab_high_2d
    {ι : Type*} [DecidableEq ι] {m K : ℕ}
    (hm : 0 < m) {c : ℝ} (hc : 0 < c)
    {h : ℝ → ℝ}
    (hconcave : ConcaveOn ℝ (Set.Icc (-c) (1 + c)) h)
    (hrange : ∀ x ∈ Set.Icc (-c) (1 + c), h x ∈ Set.Icc (0 : ℝ) 1)
    (J : Finset ι) (z : ι → EuclideanPoint 2)
    (hgraph : ∀ i ∈ J,
      lastCoordinate (z i) = h (coordinate (baseCoordinates (z i)) 0))
    (I : Finset ℕ) (hI : I.Nonempty) (hIgrid : I ⊆ Finset.range m)
    (hoccupied : ∀ k ∈ I, K ≤ (indexedLabelsOverCell1D J z m k).card) :
    ∃ k ∈ I,
      let epsilon := 1 / (c * (m : ℝ))
      let L := AffineMap.const ℝ (EuclideanPoint 1) (h (gridPoint m k))
      let slab := affineGraphSlab (graphBaseCell m k) L epsilon
      (∀ i, |affineCoordinateCoefficient L i| ≤ 0) ∧
        (∀ i ∈ indexedLabelsOverCell1D J z m k,
          lastCoordinateCLE 1 (z i) ∈ slab) ∧
        Convex ℝ slab ∧
        K ≤ (indexedLabelsOverCell1D J z m k).card ∧
        volume slab = ENNReal.ofReal ((m : ℝ)⁻¹) *
          ENNReal.ofReal (2 * epsilon) := by
  let k := hI.choose
  have hkI : k ∈ I := hI.choose_spec
  have hklt : k < m := Finset.mem_range.mp (hIgrid hkI)
  let v : Fin 1 → Fin m := fun _ ↦ ⟨k, hklt⟩
  let hlift : (Fin 1 → ℝ) → ℝ := fun x ↦ h (x 0)
  have hliftConcave : ConcaveOn ℝ (pzExpandedBox 1 c) hlift := by
    refine ⟨convex_Icc _ _, ?_⟩
    intro x hx y hy a b ha hb hab
    have hx' : x 0 ∈ Set.Icc (-c) (1 + c) := ⟨hx.1 0, hx.2 0⟩
    have hy' : y 0 ∈ Set.Icc (-c) (1 + c) := ⟨hy.1 0, hy.2 0⟩
    have hh := hconcave.2 hx' hy' ha hb hab
    simpa [hlift, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hh
  have hliftRange : ∀ x ∈ pzExpandedBox 1 c,
      hlift x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    exact hrange (x 0) ⟨hx.1 0, hx.2 0⟩
  let epsilon : ℝ := 1 / (c * (m : ℝ))
  let L : EuclideanPoint 1 →ᵃ[ℝ] ℝ :=
    AffineMap.const ℝ (EuclideanPoint 1) (h (gridPoint m k))
  refine ⟨k, hkI, ?_, ?_, ?_, hoccupied k hkI, ?_⟩
  · intro i
    simp [L, affineCoordinateCoefficient]
  · intro i hi
    have hi' := mem_indexedLabelsOverCell1D_iff.mp hi
    have hibounds := mem_graphBaseCell_iff.mp hi'.2
    have hicell : WithLp.ofLp (baseCoordinates (z i)) ∈ pzGridCell v := by
      constructor <;> intro j
      · rw [Subsingleton.elim j 0]
        simpa [v, pzFinGridPoint, pzGridPoint, gridPoint] using hibounds.1
      · rw [Subsingleton.elim j 0]
        have hiupper := hibounds.2
        rw [gridPoint_succ hm] at hiupper
        change coordinate (baseCoordinates (z i)) 0 ≤
          pzFinGridPoint v 0 + 1 / (m : ℝ)
        have hgrid : pzFinGridPoint v 0 = gridPoint m k := by
          simp [v, pzFinGridPoint, pzGridPoint, gridPoint]
        rw [hgrid, one_div]
        exact hiupper
    have hleft : pzFinGridPoint v ∈ pzGridCell v :=
      pzFinGridPoint_mem_cell hm v
    have hosc := abs_concave_sub_le_of_mem_same_pzGridCell
      hm hc hliftConcave hliftRange hicell hleft
    have hosc' :
        |h (coordinate (baseCoordinates (z i)) 0) - h (gridPoint m k)| ≤
          epsilon := by
      simpa [hlift, v, pzFinGridPoint, pzGridPoint, gridPoint, epsilon] using hosc
    rw [lastCoordinateCLE_apply]
    refine ⟨hi'.2, ?_, ?_⟩
    · change h (gridPoint m k) - epsilon ≤ lastCoordinate (z i)
      rw [hgraph i hi'.1]
      linarith [(abs_le.mp hosc').1]
    · change lastCoordinate (z i) ≤ h (gridPoint m k) + epsilon
      rw [hgraph i hi'.1]
      linarith [(abs_le.mp hosc').2]
  · exact convex_affineGraphSlab
      (convex_closedAxisBox (fun _ : Fin 1 ↦ gridPoint m k)
        (fun _ : Fin 1 ↦ gridPoint m (k + 1))) L epsilon
  · have hepsilon : 0 ≤ epsilon := by
      dsimp only [epsilon]
      positivity
    change volume (affineGraphSlab
      (closedAxisBox (fun _ : Fin 1 ↦ gridPoint m k)
        (fun _ : Fin 1 ↦ gridPoint m (k + 1))) L epsilon) = _
    rw [volume_affineGraphSlab_closedAxisBox
      (fun _ : Fin 1 ↦ gridPoint m k)
      (fun _ : Fin 1 ↦ gridPoint m (k + 1)) L hepsilon]
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
    rw [gridPoint_succ hm, one_div]
    rw [show gridPoint m k + (m : ℝ)⁻¹ - gridPoint m k =
      (m : ℝ)⁻¹ by ring]
    simp [epsilon, one_div]

end
end Erdos186.PZ.ConvexDensity
