/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.GraphDensity2D
import ErdosProblems.Erdos186.PZ.ConvexDensity.GraphSlabAmbient
import ErdosProblems.Erdos186.PZ.ConvexDensity.Thickening

/-!
# The planar graph slab in ambient Euclidean coordinates

This module adds the slope estimate needed to thicken the one-dimensional
secant slab, and transports the planar result through the last-coordinate
Euclidean splitting.
-/

open Set MeasureTheory
open scoped ENNReal

namespace Erdos186.PZ.ConvexDensity

set_option autoImplicit false

noncomputable section

open Erdos186.ConvexApprox

/-- Every secant slope over the central unit interval is bounded by the
reciprocal of the available margin. -/
theorem abs_gridSlope_succ_le_inv_margin
    {f : ℝ → ℝ} {c : ℝ} {m k : ℕ}
    (hm : 0 < m) (hmargin : (m : ℝ)⁻¹ < c) (hk : k < m)
    (hconv : ConvexOn ℝ (Set.Icc (-c) (1 + c)) f)
    (hrange : ∀ x ∈ Set.Icc (-c) (1 + c), 0 ≤ f x ∧ f x ≤ 1) :
    |gridSlope f m (k + 1)| ≤ 1 / c := by
  have hc : 0 < c := lt_of_le_of_lt (inv_nonneg.mpr (by positivity)) hmargin
  let a := gridPoint m k
  let b := gridPoint m (k + 1)
  have ha0 : 0 ≤ a := by
    dsimp [a, gridPoint]
    positivity
  have hb1 : b ≤ 1 := by
    dsimp [b, gridPoint]
    rw [div_le_one (by positivity : (0 : ℝ) < m)]
    exact_mod_cast Nat.succ_le_iff.mpr hk
  have hab : a < b := by
    dsimp [a, b]
    rw [gridPoint_succ hm]
    exact lt_add_of_pos_right _ (by positivity)
  have hnegA : -c < a := by linarith
  have hbpos : b < 1 + c := by linarith
  have hnegMem : -c ∈ Set.Icc (-c) (1 + c) := by
    constructor <;> linarith
  have haMem : a ∈ Set.Icc (-c) (1 + c) := by
    constructor <;> linarith
  have hbMem : b ∈ Set.Icc (-c) (1 + c) := by
    constructor <;> linarith
  have hrightMem : 1 + c ∈ Set.Icc (-c) (1 + c) := by
    constructor <;> linarith
  have hlowerSlope := hconv.slope_mono_adjacent hnegMem hbMem hnegA hab
  have hupperSlope := hconv.slope_mono_adjacent haMem hrightMem hab hbpos
  have hlongLower : -1 / c ≤ (f a - f (-c)) / (a - (-c)) := by
    have hden : 0 < a - (-c) := sub_pos.mpr hnegA
    rw [le_div_iff₀ hden]
    have hdenGe : c ≤ a - (-c) := by linarith
    have hcoef : -1 / c ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by norm_num) hc.le
    have hmul := mul_le_mul_of_nonpos_left hdenGe hcoef
    have hcancel : (-1 / c) * c = -1 := by field_simp
    rw [hcancel] at hmul
    have hra := hrange a haMem
    have hrneg := hrange (-c) hnegMem
    linarith
  have hlongUpper : (f (1 + c) - f b) / ((1 + c) - b) ≤ 1 / c := by
    have hden : 0 < (1 + c) - b := sub_pos.mpr hbpos
    rw [div_le_iff₀ hden]
    have hdenGe : c ≤ (1 + c) - b := by linarith
    have hcoef : 0 ≤ 1 / c := by positivity
    have hmul := mul_le_mul_of_nonneg_left hdenGe hcoef
    have hcancel : (1 / c) * c = 1 := by field_simp
    rw [hcancel] at hmul
    have hrright := hrange (1 + c) hrightMem
    have hrb := hrange b hbMem
    linarith
  have hgrid : gridSlope f m (k + 1) =
      (f b - f a) / (b - a) := by
    simpa [a, b] using (gridSlope_succ (f := f) (m := m) (k := k) hm)
  have hlower : -1 / c ≤ gridSlope f m (k + 1) := by
    rw [hgrid]
    exact hlongLower.trans hlowerSlope
  have hupper : gridSlope f m (k + 1) ≤ 1 / c := by
    rw [hgrid]
    exact hupperSlope.trans hlongUpper
  rw [abs_le]
  constructor
  · simpa only [neg_div] using hlower
  · exact hupper

/-- The linear coefficient of the reflected graph secant has the same
margin bound. -/
theorem abs_affineCoordinateCoefficient_graphCellSecant_le
    {h : ℝ → ℝ} {c : ℝ} {m k : ℕ}
    (hm : 0 < m) (hmargin : (m : ℝ)⁻¹ < c) (hk : k < m)
    (hconcave : ConcaveOn ℝ (Set.Icc (-c) (1 + c)) h)
    (hrange : ∀ x ∈ Set.Icc (-c) (1 + c), 0 ≤ h x ∧ h x ≤ 1) :
    |affineCoordinateCoefficient (graphCellSecant h m k) 0| ≤ 1 / c := by
  let f : ℝ → ℝ := fun x ↦ 1 - h x
  have hf : ConvexOn ℝ (Set.Icc (-c) (1 + c)) f := by
    apply (hconcave.neg.add_const (1 : ℝ)).congr
    intro x hx
    simp only [f, Pi.add_apply, Pi.neg_apply]
    ring
  have hfrange : ∀ x ∈ Set.Icc (-c) (1 + c), 0 ≤ f x ∧ f x ≤ 1 := by
    intro x hx
    have hh := hrange x hx
    dsimp only [f]
    constructor <;> linarith
  have hs := abs_gridSlope_succ_le_inv_margin hm hmargin hk hf hfrange
  simpa [affineCoordinateCoefficient, graphCellSecant, f, coordinate] using hs

/-- The planar occupied-cell theorem, strengthened by the coefficient bound
required by the Minkowski-thickening estimate. -/
theorem exists_occupied_graph_cell_affine_slab_with_coeff_bound
    {h : ℝ → ℝ} {c : ℝ} {m K : ℕ}
    (hm : 0 < m) (hmargin : (m : ℝ)⁻¹ < c)
    (hconcave : ConcaveOn ℝ (Set.Icc (-c) (1 + c)) h)
    (hrange : ∀ x ∈ Set.Icc (-c) (1 + c), 0 ≤ h x ∧ h x ≤ 1)
    (X : Finset (EuclideanPoint 1 × ℝ))
    (hgraph : ∀ p ∈ X, p.2 = h (coordinate p.1 0))
    (I : Finset ℕ) (hI : I.Nonempty) (hIgrid : I ⊆ Finset.range m)
    (hoccupied : ∀ k ∈ I, K ≤ (graphPointsOverCell X m k).card) :
    ∃ k ∈ I,
      let epsilon := 2 / (c * (m : ℝ) * (I.card : ℝ))
      let L := graphCellSecant h m k
      let slab := affineGraphSlab (graphBaseCell m k) L epsilon
      (∀ i, |affineCoordinateCoefficient L i| ≤ 1 / c) ∧
        (graphPointsOverCell X m k : Set (EuclideanPoint 1 × ℝ)) ⊆ slab ∧
        Convex ℝ slab ∧
        K ≤ (planarPointsIn X slab).card ∧
        volume slab = ENNReal.ofReal ((m : ℝ)⁻¹) *
          ENNReal.ofReal (4 / (c * (m : ℝ) * (I.card : ℝ))) := by
  obtain ⟨k, hkI, hsubset, hconvex, hcard, hvolume⟩ :=
    exists_occupied_graph_cell_affine_slab hm hmargin hconcave hrange
      X hgraph I hI hIgrid hoccupied
  refine ⟨k, hkI, ?_, hsubset, hconvex, hcard, hvolume⟩
  intro i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  exact abs_affineCoordinateCoefficient_graphCellSecant_le hm hmargin
    (Finset.mem_range.mp (hIgrid hkI)) hconcave hrange

end

end Erdos186.PZ.ConvexDensity
