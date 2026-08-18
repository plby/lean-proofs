/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.AxisBoxes

/-!
# Width and inradius facts for the Pham--Zakharov convex-density argument

This file isolates the elementary, fully rigorous part of the width argument.
For a compact nonempty set, support values in every direction are attained.
In the fixed Euclidean coordinates, the coordinate support intervals give a
canonical containing box and hence a product upper bound for volume.  Replacing
one side of an ambient box by the corresponding coordinate width gives the
useful ``thin direction'' estimate.

There is an important limitation.  A cube is not invariant under arbitrary
rotations, so an arbitrary directional width cannot simply be substituted for
a coordinate width with the same constant.  The rotation-independent estimate
used in the full proof of Pham--Zakharov Lemma 1 needs an additional geometric
input (equivalently, a bounded-section/slab theorem followed by a
width--inradius comparison such as Steinhagen's theorem).  That theorem is not
silently asserted here.  We do prove the unconditional qualitative inradius
fact supplied by nonempty interior, and its exact consequence that an
inscribed ball of radius `r` forces every unit directional width to be at least
`2 * r`.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal Topology

namespace Erdos186.PZ.ConvexDensity

noncomputable section

/-! ## Directional support values -/

/-- Evaluation in direction `u`.  We keep the direction unnormalized; this
makes homogeneity available to downstream arguments without side conditions. -/
def directionalValue {d : ℕ} (u x : EuclideanPoint d) : ℝ :=
  inner ℝ u x

/-- The largest support value of `P` in direction `u` (for compact nonempty
`P`, this supremum is attained). -/
def supportUpper {d : ℕ} (P : Set (EuclideanPoint d))
    (u : EuclideanPoint d) : ℝ :=
  sSup (directionalValue u '' P)

/-- The smallest support value of `P` in direction `u` (for compact nonempty
`P`, this infimum is attained). -/
def supportLower {d : ℕ} (P : Set (EuclideanPoint d))
    (u : EuclideanPoint d) : ℝ :=
  sInf (directionalValue u '' P)

/-- Directional width is upper support minus lower support. -/
def directionalWidth {d : ℕ} (P : Set (EuclideanPoint d))
    (u : EuclideanPoint d) : ℝ :=
  supportUpper P u - supportLower P u

theorem continuous_directionalValue {d : ℕ} (u : EuclideanPoint d) :
    Continuous (directionalValue u) := by
  change Continuous (fun x : EuclideanPoint d ↦ inner ℝ u x)
  exact continuous_const.inner continuous_id

/-- A continuous linear functional attains its maximum on a nonempty compact
set.  The final conjunct is the support inequality for every point of `P`. -/
theorem exists_supportUpper {d : ℕ} {P : Set (EuclideanPoint d)}
    (hP : IsCompact P) (hPne : P.Nonempty) (u : EuclideanPoint d) :
    ∃ x ∈ P, supportUpper P u = directionalValue u x ∧
      ∀ y ∈ P, directionalValue u y ≤ directionalValue u x := by
  simpa only [supportUpper] using
    hP.exists_sSup_image_eq_and_ge hPne
      (continuous_directionalValue u).continuousOn

/-- A continuous linear functional attains its minimum on a nonempty compact
set. -/
theorem exists_supportLower {d : ℕ} {P : Set (EuclideanPoint d)}
    (hP : IsCompact P) (hPne : P.Nonempty) (u : EuclideanPoint d) :
    ∃ x ∈ P, supportLower P u = directionalValue u x ∧
      ∀ y ∈ P, directionalValue u x ≤ directionalValue u y := by
  simpa only [supportLower] using
    hP.exists_sInf_image_eq_and_le hPne
      (continuous_directionalValue u).continuousOn

theorem directionalValue_le_supportUpper {d : ℕ}
    {P : Set (EuclideanPoint d)} (hP : IsCompact P) (hPne : P.Nonempty)
    {u x : EuclideanPoint d} (hx : x ∈ P) :
    directionalValue u x ≤ supportUpper P u := by
  obtain ⟨z, hz, hzeq, hzmax⟩ := exists_supportUpper hP hPne u
  rw [hzeq]
  exact hzmax x hx

theorem supportLower_le_directionalValue {d : ℕ}
    {P : Set (EuclideanPoint d)} (hP : IsCompact P) (hPne : P.Nonempty)
    {u x : EuclideanPoint d} (hx : x ∈ P) :
    supportLower P u ≤ directionalValue u x := by
  obtain ⟨z, hz, hzeq, hzmin⟩ := exists_supportLower hP hPne u
  rw [hzeq]
  exact hzmin x hx

theorem supportLower_le_supportUpper {d : ℕ}
    {P : Set (EuclideanPoint d)} (hP : IsCompact P) (hPne : P.Nonempty)
    (u : EuclideanPoint d) : supportLower P u ≤ supportUpper P u := by
  obtain ⟨x, hx⟩ := hPne
  exact (supportLower_le_directionalValue hP ⟨x, hx⟩ hx).trans
    (directionalValue_le_supportUpper hP ⟨x, hx⟩ hx)

theorem directionalWidth_nonneg {d : ℕ}
    {P : Set (EuclideanPoint d)} (hP : IsCompact P) (hPne : P.Nonempty)
    (u : EuclideanPoint d) : 0 ≤ directionalWidth P u := by
  exact sub_nonneg.mpr (supportLower_le_supportUpper hP hPne u)

/-- The closed slab between two levels of a directional functional. -/
def directionalSlab {d : ℕ} (u : EuclideanPoint d) (a b : ℝ) :
    Set (EuclideanPoint d) :=
  {x | a ≤ directionalValue u x ∧ directionalValue u x ≤ b}

@[simp]
theorem mem_directionalSlab_iff {d : ℕ} {u x : EuclideanPoint d}
    {a b : ℝ} :
    x ∈ directionalSlab u a b ↔
      a ≤ directionalValue u x ∧ directionalValue u x ≤ b :=
  Iff.rfl

theorem convex_directionalSlab {d : ℕ} (u : EuclideanPoint d) (a b : ℝ) :
    Convex ℝ (directionalSlab u a b) := by
  exact (convex_halfSpace_ge (innerSL ℝ u).isLinear a).inter
    (convex_halfSpace_le (innerSL ℝ u).isLinear b)

theorem isClosed_directionalSlab {d : ℕ} (u : EuclideanPoint d) (a b : ℝ) :
    IsClosed (directionalSlab u a b) := by
  exact (isClosed_le continuous_const (continuous_directionalValue u)).inter
    (isClosed_le (continuous_directionalValue u) continuous_const)

theorem measurableSet_directionalSlab {d : ℕ}
    (u : EuclideanPoint d) (a b : ℝ) :
    MeasurableSet (directionalSlab u a b) :=
  (isClosed_directionalSlab u a b).measurableSet

/-- A compact nonempty set lies in its supporting slab. -/
theorem subset_supportSlab {d : ℕ} {P : Set (EuclideanPoint d)}
    (hP : IsCompact P) (hPne : P.Nonempty) (u : EuclideanPoint d) :
    P ⊆ directionalSlab u (supportLower P u) (supportUpper P u) := by
  intro x hx
  exact ⟨supportLower_le_directionalValue hP hPne hx,
    directionalValue_le_supportUpper hP hPne hx⟩

/-! ## Coordinate widths and volume -/

/-- Lowest value of the `i`th coordinate on `P`. -/
def coordinateLower {d : ℕ} (P : Set (EuclideanPoint d)) (i : Fin d) : ℝ :=
  sInf ((fun x : EuclideanPoint d ↦ coordinate x i) '' P)

/-- Highest value of the `i`th coordinate on `P`. -/
def coordinateUpper {d : ℕ} (P : Set (EuclideanPoint d)) (i : Fin d) : ℝ :=
  sSup ((fun x : EuclideanPoint d ↦ coordinate x i) '' P)

/-- Width of the `i`th coordinate projection. -/
def coordinateWidth {d : ℕ} (P : Set (EuclideanPoint d)) (i : Fin d) : ℝ :=
  coordinateUpper P i - coordinateLower P i

theorem continuous_coordinate {d : ℕ} (i : Fin d) :
    Continuous (fun x : EuclideanPoint d ↦ coordinate x i) := by
  fun_prop

theorem exists_coordinateUpper {d : ℕ} {P : Set (EuclideanPoint d)}
    (hP : IsCompact P) (hPne : P.Nonempty) (i : Fin d) :
    ∃ x ∈ P, coordinateUpper P i = coordinate x i ∧
      ∀ y ∈ P, coordinate y i ≤ coordinate x i := by
  simpa only [coordinateUpper] using
    hP.exists_sSup_image_eq_and_ge hPne (continuous_coordinate i).continuousOn

theorem exists_coordinateLower {d : ℕ} {P : Set (EuclideanPoint d)}
    (hP : IsCompact P) (hPne : P.Nonempty) (i : Fin d) :
    ∃ x ∈ P, coordinateLower P i = coordinate x i ∧
      ∀ y ∈ P, coordinate x i ≤ coordinate y i := by
  simpa only [coordinateLower] using
    hP.exists_sInf_image_eq_and_le hPne (continuous_coordinate i).continuousOn

theorem coordinate_le_upper {d : ℕ} {P : Set (EuclideanPoint d)}
    (hP : IsCompact P) (hPne : P.Nonempty) {x : EuclideanPoint d}
    (hx : x ∈ P) (i : Fin d) : coordinate x i ≤ coordinateUpper P i := by
  obtain ⟨z, hz, hzeq, hzmax⟩ := exists_coordinateUpper hP hPne i
  rw [hzeq]
  exact hzmax x hx

theorem coordinateLower_le {d : ℕ} {P : Set (EuclideanPoint d)}
    (hP : IsCompact P) (hPne : P.Nonempty) {x : EuclideanPoint d}
    (hx : x ∈ P) (i : Fin d) : coordinateLower P i ≤ coordinate x i := by
  obtain ⟨z, hz, hzeq, hzmin⟩ := exists_coordinateLower hP hPne i
  rw [hzeq]
  exact hzmin x hx

theorem coordinateWidth_nonneg {d : ℕ} {P : Set (EuclideanPoint d)}
    (hP : IsCompact P) (hPne : P.Nonempty) (i : Fin d) :
    0 ≤ coordinateWidth P i := by
  obtain ⟨x, hx⟩ := hPne
  exact sub_nonneg.mpr <|
    (coordinateLower_le hP ⟨x, hx⟩ hx i).trans
      (coordinate_le_upper hP ⟨x, hx⟩ hx i)

/-- The coordinate extrema define a canonical containing axis box. -/
theorem subset_coordinateBoundingBox {d : ℕ}
    {P : Set (EuclideanPoint d)} (hP : IsCompact P) (hPne : P.Nonempty) :
    P ⊆ closedAxisBox (coordinateLower P) (coordinateUpper P) := by
  intro x hx i
  exact ⟨coordinateLower_le hP hPne hx i,
    coordinate_le_upper hP hPne hx i⟩

/-- Product of coordinate widths bounds volume.  Convexity is not needed. -/
theorem volume_le_prod_coordinateWidth {d : ℕ}
    {P : Set (EuclideanPoint d)} (hP : IsCompact P) (hPne : P.Nonempty) :
    volume P ≤ ∏ i, ENNReal.ofReal (coordinateWidth P i) := by
  calc
    volume P ≤ volume (closedAxisBox (coordinateLower P) (coordinateUpper P)) :=
      measure_mono (subset_coordinateBoundingBox hP hPne)
    _ = ∏ i, ENNReal.ofReal (coordinateWidth P i) := by
      simpa only [coordinateWidth] using
        volume_closedAxisBox (coordinateLower P) (coordinateUpper P)

/-- If `P` lies in an ambient axis box, one side of that box may be
replaced by the actual coordinate width of `P`. -/
theorem volume_le_coordinateWidth_mul_otherSides {d : ℕ}
    {P : Set (EuclideanPoint d)} (hP : IsCompact P) (hPne : P.Nonempty)
    {lower upper : Fin d → ℝ}
    (hbox : P ⊆ closedAxisBox lower upper) (i : Fin d) :
    volume P ≤
      (∏ j ∈ Finset.univ.erase i, ENNReal.ofReal (upper j - lower j)) *
        ENNReal.ofReal (coordinateWidth P i) := by
  let lo : Fin d → ℝ := fun j ↦ if j = i then coordinateLower P i else lower j
  let hi : Fin d → ℝ := fun j ↦ if j = i then coordinateUpper P i else upper j
  have hsub : P ⊆ closedAxisBox lo hi := by
    intro x hx j
    by_cases hji : j = i
    · subst j
      simp only [lo, hi, if_pos]
      exact ⟨coordinateLower_le hP hPne hx i,
        coordinate_le_upper hP hPne hx i⟩
    · simp only [lo, hi, if_neg hji]
      exact hbox hx j
  calc
    volume P ≤ volume (closedAxisBox lo hi) := measure_mono hsub
    _ = ∏ j, ENNReal.ofReal (hi j - lo j) := volume_closedAxisBox lo hi
    _ = (∏ j ∈ Finset.univ.erase i,
          ENNReal.ofReal (upper j - lower j)) *
        ENNReal.ofReal (coordinateWidth P i) := by
      rw [← Finset.prod_erase_mul Finset.univ
        (fun j ↦ ENNReal.ofReal (hi j - lo j)) (Finset.mem_univ i)]
      congr 1
      · apply Finset.prod_congr rfl
        intro j hj
        have hji : j ≠ i := Finset.ne_of_mem_erase hj
        simp only [lo, hi, if_neg hji]
      · simp only [lo, hi, if_pos, coordinateWidth]

/-- A centered coordinate cube of radius `R` has all side lengths `2R`.
Thus volume is at most one actual coordinate width times `d-1` ambient
side lengths. -/
theorem volume_le_coordinateWidth_mul_cube {d : ℕ}
    {P : Set (EuclideanPoint d)} (hP : IsCompact P) (hPne : P.Nonempty)
    (c : EuclideanPoint d) {R : ℝ} (_hR : 0 ≤ R)
    (hcube : P ⊆ closedAxisBox
      (fun j ↦ coordinate c j - R) (fun j ↦ coordinate c j + R))
    (i : Fin d) :
    volume P ≤ ENNReal.ofReal (2 * R) ^ (d - 1) *
      ENNReal.ofReal (coordinateWidth P i) := by
  have h := volume_le_coordinateWidth_mul_otherSides hP hPne hcube i
  have hside : ∀ j : Fin d,
      ENNReal.ofReal ((coordinate c j + R) - (coordinate c j - R)) =
        ENNReal.ofReal (2 * R) := by
    intro j
    congr 1
    ring
  simp_rw [hside] at h
  simpa only [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin] using h

/-- The minimum of the finitely many coordinate widths.  In dimension zero
the indexing range is empty and the conditionally complete lattice convention
for `sInf ∅` is used; all theorems selecting a minimizing coordinate assume
positive dimension. -/
def minimumCoordinateWidth {d : ℕ} (P : Set (EuclideanPoint d)) : ℝ :=
  sInf (Set.range (coordinateWidth P))

theorem exists_coordinateWidth_eq_minimum {d : ℕ} (hd : 0 < d)
    (P : Set (EuclideanPoint d)) :
    ∃ i : Fin d, coordinateWidth P i = minimumCoordinateWidth P := by
  let i0 : Fin d := ⟨0, hd⟩
  have hne : (Set.range (coordinateWidth P)).Nonempty :=
    ⟨coordinateWidth P i0, ⟨i0, rfl⟩⟩
  have hfinite : (Set.range (coordinateWidth P)).Finite := Set.finite_range _
  have hmem : minimumCoordinateWidth P ∈ Set.range (coordinateWidth P) := by
    exact hfinite.isCompact.sInf_mem hne
  exact hmem

/-- Fixed-cube volume bound using the least coordinate width. -/
theorem volume_le_minimumCoordinateWidth_mul_cube {d : ℕ} (hd : 0 < d)
    {P : Set (EuclideanPoint d)} (hP : IsCompact P) (hPne : P.Nonempty)
    (c : EuclideanPoint d) {R : ℝ} (hR : 0 ≤ R)
    (hcube : P ⊆ closedAxisBox
      (fun j ↦ coordinate c j - R) (fun j ↦ coordinate c j + R)) :
    volume P ≤ ENNReal.ofReal (2 * R) ^ (d - 1) *
      ENNReal.ofReal (minimumCoordinateWidth P) := by
  obtain ⟨i, hi⟩ := exists_coordinateWidth_eq_minimum hd P
  simpa only [hi] using
    volume_le_coordinateWidth_mul_cube hP hPne c hR hcube i

/-! ## Qualitative inradius and the induced width lower bound -/

/-- Nonempty interior contains a positive-radius closed ball.  This is the
qualitative inradius fact that follows directly from the definition of a
convex body. -/
theorem IsConvexBody.exists_closedBall_subset {d : ℕ}
    {P : Set (EuclideanPoint d)} (hP : IsConvexBody P) :
    ∃ x ∈ P, ∃ r : ℝ, 0 < r ∧ Metric.closedBall x r ⊆ P := by
  obtain ⟨x, hxint⟩ := hP.interior_nonempty
  have hnhds : P ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp hxint
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨x, interior_subset hxint, R / 2, by positivity, ?_⟩
  exact (Metric.closedBall_subset_ball (half_lt_self hR)).trans hball

/-- An inscribed radius `r` gives the sharp elementary lower bound `2r` on
every unit directional width. -/
theorem two_mul_le_directionalWidth_of_closedBall_subset {d : ℕ}
    {P : Set (EuclideanPoint d)} (hP : IsCompact P) (hPne : P.Nonempty)
    {x u : EuclideanPoint d} {r : ℝ} (hr : 0 ≤ r) (hu : ‖u‖ = 1)
    (hball : Metric.closedBall x r ⊆ P) :
    2 * r ≤ directionalWidth P u := by
  have hplus : x + r • u ∈ P := hball <| by
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp [norm_smul, hu, abs_of_nonneg hr]
  have hminus : x - r • u ∈ P := hball <| by
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp [norm_smul, hu, abs_of_nonneg hr]
  have hlo : supportLower P u ≤ directionalValue u (x - r • u) :=
    supportLower_le_directionalValue hP hPne (u := u) hminus
  have hhi : directionalValue u (x + r • u) ≤ supportUpper P u :=
    directionalValue_le_supportUpper hP hPne (u := u) hplus
  calc
    2 * r = directionalValue u (x + r • u) -
        directionalValue u (x - r • u) := by
      simp only [directionalValue, inner_add_right, inner_sub_right,
        inner_smul_right]
      rw [real_inner_self_eq_norm_sq, hu]
      ring
    _ ≤ supportUpper P u - supportLower P u := sub_le_sub hhi hlo
    _ = directionalWidth P u := by rfl

/-- Every convex body has a positive number which is a simultaneous lower
bound (up to the factor two) for all unit directional widths. -/
theorem IsConvexBody.exists_pos_le_all_unit_directionalWidth {d : ℕ}
    {P : Set (EuclideanPoint d)} (hP : IsConvexBody P) :
    ∃ r : ℝ, 0 < r ∧ ∀ u : EuclideanPoint d, ‖u‖ = 1 →
      2 * r ≤ directionalWidth P u := by
  obtain ⟨x, hx, r, hr, hball⟩ := hP.exists_closedBall_subset
  refine ⟨r, hr, fun u hu ↦ ?_⟩
  exact two_mul_le_directionalWidth_of_closedBall_subset
    hP.isCompact hP.nonempty hr.le hu hball

end

end Erdos186.PZ.ConvexDensity
