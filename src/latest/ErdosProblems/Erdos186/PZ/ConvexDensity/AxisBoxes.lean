/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.Definitions

/-!
# Axis boxes and affine graph slabs

This file contains the elementary measurable convex sets used in the
geometric part of the Pham--Zakharov density increment.  We work in the
genuine Euclidean space `EuclideanSpace ℝ (Fin d)`, but define an axis box
through its coordinates.  The canonical equivalence with `Fin d → ℝ` is
volume preserving, so the usual product formula remains available.

The final section treats a closed vertical slab of half-width `ε` around
the graph of an affine map.  Its volume is exactly the base volume times
`2 ε`; the upper bounds needed later are recorded as direct corollaries.
-/

open scoped BigOperators ENNReal
open Set MeasureTheory

namespace Erdos186.PZ.ConvexDensity

noncomputable section

/-- The `i`th coordinate of a Euclidean point. -/
abbrev coordinate {d : ℕ} (x : EuclideanPoint d) (i : Fin d) : ℝ :=
  WithLp.ofLp x i

/-- A closed axis-parallel box in Euclidean space.  It is empty when some
lower endpoint lies strictly above the corresponding upper endpoint. -/
def closedAxisBox {d : ℕ} (lower upper : Fin d → ℝ) : Set (EuclideanPoint d) :=
  {x | ∀ i, lower i ≤ coordinate x i ∧ coordinate x i ≤ upper i}

@[simp]
theorem mem_closedAxisBox_iff {d : ℕ} {lower upper : Fin d → ℝ}
    {x : EuclideanPoint d} :
    x ∈ closedAxisBox lower upper ↔
      ∀ i, lower i ≤ coordinate x i ∧ coordinate x i ≤ upper i :=
  Iff.rfl

/-- In coordinates, a Euclidean axis box is the preimage of the order
interval in `Fin d → ℝ`. -/
theorem closedAxisBox_eq_preimage_Icc {d : ℕ} (lower upper : Fin d → ℝ) :
    closedAxisBox lower upper =
      WithLp.ofLp ⁻¹' Set.Icc lower upper := by
  ext x
  change (∀ i, lower i ≤ WithLp.ofLp x i ∧ WithLp.ofLp x i ≤ upper i) ↔
    lower ≤ WithLp.ofLp x ∧ WithLp.ofLp x ≤ upper
  simp only [Pi.le_def]
  aesop

/-- Coordinatewise ordered endpoints give a point of the box. -/
theorem midpoint_mem_closedAxisBox {d : ℕ} {lower upper : Fin d → ℝ}
    (hlu : lower ≤ upper) :
    WithLp.toLp 2 (fun i ↦ (lower i + upper i) / 2) ∈
      closedAxisBox lower upper := by
  intro i
  simp only [coordinate]
  constructor <;> linarith [hlu i]

/-- Exact nonemptiness criterion for a closed axis box. -/
theorem closedAxisBox_nonempty_iff {d : ℕ} {lower upper : Fin d → ℝ} :
    (closedAxisBox lower upper).Nonempty ↔ lower ≤ upper := by
  constructor
  · rintro ⟨x, hx⟩ i
    exact (hx i).1.trans (hx i).2
  · intro hlu
    exact ⟨_, midpoint_mem_closedAxisBox hlu⟩

/-- Exact emptiness criterion for a closed axis box. -/
theorem closedAxisBox_eq_empty_iff {d : ℕ} {lower upper : Fin d → ℝ} :
    closedAxisBox lower upper = ∅ ↔ ∃ i, upper i < lower i := by
  rw [← not_nonempty_iff_eq_empty, closedAxisBox_nonempty_iff]
  simp only [Pi.le_def, not_forall, not_le]

/-- Closed axis boxes are convex. -/
theorem convex_closedAxisBox {d : ℕ} (lower upper : Fin d → ℝ) :
    Convex ℝ (closedAxisBox lower upper) := by
  rw [closedAxisBox_eq_preimage_Icc]
  exact (convex_Icc lower upper).linear_preimage
    (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).toLinearMap

/-- Closed axis boxes are topologically closed. -/
theorem isClosed_closedAxisBox {d : ℕ} (lower upper : Fin d → ℝ) :
    IsClosed (closedAxisBox lower upper) := by
  rw [closedAxisBox_eq_preimage_Icc]
  exact isClosed_Icc.preimage
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d ↦ ℝ)).continuous

/-- Closed axis boxes are Lebesgue measurable. -/
theorem measurableSet_closedAxisBox {d : ℕ} (lower upper : Fin d → ℝ) :
    MeasurableSet (closedAxisBox lower upper) :=
  (isClosed_closedAxisBox lower upper).measurableSet

/-- Exact product formula for the volume of a Euclidean axis box. -/
theorem volume_closedAxisBox {d : ℕ} (lower upper : Fin d → ℝ) :
    volume (closedAxisBox lower upper) =
      ∏ i, ENNReal.ofReal (upper i - lower i) := by
  rw [closedAxisBox_eq_preimage_Icc]
  rw [(PiLp.volume_preserving_ofLp (Fin d)).measure_preimage (by measurability)]
  exact Real.volume_Icc_pi

/-- Real-valued form of the product formula when the endpoints are
coordinatewise ordered. -/
@[simp]
theorem volume_closedAxisBox_toReal {d : ℕ} {lower upper : Fin d → ℝ}
    (hlu : lower ≤ upper) :
    (volume (closedAxisBox lower upper)).toReal =
      ∏ i, (upper i - lower i) := by
  rw [volume_closedAxisBox]
  simp only [ENNReal.toReal_prod, ENNReal.toReal_ofReal (sub_nonneg.mpr (hlu _))]

/-- Every closed axis box has finite volume. -/
theorem volume_closedAxisBox_ne_top {d : ℕ} (lower upper : Fin d → ℝ) :
    volume (closedAxisBox lower upper) ≠ ∞ := by
  rw [volume_closedAxisBox]
  exact ENNReal.prod_ne_top fun i hi ↦ ENNReal.ofReal_ne_top

/-- Enlarging every coordinate interval enlarges the box. -/
theorem closedAxisBox_mono {d : ℕ}
    {lower₁ upper₁ lower₂ upper₂ : Fin d → ℝ}
    (hlower : lower₂ ≤ lower₁) (hupper : upper₁ ≤ upper₂) :
    closedAxisBox lower₁ upper₁ ⊆ closedAxisBox lower₂ upper₂ := by
  intro x hx i
  exact ⟨(hlower i).trans (hx i).1, (hx i).2.trans (hupper i)⟩

/-- Intersection of axis boxes is obtained by taking the larger lower and
the smaller upper endpoint in each coordinate. -/
theorem closedAxisBox_inter {d : ℕ}
    (lower₁ upper₁ lower₂ upper₂ : Fin d → ℝ) :
    closedAxisBox lower₁ upper₁ ∩ closedAxisBox lower₂ upper₂ =
      closedAxisBox (fun i ↦ max (lower₁ i) (lower₂ i))
        (fun i ↦ min (upper₁ i) (upper₂ i)) := by
  ext x
  simp only [mem_inter_iff, mem_closedAxisBox_iff]
  constructor
  · rintro ⟨h₁, h₂⟩ i
    exact ⟨max_le (h₁ i).1 (h₂ i).1,
      le_min (h₁ i).2 (h₂ i).2⟩
  · intro h
    constructor
    · intro i
      exact ⟨le_max_left _ _ |>.trans (h i).1,
        (h i).2.trans (min_le_left _ _)⟩
    · intro i
      exact ⟨le_max_right _ _ |>.trans (h i).1,
        (h i).2.trans (min_le_right _ _)⟩

/-! ## Coordinate slabs -/

/-- The closed slab cut out by one coordinate interval. -/
def coordinateSlab {d : ℕ} (i : Fin d) (a b : ℝ) : Set (EuclideanPoint d) :=
  {x | a ≤ coordinate x i ∧ coordinate x i ≤ b}

@[simp]
theorem mem_coordinateSlab_iff {d : ℕ} {i : Fin d} {a b : ℝ}
    {x : EuclideanPoint d} :
    x ∈ coordinateSlab i a b ↔
      a ≤ coordinate x i ∧ coordinate x i ≤ b :=
  Iff.rfl

theorem convex_coordinateSlab {d : ℕ} (i : Fin d) (a b : ℝ) :
    Convex ℝ (coordinateSlab i a b) := by
  intro x hx y hy p q hp hq hpq
  constructor
  · change a ≤ p * coordinate x i + q * coordinate y i
    have h := add_le_add (mul_le_mul_of_nonneg_left hx.1 hp)
      (mul_le_mul_of_nonneg_left hy.1 hq)
    calc
      a = (p + q) * a := by rw [hpq, one_mul]
      _ = p * a + q * a := by ring
      _ ≤ p * coordinate x i + q * coordinate y i := h
  · change p * coordinate x i + q * coordinate y i ≤ b
    have h := add_le_add (mul_le_mul_of_nonneg_left hx.2 hp)
      (mul_le_mul_of_nonneg_left hy.2 hq)
    calc
      p * coordinate x i + q * coordinate y i ≤ p * b + q * b := h
      _ = (p + q) * b := by ring
      _ = b := by rw [hpq, one_mul]

theorem isClosed_coordinateSlab {d : ℕ} (i : Fin d) (a b : ℝ) :
    IsClosed (coordinateSlab i a b) := by
  exact (isClosed_Icc.preimage
    ((EuclideanSpace.proj i).continuous))

theorem measurableSet_coordinateSlab {d : ℕ} (i : Fin d) (a b : ℝ) :
    MeasurableSet (coordinateSlab i a b) :=
  (isClosed_coordinateSlab i a b).measurableSet

/-- Every box is contained in each of its coordinate slabs. -/
theorem closedAxisBox_subset_coordinateSlab {d : ℕ}
    (lower upper : Fin d → ℝ) (i : Fin d) :
    closedAxisBox lower upper ⊆ coordinateSlab i (lower i) (upper i) := by
  intro x hx
  exact hx i

/-- Intersection of two slabs in the same coordinate. -/
theorem coordinateSlab_inter {d : ℕ} (i : Fin d) (a b c e : ℝ) :
    coordinateSlab i a b ∩ coordinateSlab i c e =
      coordinateSlab i (max a c) (min b e) := by
  ext x
  simp only [mem_inter_iff, mem_coordinateSlab_iff]
  constructor
  · rintro ⟨hab, hce⟩
    exact ⟨max_le hab.1 hce.1, le_min hab.2 hce.2⟩
  · intro h
    exact ⟨⟨(le_max_left _ _).trans h.1, h.2.trans (min_le_left _ _)⟩,
      ⟨(le_max_right _ _).trans h.1, h.2.trans (min_le_right _ _)⟩⟩

/-! ## Affine graph slabs -/

/-- The closed vertical slab of half-width `ε` around the graph of `L`,
restricted to a base set `s`. -/
def affineGraphSlab {d : ℕ} (s : Set (EuclideanPoint d))
    (L : EuclideanPoint d →ᵃ[ℝ] ℝ) (ε : ℝ) :
    Set (EuclideanPoint d × ℝ) :=
  {p | p.1 ∈ s ∧ L p.1 - ε ≤ p.2 ∧ p.2 ≤ L p.1 + ε}

@[simp]
theorem mem_affineGraphSlab_iff {d : ℕ} {s : Set (EuclideanPoint d)}
    {L : EuclideanPoint d →ᵃ[ℝ] ℝ} {ε : ℝ}
    {p : EuclideanPoint d × ℝ} :
    p ∈ affineGraphSlab s L ε ↔
      p.1 ∈ s ∧ L p.1 - ε ≤ p.2 ∧ p.2 ≤ L p.1 + ε :=
  Iff.rfl

/-- A graph slab is contained in the vertical cylinder over its base. -/
theorem affineGraphSlab_subset_prod {d : ℕ} (s : Set (EuclideanPoint d))
    (L : EuclideanPoint d →ᵃ[ℝ] ℝ) (ε : ℝ) :
    affineGraphSlab s L ε ⊆ s ×ˢ Set.univ := by
  intro p hp
  exact ⟨hp.1, Set.mem_univ _⟩

/-- Graph slabs are monotone in their base set. -/
theorem affineGraphSlab_mono_base {d : ℕ} {s t : Set (EuclideanPoint d)}
    (hst : s ⊆ t) (L : EuclideanPoint d →ᵃ[ℝ] ℝ) (ε : ℝ) :
    affineGraphSlab s L ε ⊆ affineGraphSlab t L ε := by
  intro p hp
  exact ⟨hst hp.1, hp.2⟩

/-- Increasing the half-width enlarges an affine graph slab. -/
theorem affineGraphSlab_mono_width {d : ℕ} (s : Set (EuclideanPoint d))
    (L : EuclideanPoint d →ᵃ[ℝ] ℝ) {ε ε' : ℝ} (hε : ε ≤ ε') :
    affineGraphSlab s L ε ⊆ affineGraphSlab s L ε' := by
  intro p hp
  exact ⟨hp.1, by linarith [hp.2.1], by linarith [hp.2.2]⟩

/-- Intersection with a smaller base can be moved into the slab definition. -/
theorem affineGraphSlab_inter_base {d : ℕ}
    (s t : Set (EuclideanPoint d)) (L : EuclideanPoint d →ᵃ[ℝ] ℝ) (ε : ℝ) :
    affineGraphSlab s L ε ∩ (t ×ˢ Set.univ) =
      affineGraphSlab (s ∩ t) L ε := by
  ext p
  simp [affineGraphSlab, and_assoc, and_left_comm, and_comm]

/-- A closed graph slab over a convex base is convex. -/
theorem convex_affineGraphSlab {d : ℕ} {s : Set (EuclideanPoint d)}
    (hs : Convex ℝ s) (L : EuclideanPoint d →ᵃ[ℝ] ℝ) (ε : ℝ) :
    Convex ℝ (affineGraphSlab s L ε) := by
  intro x hx y hy a b ha hb hab
  have hbase : a • x.1 + b • y.1 ∈ s := hs hx.1 hy.1 ha hb hab
  have hL : L (a • x.1 + b • y.1) = a * L x.1 + b * L y.1 := by
    rw [show a • x.1 + b • y.1 = AffineMap.lineMap y.1 x.1 a by
      rw [AffineMap.lineMap_apply_module]
      rw [show 1 - a = b by linarith]
      abel]
    rw [← L.comp_apply (AffineMap.lineMap y.1 x.1) a]
    rw [AffineMap.comp_lineMap, AffineMap.lineMap_apply_ring]
    rw [show 1 - a = b by linarith]
    ring
  refine ⟨hbase, ?_, ?_⟩
  · change L (a • x.1 + b • y.1) - ε ≤ a * x.2 + b * y.2
    rw [hL]
    have hx' := mul_le_mul_of_nonneg_left hx.2.1 ha
    have hy' := mul_le_mul_of_nonneg_left hy.2.1 hb
    calc
      a * L x.1 + b * L y.1 - ε =
          a * (L x.1 - ε) + b * (L y.1 - ε) := by
        linear_combination ε * hab
      _ ≤ a * x.2 + b * y.2 := add_le_add hx' hy'
  · change a * x.2 + b * y.2 ≤ L (a • x.1 + b • y.1) + ε
    rw [hL]
    have hx' := mul_le_mul_of_nonneg_left hx.2.2 ha
    have hy' := mul_le_mul_of_nonneg_left hy.2.2 hb
    calc
      a * x.2 + b * y.2 ≤
          a * (L x.1 + ε) + b * (L y.1 + ε) := add_le_add hx' hy'
      _ = a * L x.1 + b * L y.1 + ε := by
        linear_combination ε * hab

/-- A graph slab over a measurable base is measurable. -/
theorem measurableSet_affineGraphSlab {d : ℕ} {s : Set (EuclideanPoint d)}
    (hs : MeasurableSet s) (L : EuclideanPoint d →ᵃ[ℝ] ℝ) (ε : ℝ) :
    MeasurableSet (affineGraphSlab s L ε) := by
  change MeasurableSet
    {p : EuclideanPoint d × ℝ |
      p.1 ∈ s ∧ p.2 ∈ Set.Icc (L p.1 - ε) (L p.1 + ε)}
  exact measurableSet_region_between_cc
    (L.continuous_of_finiteDimensional.measurable.sub measurable_const)
    (L.continuous_of_finiteDimensional.measurable.add measurable_const) hs

/-- A graph slab over a closed base is closed. -/
theorem isClosed_affineGraphSlab {d : ℕ} {s : Set (EuclideanPoint d)}
    (hs : IsClosed s) (L : EuclideanPoint d →ᵃ[ℝ] ℝ) (ε : ℝ) :
    IsClosed (affineGraphSlab s L ε) := by
  have hL : Continuous L := L.continuous_of_finiteDimensional
  exact (hs.preimage continuous_fst).inter
    ((isClosed_le (hL.comp continuous_fst |>.sub continuous_const) continuous_snd).inter
      (isClosed_le continuous_snd (hL.comp continuous_fst |>.add continuous_const)))

/-- Exact volume of a closed affine graph slab.  The slope and intercept of
the graph do not affect volume. -/
theorem volume_affineGraphSlab {d : ℕ} {s : Set (EuclideanPoint d)}
    (hs : MeasurableSet s) (L : EuclideanPoint d →ᵃ[ℝ] ℝ)
    {ε : ℝ} (_hε : 0 ≤ ε) :
    volume (affineGraphSlab s L ε) =
      volume s * ENNReal.ofReal (2 * ε) := by
  rw [Measure.volume_eq_prod]
  rw [Measure.prod_apply (measurableSet_affineGraphSlab hs L ε)]
  have hfiber : ∀ x : EuclideanPoint d,
      volume (Prod.mk x ⁻¹' affineGraphSlab s L ε) =
        s.indicator (fun _ ↦ ENNReal.ofReal (2 * ε)) x := by
    intro x
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx]
      rw [show Prod.mk x ⁻¹' affineGraphSlab s L ε =
          Set.Icc (L x - ε) (L x + ε) by
        ext y
        simp [affineGraphSlab, hx]]
      rw [Real.volume_Icc]
      congr 1
      ring
    · rw [Set.indicator_of_notMem hx]
      rw [show Prod.mk x ⁻¹' affineGraphSlab s L ε = ∅ by
        ext y
        simp [affineGraphSlab, hx]]
      simp
  simp_rw [hfiber]
  rw [lintegral_indicator hs]
  simp [mul_comm]

/-- Volume bound when only an upper bound for the base volume is known. -/
theorem volume_affineGraphSlab_le {d : ℕ} {s : Set (EuclideanPoint d)}
    (hs : MeasurableSet s) (L : EuclideanPoint d →ᵃ[ℝ] ℝ)
    {ε V : ℝ} (hε : 0 ≤ ε)
    (hbase : volume s ≤ ENNReal.ofReal V) :
    volume (affineGraphSlab s L ε) ≤
      ENNReal.ofReal V * ENNReal.ofReal (2 * ε) := by
  rw [volume_affineGraphSlab hs L hε]
  gcongr

/-- Product-form exact volume for a graph slab over an axis box. -/
theorem volume_affineGraphSlab_closedAxisBox {d : ℕ}
    (lower upper : Fin d → ℝ) (L : EuclideanPoint d →ᵃ[ℝ] ℝ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    volume (affineGraphSlab (closedAxisBox lower upper) L ε) =
      (∏ i, ENNReal.ofReal (upper i - lower i)) *
        ENNReal.ofReal (2 * ε) := by
  rw [volume_affineGraphSlab (measurableSet_closedAxisBox lower upper) L hε,
    volume_closedAxisBox]

/-- The practical slab estimate: if every base side has length at most
`w i`, the slab volume is at most the product of those bounds times its
vertical thickness. -/
theorem volume_affineGraphSlab_closedAxisBox_le {d : ℕ}
    {lower upper w : Fin d → ℝ} (L : EuclideanPoint d →ᵃ[ℝ] ℝ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hwidth : ∀ i, upper i - lower i ≤ w i) :
    volume (affineGraphSlab (closedAxisBox lower upper) L ε) ≤
      (∏ i, ENNReal.ofReal (w i)) * ENNReal.ofReal (2 * ε) := by
  rw [volume_affineGraphSlab_closedAxisBox lower upper L hε]
  gcongr with i hi
  exact hwidth i

end

end Erdos186.PZ.ConvexDensity
