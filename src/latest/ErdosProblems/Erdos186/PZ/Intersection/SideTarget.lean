/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.GAPErrorBox
import ErdosProblems.Erdos186.PZ.Intersection.FullRankObstruction

/-!
# Canonical finite targets for the PZ intersection sides

The post-CFP intersection pipeline previously allowed an arbitrary finite
`target`, followed by separate assumptions saying that its points decompose
as a structured point plus an integral zonotope point and that a thick cube
is contained in it.  Here we define the target to be exactly that finite
Minkowski sum.  Both properties then become theorems.

Finiteness of the integral points of a zonotope is proved using the explicit
coordinate box
`|x i| ≤ ∑ a ∈ core, |a i|`.  This keeps the target in the canonical
integer coordinates of the selected identified core.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-! ## The general-rank progression step lattice -/

theorem step_mem_gapStepLattice {d r : ℕ} (P : GAP d r) (i : Fin r) :
    P.steps i ∈ gapStepLattice P := by
  exact AddSubgroup.subset_closure ⟨i, rfl⟩

theorem sum_steps_mem_gapStepLattice {d r : ℕ} (P : GAP d r)
    (a : Fin r → ℤ) :
    (∑ i, a i • P.steps i) ∈ gapStepLattice P := by
  exact AddSubgroup.sum_mem _ fun i _ ↦
    AddSubgroup.zsmul_mem _ (step_mem_gapStepLattice P i) (a i)

theorem offset_mem_gapStepLattice_of_symmetric {d r : ℕ}
    (P : GAP d r) (hP : P.Symmetric) :
    P.offset ∈ gapStepLattice P := by
  obtain ⟨radii, hcenter⟩ := hP
  have hsum := sum_steps_mem_gapStepLattice P
    (fun i ↦ (radii i : ℤ))
  have hneg := AddSubgroup.neg_mem (gapStepLattice P) hsum
  have hoffset := hcenter.offset_eq
  have heq : P.offset = -(∑ i, (radii i : ℤ) • P.steps i) := by
    funext j
    rw [hoffset]
    simp [Finset.sum_apply]
  rw [heq]
  exact hneg

/-- Every point of every dilate of a symmetric GAP is in its generated step
lattice.  This works in arbitrary displayed rank. -/
theorem dilate_carrier_subset_gapStepLattice_of_symmetric {d r k : ℕ}
    (P : GAP d r) (hP : P.Symmetric) :
    ∀ ⦃x⦄, x ∈ (P.dilate k).carrier → x ∈ gapStepLattice P := by
  intro x hx
  obtain ⟨n, rfl⟩ := GAP.mem_carrier_iff.mp hx
  have hrepr : (P.dilate k).coordPoint n =
      (k : ℤ) • P.offset + ∑ i, (n i : ℤ) • P.steps i := by
    funext j
    simp [GAP.coordPoint, GAP.dilate, Finset.sum_apply]
  rw [hrepr]
  exact AddSubgroup.add_mem _
    (AddSubgroup.zsmul_mem _
      (offset_mem_gapStepLattice_of_symmetric P hP) k)
    (sum_steps_mem_gapStepLattice P fun i ↦ (n i : ℤ))

/-- Every point of a symmetric GAP itself is in its generated step lattice. -/
theorem carrier_subset_gapStepLattice_of_symmetric {d r : ℕ}
    (P : GAP d r) (hP : P.Symmetric) :
    ∀ ⦃x⦄, x ∈ P.carrier → x ∈ gapStepLattice P := by
  intro x hx
  obtain ⟨n, rfl⟩ := GAP.mem_carrier_iff.mp hx
  have hrepr : P.coordPoint n =
      P.offset + ∑ i, (n i : ℤ) • P.steps i := by
    funext j
    simp [GAP.coordPoint, Finset.sum_apply]
  rw [hrepr]
  exact AddSubgroup.add_mem _
    (offset_mem_gapStepLattice_of_symmetric P hP)
    (sum_steps_mem_gapStepLattice P fun i ↦ (n i : ℤ))

/-- Homogeneity of the covered translate implies that the translation point
itself belongs to the progression step lattice. -/
theorem enhanced_translatePoint_mem_gapStepLattice
    {d s D k loss : ℕ} {A : Finset (LatticePoint d)}
    (W : CFP.EnhancedCFPWitness A s D k loss) :
    W.translatePoint ∈ gapStepLattice W.progression := by
  obtain ⟨z, hz⟩ := W.covered_translate_homogeneous
  have hbase : W.translatePoint + (W.progression.dilate k).offset ∈
      gapStepLattice W.progression := by
    rw [hz]
    have hsum := sum_steps_mem_gapStepLattice W.progression z
    convert hsum using 1
    funext j
    simp [Finset.sum_apply]
  have hoffset : (W.progression.dilate k).offset ∈
      gapStepLattice W.progression := by
    rw [GAP.dilate_offset]
    exact AddSubgroup.zsmul_mem _
      (offset_mem_gapStepLattice_of_symmetric W.progression
        W.progression_symmetric) k
  have hsub := AddSubgroup.sub_mem (gapStepLattice W.progression) hbase hoffset
  simpa using hsub

theorem enhanced_mem_gapStepLattice_of_mem_translate_dilate
    {d s D k loss m : ℕ} {A : Finset (LatticePoint d)}
    (W : CFP.EnhancedCFPWitness A s D k loss)
    {p : LatticePoint d}
    (hp : p ∈ CFP.translate W.translatePoint
      (W.progression.dilate m).carrier) :
    p ∈ gapStepLattice W.progression := by
  obtain ⟨q, hq, rfl⟩ := CFP.mem_translate_iff.mp hp
  exact AddSubgroup.add_mem _ (enhanced_translatePoint_mem_gapStepLattice W)
    (dilate_carrier_subset_gapStepLattice_of_symmetric W.progression
      W.progression_symmetric hq)

/-- The obvious coordinate radius of a finite integer zonotope. -/
def zonotopeCoordinateRadius {d : ℕ} (A : Finset (LatticePoint d))
    (i : Fin d) : ℕ :=
  ∑ a ∈ A, (a i).natAbs

/-- An explicit integer box containing every integral point of `zonotope A`.
-/
def zonotopeBoundingBox {d : ℕ} (A : Finset (LatticePoint d)) :
    CFP.IntegerBox d where
  lower i := -(zonotopeCoordinateRadius A i : ℤ)
  upper i := zonotopeCoordinateRadius A i

/-- The finite set of integral points of the ordinary zonotope generated by
`A`. -/
def integralZonotopePoints {d : ℕ} (A : Finset (LatticePoint d)) :
    Finset (LatticePoint d) := by
  classical
  exact (zonotopeBoundingBox A).carrier.filter fun x ↦
    realVector x ∈ zonotope A

/-- Each coordinate of a zonotope point is bounded by the sum of the
absolute values of that coordinate of the generators. -/
theorem abs_coordinate_le_zonotopeCoordinateRadius {d : ℕ}
    {A : Finset (LatticePoint d)} {y : Fin d → ℝ}
    (hy : y ∈ zonotope A) (i : Fin d) :
    |y i| ≤ (zonotopeCoordinateRadius A i : ℝ) := by
  obtain ⟨c, hc, hyc⟩ := hy
  rw [hyc i]
  calc
    |∑ a ∈ A, c a * realVector a i| ≤
        ∑ a ∈ A, |c a * realVector a i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ A, |realVector a i| := by
      apply Finset.sum_le_sum
      intro a ha
      rw [abs_mul, abs_of_nonneg (hc a ha).1]
      exact mul_le_of_le_one_left (abs_nonneg _) (hc a ha).2
    _ = (zonotopeCoordinateRadius A i : ℝ) := by
      simp only [realVector, zonotopeCoordinateRadius, Nat.cast_sum,
        Nat.cast_natAbs, Int.cast_abs]

/-- The box filter defining `integralZonotopePoints` loses no integral
zonotope points. -/
@[simp] theorem mem_integralZonotopePoints_iff {d : ℕ}
    {A : Finset (LatticePoint d)} {x : LatticePoint d} :
    x ∈ integralZonotopePoints A ↔ realVector x ∈ zonotope A := by
  classical
  rw [integralZonotopePoints]
  constructor
  · intro hx
    exact (Finset.mem_filter.mp hx).2
  · intro hx
    apply Finset.mem_filter.mpr
    refine ⟨?_, hx⟩
    rw [CFP.IntegerBox.mem_carrier_iff]
    intro i
    have habs := abs_coordinate_le_zonotopeCoordinateRadius hx i
    have hl : -((zonotopeCoordinateRadius A i : ℕ) : ℝ) ≤
        (x i : ℝ) := (abs_le.mp habs).1
    have hu : (x i : ℝ) ≤
        (zonotopeCoordinateRadius A i : ℝ) := (abs_le.mp habs).2
    constructor
    · change -((zonotopeCoordinateRadius A i : ℕ) : ℤ) ≤ x i
      exact_mod_cast hl
    · change x i ≤ (zonotopeCoordinateRadius A i : ℕ)
      exact_mod_cast hu

/-- The canonical finite target attached to a structured set and a rounding
core: all structured points plus all integral points of the core zonotope. -/
def structuredZonotopeTarget {d : ℕ}
    (structured core : Finset (LatticePoint d)) :
    Finset (LatticePoint d) :=
  structured.biUnion fun p ↦
    (integralZonotopePoints core).image fun x ↦ p + x

/-- Restrict the canonical target to the side lattice.  This restriction is
what makes the eventual rounding residual a point of the progression step
lattice rather than an arbitrary ambient integer vector. -/
def structuredZonotopeTargetIn {d : ℕ} (lattice : Set (LatticePoint d))
    (structured core : Finset (LatticePoint d)) :
    Finset (LatticePoint d) := by
  classical
  exact (structuredZonotopeTarget structured core).filter fun z ↦ z ∈ lattice

@[simp] theorem mem_structuredZonotopeTarget_iff {d : ℕ}
    {structured core : Finset (LatticePoint d)} {z : LatticePoint d} :
    z ∈ structuredZonotopeTarget structured core ↔
      ∃ p ∈ structured, ∃ x : LatticePoint d,
        realVector x ∈ zonotope core ∧ z = p + x := by
  classical
  simp only [structuredZonotopeTarget, Finset.mem_biUnion,
    Finset.mem_image, mem_integralZonotopePoints_iff]
  constructor
  · rintro ⟨p, hp, x, hx, hxp⟩
    exact ⟨p, hp, x, hx, hxp.symm⟩
  · rintro ⟨p, hp, x, hx, rfl⟩
    exact ⟨p, hp, x, hx, rfl⟩

/-- Membership in the canonical target gives exactly the structured-plus-
zonotope decomposition consumed by residual rounding. -/
theorem structuredZonotopeTarget_decomposition {d : ℕ}
    (structured core : Finset (LatticePoint d)) :
    ∀ z ∈ structuredZonotopeTarget structured core,
      ∃ p ∈ structured, ∃ x : LatticePoint d,
        Zonotope.IsZonotopePoint core (fun i ↦ (x i : ℝ)) ∧
          z = p + x := by
  intro z hz
  obtain ⟨p, hp, x, hx, hzx⟩ := mem_structuredZonotopeTarget_iff.mp hz
  exact ⟨p, hp, x, hx, hzx⟩

@[simp] theorem mem_structuredZonotopeTargetIn_iff {d : ℕ}
    {lattice : Set (LatticePoint d)}
    {structured core : Finset (LatticePoint d)} {z : LatticePoint d} :
    z ∈ structuredZonotopeTargetIn lattice structured core ↔
      z ∈ lattice ∧
        ∃ p ∈ structured, ∃ x : LatticePoint d,
          realVector x ∈ zonotope core ∧ z = p + x := by
  classical
  rw [structuredZonotopeTargetIn, Finset.mem_filter,
    mem_structuredZonotopeTarget_iff]
  tauto

/-- A translated cube around `p₀ + zonotopeCenter core q` lies in the
canonical target as soon as the centered zonotope contains the corresponding
cube around zero. -/
theorem mem_structuredZonotopeTarget_of_memCube {d : ℕ}
    {structured core : Finset (LatticePoint d)}
    {p₀ z : LatticePoint d} {q : LatticePoint d → ℝ}
    {radius : ℝ}
    (hp₀ : p₀ ∈ structured)
    (hq : ∀ x ∈ core, 0 ≤ q x ∧ q x ≤ (1 : ℝ) / 2)
    (hthick : ∀ y : Fin d → ℝ, (∀ i, |y i| ≤ radius) →
      y ∈ centeredZonotope core q)
    (hz : MemCube (realVector p₀ + zonotopeCenter core q) radius z) :
    z ∈ structuredZonotopeTarget structured core := by
  apply mem_structuredZonotopeTarget_iff.mpr
  refine ⟨p₀, hp₀, z - p₀, ?_, by abel⟩
  apply mem_zonotope_of_centeredZonotope_cube core q radius hq hthick
  intro i
  have hzi := hz i
  change |(((z - p₀) i : ℤ) : ℝ) - zonotopeCenter core q i| ≤ radius
  have heq : (((z - p₀) i : ℤ) : ℝ) - zonotopeCenter core q i =
      (z i : ℝ) - ((p₀ i : ℝ) + zonotopeCenter core q i) := by
    simp only [Pi.sub_apply, Int.cast_sub]
    ring
  rw [heq]
  simpa only [realVector, Pi.add_apply] using hzi

/-- Lattice-restricted version of the cube inclusion. -/
theorem mem_structuredZonotopeTargetIn_of_memCube {d : ℕ}
    {lattice : Set (LatticePoint d)}
    {structured core : Finset (LatticePoint d)}
    {p₀ z : LatticePoint d} {q : LatticePoint d → ℝ}
    {radius : ℝ}
    (hzL : z ∈ lattice) (hp₀ : p₀ ∈ structured)
    (hq : ∀ x ∈ core, 0 ≤ q x ∧ q x ≤ (1 : ℝ) / 2)
    (hthick : ∀ y : Fin d → ℝ, (∀ i, |y i| ≤ radius) →
      y ∈ centeredZonotope core q)
    (hz : MemCube (realVector p₀ + zonotopeCenter core q) radius z) :
    z ∈ structuredZonotopeTargetIn lattice structured core := by
  rw [mem_structuredZonotopeTargetIn_iff]
  refine ⟨hzL, ?_⟩
  exact mem_structuredZonotopeTarget_iff.mp
    (mem_structuredZonotopeTarget_of_memCube hp₀ hq hthick hz)

/-- Moving the center coordinatewise by at most `error` enlarges a cube by
that amount.  This is the center-error estimate used after the small CFP
reserved and discarded pieces are removed. -/
theorem memCube_of_center_error {d : ℕ}
    {center base : Fin d → ℝ} {radius error : ℝ}
    {z : LatticePoint d}
    (hz : MemCube center radius z)
    (herror : ∀ i, |center i - base i| ≤ error) :
    MemCube base (radius + error) z := by
  intro i
  calc
    |(z i : ℝ) - base i| =
        |((z i : ℝ) - center i) + (center i - base i)| := by
          congr 1
          ring
    _ ≤ |(z i : ℝ) - center i| + |center i - base i| :=
      abs_add_le _ _
    _ ≤ radius + error := add_le_add (hz i) (herror i)

/-- Faithful step-lattice-qualified residual absorption.  The rounding error
need only be absorbed when it belongs to the progression step lattice; that
membership is proved from `hxL` and `hcoreL` after the subset is rounded. -/
theorem roundingErrorsAbsorbedBy_cfpTranslate_add_of_margin_stepLattice
    {d r structuredDilation margin coveredDilation : ℕ}
    (target core : Finset (LatticePoint d)) (width : ℝ)
    (P : GAP d r) (hP : P.Symmetric)
    (translatePoint : LatticePoint d)
    (hwidth : 0 ≤ width)
    (hcore : ∀ x ∈ core, ∀ i, |(x i : ℝ)| ≤ width)
    (hcoreL : ∀ x ∈ core, x ∈ gapStepLattice P)
    (htarget : ∀ z ∈ target,
      ∃ p ∈ CFP.translate translatePoint
          (P.dilate structuredDilation).carrier,
        ∃ x : LatticePoint d,
          Zonotope.IsZonotopePoint core (fun i ↦ (x i : ℝ)) ∧
          x ∈ gapStepLattice P ∧ z = p + x)
    (hscale : structuredDilation + margin ≤ coveredDilation)
    (herrorBox : ∀ e : LatticePoint d, e ∈ gapStepLattice P →
      (∀ i, |(e i : ℝ)| ≤
        Real.sqrt (((d * core.card : ℕ) : ℝ)) * width) →
      e ∈ (P.dilate margin).carrier) :
    RoundingErrorsAbsorbedBy target core
      (CFP.translate translatePoint
        (P.dilate coveredDilation).carrier) := by
  intro z hz
  obtain ⟨p, hp, x, hxZ, hxL, rfl⟩ := htarget z hz
  obtain ⟨T, hTcore, hTerror⟩ :=
    Zonotope.zonotope_rounding core (fun i ↦ (x i : ℝ)) width hxZ
      hwidth hcore
  have hsumL : (∑ y ∈ T, y) ∈ gapStepLattice P := by
    exact AddSubgroup.sum_mem _ fun y hy ↦ hcoreL y (hTcore hy)
  have herrL : x - ∑ y ∈ T, y ∈ gapStepLattice P :=
    AddSubgroup.sub_mem _ hxL hsumL
  have herrMargin : x - ∑ y ∈ T, y ∈ (P.dilate margin).carrier := by
    apply herrorBox _ herrL
    intro i
    simpa [Finset.sum_apply] using hTerror i
  refine ⟨T, hTcore, ?_⟩
  rw [add_sub_assoc]
  exact add_mem_translate_dilate_of_margin P hP translatePoint hscale hp
    herrMargin

namespace IntersectionSideInput

variable {d : ℕ} {pool : Finset (LatticePoint d)}
    {a : LatticePoint d} {orientation : Orientation}

/-- For a side whose target is the canonical structured-zonotope target,
the target decomposition needed by the concrete margin-rounding theorem is
automatic. -/
theorem target_decomposition_of_eq_structuredZonotopeTarget
    (I : IntersectionSideInput pool a orientation)
    (structured : Finset (LatticePoint d))
    (htarget : I.target =
      structuredZonotopeTarget structured I.roundingCore) :
    ∀ z ∈ I.target, ∃ p ∈ structured,
      ∃ x : LatticePoint d,
        Zonotope.IsZonotopePoint I.roundingCore
          (fun i ↦ (x i : ℝ)) ∧ z = p + x := by
  rw [htarget]
  exact structuredZonotopeTarget_decomposition structured I.roundingCore

/-- Lemma 14 for the canonical target.  No arbitrary target-containment
hypothesis remains. -/
theorem lemma14TargetThickness_of_eq_structuredZonotopeTarget
    (I : IntersectionSideInput pool a orientation)
    (structured : Finset (LatticePoint d)) (p₀ : LatticePoint d)
    (q : LatticePoint d → ℝ) (center : Fin d → ℝ) (radius : ℝ)
    (htarget : I.target =
      structuredZonotopeTarget structured I.roundingCore)
    (hp₀ : p₀ ∈ structured)
    (hcenter : center = realVector p₀ + zonotopeCenter I.roundingCore q)
    (hq : ∀ x ∈ I.roundingCore,
      0 ≤ q x ∧ q x ≤ (1 : ℝ) / 2)
    (hthick : ∀ y : Fin d → ℝ, (∀ i, |y i| ≤ radius) →
      y ∈ centeredZonotope I.roundingCore q) :
    I.Lemma14TargetThickness center radius := by
  intro z hzL hz
  rw [htarget]
  apply mem_structuredZonotopeTarget_of_memCube hp₀ hq hthick
  simpa only [hcenter] using hz

/-- Lemma 14 for the lattice-restricted canonical target. -/
theorem lemma14TargetThickness_of_eq_structuredZonotopeTargetIn
    (I : IntersectionSideInput pool a orientation)
    (structured : Finset (LatticePoint d)) (p₀ : LatticePoint d)
    (q : LatticePoint d → ℝ) (center : Fin d → ℝ) (radius : ℝ)
    (htarget : I.target = structuredZonotopeTargetIn I.lattice
      structured I.roundingCore)
    (hp₀ : p₀ ∈ structured)
    (hcenter : center = realVector p₀ + zonotopeCenter I.roundingCore q)
    (hq : ∀ x ∈ I.roundingCore,
      0 ≤ q x ∧ q x ≤ (1 : ℝ) / 2)
    (hthick : ∀ y : Fin d → ℝ, (∀ i, |y i| ≤ radius) →
      y ∈ centeredZonotope I.roundingCore q) :
    I.Lemma14TargetThickness center radius := by
  intro z hzL hz
  rw [htarget]
  apply mem_structuredZonotopeTargetIn_of_memCube hzL hp₀ hq hthick
  simpa only [hcenter] using hz

/-- Lemma 14 for the canonical target with the source's explicit center
error.  The error is absorbed by asking for centered-zonotope thickness at
the enlarged radius; no exact equality of real centers is required. -/
theorem lemma14TargetThickness_of_eq_structuredZonotopeTargetIn_centerError
    (I : IntersectionSideInput pool a orientation)
    (structured : Finset (LatticePoint d)) (p₀ : LatticePoint d)
    (q : LatticePoint d → ℝ) (center : Fin d → ℝ)
    (radius error : ℝ)
    (htarget : I.target = structuredZonotopeTargetIn I.lattice
      structured I.roundingCore)
    (hp₀ : p₀ ∈ structured)
    (hcenterError : ∀ i,
      |center i - (realVector p₀ + zonotopeCenter I.roundingCore q) i| ≤
        error)
    (hq : ∀ x ∈ I.roundingCore,
      0 ≤ q x ∧ q x ≤ (1 : ℝ) / 2)
    (hthick : ∀ y : Fin d → ℝ, (∀ i, |y i| ≤ radius + error) →
      y ∈ centeredZonotope I.roundingCore q) :
    I.Lemma14TargetThickness center radius := by
  intro z hzL hz
  rw [htarget]
  apply mem_structuredZonotopeTargetIn_of_memCube hzL hp₀ hq hthick
  exact memCube_of_center_error hz hcenterError

/-- Residual absorption for a side with its target definition exposed.
This removes the formerly independent structured-decomposition input. -/
theorem lemma13ResidualAbsorption_of_eq_structuredZonotopeTarget
    (I : IntersectionSideInput pool a orientation)
    (structuredDilation margin : ℕ) (width : ℝ)
    (htarget : I.target = structuredZonotopeTarget
      (CFP.translate I.witness.translatePoint
        (I.witness.progression.dilate structuredDilation).carrier)
      I.roundingCore)
    (hwidth : 0 ≤ width)
    (hcore : ∀ x ∈ I.roundingCore, ∀ i, |(x i : ℝ)| ≤ width)
    (hscale : structuredDilation + margin ≤ I.dilation)
    (herrorBox : ∀ e : LatticePoint d,
      (∀ i, |(e i : ℝ)| ≤
        Real.sqrt (((d * I.roundingCore.card : ℕ) : ℝ)) * width) →
      e ∈ (I.witness.progression.dilate margin).carrier) :
    I.Lemma13ResidualAbsorption := by
  apply I.lemma13ResidualAbsorption_of_zonotope_margin
    structuredDilation margin width hwidth hcore
  · exact I.target_decomposition_of_eq_structuredZonotopeTarget _ htarget
  · exact hscale
  · exact herrorBox

/-- Faithful residual absorption for the canonical step-lattice-restricted
target.  The error-box hypothesis is asserted only on the step lattice. -/
theorem lemma13ResidualAbsorption_of_eq_structuredZonotopeTargetIn
    (I : IntersectionSideInput pool a orientation)
    (structuredDilation margin : ℕ) (width : ℝ)
    (htarget : I.target = structuredZonotopeTargetIn
      (gapStepLattice I.witness.progression : Set (LatticePoint d))
      (CFP.translate I.witness.translatePoint
        (I.witness.progression.dilate structuredDilation).carrier)
      I.roundingCore)
    (hcoreWitness : I.roundingCore ⊆ I.witness.core)
    (hwidth : 0 ≤ width)
    (hcore : ∀ x ∈ I.roundingCore, ∀ i, |(x i : ℝ)| ≤ width)
    (hscale : structuredDilation + margin ≤ I.dilation)
    (herrorBox : ∀ e : LatticePoint d,
      e ∈ gapStepLattice I.witness.progression →
      (∀ i, |(e i : ℝ)| ≤
        Real.sqrt (((d * I.roundingCore.card : ℕ) : ℝ)) * width) →
      e ∈ (I.witness.progression.dilate margin).carrier) :
    I.Lemma13ResidualAbsorption := by
  have hcoreL : ∀ x ∈ I.roundingCore,
      x ∈ gapStepLattice I.witness.progression := by
    intro x hx
    have hxCarrier : x ∈ I.witness.progression.carrier :=
      I.witness.core_zero_subset
        (Finset.mem_insert_of_mem (hcoreWitness hx))
    apply carrier_subset_gapStepLattice_of_symmetric
      I.witness.progression I.witness.progression_symmetric
    exact hxCarrier
  have hdecomp : ∀ z ∈ I.target,
      ∃ p ∈ CFP.translate I.witness.translatePoint
          (I.witness.progression.dilate structuredDilation).carrier,
        ∃ x : LatticePoint d,
          Zonotope.IsZonotopePoint I.roundingCore (fun i ↦ (x i : ℝ)) ∧
          x ∈ gapStepLattice I.witness.progression ∧ z = p + x := by
    intro z hz
    rw [htarget, mem_structuredZonotopeTargetIn_iff] at hz
    obtain ⟨hzL, p, hp, x, hxZ, hzx⟩ := hz
    have hpL := enhanced_mem_gapStepLattice_of_mem_translate_dilate
      I.witness hp
    have hxL : x ∈ gapStepLattice I.witness.progression := by
      have hsub := AddSubgroup.sub_mem
        (gapStepLattice I.witness.progression) hzL hpL
      have hxeq : x = z - p := by rw [hzx]; abel
      rwa [hxeq]
    exact ⟨p, hp, x, hxZ, hxL, hzx⟩
  exact roundingErrorsAbsorbedBy_cfpTranslate_add_of_margin_stepLattice
    I.target I.roundingCore width I.witness.progression
    I.witness.progression_symmetric I.witness.translatePoint hwidth hcore
    hcoreL hdecomp hscale herrorBox

/-- The canonical source-faithful side input attached to an enhanced CFP
witness.  Its target is defined, rather than assumed, to be the
step-lattice-restricted structured-zonotope target. -/
def canonicalStepLattice
    {s D k loss structuredDilation : ℕ}
    (W : CFP.EnhancedCFPWitness (orientedTranslate orientation a pool)
      s D k loss)
    (roundingCore : Finset (LatticePoint d))
    (hcorePool : roundingCore ⊆ orientedTranslate orientation a pool)
    (hdisjoint : Disjoint W.reserved roundingCore) :
    IntersectionSideInput pool a orientation where
  reserveBound := s
  rankBound := D
  dilation := k
  loss := loss
  witness := W
  target := structuredZonotopeTargetIn
    (gapStepLattice W.progression : Set (LatticePoint d))
    (CFP.translate W.translatePoint
      (W.progression.dilate structuredDilation).carrier)
    roundingCore
  roundingCore := roundingCore
  roundingCore_subset := hcorePool
  reserved_disjoint_roundingCore := hdisjoint
  lattice := gapStepLattice W.progression

end IntersectionSideInput

namespace Theorem4PostCFPData

variable {d : ℕ} {A : Finset (LatticePoint d)}

/-- Assemble both canonical step-lattice targets.  The Lemma 13 and Lemma 14
predicates are proved internally from the literal target definition,
step-lattice-qualified margin absorption, and centered-zonotope thickness.
No arbitrary target or lattice is an input. -/
def ofCanonicalStepLatticeTargets
    {R : ℕ} {a : LatticePoint d}
    {A₁ A₂ : Finset (LatticePoint d)}
    {s₁ D₁ k₁ loss₁ structuredDilation₁ margin₁ : ℕ}
    {s₂ D₂ k₂ loss₂ structuredDilation₂ margin₂ : ℕ}
    (hd : 0 < d) (ha : a ∈ A)
    (hA₁ : A₁ ⊆ A.erase a) (hA₂ : A₂ ⊆ A.erase a)
    (hdisjoint : Disjoint A₁ A₂)
    (W₁ : CFP.EnhancedCFPWitness (orientedTranslate .forward a A₁)
      s₁ D₁ k₁ loss₁)
    (W₂ : CFP.EnhancedCFPWitness (orientedTranslate .reverse a A₂)
      s₂ D₂ k₂ loss₂)
    (roundingCore₁ roundingCore₂ : Finset (LatticePoint d))
    (hreserved₁ : Disjoint W₁.reserved roundingCore₁)
    (hreserved₂ : Disjoint W₂.reserved roundingCore₂)
    (hcoreWitness₁ : roundingCore₁ ⊆ W₁.core)
    (hcoreWitness₂ : roundingCore₂ ⊆ W₂.core)
    (width₁ width₂ : ℝ)
    (hwidth₁ : 0 ≤ width₁) (hwidth₂ : 0 ≤ width₂)
    (hcoreBound₁ : ∀ x ∈ roundingCore₁, ∀ i, |(x i : ℝ)| ≤ width₁)
    (hcoreBound₂ : ∀ x ∈ roundingCore₂, ∀ i, |(x i : ℝ)| ≤ width₂)
    (hscale₁ : structuredDilation₁ + margin₁ ≤ k₁)
    (hscale₂ : structuredDilation₂ + margin₂ ≤ k₂)
    (herrorBox₁ : ∀ e : LatticePoint d,
      e ∈ gapStepLattice W₁.progression →
      (∀ i, |(e i : ℝ)| ≤
        Real.sqrt (((d * roundingCore₁.card : ℕ) : ℝ)) * width₁) →
      e ∈ (W₁.progression.dilate margin₁).carrier)
    (herrorBox₂ : ∀ e : LatticePoint d,
      e ∈ gapStepLattice W₂.progression →
      (∀ i, |(e i : ℝ)| ≤
        Real.sqrt (((d * roundingCore₂.card : ℕ) : ℝ)) * width₂) →
      e ∈ (W₂.progression.dilate margin₂).carrier)
    (q₁ q₂ : LatticePoint d → ℝ) (center : Fin d → ℝ)
    (p₀₁ p₀₂ : LatticePoint d)
    (hp₀₁ : p₀₁ ∈ CFP.translate W₁.translatePoint
      (W₁.progression.dilate structuredDilation₁).carrier)
    (hp₀₂ : p₀₂ ∈ CFP.translate W₂.translatePoint
      (W₂.progression.dilate structuredDilation₂).carrier)
    (centerError₁ centerError₂ : ℝ)
    (hcenter₁ : ∀ i,
      |center i - (realVector p₀₁ + zonotopeCenter roundingCore₁ q₁) i| ≤
        centerError₁)
    (hcenter₂ : ∀ i,
      |center i - (realVector p₀₂ + zonotopeCenter roundingCore₂ q₂) i| ≤
        centerError₂)
    (hq₁ : ∀ x ∈ roundingCore₁, 0 ≤ q₁ x ∧ q₁ x ≤ (1 : ℝ) / 2)
    (hq₂ : ∀ x ∈ roundingCore₂, 0 ≤ q₂ x ∧ q₂ x ≤ (1 : ℝ) / 2)
    (hthick₁ : ∀ y : Fin d → ℝ,
      (∀ i, |y i| ≤ (3 * R + 2 : ℕ) + centerError₁) →
      y ∈ centeredZonotope roundingCore₁ q₁)
    (hthick₂ : ∀ y : Fin d → ℝ,
      (∀ i, |y i| ≤ (3 * R + 2 : ℕ) + centerError₂) →
      y ∈ centeredZonotope roundingCore₂ q₂)
    (hcover : HasCommonCoveringRadius
      (gapStepLattice W₁.progression : Set (LatticePoint d))
      (gapStepLattice W₂.progression : Set (LatticePoint d)) R) :
    Theorem4PostCFPData A := by
  let I₁ : IntersectionSideInput A₁ a .forward :=
    IntersectionSideInput.canonicalStepLattice
      (structuredDilation := structuredDilation₁) W₁ roundingCore₁
      (hcoreWitness₁.trans W₁.core_subset) hreserved₁
  let I₂ : IntersectionSideInput A₂ a .reverse :=
    IntersectionSideInput.canonicalStepLattice
      (structuredDilation := structuredDilation₂) W₂ roundingCore₂
      (hcoreWitness₂.trans W₂.core_subset) hreserved₂
  have hround₁ : I₁.Lemma13ResidualAbsorption := by
    apply I₁.lemma13ResidualAbsorption_of_eq_structuredZonotopeTargetIn
      structuredDilation₁ margin₁ width₁
    · rfl
    · exact hcoreWitness₁
    · exact hwidth₁
    · exact hcoreBound₁
    · exact hscale₁
    · exact herrorBox₁
  have hround₂ : I₂.Lemma13ResidualAbsorption := by
    apply I₂.lemma13ResidualAbsorption_of_eq_structuredZonotopeTargetIn
      structuredDilation₂ margin₂ width₂
    · rfl
    · exact hcoreWitness₂
    · exact hwidth₂
    · exact hcoreBound₂
    · exact hscale₂
    · exact herrorBox₂
  have htarget₁ : I₁.Lemma14TargetThickness center (3 * R + 2) := by
    apply I₁.lemma14TargetThickness_of_eq_structuredZonotopeTargetIn_centerError
      (CFP.translate W₁.translatePoint
        (W₁.progression.dilate structuredDilation₁).carrier)
      p₀₁ q₁ center (3 * R + 2) centerError₁
    · rfl
    · exact hp₀₁
    · exact hcenter₁
    · exact hq₁
    · simpa [I₁, IntersectionSideInput.canonicalStepLattice] using hthick₁
  have htarget₂ : I₂.Lemma14TargetThickness center (3 * R + 2) := by
    apply I₂.lemma14TargetThickness_of_eq_structuredZonotopeTargetIn_centerError
      (CFP.translate W₂.translatePoint
        (W₂.progression.dilate structuredDilation₂).carrier)
      p₀₂ q₂ center (3 * R + 2) centerError₂
    · rfl
    · exact hp₀₂
    · exact hcenter₂
    · exact hq₂
    · simpa [I₂, IntersectionSideInput.canonicalStepLattice] using hthick₂
  have hcovolume : FullRankLatticeCovolumeConclusion I₁ I₂ R := by
    exact hcover
  exact ofSourceLemmas hd ha hA₁ hA₂ hdisjoint I₁ I₂
    hround₁ hround₂ htarget₁ htarget₂ hcovolume

end Theorem4PostCFPData

end


end Erdos186.PZ.Intersection
