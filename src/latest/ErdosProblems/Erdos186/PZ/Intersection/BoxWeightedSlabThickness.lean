/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.BoxWeightedFunctionalSlab
import ErdosProblems.Erdos186.PZ.Intersection.WeightedSlabThickness

/-!
# Anisotropic thickness from box-weighted functional slabs

The support function of the coordinate box with radii proportional to the
side lengths of `B` is exactly controlled by `boxCoefficientMass B`.  This
is the separation statement which preserves all source GAP widths.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-- The support bound for a coordinate box with arbitrary coordinate
radii. -/
theorem apply_le_coordinateBoxSupport {d : ℕ}
    (f : (Fin d → ℝ) →L[ℝ] ℝ) (radius : Fin d → ℝ)
    {y : Fin d → ℝ} (hy : ∀ i, |y i| ≤ radius i) :
    f y ≤ ∑ i, radius i * |f (Pi.single i 1)| := by
  have hybasis : y = ∑ i, y i • (Pi.single i 1 : Fin d → ℝ) := by
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp
    · intro i _hi hij
      simp [Pi.single_apply, hij]
    · simp
  calc
    f y ≤ |f y| := le_abs_self _
    _ = |∑ i, y i * f (Pi.single i 1)| := by
      apply congrArg abs
      calc
        f y = f (∑ i, y i • (Pi.single i 1 : Fin d → ℝ)) :=
          congrArg f hybasis
        _ = ∑ i, y i * f (Pi.single i 1) := by
          rw [map_sum]
          simp only [map_smul, smul_eq_mul]
    _ ≤ ∑ i, |y i * f (Pi.single i 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |y i| * |f (Pi.single i 1)| := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [abs_mul]
    _ ≤ ∑ i, radius i * |f (Pi.single i 1)| := by
      apply Finset.sum_le_sum
      intro i _hi
      exact mul_le_mul_of_nonneg_right (hy i) (abs_nonneg _)

/-- A support-function lower bound implies containment of an arbitrary
coordinate box in a finite centered zonotope. -/
theorem coordinateBox_subset_centeredZonotope_of_support {d : ℕ}
    (A : Finset (LatticePoint d)) (q : LatticePoint d → ℝ)
    (hq : ∀ x ∈ A, 0 ≤ q x) (radius : Fin d → ℝ)
    (hSupport : ∀ f : (Fin d → ℝ) →L[ℝ] ℝ,
      (∑ i, radius i * |f (Pi.single i 1)|) ≤
        ∑ x ∈ A, q x * |f (realVector x)|) :
    {y : Fin d → ℝ | ∀ i, |y i| ≤ radius i} ⊆
      centeredZonotope A q := by
  intro y hy
  by_contra hnot
  obtain ⟨f, u, hzu, huy⟩ := geometric_hahn_banach_closed_point
    (convex_centeredZonotope A q) (isClosed_centeredZonotope A q hq) hnot
  obtain ⟨z, hz, hfz⟩ :=
    exists_mem_centeredZonotope_apply_eq_sum_abs A q hq f
  have hfy : f y ≤ ∑ i, radius i * |f (Pi.single i 1)| :=
    apply_le_coordinateBoxSupport f radius hy
  have hzs : ∑ x ∈ A, q x * |f (realVector x)| < u := by
    rw [← hfz]
    exact hzu z hz
  exact (not_lt_of_ge (hfy.trans (hSupport f))) (hzs.trans huy)

/-- Weighted slab-cardinality criterion for a coordinate box whose radii
are proportional to the side lengths of `B`. -/
theorem box_subset_centeredZonotope_of_boxWeighted_slabCard
    {d : ℕ} (B : IntegerBox d)
    (hBside : ∀ i, 0 < integerBoxSideLength B i)
    (input core : Finset (LatticePoint d))
    (hcore : core ⊆ input) (q : LatticePoint d → ℝ)
    (hqnonneg : ∀ x ∈ core, 0 ≤ q x)
    (cap massLower radius t : ℝ)
    (hcap : 0 ≤ cap)
    (hqcap : ∀ x ∈ input, q x ≤ cap)
    (htotal : massLower ≤ ∑ x ∈ input, q x)
    (missing slab : ℕ)
    (hmissing : (input \ core).card ≤ missing)
    (ht : 0 < t)
    (hslab : ∀ f : (Fin d → ℝ) →L[ℝ] ℝ, f ≠ 0 →
      (core.filter fun x ↦
        |f (realVector x)| < t * boxCoefficientMass B f).card ≤ slab)
    (hradius : radius ≤
      t * (massLower - ((missing + slab : ℕ) : ℝ) * cap)) :
    {y : Fin d → ℝ |
      ∀ i, |y i| ≤ radius * integerBoxSideLength B i} ⊆
      centeredZonotope core q := by
  apply coordinateBox_subset_centeredZonotope_of_support core q hqnonneg
    (fun i ↦ radius * integerBoxSideLength B i)
  intro f
  by_cases hf : f = 0
  · subst f
    simp only [zero_apply, abs_zero, mul_zero, Finset.sum_const_zero]
    exact le_rfl
  have hmassPos : 0 < boxCoefficientMass B f := by
    have hcoeffPos := coefficientMass_pos f hf
    unfold coefficientMass at hcoeffPos
    unfold boxCoefficientMass
    exact hcoeffPos.trans_le (Finset.sum_le_sum fun i _hi ↦ by
      have hsideOne : 1 ≤ integerBoxSideLength B i := by
        have hs := hBside i
        unfold integerBoxSideLength at hs
        have hintDiff : (0 : ℤ) < B.upper i - B.lower i := by
          exact_mod_cast hs
        have hintOne : (1 : ℤ) ≤ B.upper i - B.lower i := by omega
        unfold integerBoxSideLength
        exact_mod_cast hintOne
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hsideOne
        (abs_nonneg (f (Pi.single i 1))))
  have houtside := weightedOutsideMass_lower input core hcore q cap massLower
    hcap hqcap htotal
    (fun x ↦ t * boxCoefficientMass B f ≤ |f (realVector x)|)
    missing slab hmissing (by simpa only [not_le] using hslab f hf)
  calc
    (∑ i, (radius * integerBoxSideLength B i) *
        |f (Pi.single i 1)|) = radius * boxCoefficientMass B f := by
      unfold boxCoefficientMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ ≤ (t * (massLower - ((missing + slab : ℕ) : ℝ) * cap)) *
          boxCoefficientMass B f :=
      mul_le_mul_of_nonneg_right hradius hmassPos.le
    _ ≤ (t * (∑ x ∈ core.filter
          (fun x ↦ t * boxCoefficientMass B f ≤ |f (realVector x)|),
          q x)) * boxCoefficientMass B f := by
      apply mul_le_mul_of_nonneg_right _ hmassPos.le
      exact mul_le_mul_of_nonneg_left houtside ht.le
    _ = (t * boxCoefficientMass B f) *
          (∑ x ∈ core.filter
            (fun x ↦ t * boxCoefficientMass B f ≤ |f (realVector x)|),
            q x) := by ring
    _ ≤ ∑ x ∈ core, q x * |f (realVector x)| :=
      threshold_mul_massOutside_le_support core q hqnonneg f
        (t * boxCoefficientMass B f)

end

end Erdos186.PZ.Intersection
