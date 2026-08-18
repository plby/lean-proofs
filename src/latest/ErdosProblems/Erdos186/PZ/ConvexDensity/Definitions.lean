/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.ConvexGeometry
import Mathlib

/-!
# Definitions for the Pham--Zakharov convex-density lemma

This file gives a literal finite-dimensional formulation of Lemma 1 of
Pham--Zakharov.  It contains definitions and elementary interface lemmas only;
in particular, it does not assert the convex-density lemma.

There are two minor points worth making explicit.

* A convex body is required to be compact and convex and to have nonempty
  interior.  Thus its Euclidean volume is positive and finite.
* Relative volume is kept in `ENNReal`.  This avoids making an infinite measure
  look like zero through `ENNReal.toReal`; for subsets of a convex body the
  denominator is nonzero and finite, and the usual division inequality applies.

The quantifier `largeEnough` in `PZLemmaOneStatement` occurs after `delta` and
before the body and point set.  This formalizes the paper's phrase “`|A|` is
sufficiently large in `delta`”: once the dimension and error are fixed, the
threshold may depend on `delta`, but not on the particular body or point set.
-/

open Set MeasureTheory
open scoped ENNReal

namespace Erdos186.PZ.ConvexDensity

noncomputable section

/-- Euclidean `d`-space, in the same coordinate model used throughout Mathlib. -/
abbrev EuclideanPoint (d : ℕ) := EuclideanSpace ℝ (Fin d)

/--
A full-dimensional Euclidean convex body.

Mathlib's bundled `ConvexBody` only requires nonemptiness.  Lemma 1 of
Pham--Zakharov assumes nonempty interior, so we use this predicate rather than
silently weakening that hypothesis.
-/
def IsConvexBody {d : ℕ} (Omega : Set (EuclideanPoint d)) : Prop :=
  Convex ℝ Omega ∧ IsCompact Omega ∧ (interior Omega).Nonempty

namespace IsConvexBody

variable {d : ℕ} {Omega : Set (EuclideanPoint d)}

theorem convex (hOmega : IsConvexBody Omega) : Convex ℝ Omega :=
  hOmega.1

theorem isCompact (hOmega : IsConvexBody Omega) : IsCompact Omega :=
  hOmega.2.1

theorem interior_nonempty (hOmega : IsConvexBody Omega) :
    (interior Omega).Nonempty :=
  hOmega.2.2

theorem nonempty (hOmega : IsConvexBody Omega) : Omega.Nonempty :=
  hOmega.interior_nonempty.mono interior_subset

theorem measurableSet (hOmega : IsConvexBody Omega) : MeasurableSet Omega :=
  hOmega.isCompact.measurableSet

theorem nullMeasurableSet (hOmega : IsConvexBody Omega) :
    NullMeasurableSet Omega (volume : Measure (EuclideanPoint d)) :=
  hOmega.measurableSet.nullMeasurableSet

theorem volume_pos (hOmega : IsConvexBody Omega) :
    0 < (volume : Measure (EuclideanPoint d)) Omega :=
  Measure.measure_pos_of_nonempty_interior (volume : Measure (EuclideanPoint d))
    hOmega.interior_nonempty

theorem volume_ne_zero (hOmega : IsConvexBody Omega) :
    (volume : Measure (EuclideanPoint d)) Omega ≠ 0 :=
  hOmega.volume_pos.ne'

theorem volume_lt_top (hOmega : IsConvexBody Omega) :
    (volume : Measure (EuclideanPoint d)) Omega < ⊤ :=
  hOmega.isCompact.measure_lt_top

theorem volume_ne_top (hOmega : IsConvexBody Omega) :
    (volume : Measure (EuclideanPoint d)) Omega ≠ ⊤ :=
  hOmega.volume_lt_top.ne

theorem volume_toReal_pos (hOmega : IsConvexBody Omega) :
    0 < ((volume : Measure (EuclideanPoint d)) Omega).toReal :=
  ENNReal.toReal_pos hOmega.volume_ne_zero hOmega.volume_ne_top

end IsConvexBody

/-- Euclidean volume of `Omega'`, divided by Euclidean volume of `Omega`. -/
def relativeVolume {d : ℕ} (Omega' Omega : Set (EuclideanPoint d)) : ℝ≥0∞ :=
  (volume : Measure (EuclideanPoint d)) Omega' /
    (volume : Measure (EuclideanPoint d)) Omega

theorem relativeVolume_nonneg {d : ℕ} (Omega' Omega : Set (EuclideanPoint d)) :
    0 ≤ relativeVolume Omega' Omega :=
  bot_le

theorem relativeVolume_self {d : ℕ} {Omega : Set (EuclideanPoint d)}
    (hOmega : IsConvexBody Omega) : relativeVolume Omega Omega = 1 := by
  exact ENNReal.div_self hOmega.volume_ne_zero hOmega.volume_ne_top

/-- For a genuine convex body, a relative-volume bound is exactly the usual
scaled-volume bound. -/
theorem relativeVolume_le_iff {d : ℕ} {Omega' Omega : Set (EuclideanPoint d)}
    (hOmega : IsConvexBody Omega) (eta : ℝ) :
    relativeVolume Omega' Omega ≤ ENNReal.ofReal eta ↔
      (volume : Measure (EuclideanPoint d)) Omega' ≤
        ENNReal.ofReal eta * (volume : Measure (EuclideanPoint d)) Omega := by
  exact ENNReal.div_le_iff hOmega.volume_ne_zero hOmega.volume_ne_top

/-- A subset of a convex body has relative volume at most one. -/
theorem relativeVolume_le_one {d : ℕ} {Omega' Omega : Set (EuclideanPoint d)}
    (hOmega : IsConvexBody Omega) (hsub : Omega' ⊆ Omega) :
    relativeVolume Omega' Omega ≤ 1 := by
  rw [relativeVolume, ENNReal.div_le_iff hOmega.volume_ne_zero hOmega.volume_ne_top,
    one_mul]
  exact measure_mono hsub

/-- The numerator of a relative volume is finite whenever it is contained in
the reference convex body. -/
theorem volume_ne_top_of_subset {d : ℕ} {Omega' Omega : Set (EuclideanPoint d)}
    (hOmega : IsConvexBody Omega) (hsub : Omega' ⊆ Omega) :
    (volume : Measure (EuclideanPoint d)) Omega' ≠ ⊤ :=
  measure_ne_top_of_subset hsub hOmega.volume_ne_top

/-- On subsets of a convex body, `toReal` gives the ordinary real-valued
volume ratio. -/
theorem relativeVolume_toReal {d : ℕ} {Omega' Omega : Set (EuclideanPoint d)}
    (_hOmega : IsConvexBody Omega) (_hsub : Omega' ⊆ Omega) :
    (relativeVolume Omega' Omega).toReal =
      ((volume : Measure (EuclideanPoint d)) Omega').toReal /
        ((volume : Measure (EuclideanPoint d)) Omega).toReal := by
  exact ENNReal.toReal_div _ _

/-- The points of a finite set which lie in a specified region. -/
def pointsIn {d : ℕ} (X : Finset (EuclideanPoint d))
    (Omega : Set (EuclideanPoint d)) : Finset (EuclideanPoint d) := by
  classical
  exact X.filter fun x => x ∈ Omega

@[simp]
theorem mem_pointsIn {d : ℕ} {X : Finset (EuclideanPoint d)}
    {Omega : Set (EuclideanPoint d)} {x : EuclideanPoint d} :
    x ∈ pointsIn X Omega ↔ x ∈ X ∧ x ∈ Omega := by
  simp [pointsIn]

@[simp]
theorem coe_pointsIn {d : ℕ} (X : Finset (EuclideanPoint d))
    (Omega : Set (EuclideanPoint d)) :
    (pointsIn X Omega : Set (EuclideanPoint d)) = (X : Set (EuclideanPoint d)) ∩ Omega := by
  ext x
  simp

theorem pointsIn_subset {d : ℕ} (X : Finset (EuclideanPoint d))
    (Omega : Set (EuclideanPoint d)) : pointsIn X Omega ⊆ X := by
  classical
  exact Finset.filter_subset _ _

theorem card_pointsIn_le {d : ℕ} (X : Finset (EuclideanPoint d))
    (Omega : Set (EuclideanPoint d)) : (pointsIn X Omega).card ≤ X.card := by
  classical
  exact Finset.card_filter_le _ _

theorem card_pointsIn_cast_le {d : ℕ} (X : Finset (EuclideanPoint d))
    (Omega : Set (EuclideanPoint d)) :
    ((pointsIn X Omega).card : ℝ) ≤ (X.card : ℝ) := by
  exact_mod_cast card_pointsIn_le X Omega

theorem pointsIn_eq_self_of_subset {d : ℕ} {X : Finset (EuclideanPoint d)}
    {Omega : Set (EuclideanPoint d)} (hX : (X : Set (EuclideanPoint d)) ⊆ Omega) :
    pointsIn X Omega = X := by
  classical
  apply Finset.filter_eq_self.mpr
  intro x hx
  exact hX hx

/-- Intersecting a region with a set which already contains all of `X` does
not discard any of the selected points. -/
theorem pointsIn_inter_eq_left_of_subset {d : ℕ}
    {X : Finset (EuclideanPoint d)} {Omega' Omega : Set (EuclideanPoint d)}
    (hX : (X : Set (EuclideanPoint d)) ⊆ Omega) :
    pointsIn X (Omega' ∩ Omega) = pointsIn X Omega' := by
  ext x
  simp only [mem_pointsIn, mem_inter_iff]
  constructor
  · rintro ⟨hx, hx', _⟩
    exact ⟨hx, hx'⟩
  · rintro ⟨hx, hx'⟩
    exact ⟨hx, hx', hX hx⟩

/-- Intersecting two convex regions preserves convexity. -/
theorem convex_inter {d : ℕ} {Omega' Omega : Set (EuclideanPoint d)}
    (hOmega' : Convex ℝ Omega') (hOmega : Convex ℝ Omega) :
    Convex ℝ (Omega' ∩ Omega) :=
  hOmega'.inter hOmega

/-- Intersecting back into the original region can only decrease volume. -/
theorem volume_inter_le_left {d : ℕ} (Omega' Omega : Set (EuclideanPoint d)) :
    (volume : Measure (EuclideanPoint d)) (Omega' ∩ Omega) ≤
      (volume : Measure (EuclideanPoint d)) Omega' :=
  measure_mono inter_subset_left

/-- Relative volume is monotone in its numerator. -/
theorem relativeVolume_mono_left {d : ℕ}
    {S T : Set (EuclideanPoint d)} (hST : S ⊆ T)
    (Omega : Set (EuclideanPoint d)) :
    relativeVolume S Omega ≤ relativeVolume T Omega := by
  exact ENNReal.div_le_div_right (measure_mono hST) _

/-- Intersecting back into a region can only decrease relative volume with
respect to any fixed reference region. -/
theorem relativeVolume_inter_le_left {d : ℕ}
    (Omega' Omega reference : Set (EuclideanPoint d)) :
    relativeVolume (Omega' ∩ Omega) reference ≤
      relativeVolume Omega' reference :=
  relativeVolume_mono_left inter_subset_left reference

/--
The elementary “intersect back with the original body” package.

This is used after running a geometric argument in a convenient ambient
covering body.  If all points already lie in `Omega`, replacing `Omega'` by
`Omega' ∩ Omega` preserves its selected points and convexity while decreasing
both its volume and its relative volume against every fixed reference body.
-/
theorem intersectBack {d : ℕ} {X : Finset (EuclideanPoint d)}
    {Omega' Omega reference : Set (EuclideanPoint d)}
    (hOmega' : Convex ℝ Omega') (hOmega : Convex ℝ Omega)
    (hX : (X : Set (EuclideanPoint d)) ⊆ Omega) :
    Convex ℝ (Omega' ∩ Omega) ∧
      Omega' ∩ Omega ⊆ Omega ∧
      pointsIn X (Omega' ∩ Omega) = pointsIn X Omega' ∧
      (volume : Measure (EuclideanPoint d)) (Omega' ∩ Omega) ≤
        (volume : Measure (EuclideanPoint d)) Omega' ∧
      relativeVolume (Omega' ∩ Omega) reference ≤ relativeVolume Omega' reference := by
  exact ⟨convex_inter hOmega' hOmega, inter_subset_right,
    pointsIn_inter_eq_left_of_subset hX, volume_inter_le_left Omega' Omega,
    relativeVolume_inter_le_left Omega' Omega reference⟩

/-- The exponent `(d - 1) / (d + 1) + epsilon` in PZ Lemma 1.

The subtraction is in `ℝ`, not truncated natural subtraction. -/
def densityExponent (d : ℕ) (epsilon : ℝ) : ℝ :=
  ((d : ℝ) - 1) / ((d : ℝ) + 1) + epsilon

/--
The exact output of PZ Lemma 1 for fixed parameters and input data.

The witness `Omega'` is only required to be a convex subset, exactly as in
the paper.  Convexity implies null-measurability for Euclidean volume, while
containment in the compact body `Omega` guarantees finite volume.
-/
def ConvexDensityOutput {d : ℕ} (epsilon tau delta : ℝ)
    (Omega : Set (EuclideanPoint d)) (X : Finset (EuclideanPoint d)) : Prop :=
  ∃ eta : ℝ, eta ∈ Set.Icc delta (delta ^ tau) ∧
    ∃ Omega' : Set (EuclideanPoint d),
      Convex ℝ Omega' ∧
      Omega' ⊆ Omega ∧
      relativeVolume Omega' Omega ≤ ENNReal.ofReal eta ∧
      eta ^ densityExponent d epsilon * (X.card : ℝ) ≤
        ((pointsIn X Omega').card : ℝ)

/--
The literal quantifier structure of Pham--Zakharov Lemma 1.

No inhabitant of this proposition is provided here.  The threshold
`largeEnough` is allowed to depend on `delta` (as well as on the already fixed
`d` and `epsilon`) but is uniform in `Omega` and `X`.
-/
def PZLemmaOneStatement : Prop :=
  ∀ d : ℕ, 1 ≤ d →
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ tau deltaZero : ℝ,
        0 < tau ∧ tau < 1 ∧ 0 < deltaZero ∧
        ∀ delta : ℝ, 0 < delta → delta < deltaZero →
          ∃ largeEnough : ℕ,
            ∀ (Omega : Set (EuclideanPoint d)) (X : Finset (EuclideanPoint d)),
              IsConvexBody Omega →
              (X : Set (EuclideanPoint d)) ⊆ Omega →
              largeEnough ≤ X.card →
              ConvexGeometry.IsDeltaConvexPosition delta X →
              ConvexDensityOutput epsilon tau delta Omega X

end

end Erdos186.PZ.ConvexDensity
