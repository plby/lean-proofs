/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.Definitions

/-!
# Clipping a retained finite set by its convex hull

The geometric regions produced in the proof of the Pham--Zakharov
convex-density lemma (for example, thin affine slabs) need not be contained in
the original convex body.  Intersecting with the original body fixes
containment, but it can make the bookkeeping around the retained finite set
unnecessarily indirect.  The source proof has a cleaner repair: replace the
region by the convex hull of the retained points.

This file records that repair.  If `T` is the retained part of `X`, all of
`T` lies in both the original convex body `Omega` and the auxiliary convex
region `S`.  Consequently `convexHull R T` lies in their intersection.  It is
compact, its volume is no larger than that of `S`, and it contains at least
`T.card` points of `X`.  The final theorem packages exactly the two numerical
estimates needed to construct `ConvexDensityOutput`.
-/

open Set MeasureTheory
open scoped ENNReal

namespace Erdos186.PZ.ConvexDensity

noncomputable section

/-- The convex region obtained by retaining exactly the finite set `T` and
taking its convex hull. -/
def retainedConvexHull {d : ℕ} (T : Finset (EuclideanPoint d)) :
    Set (EuclideanPoint d) :=
  convexHull ℝ (T : Set (EuclideanPoint d))

@[simp]
theorem mem_retainedConvexHull_of_mem {d : ℕ}
    {T : Finset (EuclideanPoint d)} {x : EuclideanPoint d} (hx : x ∈ T) :
    x ∈ retainedConvexHull T := by
  exact subset_convexHull ℝ (T : Set (EuclideanPoint d)) hx

/-- A retained convex hull is convex. -/
theorem convex_retainedConvexHull {d : ℕ}
    (T : Finset (EuclideanPoint d)) : Convex ℝ (retainedConvexHull T) := by
  exact convex_convexHull ℝ (T : Set (EuclideanPoint d))

/-- A retained convex hull is compact because the retained set is finite and
the ambient Euclidean space is finite-dimensional. -/
theorem isCompact_retainedConvexHull {d : ℕ}
    (T : Finset (EuclideanPoint d)) : IsCompact (retainedConvexHull T) := by
  exact T.finite_toSet.isCompact_convexHull ℝ

/-- The retained points are contained in their convex hull. -/
theorem coe_subset_retainedConvexHull {d : ℕ}
    (T : Finset (EuclideanPoint d)) :
    (T : Set (EuclideanPoint d)) ⊆ retainedConvexHull T := by
  exact subset_convexHull ℝ (T : Set (EuclideanPoint d))

/-- Minimality of the retained convex hull, specialized to the local
definition. -/
theorem retainedConvexHull_subset_of_convex {d : ℕ}
    {T : Finset (EuclideanPoint d)} {S : Set (EuclideanPoint d)}
    (hS : Convex ℝ S) (hTS : (T : Set (EuclideanPoint d)) ⊆ S) :
    retainedConvexHull T ⊆ S := by
  exact convexHull_min hTS hS

/-- If `T ⊆ X ⊆ Omega` and `Omega` is convex, the retained convex hull
is contained in `Omega`. -/
theorem retainedConvexHull_subset_body {d : ℕ}
    {T X : Finset (EuclideanPoint d)} {Omega : Set (EuclideanPoint d)}
    (hTX : T ⊆ X) (hXOmega : (X : Set (EuclideanPoint d)) ⊆ Omega)
    (hOmega : Convex ℝ Omega) : retainedConvexHull T ⊆ Omega := by
  apply retainedConvexHull_subset_of_convex hOmega
  intro x hx
  exact hXOmega (hTX hx)

/-- Every retained point is counted among the points of `X` in the retained
convex hull. -/
theorem subset_pointsIn_retainedConvexHull {d : ℕ}
    {T X : Finset (EuclideanPoint d)} (hTX : T ⊆ X) :
    T ⊆ pointsIn X (retainedConvexHull T) := by
  intro x hx
  rw [mem_pointsIn]
  exact ⟨hTX hx, mem_retainedConvexHull_of_mem hx⟩

/-- Hence passing to the convex hull loses none of the retained points. -/
theorem card_le_pointsIn_retainedConvexHull {d : ℕ}
    {T X : Finset (EuclideanPoint d)} (hTX : T ⊆ X) :
    T.card ≤ (pointsIn X (retainedConvexHull T)).card := by
  exact Finset.card_le_card (subset_pointsIn_retainedConvexHull hTX)

/-- Real-cast form of `card_le_pointsIn_retainedConvexHull`. -/
theorem card_cast_le_pointsIn_retainedConvexHull {d : ℕ}
    {T X : Finset (EuclideanPoint d)} (hTX : T ⊆ X) :
    (T.card : ℝ) ≤ ((pointsIn X (retainedConvexHull T)).card : ℝ) := by
  exact_mod_cast card_le_pointsIn_retainedConvexHull hTX

/-- If a convex auxiliary region contains `T`, the volume of the retained
convex hull is at most the volume of that region. -/
theorem volume_retainedConvexHull_le {d : ℕ}
    {T : Finset (EuclideanPoint d)} {S : Set (EuclideanPoint d)}
    (hS : Convex ℝ S) (hTS : (T : Set (EuclideanPoint d)) ⊆ S) :
    (volume : Measure (EuclideanPoint d)) (retainedConvexHull T) ≤
      (volume : Measure (EuclideanPoint d)) S := by
  exact measure_mono (retainedConvexHull_subset_of_convex hS hTS)

/--
The complete geometric convex-hull clipping package.

The hypotheses match the use in the source proof: `T` is a finite retained
subset of `X`, all of `X` lies in the original convex body `Omega`, and the
auxiliary convex region `S` contains `T`.  The witness is definitionally
`retainedConvexHull T`.
-/
theorem retainedConvexHull_properties {d : ℕ}
    {T X : Finset (EuclideanPoint d)}
    {Omega S : Set (EuclideanPoint d)}
    (hTX : T ⊆ X) (hXOmega : (X : Set (EuclideanPoint d)) ⊆ Omega)
    (hOmega : Convex ℝ Omega) (hS : Convex ℝ S)
    (hTS : (T : Set (EuclideanPoint d)) ⊆ S) :
    Convex ℝ (retainedConvexHull T) ∧
      IsCompact (retainedConvexHull T) ∧
      retainedConvexHull T ⊆ Omega ∧
      (T : Set (EuclideanPoint d)) ⊆ retainedConvexHull T ∧
      T.card ≤ (pointsIn X (retainedConvexHull T)).card ∧
      (volume : Measure (EuclideanPoint d)) (retainedConvexHull T) ≤
        (volume : Measure (EuclideanPoint d)) S := by
  exact ⟨convex_retainedConvexHull T, isCompact_retainedConvexHull T,
    retainedConvexHull_subset_body hTX hXOmega hOmega,
    coe_subset_retainedConvexHull T,
    card_le_pointsIn_retainedConvexHull hTX,
    volume_retainedConvexHull_le hS hTS⟩

/-- A relative-volume variant convenient when the auxiliary construction
already gives its estimate as a ratio. -/
theorem relativeVolume_retainedConvexHull_le {d : ℕ}
    {T : Finset (EuclideanPoint d)}
    {S Omega : Set (EuclideanPoint d)}
    (hS : Convex ℝ S) (hTS : (T : Set (EuclideanPoint d)) ⊆ S) :
    relativeVolume (retainedConvexHull T) Omega ≤ relativeVolume S Omega := by
  exact relativeVolume_mono_left
    (retainedConvexHull_subset_of_convex hS hTS) Omega

/--
Construct the output of the PZ convex-density lemma from the two estimates
actually delivered by an auxiliary slab argument.

The volume hypothesis is in multiplication form, avoiding division by the
volume of `Omega`.  The `IsConvexBody` hypothesis then converts it into the
required relative-volume estimate.  The cardinality hypothesis only needs to
count the retained set `T`; convex-hull clipping preserves all those points.
-/
theorem convexDensityOutput_of_retainedConvexHull {d : ℕ}
    {epsilon tau delta eta : ℝ}
    {Omega S : Set (EuclideanPoint d)}
    {X T : Finset (EuclideanPoint d)}
    (hEta : eta ∈ Set.Icc delta (delta ^ tau))
    (hOmega : IsConvexBody Omega)
    (hXOmega : (X : Set (EuclideanPoint d)) ⊆ Omega)
    (hTX : T ⊆ X)
    (hS : Convex ℝ S)
    (hTS : (T : Set (EuclideanPoint d)) ⊆ S)
    (hVolume : (volume : Measure (EuclideanPoint d)) S ≤
      ENNReal.ofReal eta * (volume : Measure (EuclideanPoint d)) Omega)
    (hCard : eta ^ densityExponent d epsilon * (X.card : ℝ) ≤
      (T.card : ℝ)) :
    ConvexDensityOutput epsilon tau delta Omega X := by
  refine ⟨eta, hEta, retainedConvexHull T,
    convex_retainedConvexHull T,
    retainedConvexHull_subset_body hTX hXOmega hOmega.convex, ?_, ?_⟩
  · rw [relativeVolume_le_iff hOmega eta]
    exact (volume_retainedConvexHull_le hS hTS).trans hVolume
  · exact hCard.trans (card_cast_le_pointsIn_retainedConvexHull hTX)

/-- Same constructor when the auxiliary region's estimate has already been
expressed in relative-volume form. -/
theorem convexDensityOutput_of_retainedConvexHull_relative {d : ℕ}
    {epsilon tau delta eta : ℝ}
    {Omega S : Set (EuclideanPoint d)}
    {X T : Finset (EuclideanPoint d)}
    (hEta : eta ∈ Set.Icc delta (delta ^ tau))
    (hOmega : IsConvexBody Omega)
    (hXOmega : (X : Set (EuclideanPoint d)) ⊆ Omega)
    (hTX : T ⊆ X)
    (hS : Convex ℝ S)
    (hTS : (T : Set (EuclideanPoint d)) ⊆ S)
    (hVolume : relativeVolume S Omega ≤ ENNReal.ofReal eta)
    (hCard : eta ^ densityExponent d epsilon * (X.card : ℝ) ≤
      (T.card : ℝ)) :
    ConvexDensityOutput epsilon tau delta Omega X := by
  refine ⟨eta, hEta, retainedConvexHull T,
    convex_retainedConvexHull T,
    retainedConvexHull_subset_body hTX hXOmega hOmega.convex, ?_, ?_⟩
  · exact (relativeVolume_retainedConvexHull_le hS hTS).trans hVolume
  · exact hCard.trans (card_cast_le_pointsIn_retainedConvexHull hTX)

end

end Erdos186.PZ.ConvexDensity
