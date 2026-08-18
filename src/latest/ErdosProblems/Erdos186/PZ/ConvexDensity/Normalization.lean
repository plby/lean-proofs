/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.Definitions

/-!
# Isometric normalization for the convex-density lemma

This file records the exact invariance facts used when the geometric argument
is moved to convenient Euclidean coordinates.  An affine isometry preserves
the finite point set (including all half-space counts), convexity, Euclidean
volume, and hence relative volume.  We also package the elementary operation
of intersecting a normalized convex witness with the convex hull of the
normalized point set.
-/

open Set MeasureTheory
open scoped ENNReal

namespace Erdos186.PZ.ConvexDensity

noncomputable section

variable {d : ℕ}

/-- The image of a finite point set under an affine isometry. -/
def affineImageFinset (e : EuclideanPoint d ≃ᵃⁱ[ℝ] EuclideanPoint d)
    (X : Finset (EuclideanPoint d)) : Finset (EuclideanPoint d) :=
  X.map e.toAffineEquiv.toEquiv.toEmbedding

@[simp]
theorem mem_affineImageFinset (e : EuclideanPoint d ≃ᵃⁱ[ℝ] EuclideanPoint d)
    (X : Finset (EuclideanPoint d)) (x : EuclideanPoint d) :
    x ∈ affineImageFinset e X ↔ e.symm x ∈ X := by
  exact Finset.mem_map_equiv

@[simp]
theorem card_affineImageFinset (e : EuclideanPoint d ≃ᵃⁱ[ℝ] EuclideanPoint d)
    (X : Finset (EuclideanPoint d)) :
    (affineImageFinset e X).card = X.card := by
  exact Finset.card_map _

@[simp]
theorem affineImageFinset_symm (e : EuclideanPoint d ≃ᵃⁱ[ℝ] EuclideanPoint d)
    (X : Finset (EuclideanPoint d)) :
    affineImageFinset e.symm (affineImageFinset e X) = X := by
  ext x
  simp

/-- A continuous linear functional transported through the linear part of an
affine isometry.  Its absolute values change by an additive constant, while
all comparisons between two points are unchanged. -/
def transportFunctional (e : EuclideanPoint d ≃ᵃⁱ[ℝ] EuclideanPoint d)
    (ℓ : EuclideanPoint d →L[ℝ] ℝ) : EuclideanPoint d →L[ℝ] ℝ :=
  ℓ.comp e.linearIsometryEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem transportFunctional_sub (e : EuclideanPoint d ≃ᵃⁱ[ℝ] EuclideanPoint d)
    (ℓ : EuclideanPoint d →L[ℝ] ℝ) (x y : EuclideanPoint d) :
    transportFunctional e ℓ (e x) - transportFunctional e ℓ (e y) = ℓ x - ℓ y := by
  change
    ℓ (e.linearIsometryEquiv.symm (e x)) -
        ℓ (e.linearIsometryEquiv.symm (e y)) = ℓ x - ℓ y
  rw [← ℓ.map_sub, ← ℓ.map_sub]
  rw [← e.linearIsometryEquiv.symm.map_sub]
  have hxy : e.linearIsometryEquiv.symm (e x - e y) = x - y := by
    apply e.linearIsometryEquiv.injective
    rw [e.linearIsometryEquiv.apply_symm_apply]
    exact (e.map_vsub x y).symm
  rw [hxy]

theorem transportFunctional_le_iff
    (e : EuclideanPoint d ≃ᵃⁱ[ℝ] EuclideanPoint d)
    (ℓ : EuclideanPoint d →L[ℝ] ℝ) (x y : EuclideanPoint d) :
    transportFunctional e ℓ (e x) ≤ transportFunctional e ℓ (e y) ↔
      ℓ x ≤ ℓ y := by
  have h := transportFunctional_sub e ℓ y x
  constructor <;> intro hle <;> linarith

/-- An affine Euclidean isometry is volume preserving. -/
theorem affineIsometryEquiv_measurePreserving
    (e : EuclideanPoint d ≃ᵃⁱ[ℝ] EuclideanPoint d) :
    MeasurePreserving e
      (volume : Measure (EuclideanPoint d))
      (volume : Measure (EuclideanPoint d)) := by
  have hlinear : MeasurePreserving e.linearIsometryEquiv
      (volume : Measure (EuclideanPoint d)) volume :=
    e.linearIsometryEquiv.measurePreserving
  have htranslate : MeasurePreserving (fun x : EuclideanPoint d ↦ x + e 0)
      (volume : Measure (EuclideanPoint d)) volume :=
    measurePreserving_add_right (volume : Measure (EuclideanPoint d)) (e 0)
  refine ⟨e.continuous.measurable, ?_⟩
  have he : (e : EuclideanPoint d → EuclideanPoint d) =
      (fun x ↦ e.linearIsometryEquiv x + e 0) := by
    funext x
    simpa using e.map_vadd (0 : EuclideanPoint d) x
  rw [he]
  change Measure.map
      ((fun z : EuclideanPoint d ↦ z + e 0) ∘ e.linearIsometryEquiv) volume = volume
  rw [← Measure.map_map htranslate.measurable hlinear.measurable,
    hlinear.map_eq, htranslate.map_eq]

/-- Every set, measurable or not, has the same outer Euclidean volume as its
image under an affine isometry. -/
theorem volume_affineImage
    (e : EuclideanPoint d ≃ᵃⁱ[ℝ] EuclideanPoint d)
    (S : Set (EuclideanPoint d)) :
    (volume : Measure (EuclideanPoint d)) (e '' S) = volume S := by
  have himage : e '' S = e.symm ⁻¹' S :=
    e.toAffineEquiv.toEquiv.image_eq_preimage_symm S
  rw [himage]
  exact (affineIsometryEquiv_measurePreserving e.symm).measure_preimage_emb
    e.symm.toHomeomorph.measurableEmbedding S

/-- Relative Euclidean volume is exactly invariant under simultaneous affine
isometric normalization of the numerator and denominator. -/
theorem relativeVolume_affineImage
    (e : EuclideanPoint d ≃ᵃⁱ[ℝ] EuclideanPoint d)
    (S Omega : Set (EuclideanPoint d)) :
    relativeVolume (e '' S) (e '' Omega) = relativeVolume S Omega := by
  simp only [relativeVolume, volume_affineImage]

@[simp]
theorem transportFunctional_le_apply_symm_iff
    (e : EuclideanPoint d ≃ᵃⁱ[ℝ] EuclideanPoint d)
    (ℓ : EuclideanPoint d →L[ℝ] ℝ) (x y : EuclideanPoint d) :
    transportFunctional e ℓ (e x) ≤ transportFunctional e ℓ y ↔
      ℓ x ≤ ℓ (e.symm y) := by
  simpa using transportFunctional_le_iff e ℓ x (e.symm y)

/-- Supporting-halfspace counts are unchanged by affine isometries. -/
theorem halfspaceCount_affineImage
    (e : EuclideanPoint d ≃ᵃⁱ[ℝ] EuclideanPoint d)
    (X : Finset (EuclideanPoint d)) (ℓ : EuclideanPoint d →L[ℝ] ℝ)
    (a : EuclideanPoint d) :
    ConvexGeometry.halfspaceCount (affineImageFinset e X)
        (transportFunctional e ℓ) (transportFunctional e ℓ (e a)) =
      ConvexGeometry.halfspaceCount X ℓ (ℓ a) := by
  classical
  rw [ConvexGeometry.halfspaceCount_eq_card_filter,
    ConvexGeometry.halfspaceCount_eq_card_filter]
  have hfilter :
      (affineImageFinset e X).filter
          (fun y ↦ transportFunctional e ℓ (e a) ≤ transportFunctional e ℓ y) =
        affineImageFinset e (X.filter fun x ↦ ℓ a ≤ ℓ x) := by
    ext y
    simp
  rw [hfilter, card_affineImageFinset]

/-- The forward transport of `δ`-convex position under an affine isometry. -/
theorem isDeltaConvexPosition_affineImage_of
    (e : EuclideanPoint d ≃ᵃⁱ[ℝ] EuclideanPoint d)
    {X : Finset (EuclideanPoint d)} {δ : ℝ}
    (hX : ConvexGeometry.IsDeltaConvexPosition δ X) :
    ConvexGeometry.IsDeltaConvexPosition δ (affineImageFinset e X) := by
  rw [ConvexGeometry.isDeltaConvexPosition_iff_supporting_through_point] at hX ⊢
  intro y hy
  let x := e.symm y
  have hx : x ∈ X := by
    simpa [x] using hy
  obtain ⟨ℓ, hℓ⟩ := hX x hx
  refine ⟨transportFunctional e ℓ, ?_⟩
  have hyx : y = e x := by simp [x]
  rw [hyx, halfspaceCount_affineImage, card_affineImageFinset]
  exact hℓ

/-- `δ`-convex position is invariant under affine Euclidean isometries. -/
theorem isDeltaConvexPosition_affineImage_iff
    (e : EuclideanPoint d ≃ᵃⁱ[ℝ] EuclideanPoint d)
    (X : Finset (EuclideanPoint d)) (δ : ℝ) :
    ConvexGeometry.IsDeltaConvexPosition δ (affineImageFinset e X) ↔
      ConvexGeometry.IsDeltaConvexPosition δ X := by
  constructor
  · intro h
    have hs := isDeltaConvexPosition_affineImage_of e.symm h
    simpa using hs
  · exact isDeltaConvexPosition_affineImage_of e

/-- Convexity is invariant under affine isometric normalization. -/
theorem convex_affineImage_iff
    (e : EuclideanPoint d ≃ᵃⁱ[ℝ] EuclideanPoint d)
    (S : Set (EuclideanPoint d)) :
    Convex ℝ (e '' S) ↔ Convex ℝ S := by
  constructor
  · intro h
    have hs := h.affine_image e.symm.toAffineIsometry.toAffineMap
    simpa [Set.image_image] using hs
  · exact fun h ↦ h.affine_image e.toAffineIsometry.toAffineMap

/-- Selecting points commutes exactly with affine isometric normalization. -/
theorem pointsIn_affineImage
    (e : EuclideanPoint d ≃ᵃⁱ[ℝ] EuclideanPoint d)
    (X : Finset (EuclideanPoint d)) (S : Set (EuclideanPoint d)) :
    pointsIn (affineImageFinset e X) (e '' S) =
      affineImageFinset e (pointsIn X S) := by
  ext y
  simp only [mem_pointsIn, mem_affineImageFinset]
  constructor
  · rintro ⟨hyX, x, hxS, hxy⟩
    subst y
    have hxX : x ∈ X := by simpa using hyX
    simpa using ⟨hxX, hxS⟩
  · intro hy
    refine ⟨hy.1, e.symm y, hy.2, ?_⟩
    simp

/-- In particular, the number of selected points is unchanged. -/
theorem card_pointsIn_affineImage
    (e : EuclideanPoint d ≃ᵃⁱ[ℝ] EuclideanPoint d)
    (X : Finset (EuclideanPoint d)) (S : Set (EuclideanPoint d)) :
    (pointsIn (affineImageFinset e X) (e '' S)).card =
      (pointsIn X S).card := by
  rw [pointsIn_affineImage, card_affineImageFinset]

/-- Set containment is preserved and reflected by an affine equivalence. -/
theorem affineImage_subset_affineImage_iff
    (e : EuclideanPoint d ≃ᵃⁱ[ℝ] EuclideanPoint d)
    (S T : Set (EuclideanPoint d)) :
    e '' S ⊆ e '' T ↔ S ⊆ T := by
  constructor
  · intro h x hx
    obtain ⟨y, hy, hey⟩ := h ⟨x, hx, rfl⟩
    have hyx : y = x := e.injective hey
    simpa [hyx] using hy
  · exact Set.image_mono

/-- Intersecting a region with the convex hull of the finite point set does
not discard any of the points selected from that region. -/
theorem pointsIn_inter_convexHull
    (X : Finset (EuclideanPoint d)) (S : Set (EuclideanPoint d)) :
    pointsIn X (S ∩ convexHull ℝ (X : Set (EuclideanPoint d))) = pointsIn X S := by
  ext x
  simp only [mem_pointsIn, mem_inter_iff]
  constructor
  · rintro ⟨hxX, hxS, _⟩
    exact ⟨hxX, hxS⟩
  · rintro ⟨hxX, hxS⟩
    exact ⟨hxX, hxS, subset_convexHull ℝ _ hxX⟩

/-- The complete convex-hull intersection package used after normalization:
convexity and all selected points are preserved, the new region lies in the
point hull, and both absolute and relative volume can only decrease. -/
theorem intersectConvexHull
    (X : Finset (EuclideanPoint d))
    {S reference : Set (EuclideanPoint d)} (hS : Convex ℝ S) :
    Convex ℝ (S ∩ convexHull ℝ (X : Set (EuclideanPoint d))) ∧
      S ∩ convexHull ℝ (X : Set (EuclideanPoint d)) ⊆
        convexHull ℝ (X : Set (EuclideanPoint d)) ∧
      pointsIn X (S ∩ convexHull ℝ (X : Set (EuclideanPoint d))) = pointsIn X S ∧
      (volume : Measure (EuclideanPoint d))
          (S ∩ convexHull ℝ (X : Set (EuclideanPoint d))) ≤ volume S ∧
      relativeVolume (S ∩ convexHull ℝ (X : Set (EuclideanPoint d))) reference ≤
        relativeVolume S reference := by
  refine ⟨hS.inter (convex_convexHull ℝ _), inter_subset_right,
    pointsIn_inter_convexHull X S, measure_mono inter_subset_left, ?_⟩
  exact relativeVolume_mono_left inter_subset_left reference

/-! ## Linear-isometry specializations -/

/-- The image of a finite point set under a linear isometry equivalence. -/
def linearImageFinset (e : EuclideanPoint d ≃ₗᵢ[ℝ] EuclideanPoint d)
    (X : Finset (EuclideanPoint d)) : Finset (EuclideanPoint d) :=
  X.map e.toLinearEquiv.toEquiv.toEmbedding

@[simp]
theorem mem_linearImageFinset
    (e : EuclideanPoint d ≃ₗᵢ[ℝ] EuclideanPoint d)
    (X : Finset (EuclideanPoint d)) (x : EuclideanPoint d) :
    x ∈ linearImageFinset e X ↔ e.symm x ∈ X := by
  exact Finset.mem_map_equiv

@[simp]
theorem card_linearImageFinset
    (e : EuclideanPoint d ≃ₗᵢ[ℝ] EuclideanPoint d)
    (X : Finset (EuclideanPoint d)) :
    (linearImageFinset e X).card = X.card := by
  exact Finset.card_map _

theorem linearImageFinset_eq_affineImageFinset
    (e : EuclideanPoint d ≃ₗᵢ[ℝ] EuclideanPoint d)
    (X : Finset (EuclideanPoint d)) :
    linearImageFinset e X = affineImageFinset e.toAffineIsometryEquiv X := by
  ext x
  rw [mem_linearImageFinset, mem_affineImageFinset]
  rfl

theorem isDeltaConvexPosition_linearImage_iff
    (e : EuclideanPoint d ≃ₗᵢ[ℝ] EuclideanPoint d)
    (X : Finset (EuclideanPoint d)) (δ : ℝ) :
    ConvexGeometry.IsDeltaConvexPosition δ (linearImageFinset e X) ↔
      ConvexGeometry.IsDeltaConvexPosition δ X := by
  rw [linearImageFinset_eq_affineImageFinset]
  exact isDeltaConvexPosition_affineImage_iff e.toAffineIsometryEquiv X δ

theorem convex_linearImage_iff
    (e : EuclideanPoint d ≃ₗᵢ[ℝ] EuclideanPoint d)
    (S : Set (EuclideanPoint d)) :
    Convex ℝ (e '' S) ↔ Convex ℝ S := by
  simpa using convex_affineImage_iff e.toAffineIsometryEquiv S

theorem volume_linearImage
    (e : EuclideanPoint d ≃ₗᵢ[ℝ] EuclideanPoint d)
    (S : Set (EuclideanPoint d)) :
    (volume : Measure (EuclideanPoint d)) (e '' S) = volume S := by
  simpa using volume_affineImage e.toAffineIsometryEquiv S

theorem relativeVolume_linearImage
    (e : EuclideanPoint d ≃ₗᵢ[ℝ] EuclideanPoint d)
    (S Omega : Set (EuclideanPoint d)) :
    relativeVolume (e '' S) (e '' Omega) = relativeVolume S Omega := by
  simpa using relativeVolume_affineImage e.toAffineIsometryEquiv S Omega

theorem pointsIn_linearImage
    (e : EuclideanPoint d ≃ₗᵢ[ℝ] EuclideanPoint d)
    (X : Finset (EuclideanPoint d)) (S : Set (EuclideanPoint d)) :
    pointsIn (linearImageFinset e X) (e '' S) =
      linearImageFinset e (pointsIn X S) := by
  rw [linearImageFinset_eq_affineImageFinset,
    linearImageFinset_eq_affineImageFinset]
  simpa using pointsIn_affineImage e.toAffineIsometryEquiv X S

theorem card_pointsIn_linearImage
    (e : EuclideanPoint d ≃ₗᵢ[ℝ] EuclideanPoint d)
    (X : Finset (EuclideanPoint d)) (S : Set (EuclideanPoint d)) :
    (pointsIn (linearImageFinset e X) (e '' S)).card =
      (pointsIn X S).card := by
  rw [pointsIn_linearImage, card_linearImageFinset]

/-! ## Arbitrary affine equivalences -/

/-- The image of a finite point set under an arbitrary affine equivalence. -/
def affineEquivImageFinset (e : EuclideanPoint d ≃ᵃ[ℝ] EuclideanPoint d)
    (X : Finset (EuclideanPoint d)) : Finset (EuclideanPoint d) :=
  X.map e.toEquiv.toEmbedding

@[simp]
theorem mem_affineEquivImageFinset
    (e : EuclideanPoint d ≃ᵃ[ℝ] EuclideanPoint d)
    (X : Finset (EuclideanPoint d)) (x : EuclideanPoint d) :
    x ∈ affineEquivImageFinset e X ↔ e.symm x ∈ X := by
  exact Finset.mem_map_equiv

@[simp]
theorem card_affineEquivImageFinset
    (e : EuclideanPoint d ≃ᵃ[ℝ] EuclideanPoint d)
    (X : Finset (EuclideanPoint d)) :
    (affineEquivImageFinset e X).card = X.card := by
  exact Finset.card_map _

@[simp]
theorem affineEquivImageFinset_symm
    (e : EuclideanPoint d ≃ᵃ[ℝ] EuclideanPoint d)
    (X : Finset (EuclideanPoint d)) :
    affineEquivImageFinset e.symm (affineEquivImageFinset e X) = X := by
  ext x
  simp

/-- Transport a continuous functional through the inverse linear part of an
arbitrary finite-dimensional affine equivalence. -/
def affineEquivTransportFunctional
    (e : EuclideanPoint d ≃ᵃ[ℝ] EuclideanPoint d)
    (ℓ : EuclideanPoint d →L[ℝ] ℝ) : EuclideanPoint d →L[ℝ] ℝ :=
  ℓ.comp e.linear.symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem affineEquivTransportFunctional_sub
    (e : EuclideanPoint d ≃ᵃ[ℝ] EuclideanPoint d)
    (ℓ : EuclideanPoint d →L[ℝ] ℝ) (x y : EuclideanPoint d) :
    affineEquivTransportFunctional e ℓ (e x) -
        affineEquivTransportFunctional e ℓ (e y) = ℓ x - ℓ y := by
  change ℓ (e.linear.symm (e x)) - ℓ (e.linear.symm (e y)) = ℓ x - ℓ y
  rw [← ℓ.map_sub, ← ℓ.map_sub]
  congr 1
  apply e.linear.injective
  calc
    e.linear (e.linear.symm (e x) - e.linear.symm (e y)) =
        e.linear (e.linear.symm (e x)) - e.linear (e.linear.symm (e y)) :=
      e.linear.map_sub _ _
    _ = e x - e y := by rw [e.linear.apply_symm_apply, e.linear.apply_symm_apply]
    _ = e.linear (x - y) := (AffineMap.linearMap_vsub e.toAffineMap x y).symm

theorem affineEquivTransportFunctional_le_iff
    (e : EuclideanPoint d ≃ᵃ[ℝ] EuclideanPoint d)
    (ℓ : EuclideanPoint d →L[ℝ] ℝ) (x y : EuclideanPoint d) :
    affineEquivTransportFunctional e ℓ (e x) ≤
        affineEquivTransportFunctional e ℓ (e y) ↔ ℓ x ≤ ℓ y := by
  have h := affineEquivTransportFunctional_sub e ℓ y x
  constructor <;> intro hle <;> linarith

@[simp]
theorem affineEquivTransportFunctional_le_apply_symm_iff
    (e : EuclideanPoint d ≃ᵃ[ℝ] EuclideanPoint d)
    (ℓ : EuclideanPoint d →L[ℝ] ℝ) (x y : EuclideanPoint d) :
    affineEquivTransportFunctional e ℓ (e x) ≤
        affineEquivTransportFunctional e ℓ y ↔ ℓ x ≤ ℓ (e.symm y) := by
  simpa using affineEquivTransportFunctional_le_iff e ℓ x (e.symm y)

/-- Supporting-halfspace counts are invariant under arbitrary affine
equivalences. -/
theorem halfspaceCount_affineEquivImage
    (e : EuclideanPoint d ≃ᵃ[ℝ] EuclideanPoint d)
    (X : Finset (EuclideanPoint d)) (ℓ : EuclideanPoint d →L[ℝ] ℝ)
    (a : EuclideanPoint d) :
    ConvexGeometry.halfspaceCount (affineEquivImageFinset e X)
        (affineEquivTransportFunctional e ℓ)
        (affineEquivTransportFunctional e ℓ (e a)) =
      ConvexGeometry.halfspaceCount X ℓ (ℓ a) := by
  classical
  rw [ConvexGeometry.halfspaceCount_eq_card_filter,
    ConvexGeometry.halfspaceCount_eq_card_filter]
  have hfilter :
      (affineEquivImageFinset e X).filter (fun y ↦
          affineEquivTransportFunctional e ℓ (e a) ≤
            affineEquivTransportFunctional e ℓ y) =
        affineEquivImageFinset e (X.filter fun x ↦ ℓ a ≤ ℓ x) := by
    ext y
    simp
  rw [hfilter, card_affineEquivImageFinset]

theorem isDeltaConvexPosition_affineEquivImage_of
    (e : EuclideanPoint d ≃ᵃ[ℝ] EuclideanPoint d)
    {X : Finset (EuclideanPoint d)} {δ : ℝ}
    (hX : ConvexGeometry.IsDeltaConvexPosition δ X) :
    ConvexGeometry.IsDeltaConvexPosition δ (affineEquivImageFinset e X) := by
  rw [ConvexGeometry.isDeltaConvexPosition_iff_supporting_through_point] at hX ⊢
  intro y hy
  let x := e.symm y
  have hx : x ∈ X := by simpa [x] using hy
  obtain ⟨ℓ, hℓ⟩ := hX x hx
  refine ⟨affineEquivTransportFunctional e ℓ, ?_⟩
  have hyx : y = e x := by simp [x]
  rw [hyx, halfspaceCount_affineEquivImage, card_affineEquivImageFinset]
  exact hℓ

/-- `δ`-convex position is invariant under every invertible affine change
of Euclidean coordinates. -/
theorem isDeltaConvexPosition_affineEquivImage_iff
    (e : EuclideanPoint d ≃ᵃ[ℝ] EuclideanPoint d)
    (X : Finset (EuclideanPoint d)) (δ : ℝ) :
    ConvexGeometry.IsDeltaConvexPosition δ (affineEquivImageFinset e X) ↔
      ConvexGeometry.IsDeltaConvexPosition δ X := by
  constructor
  · intro h
    have hs := isDeltaConvexPosition_affineEquivImage_of e.symm h
    simpa using hs
  · exact isDeltaConvexPosition_affineEquivImage_of e

/-- Convexity is invariant under arbitrary affine equivalences. -/
theorem convex_affineEquivImage_iff
    (e : EuclideanPoint d ≃ᵃ[ℝ] EuclideanPoint d)
    (S : Set (EuclideanPoint d)) :
    Convex ℝ (e '' S) ↔ Convex ℝ S := by
  constructor
  · intro h
    have hs := h.affine_image e.symm.toAffineMap
    simpa [Set.image_image] using hs
  · exact fun h ↦ h.affine_image e.toAffineMap

/-- Selecting points commutes with every invertible affine change of
coordinates. -/
theorem pointsIn_affineEquivImage
    (e : EuclideanPoint d ≃ᵃ[ℝ] EuclideanPoint d)
    (X : Finset (EuclideanPoint d)) (S : Set (EuclideanPoint d)) :
    pointsIn (affineEquivImageFinset e X) (e '' S) =
      affineEquivImageFinset e (pointsIn X S) := by
  ext y
  simp only [mem_pointsIn, mem_affineEquivImageFinset]
  constructor
  · rintro ⟨hyX, x, hxS, hxy⟩
    subst y
    have hxX : x ∈ X := by simpa using hyX
    simpa using ⟨hxX, hxS⟩
  · intro hy
    refine ⟨hy.1, e.symm y, hy.2, ?_⟩
    simp

theorem card_pointsIn_affineEquivImage
    (e : EuclideanPoint d ≃ᵃ[ℝ] EuclideanPoint d)
    (X : Finset (EuclideanPoint d)) (S : Set (EuclideanPoint d)) :
    (pointsIn (affineEquivImageFinset e X) (e '' S)).card =
      (pointsIn X S).card := by
  rw [pointsIn_affineEquivImage, card_affineEquivImageFinset]

/-- The positive finite Jacobian factor of an invertible affine change of
Euclidean coordinates. -/
def affineEquivVolumeFactor
    (e : EuclideanPoint d ≃ᵃ[ℝ] EuclideanPoint d) : ℝ≥0∞ :=
  ENNReal.ofReal |LinearMap.det (e.linear : EuclideanPoint d →ₗ[ℝ] EuclideanPoint d)|

theorem affineEquivVolumeFactor_ne_zero
    (e : EuclideanPoint d ≃ᵃ[ℝ] EuclideanPoint d) :
    affineEquivVolumeFactor e ≠ 0 := by
  have hdet :
      LinearMap.det (e.linear : EuclideanPoint d →ₗ[ℝ] EuclideanPoint d) ≠ 0 :=
    (LinearEquiv.isUnit_det' e.linear).ne_zero
  simp [affineEquivVolumeFactor, hdet]

theorem affineEquivVolumeFactor_ne_top
    (e : EuclideanPoint d ≃ᵃ[ℝ] EuclideanPoint d) :
    affineEquivVolumeFactor e ≠ ⊤ := by
  simp [affineEquivVolumeFactor]

/-- An arbitrary affine equivalence rescales every set by the absolute
determinant of its linear part. -/
theorem volume_affineEquivImage
    (e : EuclideanPoint d ≃ᵃ[ℝ] EuclideanPoint d)
    (S : Set (EuclideanPoint d)) :
    (volume : Measure (EuclideanPoint d)) (e '' S) =
      affineEquivVolumeFactor e * volume S := by
  let t : EuclideanPoint d ≃ᵃⁱ[ℝ] EuclideanPoint d :=
    AffineIsometryEquiv.vaddConst ℝ (e 0)
  have hefun : (e : EuclideanPoint d → EuclideanPoint d) =
      (t : EuclideanPoint d → EuclideanPoint d) ∘ e.linear := by
    funext x
    simpa [t] using e.toAffineMap.map_vadd 0 x
  have himage : e '' S = t '' (e.linear '' S) := by
    calc
      e '' S = ((t : EuclideanPoint d → EuclideanPoint d) ∘ e.linear) '' S :=
        congrArg (fun f : EuclideanPoint d → EuclideanPoint d ↦ f '' S) hefun
      _ = t '' (e.linear '' S) := by
        rw [Set.image_image]
        rfl
  rw [himage, volume_affineImage]
  exact Measure.addHaar_image_linearMap volume
    (e.linear : EuclideanPoint d →ₗ[ℝ] EuclideanPoint d) S

/-- Relative Euclidean volume is invariant under every invertible affine
change of coordinates: the same positive finite determinant factor occurs
in the numerator and denominator and therefore cancels. -/
theorem relativeVolume_affineEquivImage
    (e : EuclideanPoint d ≃ᵃ[ℝ] EuclideanPoint d)
    (S Omega : Set (EuclideanPoint d)) :
    relativeVolume (e '' S) (e '' Omega) = relativeVolume S Omega := by
  rw [relativeVolume, volume_affineEquivImage, volume_affineEquivImage]
  exact ENNReal.mul_div_mul_left _ _
    (affineEquivVolumeFactor_ne_zero e) (affineEquivVolumeFactor_ne_top e)

end

end Erdos186.PZ.ConvexDensity
