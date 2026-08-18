/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.Definitions
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# General linear normalization for PZ Lemma 1

Unlike an isometry, the simplex normalization used in the geometric proof
changes Euclidean volume by a determinant.  It nevertheless preserves
*relative* volume, since the same nonzero finite determinant factor occurs in
the numerator and denominator.  This file records the exact transport facts
for an arbitrary linear equivalence of Euclidean `d`-space.
-/

open Set MeasureTheory
open scoped ENNReal

namespace Erdos186.PZ.ConvexDensity

noncomputable section

variable {d : ℕ}

/-- Image of a finite point set under a linear equivalence. -/
def linearEquivImageFinset (e : EuclideanPoint d ≃ₗ[ℝ] EuclideanPoint d)
    (X : Finset (EuclideanPoint d)) : Finset (EuclideanPoint d) :=
  X.map e.toEquiv.toEmbedding

@[simp]
theorem mem_linearEquivImageFinset (e : EuclideanPoint d ≃ₗ[ℝ] EuclideanPoint d)
    (X : Finset (EuclideanPoint d)) (x : EuclideanPoint d) :
    x ∈ linearEquivImageFinset e X ↔ e.symm x ∈ X := by
  exact Finset.mem_map_equiv

@[simp]
theorem card_linearEquivImageFinset (e : EuclideanPoint d ≃ₗ[ℝ] EuclideanPoint d)
    (X : Finset (EuclideanPoint d)) :
    (linearEquivImageFinset e X).card = X.card := by
  exact Finset.card_map _

@[simp]
theorem linearEquivImageFinset_symm
    (e : EuclideanPoint d ≃ₗ[ℝ] EuclideanPoint d)
    (X : Finset (EuclideanPoint d)) :
    linearEquivImageFinset e.symm (linearEquivImageFinset e X) = X := by
  ext x
  simp

/-- Pull a continuous functional back through an arbitrary finite-dimensional
linear equivalence. -/
def transportFunctionalLinearEquiv
    (e : EuclideanPoint d ≃ₗ[ℝ] EuclideanPoint d)
    (ℓ : EuclideanPoint d →L[ℝ] ℝ) : EuclideanPoint d →L[ℝ] ℝ :=
  ℓ.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap

@[simp]
theorem transportFunctionalLinearEquiv_apply
    (e : EuclideanPoint d ≃ₗ[ℝ] EuclideanPoint d)
    (ℓ : EuclideanPoint d →L[ℝ] ℝ) (x : EuclideanPoint d) :
    transportFunctionalLinearEquiv e ℓ (e x) = ℓ x := by
  simp [transportFunctionalLinearEquiv]

/-- Supporting half-space counts are invariant under a linear equivalence. -/
theorem halfspaceCount_linearEquivImage
    (e : EuclideanPoint d ≃ₗ[ℝ] EuclideanPoint d)
    (X : Finset (EuclideanPoint d)) (ℓ : EuclideanPoint d →L[ℝ] ℝ)
    (a : EuclideanPoint d) :
    ConvexGeometry.halfspaceCount (linearEquivImageFinset e X)
        (transportFunctionalLinearEquiv e ℓ)
        (transportFunctionalLinearEquiv e ℓ (e a)) =
      ConvexGeometry.halfspaceCount X ℓ (ℓ a) := by
  classical
  rw [ConvexGeometry.halfspaceCount_eq_card_filter,
    ConvexGeometry.halfspaceCount_eq_card_filter]
  have hfilter :
      (linearEquivImageFinset e X).filter
          (fun y ↦ transportFunctionalLinearEquiv e ℓ (e a) ≤
            transportFunctionalLinearEquiv e ℓ y) =
        linearEquivImageFinset e (X.filter fun x ↦ ℓ a ≤ ℓ x) := by
    ext y
    simp [transportFunctionalLinearEquiv]
  rw [hfilter, card_linearEquivImageFinset]

/-- `delta`-convex position is preserved by a linear equivalence. -/
theorem isDeltaConvexPosition_linearEquivImage_of
    (e : EuclideanPoint d ≃ₗ[ℝ] EuclideanPoint d)
    {X : Finset (EuclideanPoint d)} {delta : ℝ}
    (hX : ConvexGeometry.IsDeltaConvexPosition delta X) :
    ConvexGeometry.IsDeltaConvexPosition delta (linearEquivImageFinset e X) := by
  rw [ConvexGeometry.isDeltaConvexPosition_iff_supporting_through_point] at hX ⊢
  intro y hy
  let x := e.symm y
  have hx : x ∈ X := by simpa [x] using hy
  obtain ⟨ℓ, hℓ⟩ := hX x hx
  refine ⟨transportFunctionalLinearEquiv e ℓ, ?_⟩
  have hyx : y = e x := by simp [x]
  rw [hyx, halfspaceCount_linearEquivImage, card_linearEquivImageFinset]
  exact hℓ

/-- `delta`-convex position is invariant under a linear equivalence. -/
theorem isDeltaConvexPosition_linearEquivImage_iff
    (e : EuclideanPoint d ≃ₗ[ℝ] EuclideanPoint d)
    (X : Finset (EuclideanPoint d)) (delta : ℝ) :
    ConvexGeometry.IsDeltaConvexPosition delta (linearEquivImageFinset e X) ↔
      ConvexGeometry.IsDeltaConvexPosition delta X := by
  constructor
  · intro h
    have hs := isDeltaConvexPosition_linearEquivImage_of e.symm h
    simpa using hs
  · exact isDeltaConvexPosition_linearEquivImage_of e

/-- Euclidean volume scales by the absolute determinant under a linear
equivalence. -/
theorem volume_linearEquivImage
    (e : EuclideanPoint d ≃ₗ[ℝ] EuclideanPoint d)
    (S : Set (EuclideanPoint d)) :
    (volume : Measure (EuclideanPoint d)) (e '' S) =
      ENNReal.ofReal |LinearMap.det (e : EuclideanPoint d →ₗ[ℝ] EuclideanPoint d)| *
        volume S := by
  exact Measure.addHaar_image_linearMap volume e.toLinearMap S

/-- Relative volume is invariant under every invertible linear change of
coordinates. -/
theorem relativeVolume_linearEquivImage_general
    (e : EuclideanPoint d ≃ₗ[ℝ] EuclideanPoint d)
    (S Omega : Set (EuclideanPoint d)) :
    relativeVolume (e '' S) (e '' Omega) = relativeVolume S Omega := by
  let c : ℝ≥0∞ :=
    ENNReal.ofReal |LinearMap.det (e : EuclideanPoint d →ₗ[ℝ] EuclideanPoint d)|
  have hdet : LinearMap.det (e : EuclideanPoint d →ₗ[ℝ] EuclideanPoint d) ≠ 0 :=
    (LinearEquiv.isUnit_det' e).ne_zero
  have hc0 : c ≠ 0 := by
    exact (ENNReal.ofReal_pos.mpr (abs_pos.mpr hdet)).ne'
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [relativeVolume, volume_linearEquivImage, volume_linearEquivImage]
  exact ENNReal.mul_div_mul_left _ _ hc0 hctop

/-- Full-dimensional convex bodies are preserved by a linear equivalence. -/
theorem isConvexBody_linearEquivImage
    (e : EuclideanPoint d ≃ₗ[ℝ] EuclideanPoint d)
    {Omega : Set (EuclideanPoint d)} (hOmega : IsConvexBody Omega) :
    IsConvexBody (e '' Omega) := by
  refine ⟨hOmega.convex.linear_image e.toLinearMap,
    hOmega.isCompact.image e.toContinuousLinearEquiv.continuous, ?_⟩
  change (interior (e.toContinuousLinearEquiv.toHomeomorph '' Omega)).Nonempty
  rw [← e.toContinuousLinearEquiv.toHomeomorph.image_interior]
  exact hOmega.interior_nonempty.image e

/-- Convexity is preserved and reflected by a linear equivalence. -/
theorem convex_linearEquivImage_iff
    (e : EuclideanPoint d ≃ₗ[ℝ] EuclideanPoint d)
    (S : Set (EuclideanPoint d)) :
    Convex ℝ (e '' S) ↔ Convex ℝ S := by
  constructor
  · intro h
    have hs := h.linear_image e.symm.toLinearMap
    simpa [Set.image_image] using hs
  · intro h
    exact h.linear_image e.toLinearMap

/-- Selecting finite points commutes with a linear equivalence. -/
theorem pointsIn_linearEquivImage
    (e : EuclideanPoint d ≃ₗ[ℝ] EuclideanPoint d)
    (X : Finset (EuclideanPoint d)) (S : Set (EuclideanPoint d)) :
    pointsIn (linearEquivImageFinset e X) (e '' S) =
      linearEquivImageFinset e (pointsIn X S) := by
  ext y
  simp only [mem_pointsIn, mem_linearEquivImageFinset]
  constructor
  · rintro ⟨hyX, x, hxS, hxy⟩
    subst y
    have hxX : x ∈ X := by simpa using hyX
    simpa using ⟨hxX, hxS⟩
  · intro hy
    refine ⟨hy.1, e.symm y, hy.2, ?_⟩
    simp

@[simp]
theorem card_pointsIn_linearEquivImage
    (e : EuclideanPoint d ≃ₗ[ℝ] EuclideanPoint d)
    (X : Finset (EuclideanPoint d)) (S : Set (EuclideanPoint d)) :
    (pointsIn (linearEquivImageFinset e X) (e '' S)).card =
      (pointsIn X S).card := by
  rw [pointsIn_linearEquivImage, card_linearEquivImageFinset]

/-- The full convex-density output is invariant under an invertible linear
change of coordinates. -/
theorem convexDensityOutput_linearEquivImage_iff
    (e : EuclideanPoint d ≃ₗ[ℝ] EuclideanPoint d)
    (epsilon tau delta : ℝ) (Omega : Set (EuclideanPoint d))
    (X : Finset (EuclideanPoint d)) :
    ConvexDensityOutput epsilon tau delta (e '' Omega)
        (linearEquivImageFinset e X) ↔
      ConvexDensityOutput epsilon tau delta Omega X := by
  have forward :
      ∀ (f : EuclideanPoint d ≃ₗ[ℝ] EuclideanPoint d)
        (U : Set (EuclideanPoint d)) (Y : Finset (EuclideanPoint d)),
        ConvexDensityOutput epsilon tau delta U Y →
          ConvexDensityOutput epsilon tau delta (f '' U)
            (linearEquivImageFinset f Y) := by
    intro f U Y h
    obtain ⟨eta, heta, U', hconvex, hsubset, hvolume, hpoints⟩ := h
    refine ⟨eta, heta, f '' U', hconvex.linear_image f.toLinearMap,
      Set.image_mono hsubset, ?_, ?_⟩
    · rwa [relativeVolume_linearEquivImage_general]
    · simpa using hpoints
  constructor
  · intro h
    have hs := forward e.symm (e '' Omega) (linearEquivImageFinset e X) h
    simpa [Set.image_image] using hs
  · exact forward e Omega X

end

end Erdos186.PZ.ConvexDensity
