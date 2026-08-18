/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.EnclosingBox
import ErdosProblems.Erdos186.PZ.ConvexDensity.FullReduction
import ErdosProblems.Erdos186.PZ.ConvexDensity.Normalization

/-!
# Reduction to a uniformly normalized finite convex hull

The maximal-simplex normalization puts every full-dimensional finite point
set in a fixed outer cube and puts a fixed inner cube in its convex hull.
This file completes the exact transport of `ConvexDensityOutput` through the
arbitrary affine equivalence supplied by that normalization and packages the
result as a reduction of `PZFullSpanHullCore` to a uniformly normalized core.
-/

open Set MeasureTheory

namespace Erdos186.PZ.ConvexDensity

noncomputable section

variable {d : ℕ}

/-- The coercion of an affine image finset is the set-theoretic affine image. -/
theorem coe_affineEquivImageFinset
    (e : EuclideanPoint d ≃ᵃ[ℝ] EuclideanPoint d)
    (X : Finset (EuclideanPoint d)) :
    (affineEquivImageFinset e X : Set (EuclideanPoint d)) =
      e '' (X : Set (EuclideanPoint d)) := by
  ext y
  constructor
  · intro hy
    have hy' : e.symm y ∈ X :=
      (mem_affineEquivImageFinset e X y).mp hy
    exact ⟨e.symm y, hy', e.apply_symm_apply y⟩
  · rintro ⟨x, hx, rfl⟩
    exact (mem_affineEquivImageFinset e X (e x)).mpr (by simpa using hx)

/-- Convex hull commutes with the affine image finset. -/
theorem convexHull_affineEquivImageFinset
    (e : EuclideanPoint d ≃ᵃ[ℝ] EuclideanPoint d)
    (X : Finset (EuclideanPoint d)) :
    convexHull ℝ (affineEquivImageFinset e X : Set (EuclideanPoint d)) =
      e '' convexHull ℝ (X : Set (EuclideanPoint d)) := by
  rw [coe_affineEquivImageFinset]
  exact (e.toAffineMap.image_convexHull (X : Set (EuclideanPoint d))).symm

/-- The complete convex-density output is invariant under an arbitrary
invertible affine change of Euclidean coordinates. -/
theorem convexDensityOutput_affineEquivImage_iff
    (e : EuclideanPoint d ≃ᵃ[ℝ] EuclideanPoint d)
    (epsilon tau delta : ℝ) (Omega : Set (EuclideanPoint d))
    (X : Finset (EuclideanPoint d)) :
    ConvexDensityOutput epsilon tau delta (e '' Omega)
        (affineEquivImageFinset e X) ↔
      ConvexDensityOutput epsilon tau delta Omega X := by
  have forward :
      ∀ (f : EuclideanPoint d ≃ᵃ[ℝ] EuclideanPoint d)
        (U : Set (EuclideanPoint d)) (Y : Finset (EuclideanPoint d)),
        ConvexDensityOutput epsilon tau delta U Y →
          ConvexDensityOutput epsilon tau delta (f '' U)
            (affineEquivImageFinset f Y) := by
    intro f U Y h
    obtain ⟨eta, heta, U', hconvex, hsubset, hvolume, hpoints⟩ := h
    refine ⟨eta, heta, f '' U', hconvex.affine_image f.toAffineMap,
      Set.image_mono hsubset, ?_, ?_⟩
    · rwa [relativeVolume_affineEquivImage]
    · rw [card_affineEquivImageFinset,
        card_pointsIn_affineEquivImage]
      exact hpoints
  constructor
  · intro h
    have hs := forward e.symm (e '' Omega) (affineEquivImageFinset e X) h
    simpa [Set.image_image] using hs
  · exact forward e Omega X

/-- The finite-hull core after maximal-simplex normalization.  Both ambient
geometry hypotheses are uniform in the finite set: the convex hull contains
`normalizedInnerCube` and lies in `normalizedOuterCube`; the last inequality
records the uniform comparison of outer-cube and hull volume.

No affine-span hypothesis is needed here, since the inner-cube containment is
already the stronger quantitative full-dimensionality input. -/
def PZNormalizedFiniteHullCore : Prop :=
  ∀ d : ℕ, 2 ≤ d →
    ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 / ((d : ℝ) + 1) →
      ∃ deltaZero : ℝ, 0 < deltaZero ∧ deltaZero ≤ 1 ∧
        ∀ delta : ℝ, 0 < delta → delta < deltaZero →
          ∃ largeEnough : ℕ,
            ∀ Y : Finset (EuclideanPoint d),
              largeEnough ≤ Y.card →
              ConvexGeometry.IsDeltaConvexPosition delta Y →
              normalizedInnerCube d ⊆
                convexHull ℝ (Y : Set (EuclideanPoint d)) →
              convexHull ℝ (Y : Set (EuclideanPoint d)) ⊆
                normalizedOuterCube d →
              volume (normalizedOuterCube d) ≤ normalizedBoxConstant d *
                volume (convexHull ℝ (Y : Set (EuclideanPoint d))) →
              ConvexDensityOutput epsilon (tau epsilon) delta
                (convexHull ℝ (Y : Set (EuclideanPoint d))) Y

/-- The uniformly normalized finite-hull core implies the exact full-span
convex-hull core. -/
theorem pzFullSpanHullCore_of_normalizedFiniteHullCore
    (hcore : PZNormalizedFiniteHullCore) : PZFullSpanHullCore := by
  intro d hd epsilon hepsilon hepsilonLe
  obtain ⟨deltaZero, hdeltaZero, hdeltaZeroOne, hdelta⟩ :=
    hcore d hd epsilon hepsilon hepsilonLe
  refine ⟨deltaZero, hdeltaZero, hdeltaZeroOne, ?_⟩
  intro delta hdeltaPos hdeltaSmall
  obtain ⟨largeEnough, hlarge⟩ := hdelta delta hdeltaPos hdeltaSmall
  refine ⟨largeEnough, ?_⟩
  intro X hcard hspan hposition
  obtain ⟨p, hp, e, hpX, he, hinner, houter, hvolume⟩ :=
    exists_comparable_enclosing_box X hspan
  let Y : Finset (EuclideanPoint d) := affineEquivImageFinset e X
  have hcardY : largeEnough ≤ Y.card := by
    simpa [Y] using hcard
  have hpositionY : ConvexGeometry.IsDeltaConvexPosition delta Y := by
    exact (isDeltaConvexPosition_affineEquivImage_iff e X delta).2 hposition
  have hhull : convexHull ℝ (Y : Set (EuclideanPoint d)) =
      e '' convexHull ℝ (X : Set (EuclideanPoint d)) := by
    exact convexHull_affineEquivImageFinset e X
  have hnormalized : ConvexDensityOutput epsilon (tau epsilon) delta
      (convexHull ℝ (Y : Set (EuclideanPoint d))) Y := by
    apply hlarge Y hcardY hpositionY
    · simpa only [hhull] using hinner
    · simpa only [hhull] using houter
    · simpa only [hhull] using hvolume
  apply (convexDensityOutput_affineEquivImage_iff e epsilon (tau epsilon) delta
    (convexHull ℝ (X : Set (EuclideanPoint d))) X).1
  simpa only [hhull] using hnormalized

/-- End-to-end reduction from the uniformly normalized geometric core to the
literal all-dimensional statement of Pham--Zakharov Lemma 1. -/
theorem pzLemmaOneStatement_of_normalizedFiniteHullCore
    (hcore : PZNormalizedFiniteHullCore) : PZLemmaOneStatement :=
  pzLemmaOneStatement_of_smallEpsilon
    (pzLemmaOneSmallEpsilon_of_fullSpanHullCore
      (pzFullSpanHullCore_of_normalizedFiniteHullCore hcore))

end

end Erdos186.PZ.ConvexDensity
