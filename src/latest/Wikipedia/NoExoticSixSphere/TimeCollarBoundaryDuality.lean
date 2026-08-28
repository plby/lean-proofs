import Wikipedia.NoExoticSixSphere.TimeCollarCoreNaturality
import Wikipedia.NoExoticSixSphere.CompactSupportCofinalComponent
import Wikipedia.NoExoticSixSphere.TimeCollarInteriorCapDuality

/-!
# Actual boundary-relative cap duality for a collared seven-dimensional half

The cofinal compact cores and their original support transitions identify
boundary-relative cohomology with the genuine interior compact-support
direct limit. The comparison is independent of cutoff. Composing with
the actual interior cap map gives a bijection to homology of the half.
Compatibility with the boundary connecting class is still separate.
-/

noncomputable section

open Set Function TopologicalSpace ContinuousMap
open scoped Manifold ContDiff

namespace NoExoticSixSphere.TimeCollarDuality

open GLOrthonormalization RelativeModTwoCochains
open Wikipedia.HopfProblem.DegreeCollapse Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
open Wikipedia.HopfProblem.SphereHomologyCoefficients

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B] [CompactSpace M]
  {t : M → ℝ} (C : TimeCollar t B) (δ : ℝ) (hδ : 0 < δ) (hδw : δ ≤ C.width)

include hδw in
theorem compactCore_of_bijective (p : ℕ) :
    Bijective (CompactSupportCohomology.of C.positiveInterior p (compactCore C δ hδ)) := by
  apply CompactSupportCohomology.of_bijective_of_cofinal
  intro K
  obtain ⟨ε, hε, _, hK⟩ := compactCore_cofinal C K
  let η := min δ ε
  have hη : 0 < η := lt_min hδ hε
  have hηw : η ≤ C.width := (min_le_left _ _).trans hδw
  refine ⟨compactCore C η hη, compactCore_mono C δ η hδ hη (min_le_left _ _),
    hK.trans (compactCore_mono C ε η hε hη (min_le_right _ _)), ?_⟩
  exact compactCore_extend_bijective C δ hδ hδw η hη hηw (min_le_left _ _) p

def boundaryCompactSupportMap (p : ℕ) :
    Cohomology (boundary t) p →ₗ[ℤ] CompactSupportCohomology.Cohomology C.positiveInterior p :=
  (CompactSupportCohomology.of C.positiveInterior p (compactCore C δ hδ)).comp
    (boundaryCoreEquiv C δ hδ hδw p).toLinearMap

theorem boundaryCompactSupportMap_bijective (p : ℕ) :
    Bijective (boundaryCompactSupportMap C δ hδ hδw p) :=
  (compactCore_of_bijective C δ hδ hδw p).comp (boundaryCoreEquiv C δ hδ hδw p).bijective

def boundaryCompactSupportEquiv (p : ℕ) :
    Cohomology (boundary t) p ≃ₗ[ℤ] CompactSupportCohomology.Cohomology C.positiveInterior p :=
  LinearEquiv.ofBijective (boundaryCompactSupportMap C δ hδ hδw p)
    (boundaryCompactSupportMap_bijective C δ hδ hδw p)

theorem boundaryCompactSupportEquiv_toLinearMap (p : ℕ) :
    (boundaryCompactSupportEquiv C δ hδ hδw p).toLinearMap =
      boundaryCompactSupportMap C δ hδ hδw p := rfl

variable (ε : ℝ) (hε : 0 < ε) (hεw : ε ≤ C.width)

theorem boundaryCompactSupportMap_mono (hεδ : ε ≤ δ) (p : ℕ) :
    boundaryCompactSupportMap C ε hε hεw p = boundaryCompactSupportMap C δ hδ hδw p := by
  apply LinearMap.ext
  intro c
  change CompactSupportCohomology.of C.positiveInterior p (compactCore C ε hε)
    (boundaryCoreEquiv C ε hε hεw p c) = _
  rw [boundaryCoreEquiv_natural C δ hδ hδw ε hε hεw hεδ p c]
  exact CompactSupportCohomology.of_transition C.positiveInterior p
    (compactCore_mono C δ ε hδ hε hεδ) _

theorem boundaryCompactSupportMap_independent (p : ℕ) :
    boundaryCompactSupportMap C δ hδ hδw p = boundaryCompactSupportMap C ε hε hεw p := by
  let η := min δ ε
  have hη : 0 < η := lt_min hδ hε
  have hηw : η ≤ C.width := (min_le_left _ _).trans hδw
  exact (boundaryCompactSupportMap_mono C δ hδ hδw η hη hηw (min_le_left _ _) p).symm.trans
    (boundaryCompactSupportMap_mono C ε hε hεw η hη hηw (min_le_right _ _) p)

def boundaryCompactSupportCanonical (p : ℕ) :
    Cohomology (boundary t) p ≃ₗ[ℤ] CompactSupportCohomology.Cohomology C.positiveInterior p :=
  boundaryCompactSupportEquiv C (C.width / 2) (half_pos C.width_pos)
    (half_lt_self C.width_pos).le p

variable [ChartedSpace (Vector 7) M] [IsManifold (𝓡 7) ∞ M] [T2Space M]

def boundaryDualityMap (p q : ℕ) (h : p + q = 7) :
    Cohomology (boundary t) p →ₗ[ℤ] ModHomology 2 (NonnegativeHalf t) q :=
  (interiorCapMap C p q h).comp (boundaryCompactSupportCanonical C p).toLinearMap

theorem boundaryDualityMap_bijective (p q : ℕ) (h : p + q = 7) :
    Bijective (boundaryDualityMap C p q h) :=
  (interiorCapMap_bijective C p q h).comp (boundaryCompactSupportCanonical C p).bijective

def boundaryDualityEquiv (p q : ℕ) (h : p + q = 7) :
    Cohomology (boundary t) p ≃ₗ[ℤ] ModHomology 2 (NonnegativeHalf t) q :=
  LinearEquiv.ofBijective (boundaryDualityMap C p q h) (boundaryDualityMap_bijective C p q h)

theorem boundaryDualityEquiv_toLinearMap (p q : ℕ) (h : p + q = 7) :
    (boundaryDualityEquiv C p q h).toLinearMap = boundaryDualityMap C p q h := rfl

end NoExoticSixSphere.TimeCollarDuality
