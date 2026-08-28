import Wikipedia.NoExoticSixSphere.SevenDimensionalSmoothOpenTube
import Wikipedia.HopfProblem.DegreeCollapseTimeCollarPositiveCore

/-!
# A positive smooth four-normal tube for an actual integral half-image class

The two-connected half supplies an embedded positive interior sphere with
the original integral homology marking. Its full original normal framing
constructs a smooth open four-normal tube staying entirely at positive
time, with the exact sphere as zero section.
-/

noncomputable section

open Function Set Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology
open Wikipedia.HopfProblem.SphereHomology

variable {M B : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [IsManifold (𝓡 7) ∞ M] [CompactSpace M] [T2Space M] [TopologicalSpace B]
  (e : EuclideanEmbedding 7 M) (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
  {t : M → ℝ} (C : TimeCollar t B)
  [SimplyConnectedSpace (TimeCollar.NonnegativeHalf t)]
  [Subsingleton (SingularHomology (TimeCollar.NonnegativeHalf t) 2)]

include e a in
theorem exists_positive_core_fourNormalTube
    (c : SingularHomology (TimeCollar.NonnegativeHalf t) 3) :
    ∃ g : C(Sphere 3, C.positiveInterior),
      ContMDiff (𝓡 3) (𝓡 7) ∞ ((subtypeInclusion (C.positiveInterior : Set M)).comp g) ∧
      IsClosedEmbedding ((subtypeInclusion (C.positiveInterior : Set M)).comp g) ∧
      (∀ s, Injective (mfderiv (𝓡 3) (𝓡 7)
        ((subtypeInclusion (C.positiveInterior : Set M)).comp g) s)) ∧
      singularHomologyMap (C.interiorToHalf.comp g) 3 (unitSphereTopClass 2) = c ∧
      ∃ Φ : PartialDiffeomorph ((𝓡 3).prod (𝓡 4)) (𝓡 7) (Sphere 3 × Vector 4) M ∞,
        Φ.source = univ ∧ Φ.target ⊆ C.positiveInterior ∧ ∀ s, Φ (s, 0) = (g s).val := by
  obtain ⟨g, hg, hi, hd, hclass⟩ := C.exists_interior_core_representative e a c
  obtain ⟨Φ, hΦ, hΦU, hΦcore⟩ := e.exists_fourNormalSmoothOpenTube a
    ((subtypeInclusion (C.positiveInterior : Set M)).comp g) hg hi.injective hd
    C.positiveInterior C.positiveInterior.isOpen (fun s ↦ (g s).property)
  exact ⟨g, hg, hi, hd, hclass, Φ, hΦ, hΦU, hΦcore⟩

end NoExoticSixSphere
