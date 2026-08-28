import Wikipedia.HopfProblem.DegreeCollapseTimeCollarInterior
import Wikipedia.HopfProblem.DegreeCollapseLowSphereOpenRepresentative
import Wikipedia.HopfProblem.DegreeCollapseIntegralTwoSphereRepresentatives

/-!

# Positive embedded two-spheres with the original integral half-H2 marking

The actual interior inclusion is a homotopy equivalence. Transfer simple
connectivity and the chosen homology class through it, use the integral
second Hurewicz theorem, and perturb inside the same original open subset.
The resulting core represents exactly the original class in the half.
No vanishing of H2 or supplied embedded representative is assumed.
-/

noncomputable section

open Function Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.TimeCollar

open NoExoticSixSphere GLOrthonormalization SingularMayerVietoris
open PeriodTorusHigherHomology SphereHomology

variable {M B : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [IsManifold (𝓡 7) ∞ M] [CompactSpace M] [T2Space M] [TopologicalSpace B]
  (e : EuclideanEmbedding 7 M) (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
  {t : M → ℝ} (C : TimeCollar t B) [SimplyConnectedSpace (NonnegativeHalf t)]

include e a in
theorem exists_interior_twoSphere_representative (c : SingularHomology (NonnegativeHalf t) 2) :
    ∃ g : C(Sphere 2, C.positiveInterior),
      ContMDiff (𝓡 2) (𝓡 7) ∞ ((subtypeInclusion (C.positiveInterior : Set M)).comp g) ∧
      IsClosedEmbedding ((subtypeInclusion (C.positiveInterior : Set M)).comp g) ∧
      (∀ s, Injective (mfderiv (𝓡 2) (𝓡 7)
        ((subtypeInclusion (C.positiveInterior : Set M)).comp g) s)) ∧
      singularHomologyMap (C.interiorToHalf.comp g) 2 (unitSphereTopClass 1) = c := by
  let : SimplyConnectedSpace C.positiveInterior := C.interiorHalfHomotopyEquiv.simplyConnectedSpace
  obtain ⟨u, hu⟩ := (C.interiorToHalf_homology_bijective 2).2 c
  obtain ⟨f, hf⟩ := IntegralTwoSphereRepresentatives.exists_sphereMap
    (Classical.arbitrary C.positiveInterior) u
  let : Nonempty M := ⟨(Classical.arbitrary (NonnegativeHalf t)).val⟩
  obtain ⟨R⟩ := EuclideanEmbedding.nonempty_tubularRetraction e a
  obtain ⟨g, hg, H, hi, hd⟩ := LowSphereParameters.exists_embedded_representative_in_open
    e R (by decide) C.positiveInterior f
  have hgclass : singularHomologyMap g 2 (unitSphereTopClass 1) = u := by
    rw [← homotopic_homologyMap H 2]
    exact hf
  refine ⟨g, hg, hi, hd, ?_⟩
  rw [singularHomologyMap_comp, LinearMap.comp_apply, hgclass, hu]

end Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
