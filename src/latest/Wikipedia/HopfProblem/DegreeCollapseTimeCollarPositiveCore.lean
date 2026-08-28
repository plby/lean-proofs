import Wikipedia.HopfProblem.DegreeCollapseTimeCollarInterior
import Wikipedia.HopfProblem.DegreeCollapseSevenSphereOpenRepresentative
import Wikipedia.HopfProblem.DegreeCollapseIntegralSphereRepresentatives

/-!
# Positive embedded representatives from the actual time collar

Transfer simple connectivity and zero second homology through the actual
interior inclusion. Hurewicz supplies a sphere with the original integral
marking, and the open perturbation preserves its interior homotopy class.
The supplied ambient embedding and normal framing construct the required
tubular retraction. There is no reflected-cylinder hypothesis.
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
  {t : M → ℝ} (C : TimeCollar t B)
  [SimplyConnectedSpace (NonnegativeHalf t)] [Subsingleton (SingularHomology (NonnegativeHalf t) 2)]

include e a in
theorem exists_interior_core_representative (c : SingularHomology (NonnegativeHalf t) 3) :
    ∃ g : C(Sphere 3, C.positiveInterior),
      ContMDiff (𝓡 3) (𝓡 7) ∞ ((subtypeInclusion (C.positiveInterior : Set M)).comp g) ∧
      IsClosedEmbedding ((subtypeInclusion (C.positiveInterior : Set M)).comp g) ∧
      (∀ s, Injective (mfderiv (𝓡 3) (𝓡 7)
        ((subtypeInclusion (C.positiveInterior : Set M)).comp g) s)) ∧
      singularHomologyMap (C.interiorToHalf.comp g) 3 (unitSphereTopClass 2) = c := by
  let : SimplyConnectedSpace C.positiveInterior := C.interiorHalfHomotopyEquiv.simplyConnectedSpace
  let : Subsingleton (SingularHomology C.positiveInterior 2) :=
    (homotopyEquivHomologyEquiv C.interiorHalfHomotopyEquiv 2).injective.subsingleton
  obtain ⟨u, hu⟩ := (C.interiorToHalf_homology_bijective 3).2 c
  obtain ⟨f, hf⟩ := IntegralSphereRepresentatives.exists_sphereMap
    (Classical.arbitrary C.positiveInterior) u
  let : Nonempty M := ⟨(Classical.arbitrary (NonnegativeHalf t)).val⟩
  obtain ⟨R⟩ := EuclideanEmbedding.nonempty_tubularRetraction e a
  obtain ⟨g, hg, H, hi, hd⟩ := SevenSphereParameters.exists_embedded_representative_in_open
    e R (by decide) C.positiveInterior f
  have hgclass : singularHomologyMap g 3 (unitSphereTopClass 2) = u := by
    rw [← homotopic_homologyMap H 3]
    exact hf
  refine ⟨g, hg, hi, hd, ?_⟩
  rw [singularHomologyMap_comp, LinearMap.comp_apply, hgclass, hu]

include e a C in
theorem exists_positive_homology_core (c : SingularHomology (NonnegativeHalf t) 3) :
    ∃ f : C(Sphere 3, M), ContMDiff (𝓡 3) (𝓡 7) ∞ f ∧ Injective f ∧
      (∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s)) ∧ (∀ s, 0 < t (f s)) ∧
      singularHomologyMap f 3 (unitSphereTopClass 2) =
        singularHomologyMap (halfInclusion t) 3 c := by
  obtain ⟨g, hg, hi, hd, hclass⟩ := C.exists_interior_core_representative e a c
  refine ⟨(subtypeInclusion (C.positiveInterior : Set M)).comp g,
    hg, hi.injective, hd, fun s ↦ (g s).property, ?_⟩
  exact (LinearMap.congr_fun
    (singularHomologyMap_comp (C.interiorToHalf.comp g) (halfInclusion t) 3)
      (unitSphereTopClass 2)).trans (congrArg (singularHomologyMap (halfInclusion t) 3) hclass)

end Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
