import Wikipedia.HopfProblem.DegreeCollapseTimeCollarInterior
import Wikipedia.HopfProblem.DegreeCollapseLowSphereOpenRepresentative
import Wikipedia.HopfProblem.DegreeCollapseCircleLoopRepresentatives

/-!

# Embedded positive circles retaining each original based loop

First factor the specified based loop through the literal unit circle.
The actual collar homotopy moves that circle into the strict positive
half. Smoothing and affine perturbation then produce an embedded circle
there. The composed homotopy remains in the original half throughout,
so nullity after any subsequent actual map can be compared directly.
No simple-connectivity assumption is used.
-/

noncomputable section

open Function Topology ContinuousMap
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.TimeCollar

open NoExoticSixSphere GLOrthonormalization SingularMayerVietoris

variable {M B : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [IsManifold (𝓡 7) ∞ M] [CompactSpace M] [T2Space M] [TopologicalSpace B]
  (e : EuclideanEmbedding 7 M) (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
  {t : M → ℝ} (C : TimeCollar t B)

include e a in
theorem exists_interior_circle_representative (x : NonnegativeHalf t)
    (c : FundamentalGroup (NonnegativeHalf t) x) :
    ∃ (f : SmoothCube.BasedMap 1 (NonnegativeHalf t) x)
      (g : C(Sphere 1, C.positiveInterior)),
      FundamentalGroup.mapOfEq f.val f.property CircleLoopRepresentatives.parameterClass = c ∧
      ContMDiff (𝓡 1) (𝓡 7) ∞ ((subtypeInclusion (C.positiveInterior : Set M)).comp g) ∧
      IsClosedEmbedding ((subtypeInclusion (C.positiveInterior : Set M)).comp g) ∧
      (∀ s, Injective (mfderiv (𝓡 1) (𝓡 7)
        ((subtypeInclusion (C.positiveInterior : Set M)).comp g) s)) ∧
      f.val.Homotopic (C.interiorToHalf.comp g) := by
  obtain ⟨f, hf, hc⟩ := CircleLoopRepresentatives.exists_circleMap x c
  let : Nonempty M := ⟨x.val⟩
  obtain ⟨R⟩ := EuclideanEmbedding.nonempty_tubularRetraction e a
  obtain ⟨g, hg, ⟨H⟩, hi, hd⟩ := LowSphereParameters.exists_embedded_representative_in_open
    e R (by decide) C.positiveInterior (C.halfToInterior.comp f)
  refine ⟨⟨f, hf⟩, g, hc, hg, hi, hd, ⟨?_⟩⟩
  exact (C.halfInteriorSlide.compContinuousMap f).trans
    ((ContinuousMap.Homotopy.refl C.interiorToHalf).comp H)

end Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
