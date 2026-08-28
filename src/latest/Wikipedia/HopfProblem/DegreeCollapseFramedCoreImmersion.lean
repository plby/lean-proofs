import Wikipedia.HopfProblem.DegreeCollapseSurgeryDualConnectivity

/-!
# The actual framed-face core is an embedded native immersion

The full closed face supplies injectivity. Its genuine extending chart
factors the native core derivative through the injective zero-section
derivative. Postcomposition transports the entire face, retaining the
literal composed core map.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.FramedCore

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open Wikipedia.SmoothSixDPoincare

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [T2Space M] [IsManifold (𝓡 6) ∞ M]
  (B : SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) M)

theorem injective_core : Injective (FramedSurgery.coreMap (E := Vector 4) B) := by
  intro x y hxy
  exact congrArg Prod.fst (B.closedEmbedding.injective hxy)

theorem injective_core_derivative (x : Sphere 3) :
    Injective (mfderiv (𝓡 3) (𝓡 6) (FramedSurgery.coreMap (E := Vector 4) B) x) := by
  have he : (FramedSurgery.coreMap (E := Vector 4) B : Sphere 3 → M) =
      B.chart ∘ (fun u : Sphere 3 => (u, (0 : Vector 3))) :=
    funext (fun u => (B.point u ⟨0, by simp⟩).symm)
  have hx : (x, (0 : Vector 3)) ∈ B.chart.source :=
    B.source ⟨mem_univ _, mem_closedBall_self zero_le_one⟩
  have hs : MDifferentiableAt (𝓡 3) ((𝓡 3).prod 𝓘(ℝ, Vector 3))
      (fun u : Sphere 3 => (u, (0 : Vector 3))) x :=
    mdifferentiableAt_id.prodMk mdifferentiableAt_const
  have hc := mfderiv_comp x (B.chart.mdifferentiableAt (by simp) hx) hs
  rw [he, hc]
  apply (PartialChart.bijective_mfderiv B.chart hx).injective.comp
  rw [mfderiv_prod_left]
  intro v w hvw
  exact congrArg Prod.fst hvw

theorem postcompose_core (ψ : Diffeomorph (𝓡 6) (𝓡 6) M M ∞) :
    FramedSurgery.coreMap (E := Vector 4) (B.postcompose ψ) =
      ψ.toHomeomorph.toHomotopyEquiv.toFun.comp (FramedSurgery.coreMap (E := Vector 4) B) := rfl

end Wikipedia.HopfProblem.DegreeCollapse.FramedCore
