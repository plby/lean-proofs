import Wikipedia.HopfProblem.DegreeCollapseNativeOppositePassages
import Wikipedia.SmoothSixDPoincare.LinearSphereEquiv

/-!
# Select either prescribed integral unit using the two actual passages

The first normalized derivative acts by an integral unit relative to the
original sphere parametrization. The second acts by its negative. Thus
either requested unit is realized by one of the actual protected isotopies.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris PeriodTorusHigherHomology

local notation "P₃" => EuclideanSpace ℝ (Fin 3)
local notation "S₂" => Hemisphere.Sphere 2

variable {E M Y N : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [NormedAddCommGroup N] [NormedSpace ℝ N]

theorem choose_prescribed_normal_passage
    {f : S₂ → M} {g : Y → M} {x : S₂} {y : Y} {O : Set M}
    (n : M → N) (e : S₂ ≃ₜ sphere (0 : N) 1)
    (A₀ A₁ : CenteredSheetPassage E f g x y O) (L₀ L₁ : P₃ ≃L[ℝ] N)
    (hL₀ : HasFDerivAt (fun z : P₃ => n (A₀.family
      ((radialParameterChart (1 / 2) x z).1, f (radialParameterChart (1 / 2) x z).2)))
      L₀.toContinuousLinearMap 0)
    (hL₁ : HasFDerivAt (fun z : P₃ => n (A₁.family
      ((radialParameterChart (1 / 2) x z).1, f (radialParameterChart (1 / 2) x z).2)))
      L₁.toContinuousLinearMap 0)
    (hdet : (L₁.trans L₀.symm).toLinearMap.det < 0)
    (k : ℤ) (hk : k = 1 ∨ k = -1) :
    ∃ (A : CenteredSheetPassage E f g x y O) (L : P₃ ≃L[ℝ] N),
      HasFDerivAt (fun z : P₃ => n (A.family
        ((radialParameterChart (1 / 2) x z).1, f (radialParameterChart (1 / 2) x z).2)))
        L.toContinuousLinearMap 0 ∧
      singularHomologyMap (LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective) 2 =
        k • singularHomologyMap (e : C(S₂, sphere (0 : N) 1)) 2 := by
  have hbij : Bijective (singularHomologyMap
      (LinearSphereAction.sphereMap L₀.toContinuousLinearMap L₀.injective) 2) := by
    have heq : (LinearSphereAction.homologyEquiv L₀ 2 :
        SingularHomology S₂ 2 → SingularHomology (sphere (0 : N) 1) 2) =
        singularHomologyMap (LinearSphereAction.sphereMap L₀.toContinuousLinearMap L₀.injective) 2 :=
      funext (LinearSphereAction.homologyEquiv_apply L₀ 2)
    rw [← heq]
    exact (LinearSphereAction.homologyEquiv L₀ 2).bijective
  obtain ⟨u, hu, hunit⟩ := two_sphere_map_unit_of_homology_bijective e
    (LinearSphereAction.sphereMap L₀.toContinuousLinearMap L₀.injective) hbij
  have hopp : singularHomologyMap
      (LinearSphereAction.sphereMap L₁.toContinuousLinearMap L₁.injective) 2 =
      -singularHomologyMap (LinearSphereAction.sphereMap L₀.toContinuousLinearMap L₀.injective) 2 := by
    simpa using attaching_contributions_opposite_of_relative_det_neg
      (ContinuousMap.id (sphere (0 : N) 1)) L₀ L₁ hdet
  by_cases huk : u = k
  · exact ⟨A₀, L₀, hL₀, huk ▸ hunit⟩
  · have hneg : -u = k := by
      rcases hu with rfl | rfl <;> rcases hk with rfl | rfl <;> norm_num at *
    refine ⟨A₁, L₁, hL₁, ?_⟩
    rw [hopp, hunit, ← neg_zsmul, hneg]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
