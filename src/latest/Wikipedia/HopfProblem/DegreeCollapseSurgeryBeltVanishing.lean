import Wikipedia.HopfProblem.DegreeCollapseSurgeryBeltLink
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# A bounding old link with surjective normal degree kills the actual belt

The old link factors through a space with zero homology. Its image in the
actual surgery target is therefore zero. The tube-to-belt homotopy and
surjectivity of the actual normal map then kill the entire belt homology
map. No vanishing of the belt is supplied as a hypothesis.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SurgeryLink

open Wikipedia.SmoothSixDPoincare FramedSurgery PuncturedHandle
open SingularMayerVietoris PeriodTorusHigherHomology

variable {E F G H X : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X)
  (n : ℕ) [Fact (Module.finrank ℝ F = n + 1)]

theorem belt_homology_zero_of_link {Z T : Type} [TopologicalSpace Z] [TopologicalSpace T]
    (k : ℕ) [Subsingleton (SingularHomology Z k)]
    (g : C(Z, oldPatch A)) (l : C(T, Z)) (a : C(T, Overlap E F))
    (hlink : g.comp l = (oldTube A).comp a)
    (hnormal : Surjective (singularHomologyMap
      ((normalDirection (E := E) (m := m) n).comp a) k)) :
    singularHomologyMap (beltMap A n) k = 0 := by
  have hzero (x : SingularHomology T k) :
      singularHomologyMap ((oldTube A).comp a) k x = 0 := by
    rw [← hlink, singularHomologyMap_comp, LinearMap.comp_apply,
      Subsingleton.elim (singularHomologyMap l k x) 0, map_zero]
  apply LinearMap.ext
  intro y
  obtain ⟨x, hx⟩ := hnormal y
  have hh := DFunLike.congr_fun
    (homotopy_homologyMap ((tubeToBelt A n).compContinuousMap a) k) x
  simp only [singularHomologyMap_comp, LinearMap.comp_apply] at hh
  change singularHomologyMap (beltMap A n) k y = 0
  rw [← hx, singularHomologyMap_comp, LinearMap.comp_apply, ← hh]
  have hz : singularHomologyMap (oldTube A) k (singularHomologyMap a k x) = 0 := by
    simpa only [singularHomologyMap_comp, LinearMap.comp_apply] using hzero x
  rw [hz, map_zero]

end Wikipedia.HopfProblem.DegreeCollapse.SurgeryLink
