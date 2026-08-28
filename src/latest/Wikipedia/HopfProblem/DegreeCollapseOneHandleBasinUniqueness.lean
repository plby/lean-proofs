import Wikipedia.HopfProblem.DegreeCollapseBasinSublevelPaths
import Wikipedia.HopfProblem.DegreeCollapseUnitSphereOnePoints
import Wikipedia.HopfProblem.DegreeCollapseZeroOneBasinCancellation
import Wikipedia.SmoothSixDPoincare.MorseCellCover

/-!
# Distinct attaching components give a single minimum-basin branch

The two actual attaching points of an index-one handle cannot have a common
forward limit strictly below its lower level if their images are not joined
in that original sublevel. Once one branch is known to limit to a chosen
critical point, exactly one attaching parameter and exactly one lower-level
basin point have that endpoint.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.one_handle_forward_parameters_single
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : criticalPoints E f) (hp : f p < S.toSurgeryWindows.lower q)
    (hone : nativeMorseIndex E f q = 1)
    (u v : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (hnot : ¬Joined ((S.data q).coreBoundaryMap u) ((S.data q).coreBoundaryMap v))
    (hu : Tendsto (fun t => S.flow t ((S.data q).coreBoundaryMap u).val) atTop (𝓝 p.val)) :
    {w : sphere (0 : (S.data q).chart.NegativeCoordinates) 1 |
      Tendsto (fun t => S.flow t ((S.data q).coreBoundaryMap w).val) atTop (𝓝 p.val)}.ncard = 1 := by
  let : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace E M
  have hindex : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 1 :=
    (nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hone
  apply ncard_unitSphere_predicate_one hindex _ u v hu
  intro hv
  exact hnot (joined_sublevel_of_common_forward_limit S.flow hf.continuous
    (FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent)
    ((S.data q).coreBoundaryMap u) ((S.data q).coreBoundaryMap v) hp hu hv)

theorem AdaptedSurgeryWindows.one_handle_lower_basin_single
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : criticalPoints E f) (hp : f p < S.toSurgeryWindows.lower q)
    (hone : nativeMorseIndex E f q = 1)
    (u v : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (hnot : ¬Joined ((S.data q).coreBoundaryMap u) ((S.data q).coreBoundaryMap v))
    (hu : Tendsto (fun t => S.flow t ((S.data q).coreBoundaryMap u).val) atTop (𝓝 p.val)) :
    {x : (S.data q).LowerLevel |
      Tendsto (fun t => S.flow t x) atBot (𝓝 q.val) ∧
      Tendsto (fun t => S.flow t x) atTop (𝓝 p.val)}.ncard = 1 := by
  let P := {w : sphere (0 : (S.data q).chart.NegativeCoordinates) 1 |
    Tendsto (fun t => S.flow t ((S.data q).coreBoundaryMap w).val) atTop (𝓝 p.val)}
  have hP : P.ncard = 1 := S.one_handle_forward_parameters_single hf p q hp hone u v hnot hu
  obtain ⟨w, hw⟩ := Set.ncard_eq_one.mp hP
  have heq : {x : (S.data q).LowerLevel |
      Tendsto (fun t => S.flow t x) atBot (𝓝 q.val) ∧
      Tendsto (fun t => S.flow t x) atTop (𝓝 p.val)} =
      (S.data q).surgery.attachingSphere '' P := by
    ext x
    constructor
    · rintro ⟨hxq, hxp⟩
      obtain ⟨z, hz⟩ := (S.attaching_basin_iff hf q x).mp hxq
      refine ⟨z, ?_, hz⟩
      change Tendsto (fun t => S.flow t ((S.data q).surgery.attachingSphere z).val)
        atTop (𝓝 p.val)
      rw [hz]
      exact hxp
    · rintro ⟨z, hz, rfl⟩
      exact ⟨(S.attaching_basin_iff hf q _).mpr ⟨z, rfl⟩, hz⟩
  rw [heq, hw, image_singleton, ncard_singleton]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
