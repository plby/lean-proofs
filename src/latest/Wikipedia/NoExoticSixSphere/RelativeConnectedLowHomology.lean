import Wikipedia.NoExoticSixSphere.RelativeSingularHomology
import Wikipedia.HopfProblem.SphereHomologySuspensionOneZero
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCirclePoint

/-!
# The two lowest relative homology groups of a connected pair

The actual subspace inclusion is an isomorphism on degree-zero homology
when both spaces are path connected. The original pair sequence then
gives relative degree-zero vanishing; if the ambient space is contractible,
it also gives relative degree-one vanishing.
-/

noncomputable section

open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology SphereHomology

namespace NoExoticSixSphere.RelativeSingularHomology

variable {X : Type} [TopologicalSpace X] (U : Set X) [PathConnectedSpace U]

/-- The actual relative zero-dimensional group vanishes for a path-connected pair. -/
theorem connected_homologyZero_eq_zero [PathConnectedSpace X] (c : Homology U 0) : c = 0 := by
  obtain ⟨a, rfl⟩ := toRelative_zero_surjective U c
  have ha : a ∈ LinearMap.range (singularHomologyMap (subtypeInclusion U) 0) :=
    singularHomologyMap_zero_surjective (subtypeInclusion U) a
  rw [exact_at_ambient] at ha
  exact ha

theorem connected_homologyZero_subsingleton [PathConnectedSpace X] :
    Subsingleton (Homology U 0) :=
  ⟨fun a b => (connected_homologyZero_eq_zero U a).trans
    (connected_homologyZero_eq_zero U b).symm⟩

/-- The original connecting map to degree-zero subspace homology is zero. -/
theorem connected_connecting_zero [PathConnectedSpace X] (c : Homology U 1) :
    connecting U 0 c = 0 := by
  have hc : connecting U 0 c ∈ LinearMap.ker (singularHomologyMap (subtypeInclusion U) 0) :=
    (exact_at_subspace U 0).le ⟨c, rfl⟩
  exact singularHomologyMap_zero_injective (subtypeInclusion U)
    (hc.trans (singularHomologyMap (subtypeInclusion U) 0).map_zero.symm)

/-- Contractibility of the ambient space gives actual relative degree-one vanishing. -/
theorem connected_homologyOne_subsingleton [ContractibleSpace X] :
    Subsingleton (Homology U 1) := by
  let := contractible_homology_subsingleton X 1 (by decide)
  have hs : Function.Surjective (toRelative U 1) := by
    intro c
    have hc : c ∈ LinearMap.ker (connecting U 0) := connected_connecting_zero U c
    rw [← exact_at_relative] at hc
    exact hc
  exact hs.subsingleton

end NoExoticSixSphere.RelativeSingularHomology
