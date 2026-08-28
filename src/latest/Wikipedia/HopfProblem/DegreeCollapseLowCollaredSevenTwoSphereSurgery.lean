import Wikipedia.HopfProblem.DegreeCollapseLowCollaredSevenBoundary
import Wikipedia.HopfProblem.DegreeCollapseLowSurgeryHalfSecondHomology
import Wikipedia.HopfProblem.DegreeCollapseTimeCollarInterior

/-!

# An actual positive two-sphere step with the original half-homology marking

An embedded representative in the positive interior determines a complete
native framed surgery step. Its time, margin, regular collar and zero-atlas
diffeomorphism are constructed. The quotient kills the marked class in the
original nonnegative half, without assuming that class vanishes beforehand.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowCollaredSevenState

open NoExoticSixSphere GLOrthonormalization LowSurgery
open FramedAttachingProduct NativeSurgery SingularMayerVietoris SphereHomology

variable {B : Type} [TopologicalSpace B] (S : LowCollaredSevenState B)

theorem exists_twoSphere_step_of_embedded_representative
    (g : C(Sphere 2, S.collar.positiveInterior))
    (hg : ContMDiff (𝓡 2) (𝓡 7) ∞
      ((subtypeInclusion (S.collar.positiveInterior : Set S.Space)).comp g))
    (hi : Injective ((subtypeInclusion (S.collar.positiveInterior : Set S.Space)).comp g))
    (hd : ∀ s, Injective (mfderiv (𝓡 2) (𝓡 7)
      ((subtypeInclusion (S.collar.positiveInterior : Set S.Space)).comp g) s))
    (c : SingularHomology S.PositiveHalf 2)
    (hc : singularHomologyMap (S.collar.interiorToHalf.comp g) 2 (unitSphereTopClass 1) = c) :
    ∃ U : LowCollaredSevenState B, S.Step U ∧
      (SimplyConnectedSpace U.PositiveHalf ↔ SimplyConnectedSpace S.PositiveHalf) ∧
      ∃ φ : SingularHomology S.PositiveHalf 2 →ₗ[ℤ] SingularHomology U.PositiveHalf 2,
        Surjective φ ∧ LinearMap.ker φ = Submodule.span ℤ {c} := by
  let f := (subtypeInclusion (S.collar.positiveInterior : Set S.Space)).comp g
  have hpos : ∀ s, 0 < S.time (f s) := fun s ↦ (g s).property
  obtain ⟨A, hA, T, hT⟩ := exists_positive_framed_surgery_timeData (by decide) (by decide)
    S.embedding S.normalFrame f hg hi hd S.time S.time_smooth S.time_regular hpos
  let T' : TimeData A :=
    { time := S.time
      smooth := S.time_smooth
      regular := S.time_regular
      margin := T.margin
      margin_pos := T.margin_pos
      tube_time := by
        intro s v hv
        rw [← hT]
        exact T.tube_time s v hv }
  let U := S.perform A hA T' rfl
  have hm : (halfBoundaryPair A hA T').attachingSphere = S.collar.interiorToHalf.comp g := by
    apply ContinuousMap.ext
    intro s
    exact Subtype.ext (halfBoundaryPair_attaching A hA T' s)
  have hclass : TwoSphereHalf.attachingClass A hA T' = c := by
    rw [TwoSphereHalf.attachingClass_eq, hm]
    exact hc
  refine ⟨U, S.step_perform (by decide) (by decide) A hA T' rfl,
    TwoSphereHalf.positiveHalf_simplyConnected_iff A hA T',
    TwoSphereHalf.secondHomologyMap A hA T',
    TwoSphereHalf.secondHomologyMap_surjective A hA T', ?_⟩
  exact (TwoSphereHalf.secondHomologyMap_ker A hA T').trans
    (congrArg (fun v ↦ Submodule.span ℤ {v}) hclass)

end Wikipedia.HopfProblem.DegreeCollapse.LowCollaredSevenState
