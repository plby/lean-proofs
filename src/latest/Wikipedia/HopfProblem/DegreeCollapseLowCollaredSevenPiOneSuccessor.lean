import Wikipedia.HopfProblem.DegreeCollapseLowCollaredSevenBoundary
import Wikipedia.HopfProblem.DegreeCollapseTimeCollarPositiveCircle
import Wikipedia.HopfProblem.DegreeCollapseLowSurgeryHalfFundamentalGroup
import Wikipedia.HopfProblem.DegreeCollapseLowSurgeryZeroBasepoint

/-!

# An actual native circle surgery kills any specified original based loop

The boundary point supplies a fixed basepoint throughout the construction.
An actual circle map represents the chosen original class, and its homotopy
to the embedded positive core remains inside the original half. The whole
handle kills the core-circle classes; homotopy naturality therefore kills
the chosen original class. The native surgery surjection is based at the
same original boundary point in the preserved collar.
-/

noncomputable section

open Function ContinuousMap
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowCollaredSevenState

open NoExoticSixSphere GLOrthonormalization LowSurgery
open FramedAttachingProduct NativeSurgery SingularMayerVietoris
open Wikipedia.SmoothSixDPoincare

variable {B : Type} [TopologicalSpace B] (S : LowCollaredSevenState B)

def positiveBasepoint (b : B) : S.PositiveHalf :=
  ⟨(S.collar.zeroPoint b).val, (S.collar.zeroPoint_time b).ge⟩

theorem exists_piOne_killing_step [PathConnectedSpace S.PositiveHalf] (b : B)
    (c : FundamentalGroup S.PositiveHalf (S.positiveBasepoint b)) :
    ∃ U : LowCollaredSevenState B, S.Step U ∧ PathConnectedSpace U.PositiveHalf ∧
      ∃ φ : FundamentalGroup S.PositiveHalf (S.positiveBasepoint b) →*
          FundamentalGroup U.PositiveHalf (U.positiveBasepoint b),
        Surjective φ ∧ φ c = 1 := by
  obtain ⟨F, g, hF, hg, hi, hd, HF⟩ :=
    S.collar.exists_interior_circle_representative S.embedding S.normalFrame
      (S.positiveBasepoint b) c
  let f := (subtypeInclusion (S.collar.positiveInterior : Set S.Space)).comp g
  have hpos : ∀ s, 0 < S.time (f s) := fun s ↦ (g s).property
  obtain ⟨A, hA, T, hT⟩ := exists_positive_framed_surgery_timeData (by decide) (by decide)
    S.embedding S.normalFrame f hg hi.injective hd S.time S.time_smooth S.time_regular hpos
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
  let D := halfBoundaryPair A hA T'
  let r := zeroHalfExteriorPoint A hA T' S.collar b
  let : CompactSpace (OldPositiveHalf A T') := compactSpace_oldPositiveHalf A T'
  let : CompactSpace (NativeSurgery.PositiveHalf A hA T') := compactSpace_positiveHalf A hA T'
  let : SimplyConnectedSpace (Sphere 5) := EuclideanSphere.simplyConnectedSpace 3
  have hm : D.attachingSphere = S.collar.interiorToHalf.comp g := by
    apply ContinuousMap.ext
    intro s
    exact Subtype.ext (halfBoundaryPair_attaching A hA T' s)
  have hnew : D.newExterior r = U.positiveBasepoint b :=
    newExterior_zeroHalfExteriorPoint A hA T' S.collar b
  let φ := OneSphereHalf.fundamentalGroupMap A hA T' r
  have hkill : φ c = 1 := by
    change c ∈ (SurgeryPairBody.fundamentalGroupMap D r).ker
    rw [SurgeryPairBody.fundamentalGroupMap_ker]
    let q := SurgeryPairBody.oldMap D
    have H : F.val.Homotopic D.attachingSphere := by
      rw [hm]
      exact HF
    have horig : FundamentalGroup.map (q.comp F.val) (spherePole 1)
        CircleLoopRepresentatives.parameterClass = 1 :=
      SurgeryPairBody.homotopic_attaching_map_eq_one D H.some (spherePole 1)
        CircleLoopRepresentatives.parameterClass
    exact (CircleLoopRepresentatives.mapped_class_eq_one_iff F.property hF q).mpr horig
  refine ⟨U, S.step_perform (by decide) (by decide) A hA T' rfl,
    (OneSphereHalf.positiveHalf_pathConnected_iff A hA T').mpr inferInstance, ?_⟩
  have result : ∃ ψ : FundamentalGroup S.PositiveHalf (S.positiveBasepoint b) →*
      FundamentalGroup U.PositiveHalf (D.newExterior r), Surjective ψ ∧ ψ c = 1 :=
    ⟨φ, OneSphereHalf.fundamentalGroupMap_surjective A hA T' r, hkill⟩
  rw [hnew] at result
  exact result

end Wikipedia.HopfProblem.DegreeCollapse.LowCollaredSevenState
