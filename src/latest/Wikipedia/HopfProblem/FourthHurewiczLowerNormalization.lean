import Wikipedia.HopfProblem.ThirdHurewiczNormalizationHomotopies

/-!
# Extending the constructed lower-dimensional normalization through degree five

The actual composed vertex, edge, and triangle homotopy already exists
on three-simplices. Its exact face compatibility allows the proved
simplex-cylinder retraction to extend that single family over four- and
five-simplices. No further connectivity or extension property is assumed.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.FourthHurewicz

open FirstHurewicz SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)]

/-- The frozen composed degree-three homotopy fixes the literal constant simplex. -/
@[simp] theorem lowerThreeSimplexHomotopy_const :
    ThirdHurewicz.normalizationThreeSimplexHomotopy x
        (ContinuousMap.const (Simplex 3) x) =
      ContinuousMap.const (I × Simplex 3) x := by
  have hVE : ThirdHurewicz.vertexEdgeThreeSimplexHomotopy x
      (ContinuousMap.const (Simplex 3) x) =
      ContinuousMap.const (I × Simplex 3) x :=
    ThirdHurewicz.composeSimplexHomotopies_const (vertexStraighteningHomotopy x 3)
      (tetrahedronEdgeStraighteningHomotopy x) (vertexStraighteningHomotopy_zero x 3)
      (tetrahedronEdgeStraighteningHomotopy_zero x) x
      (vertexStraighteningHomotopy_const x 3) (ThirdHurewicz.edgeTetrahedronHomotopy_const x)
  exact ThirdHurewicz.composeSimplexHomotopies_const
    (ThirdHurewicz.vertexEdgeThreeSimplexHomotopy x)
    (ThirdHurewicz.triangleThreeSimplexHomotopy x)
    (ThirdHurewicz.vertexEdgeThreeSimplexHomotopy_zero x)
    (ThirdHurewicz.triangleThreeSimplexHomotopy_zero x) x hVE
    (ThirdHurewicz.triangleThreeSimplexHomotopy_const x)

/-- The genuine extension of all lower-dimensional stages to four-simplices. -/
def lowerFourSimplexHomotopy (smp : SingularSimplex X 4) : C(I × Simplex 4, X) :=
  extendCoherentSimplexHomotopy (ThirdHurewicz.normalizationTriangleHomotopy x)
    (ThirdHurewicz.normalizationThreeSimplexHomotopy x)
    (ThirdHurewicz.normalizationHomotopy_face x)
    (ThirdHurewicz.normalizationThreeSimplexHomotopy_zero x) smp

@[simp] theorem lowerFourSimplexHomotopy_zero (smp : SingularSimplex X 4)
    (s : Simplex 4) : lowerFourSimplexHomotopy x smp (0, s) = smp s :=
  extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

theorem lowerFourSimplexHomotopy_face :
    FaceCompatibleHomotopies 3 (ThirdHurewicz.normalizationThreeSimplexHomotopy x)
      (lowerFourSimplexHomotopy x) :=
  extendCoherentSimplexHomotopy_face (ThirdHurewicz.normalizationTriangleHomotopy x)
    (ThirdHurewicz.normalizationThreeSimplexHomotopy x)
    (ThirdHurewicz.normalizationHomotopy_face x)
    (ThirdHurewicz.normalizationThreeSimplexHomotopy_zero x)

@[simp] theorem lowerFourSimplexHomotopy_const :
    lowerFourSimplexHomotopy x (ContinuousMap.const (Simplex 4) x) =
      ContinuousMap.const (I × Simplex 4) x :=
  ThirdHurewicz.extendCoherentSimplexHomotopy_const
    (ThirdHurewicz.normalizationTriangleHomotopy x)
    (ThirdHurewicz.normalizationThreeSimplexHomotopy x)
    (ThirdHurewicz.normalizationHomotopy_face x)
    (ThirdHurewicz.normalizationThreeSimplexHomotopy_zero x) x
    (lowerThreeSimplexHomotopy_const x)

/-- The coherent degree-five extension needed for actual four-boundary relations. -/
def lowerFiveSimplexHomotopy (smp : SingularSimplex X 5) : C(I × Simplex 5, X) :=
  extendCoherentSimplexHomotopy (ThirdHurewicz.normalizationThreeSimplexHomotopy x)
    (lowerFourSimplexHomotopy x) (lowerFourSimplexHomotopy_face x)
    (lowerFourSimplexHomotopy_zero x) smp

@[simp] theorem lowerFiveSimplexHomotopy_zero (smp : SingularSimplex X 5)
    (s : Simplex 5) : lowerFiveSimplexHomotopy x smp (0, s) = smp s :=
  extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

theorem lowerFiveSimplexHomotopy_face :
    FaceCompatibleHomotopies 4 (lowerFourSimplexHomotopy x)
      (lowerFiveSimplexHomotopy x) :=
  extendCoherentSimplexHomotopy_face (ThirdHurewicz.normalizationThreeSimplexHomotopy x)
    (lowerFourSimplexHomotopy x) (lowerFourSimplexHomotopy_face x)
    (lowerFourSimplexHomotopy_zero x)

@[simp] theorem lowerFiveSimplexHomotopy_const :
    lowerFiveSimplexHomotopy x (ContinuousMap.const (Simplex 5) x) =
      ContinuousMap.const (I × Simplex 5) x :=
  ThirdHurewicz.extendCoherentSimplexHomotopy_const
    (ThirdHurewicz.normalizationThreeSimplexHomotopy x) (lowerFourSimplexHomotopy x)
    (lowerFourSimplexHomotopy_face x) (lowerFourSimplexHomotopy_zero x) x
    (lowerFourSimplexHomotopy_const x)

end Wikipedia.HopfProblem.FourthHurewicz
