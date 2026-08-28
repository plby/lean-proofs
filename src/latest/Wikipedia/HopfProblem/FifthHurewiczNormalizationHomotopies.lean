import Wikipedia.HopfProblem.FifthHurewiczLowerNormalization
import Wikipedia.HopfProblem.FifthHurewiczFourSimplexNormalization

/-!
# Complete normalization homotopies in dimensions four through six

The previously constructed lower-dimensional normalization is followed
by the genuine native fourth-homotopy contraction. Actual concatenation
retains exact face compatibility, fixes constant inputs, and contracts
each final four-simplex to the base point.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.FifthHurewicz

open FirstHurewicz SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
  [Subsingleton (π_ 4 X x)]

/-- Complete normalization of actual four-simplices. -/
def normalizationFourSimplexHomotopy : SingularSimplex X 4 → C(I × Simplex 4, X) :=
  ThirdHurewicz.composeSimplexHomotopies (FourthHurewicz.normalizationFourSimplexHomotopy x)
    (HigherHurewicz.simplexStraighteningHomotopy 4 x)
    (FourthHurewicz.normalizationFourSimplexHomotopy_zero x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 4 x)

/-- Complete normalization of actual five-simplices. -/
def normalizationFiveSimplexHomotopy : SingularSimplex X 5 → C(I × Simplex 5, X) :=
  ThirdHurewicz.composeSimplexHomotopies (FourthHurewicz.normalizationFiveSimplexHomotopy x)
    (fourFiveSimplexHomotopy x) (FourthHurewicz.normalizationFiveSimplexHomotopy_zero x)
    (fourFiveSimplexHomotopy_zero x)

/-- The same complete family on actual six-simplices. -/
def normalizationSixSimplexHomotopy : SingularSimplex X 6 → C(I × Simplex 6, X) :=
  ThirdHurewicz.composeSimplexHomotopies (lowerSixSimplexHomotopy x)
    (fourSixSimplexHomotopy x) (lowerSixSimplexHomotopy_zero x)
    (fourSixSimplexHomotopy_zero x)

@[simp] theorem normalizationFourSimplexHomotopy_zero (smp : SingularSimplex X 4)
    (s : Simplex 4) : normalizationFourSimplexHomotopy x smp (0, s) = smp s :=
  ThirdHurewicz.composeSimplexHomotopies_zero _ _ _ _ smp s

@[simp] theorem normalizationFiveSimplexHomotopy_zero (smp : SingularSimplex X 5)
    (s : Simplex 5) : normalizationFiveSimplexHomotopy x smp (0, s) = smp s :=
  ThirdHurewicz.composeSimplexHomotopies_zero _ _ _ _ smp s

@[simp] theorem normalizationSixSimplexHomotopy_zero (smp : SingularSimplex X 6)
    (s : Simplex 6) : normalizationSixSimplexHomotopy x smp (0, s) = smp s :=
  ThirdHurewicz.composeSimplexHomotopies_zero _ _ _ _ smp s

/-- Exact compatibility of the complete four- and five-simplex homotopies. -/
theorem normalizationHomotopy_face :
    FaceCompatibleHomotopies 4 (normalizationFourSimplexHomotopy x)
      (normalizationFiveSimplexHomotopy x) :=
  ThirdHurewicz.composeSimplexHomotopies_face
    (FourthHurewicz.normalizationFourSimplexHomotopy x)
    (HigherHurewicz.simplexStraighteningHomotopy 4 x)
    (FourthHurewicz.normalizationFiveSimplexHomotopy x) (fourFiveSimplexHomotopy x)
    (FourthHurewicz.normalizationFourSimplexHomotopy_zero x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 4 x)
    (FourthHurewicz.normalizationFiveSimplexHomotopy_zero x) (fourFiveSimplexHomotopy_zero x)
    (FourthHurewicz.normalizationFiveHomotopy_face x) (fourFiveSimplexHomotopy_face x)

/-- The companion homotopy supplying actual six-boundaries has the same original faces. -/
theorem normalizationSixHomotopy_face :
    FaceCompatibleHomotopies 5 (normalizationFiveSimplexHomotopy x)
      (normalizationSixSimplexHomotopy x) :=
  ThirdHurewicz.composeSimplexHomotopies_face
    (FourthHurewicz.normalizationFiveSimplexHomotopy x) (fourFiveSimplexHomotopy x)
    (lowerSixSimplexHomotopy x) (fourSixSimplexHomotopy x)
    (FourthHurewicz.normalizationFiveSimplexHomotopy_zero x) (fourFiveSimplexHomotopy_zero x)
    (lowerSixSimplexHomotopy_zero x) (fourSixSimplexHomotopy_zero x)
    (lowerSixSimplexHomotopy_face x) (fourSixSimplexHomotopy_face x)

@[simp] theorem normalizationFourSimplexHomotopy_const :
    normalizationFourSimplexHomotopy x (ContinuousMap.const (Simplex 4) x) =
      ContinuousMap.const (I × Simplex 4) x :=
  ThirdHurewicz.composeSimplexHomotopies_const
    (FourthHurewicz.normalizationFourSimplexHomotopy x)
    (HigherHurewicz.simplexStraighteningHomotopy 4 x)
    (FourthHurewicz.normalizationFourSimplexHomotopy_zero x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 4 x) x
    (FourthHurewicz.normalizationFourSimplexHomotopy_const x)
    (HigherHurewicz.simplexStraighteningHomotopy_const 4 x)

@[simp] theorem normalizationFiveSimplexHomotopy_const :
    normalizationFiveSimplexHomotopy x (ContinuousMap.const (Simplex 5) x) =
      ContinuousMap.const (I × Simplex 5) x :=
  ThirdHurewicz.composeSimplexHomotopies_const
    (FourthHurewicz.normalizationFiveSimplexHomotopy x) (fourFiveSimplexHomotopy x)
    (FourthHurewicz.normalizationFiveSimplexHomotopy_zero x) (fourFiveSimplexHomotopy_zero x) x
    (FourthHurewicz.normalizationFiveSimplexHomotopy_const x) (fourFiveSimplexHomotopy_const x)

@[simp] theorem normalizationSixSimplexHomotopy_const :
    normalizationSixSimplexHomotopy x (ContinuousMap.const (Simplex 6) x) =
      ContinuousMap.const (I × Simplex 6) x :=
  ThirdHurewicz.composeSimplexHomotopies_const (lowerSixSimplexHomotopy x)
    (fourSixSimplexHomotopy x) (lowerSixSimplexHomotopy_zero x)
    (fourSixSimplexHomotopy_zero x) x (lowerSixSimplexHomotopy_const x)
    (fourSixSimplexHomotopy_const x)

/-- The final four-simplex is constant by the actual native fourth-homotopy contraction. -/
@[simp] theorem normalizationFourSimplexHomotopy_endpoint (smp : SingularSimplex X 4) :
    timeSlice (normalizationFourSimplexHomotopy x smp) 1 =
      ContinuousMap.const (Simplex 4) x := by
  rw [normalizationFourSimplexHomotopy, ThirdHurewicz.timeSlice_composeSimplexHomotopies_one,
    FourthHurewicz.normalizationFourSimplexHomotopy_endpoint]
  ext s
  exact HigherHurewicz.simplexStraighteningHomotopy_one 4 x
    (FourthHurewicz.normalizedFourSimplex x smp).val
    (FourthHurewicz.normalizedFourSimplex x smp).property s

end Wikipedia.HopfProblem.FifthHurewicz
