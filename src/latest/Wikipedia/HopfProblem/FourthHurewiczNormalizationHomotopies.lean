import Wikipedia.HopfProblem.FourthHurewiczLowerNormalization
import Wikipedia.HopfProblem.FourthHurewiczThreeSimplexNormalization

/-!
# The complete coherent normalization homotopies in dimensions three through five

The already constructed lower-dimensional normalization is followed by
the genuine native third-homotopy contraction stage. Their actual
concatenation retains exact face compatibility. Every three-simplex ends
at the constant map, and constant inputs stay fixed throughout.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.FourthHurewicz

open FirstHurewicz SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]

/-- Complete normalization on actual three-simplices. -/
def normalizationThreeSimplexHomotopy : SingularSimplex X 3 → C(I × Simplex 3, X) :=
  ThirdHurewicz.composeSimplexHomotopies (ThirdHurewicz.normalizationThreeSimplexHomotopy x)
    (HigherHurewicz.simplexStraighteningHomotopy 3 x)
    (ThirdHurewicz.normalizationThreeSimplexHomotopy_zero x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 3 x)

/-- Complete normalization on actual four-simplices. -/
def normalizationFourSimplexHomotopy : SingularSimplex X 4 → C(I × Simplex 4, X) :=
  ThirdHurewicz.composeSimplexHomotopies (lowerFourSimplexHomotopy x)
    (threeFourSimplexHomotopy x) (lowerFourSimplexHomotopy_zero x)
    (threeFourSimplexHomotopy_zero x)

/-- The same complete normalization on actual five-simplices. -/
def normalizationFiveSimplexHomotopy : SingularSimplex X 5 → C(I × Simplex 5, X) :=
  ThirdHurewicz.composeSimplexHomotopies (lowerFiveSimplexHomotopy x)
    (threeFiveSimplexHomotopy x) (lowerFiveSimplexHomotopy_zero x)
    (threeFiveSimplexHomotopy_zero x)

@[simp] theorem normalizationThreeSimplexHomotopy_zero (smp : SingularSimplex X 3)
    (s : Simplex 3) : normalizationThreeSimplexHomotopy x smp (0, s) = smp s :=
  ThirdHurewicz.composeSimplexHomotopies_zero _ _ _ _ smp s

@[simp] theorem normalizationFourSimplexHomotopy_zero (smp : SingularSimplex X 4)
    (s : Simplex 4) : normalizationFourSimplexHomotopy x smp (0, s) = smp s :=
  ThirdHurewicz.composeSimplexHomotopies_zero _ _ _ _ smp s

@[simp] theorem normalizationFiveSimplexHomotopy_zero (smp : SingularSimplex X 5)
    (s : Simplex 5) : normalizationFiveSimplexHomotopy x smp (0, s) = smp s :=
  ThirdHurewicz.composeSimplexHomotopies_zero _ _ _ _ smp s

/-- Literal compatibility of the complete degree-three and degree-four families. -/
theorem normalizationHomotopy_face :
    FaceCompatibleHomotopies 3 (normalizationThreeSimplexHomotopy x)
      (normalizationFourSimplexHomotopy x) :=
  ThirdHurewicz.composeSimplexHomotopies_face
    (ThirdHurewicz.normalizationThreeSimplexHomotopy x)
    (HigherHurewicz.simplexStraighteningHomotopy 3 x)
    (lowerFourSimplexHomotopy x) (threeFourSimplexHomotopy x)
    (ThirdHurewicz.normalizationThreeSimplexHomotopy_zero x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 3 x)
    (lowerFourSimplexHomotopy_zero x) (threeFourSimplexHomotopy_zero x)
    (lowerFourSimplexHomotopy_face x) (threeFourSimplexHomotopy_face x)

/-- Literal compatibility also holds in the dimension supplying four-boundaries. -/
theorem normalizationFiveHomotopy_face :
    FaceCompatibleHomotopies 4 (normalizationFourSimplexHomotopy x)
      (normalizationFiveSimplexHomotopy x) :=
  ThirdHurewicz.composeSimplexHomotopies_face (lowerFourSimplexHomotopy x)
    (threeFourSimplexHomotopy x) (lowerFiveSimplexHomotopy x)
    (threeFiveSimplexHomotopy x) (lowerFourSimplexHomotopy_zero x)
    (threeFourSimplexHomotopy_zero x) (lowerFiveSimplexHomotopy_zero x)
    (threeFiveSimplexHomotopy_zero x) (lowerFiveSimplexHomotopy_face x)
    (threeFiveSimplexHomotopy_face x)

@[simp] theorem normalizationThreeSimplexHomotopy_const :
    normalizationThreeSimplexHomotopy x (ContinuousMap.const (Simplex 3) x) =
      ContinuousMap.const (I × Simplex 3) x :=
  ThirdHurewicz.composeSimplexHomotopies_const
    (ThirdHurewicz.normalizationThreeSimplexHomotopy x)
    (HigherHurewicz.simplexStraighteningHomotopy 3 x)
    (ThirdHurewicz.normalizationThreeSimplexHomotopy_zero x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 3 x) x
    (lowerThreeSimplexHomotopy_const x) (HigherHurewicz.simplexStraighteningHomotopy_const 3 x)

@[simp] theorem normalizationFourSimplexHomotopy_const :
    normalizationFourSimplexHomotopy x (ContinuousMap.const (Simplex 4) x) =
      ContinuousMap.const (I × Simplex 4) x :=
  ThirdHurewicz.composeSimplexHomotopies_const (lowerFourSimplexHomotopy x)
    (threeFourSimplexHomotopy x) (lowerFourSimplexHomotopy_zero x)
    (threeFourSimplexHomotopy_zero x) x (lowerFourSimplexHomotopy_const x)
    (threeFourSimplexHomotopy_const x)

@[simp] theorem normalizationFiveSimplexHomotopy_const :
    normalizationFiveSimplexHomotopy x (ContinuousMap.const (Simplex 5) x) =
      ContinuousMap.const (I × Simplex 5) x :=
  ThirdHurewicz.composeSimplexHomotopies_const (lowerFiveSimplexHomotopy x)
    (threeFiveSimplexHomotopy x) (lowerFiveSimplexHomotopy_zero x)
    (threeFiveSimplexHomotopy_zero x) x (lowerFiveSimplexHomotopy_const x)
    (threeFiveSimplexHomotopy_const x)

/-- Every final three-simplex is constant, by its actual native nullhomotopy. -/
@[simp] theorem normalizationThreeSimplexHomotopy_endpoint (smp : SingularSimplex X 3) :
    timeSlice (normalizationThreeSimplexHomotopy x smp) 1 =
      ContinuousMap.const (Simplex 3) x := by
  rw [normalizationThreeSimplexHomotopy, ThirdHurewicz.timeSlice_composeSimplexHomotopies_one,
    ThirdHurewicz.normalizationThreeSimplexHomotopy_endpoint]
  ext s
  exact HigherHurewicz.simplexStraighteningHomotopy_one 3 x
    (ThirdHurewicz.normalizedThreeSimplex x smp).val
    (ThirdHurewicz.normalizedThreeSimplex x smp).property s

end Wikipedia.HopfProblem.FourthHurewicz
