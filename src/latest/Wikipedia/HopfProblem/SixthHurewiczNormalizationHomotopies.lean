import Wikipedia.HopfProblem.SixthHurewiczLowerNormalization
import Wikipedia.HopfProblem.SixthHurewiczFiveSimplexNormalization

/-!
# Complete normalization homotopies in dimensions five through seven

The previously constructed lower-dimensional normalization is followed
by the genuine native fifth-homotopy contraction. Actual concatenation
retains exact face compatibility, fixes constant inputs, and contracts
each final five-simplex to the base point.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SixthHurewicz

open FirstHurewicz SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
  [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)]

/-- Complete normalization of actual five-simplices. -/
def normalizationFiveSimplexHomotopy : SingularSimplex X 5 → C(I × Simplex 5, X) :=
  ThirdHurewicz.composeSimplexHomotopies (FifthHurewicz.normalizationFiveSimplexHomotopy x)
    (HigherHurewicz.simplexStraighteningHomotopy 5 x)
    (FifthHurewicz.normalizationFiveSimplexHomotopy_zero x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 5 x)

/-- Complete normalization of actual six-simplices. -/
def normalizationSixSimplexHomotopy : SingularSimplex X 6 → C(I × Simplex 6, X) :=
  ThirdHurewicz.composeSimplexHomotopies (FifthHurewicz.normalizationSixSimplexHomotopy x)
    (fiveSixSimplexHomotopy x) (FifthHurewicz.normalizationSixSimplexHomotopy_zero x)
    (fiveSixSimplexHomotopy_zero x)

/-- The same complete family on actual seven-simplices. -/
def normalizationSevenSimplexHomotopy : SingularSimplex X 7 → C(I × Simplex 7, X) :=
  ThirdHurewicz.composeSimplexHomotopies (lowerSevenSimplexHomotopy x)
    (fiveSevenSimplexHomotopy x) (lowerSevenSimplexHomotopy_zero x)
    (fiveSevenSimplexHomotopy_zero x)

@[simp] theorem normalizationFiveSimplexHomotopy_zero (smp : SingularSimplex X 5)
    (s : Simplex 5) : normalizationFiveSimplexHomotopy x smp (0, s) = smp s :=
  ThirdHurewicz.composeSimplexHomotopies_zero _ _ _ _ smp s

@[simp] theorem normalizationSixSimplexHomotopy_zero (smp : SingularSimplex X 6)
    (s : Simplex 6) : normalizationSixSimplexHomotopy x smp (0, s) = smp s :=
  ThirdHurewicz.composeSimplexHomotopies_zero _ _ _ _ smp s

@[simp] theorem normalizationSevenSimplexHomotopy_zero (smp : SingularSimplex X 7)
    (s : Simplex 7) : normalizationSevenSimplexHomotopy x smp (0, s) = smp s :=
  ThirdHurewicz.composeSimplexHomotopies_zero _ _ _ _ smp s

/-- Exact compatibility of the complete five- and six-simplex homotopies. -/
theorem normalizationHomotopy_face :
    FaceCompatibleHomotopies 5 (normalizationFiveSimplexHomotopy x)
      (normalizationSixSimplexHomotopy x) :=
  ThirdHurewicz.composeSimplexHomotopies_face
    (FifthHurewicz.normalizationFiveSimplexHomotopy x)
    (HigherHurewicz.simplexStraighteningHomotopy 5 x)
    (FifthHurewicz.normalizationSixSimplexHomotopy x) (fiveSixSimplexHomotopy x)
    (FifthHurewicz.normalizationFiveSimplexHomotopy_zero x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 5 x)
    (FifthHurewicz.normalizationSixSimplexHomotopy_zero x) (fiveSixSimplexHomotopy_zero x)
    (FifthHurewicz.normalizationSixHomotopy_face x) (fiveSixSimplexHomotopy_face x)

/-- The companion homotopy supplying actual seven-boundaries has the same original faces. -/
theorem normalizationSevenHomotopy_face :
    FaceCompatibleHomotopies 6 (normalizationSixSimplexHomotopy x)
      (normalizationSevenSimplexHomotopy x) :=
  ThirdHurewicz.composeSimplexHomotopies_face
    (FifthHurewicz.normalizationSixSimplexHomotopy x) (fiveSixSimplexHomotopy x)
    (lowerSevenSimplexHomotopy x) (fiveSevenSimplexHomotopy x)
    (FifthHurewicz.normalizationSixSimplexHomotopy_zero x) (fiveSixSimplexHomotopy_zero x)
    (lowerSevenSimplexHomotopy_zero x) (fiveSevenSimplexHomotopy_zero x)
    (lowerSevenSimplexHomotopy_face x) (fiveSevenSimplexHomotopy_face x)

@[simp] theorem normalizationFiveSimplexHomotopy_const :
    normalizationFiveSimplexHomotopy x (ContinuousMap.const (Simplex 5) x) =
      ContinuousMap.const (I × Simplex 5) x :=
  ThirdHurewicz.composeSimplexHomotopies_const
    (FifthHurewicz.normalizationFiveSimplexHomotopy x)
    (HigherHurewicz.simplexStraighteningHomotopy 5 x)
    (FifthHurewicz.normalizationFiveSimplexHomotopy_zero x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 5 x) x
    (FifthHurewicz.normalizationFiveSimplexHomotopy_const x)
    (HigherHurewicz.simplexStraighteningHomotopy_const 5 x)

@[simp] theorem normalizationSixSimplexHomotopy_const :
    normalizationSixSimplexHomotopy x (ContinuousMap.const (Simplex 6) x) =
      ContinuousMap.const (I × Simplex 6) x :=
  ThirdHurewicz.composeSimplexHomotopies_const
    (FifthHurewicz.normalizationSixSimplexHomotopy x) (fiveSixSimplexHomotopy x)
    (FifthHurewicz.normalizationSixSimplexHomotopy_zero x) (fiveSixSimplexHomotopy_zero x) x
    (FifthHurewicz.normalizationSixSimplexHomotopy_const x) (fiveSixSimplexHomotopy_const x)

@[simp] theorem normalizationSevenSimplexHomotopy_const :
    normalizationSevenSimplexHomotopy x (ContinuousMap.const (Simplex 7) x) =
      ContinuousMap.const (I × Simplex 7) x :=
  ThirdHurewicz.composeSimplexHomotopies_const (lowerSevenSimplexHomotopy x)
    (fiveSevenSimplexHomotopy x) (lowerSevenSimplexHomotopy_zero x)
    (fiveSevenSimplexHomotopy_zero x) x (lowerSevenSimplexHomotopy_const x)
    (fiveSevenSimplexHomotopy_const x)

/-- The final five-simplex is constant by the actual native fifth-homotopy contraction. -/
@[simp] theorem normalizationFiveSimplexHomotopy_endpoint (smp : SingularSimplex X 5) :
    timeSlice (normalizationFiveSimplexHomotopy x smp) 1 =
      ContinuousMap.const (Simplex 5) x := by
  rw [normalizationFiveSimplexHomotopy, ThirdHurewicz.timeSlice_composeSimplexHomotopies_one,
    FifthHurewicz.normalizationFiveSimplexHomotopy_endpoint]
  ext s
  exact HigherHurewicz.simplexStraighteningHomotopy_one 5 x
    (FifthHurewicz.normalizedFiveSimplex x smp).val
    (FifthHurewicz.normalizedFiveSimplex x smp).property s

end Wikipedia.HopfProblem.SixthHurewicz
