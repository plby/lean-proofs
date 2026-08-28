import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.LowerNormalization
import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.SixSimplexNormalization

/-!
# Complete normalization homotopies in dimensions six through eight

The previously constructed lower-dimensional normalization is followed
by the genuine native sixth-homotopy contraction. Actual concatenation
retains exact face compatibility, fixes constant inputs, and contracts
each final six-simplex to the base point.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz

open Wikipedia.HopfProblem

open FirstHurewicz SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
  [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] [Subsingleton (π_ 6 X x)]

/-- Complete normalization of actual six-simplices. -/
def normalizationSixSimplexHomotopy : SingularSimplex X 6 → C(I × Simplex 6, X) :=
  ThirdHurewicz.composeSimplexHomotopies (SixthHurewicz.normalizationSixSimplexHomotopy x)
    (HigherHurewicz.simplexStraighteningHomotopy 6 x)
    (SixthHurewicz.normalizationSixSimplexHomotopy_zero x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 6 x)

/-- Complete normalization of actual seven-simplices. -/
def normalizationSevenSimplexHomotopy : SingularSimplex X 7 → C(I × Simplex 7, X) :=
  ThirdHurewicz.composeSimplexHomotopies (SixthHurewicz.normalizationSevenSimplexHomotopy x)
    (sixSevenSimplexHomotopy x) (SixthHurewicz.normalizationSevenSimplexHomotopy_zero x)
    (sixSevenSimplexHomotopy_zero x)

/-- The same complete family on actual eight-simplices. -/
def normalizationEightSimplexHomotopy : SingularSimplex X 8 → C(I × Simplex 8, X) :=
  ThirdHurewicz.composeSimplexHomotopies (lowerEightSimplexHomotopy x)
    (sixEightSimplexHomotopy x) (lowerEightSimplexHomotopy_zero x)
    (sixEightSimplexHomotopy_zero x)

@[simp] theorem normalizationSixSimplexHomotopy_zero (smp : SingularSimplex X 6)
    (s : Simplex 6) : normalizationSixSimplexHomotopy x smp (0, s) = smp s :=
  ThirdHurewicz.composeSimplexHomotopies_zero _ _ _ _ smp s

@[simp] theorem normalizationSevenSimplexHomotopy_zero (smp : SingularSimplex X 7)
    (s : Simplex 7) : normalizationSevenSimplexHomotopy x smp (0, s) = smp s :=
  ThirdHurewicz.composeSimplexHomotopies_zero _ _ _ _ smp s

@[simp] theorem normalizationEightSimplexHomotopy_zero (smp : SingularSimplex X 8)
    (s : Simplex 8) : normalizationEightSimplexHomotopy x smp (0, s) = smp s :=
  ThirdHurewicz.composeSimplexHomotopies_zero _ _ _ _ smp s

/-- Exact compatibility of the complete six- and seven-simplex homotopies. -/
theorem normalizationHomotopy_face :
    FaceCompatibleHomotopies 6 (normalizationSixSimplexHomotopy x)
      (normalizationSevenSimplexHomotopy x) :=
  ThirdHurewicz.composeSimplexHomotopies_face
    (SixthHurewicz.normalizationSixSimplexHomotopy x)
    (HigherHurewicz.simplexStraighteningHomotopy 6 x)
    (SixthHurewicz.normalizationSevenSimplexHomotopy x) (sixSevenSimplexHomotopy x)
    (SixthHurewicz.normalizationSixSimplexHomotopy_zero x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 6 x)
    (SixthHurewicz.normalizationSevenSimplexHomotopy_zero x) (sixSevenSimplexHomotopy_zero x)
    (SixthHurewicz.normalizationSevenHomotopy_face x) (sixSevenSimplexHomotopy_face x)

/-- The companion homotopy supplying actual eight-boundaries has the same original faces. -/
theorem normalizationEightHomotopy_face :
    FaceCompatibleHomotopies 7 (normalizationSevenSimplexHomotopy x)
      (normalizationEightSimplexHomotopy x) :=
  ThirdHurewicz.composeSimplexHomotopies_face
    (SixthHurewicz.normalizationSevenSimplexHomotopy x) (sixSevenSimplexHomotopy x)
    (lowerEightSimplexHomotopy x) (sixEightSimplexHomotopy x)
    (SixthHurewicz.normalizationSevenSimplexHomotopy_zero x) (sixSevenSimplexHomotopy_zero x)
    (lowerEightSimplexHomotopy_zero x) (sixEightSimplexHomotopy_zero x)
    (lowerEightSimplexHomotopy_face x) (sixEightSimplexHomotopy_face x)

@[simp] theorem normalizationSixSimplexHomotopy_const :
    normalizationSixSimplexHomotopy x (ContinuousMap.const (Simplex 6) x) =
      ContinuousMap.const (I × Simplex 6) x :=
  ThirdHurewicz.composeSimplexHomotopies_const
    (SixthHurewicz.normalizationSixSimplexHomotopy x)
    (HigherHurewicz.simplexStraighteningHomotopy 6 x)
    (SixthHurewicz.normalizationSixSimplexHomotopy_zero x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 6 x) x
    (SixthHurewicz.normalizationSixSimplexHomotopy_const x)
    (HigherHurewicz.simplexStraighteningHomotopy_const 6 x)

@[simp] theorem normalizationSevenSimplexHomotopy_const :
    normalizationSevenSimplexHomotopy x (ContinuousMap.const (Simplex 7) x) =
      ContinuousMap.const (I × Simplex 7) x :=
  ThirdHurewicz.composeSimplexHomotopies_const
    (SixthHurewicz.normalizationSevenSimplexHomotopy x) (sixSevenSimplexHomotopy x)
    (SixthHurewicz.normalizationSevenSimplexHomotopy_zero x) (sixSevenSimplexHomotopy_zero x) x
    (SixthHurewicz.normalizationSevenSimplexHomotopy_const x) (sixSevenSimplexHomotopy_const x)

@[simp] theorem normalizationEightSimplexHomotopy_const :
    normalizationEightSimplexHomotopy x (ContinuousMap.const (Simplex 8) x) =
      ContinuousMap.const (I × Simplex 8) x :=
  ThirdHurewicz.composeSimplexHomotopies_const (lowerEightSimplexHomotopy x)
    (sixEightSimplexHomotopy x) (lowerEightSimplexHomotopy_zero x)
    (sixEightSimplexHomotopy_zero x) x (lowerEightSimplexHomotopy_const x)
    (sixEightSimplexHomotopy_const x)

/-- The final six-simplex is constant by the actual native sixth-homotopy contraction. -/
@[simp] theorem normalizationSixSimplexHomotopy_endpoint (smp : SingularSimplex X 6) :
    timeSlice (normalizationSixSimplexHomotopy x smp) 1 =
      ContinuousMap.const (Simplex 6) x := by
  rw [normalizationSixSimplexHomotopy, ThirdHurewicz.timeSlice_composeSimplexHomotopies_one,
    SixthHurewicz.normalizationSixSimplexHomotopy_endpoint]
  ext s
  exact HigherHurewicz.simplexStraighteningHomotopy_one 6 x
    (SixthHurewicz.normalizedSixSimplex x smp).val
    (SixthHurewicz.normalizedSixSimplex x smp).property s

end Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz
