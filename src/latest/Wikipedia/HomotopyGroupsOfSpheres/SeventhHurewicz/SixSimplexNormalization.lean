import Wikipedia.HopfProblem.HigherHurewiczSimplexStraightening
import Wikipedia.HopfProblem.ThirdHurewiczCoherentHomotopyConstants

/-!
# Coherent native sixth-homotopy contraction through degree eight

The proved dimension-independent nullhomotopy construction contracts
actual based six-simplices from trivial native sixth homotopy. Genuine
coherent extensions propagate these homotopies over seven- and eight-
simplices, retaining all literal face restrictions.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz

open Wikipedia.HopfProblem

open FirstHurewicz SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X]
variable (x : X) [Subsingleton (π_ 6 X x)]

/-- Extend the actual six-simplex contractions over original seven-simplices. -/
def sixSevenSimplexHomotopy (smp : SingularSimplex X 7) : C(I × Simplex 7, X) :=
  extendCoherentSimplexHomotopy (stationarySimplexHomotopy 5)
    (HigherHurewicz.simplexStraighteningHomotopy 6 x)
    (HigherHurewicz.simplexStraighteningHomotopy_face 5 x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 6 x) smp

@[simp] theorem sixSevenSimplexHomotopy_zero (smp : SingularSimplex X 7)
    (s : Simplex 7) : sixSevenSimplexHomotopy x smp (0, s) = smp s :=
  extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

theorem sixSevenSimplexHomotopy_face :
    FaceCompatibleHomotopies 6 (HigherHurewicz.simplexStraighteningHomotopy 6 x)
      (sixSevenSimplexHomotopy x) :=
  extendCoherentSimplexHomotopy_face (stationarySimplexHomotopy 5)
    (HigherHurewicz.simplexStraighteningHomotopy 6 x)
    (HigherHurewicz.simplexStraighteningHomotopy_face 5 x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 6 x)

@[simp] theorem sixSevenSimplexHomotopy_const :
    sixSevenSimplexHomotopy x (ContinuousMap.const (Simplex 7) x) =
      ContinuousMap.const (I × Simplex 7) x :=
  ThirdHurewicz.extendCoherentSimplexHomotopy_const (stationarySimplexHomotopy 5)
    (HigherHurewicz.simplexStraighteningHomotopy 6 x)
    (HigherHurewicz.simplexStraighteningHomotopy_face 5 x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 6 x) x
    (HigherHurewicz.simplexStraighteningHomotopy_const 6 x)

/-- Extend that same compatible seven-simplex family over original eight-simplices. -/
def sixEightSimplexHomotopy (smp : SingularSimplex X 8) : C(I × Simplex 8, X) :=
  extendCoherentSimplexHomotopy (HigherHurewicz.simplexStraighteningHomotopy 6 x)
    (sixSevenSimplexHomotopy x) (sixSevenSimplexHomotopy_face x)
    (sixSevenSimplexHomotopy_zero x) smp

@[simp] theorem sixEightSimplexHomotopy_zero (smp : SingularSimplex X 8)
    (s : Simplex 8) : sixEightSimplexHomotopy x smp (0, s) = smp s :=
  extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

theorem sixEightSimplexHomotopy_face :
    FaceCompatibleHomotopies 7 (sixSevenSimplexHomotopy x) (sixEightSimplexHomotopy x) :=
  extendCoherentSimplexHomotopy_face (HigherHurewicz.simplexStraighteningHomotopy 6 x)
    (sixSevenSimplexHomotopy x) (sixSevenSimplexHomotopy_face x)
    (sixSevenSimplexHomotopy_zero x)

@[simp] theorem sixEightSimplexHomotopy_const :
    sixEightSimplexHomotopy x (ContinuousMap.const (Simplex 8) x) =
      ContinuousMap.const (I × Simplex 8) x :=
  ThirdHurewicz.extendCoherentSimplexHomotopy_const
    (HigherHurewicz.simplexStraighteningHomotopy 6 x) (sixSevenSimplexHomotopy x)
    (sixSevenSimplexHomotopy_face x) (sixSevenSimplexHomotopy_zero x) x
    (sixSevenSimplexHomotopy_const x)

end Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz
