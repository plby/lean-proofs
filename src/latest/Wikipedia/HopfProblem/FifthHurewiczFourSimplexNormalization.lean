import Wikipedia.HopfProblem.HigherHurewiczSimplexStraightening
import Wikipedia.HopfProblem.ThirdHurewiczCoherentHomotopyConstants

/-!
# Coherent native fourth-homotopy contraction through degree six

The already proved dimension-independent nullhomotopy construction
contracts actual based four-simplices from trivial native fourth
homotopy. Genuine coherent extensions propagate these homotopies over
five- and six-simplices, retaining all literal face restrictions.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.FifthHurewicz

open FirstHurewicz SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X]
variable (x : X) [Subsingleton (π_ 4 X x)]

/-- Extend the actual four-simplex contractions over original five-simplices. -/
def fourFiveSimplexHomotopy (smp : SingularSimplex X 5) : C(I × Simplex 5, X) :=
  extendCoherentSimplexHomotopy (stationarySimplexHomotopy 3)
    (HigherHurewicz.simplexStraighteningHomotopy 4 x)
    (HigherHurewicz.simplexStraighteningHomotopy_face 3 x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 4 x) smp

@[simp] theorem fourFiveSimplexHomotopy_zero (smp : SingularSimplex X 5)
    (s : Simplex 5) : fourFiveSimplexHomotopy x smp (0, s) = smp s :=
  extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

theorem fourFiveSimplexHomotopy_face :
    FaceCompatibleHomotopies 4 (HigherHurewicz.simplexStraighteningHomotopy 4 x)
      (fourFiveSimplexHomotopy x) :=
  extendCoherentSimplexHomotopy_face (stationarySimplexHomotopy 3)
    (HigherHurewicz.simplexStraighteningHomotopy 4 x)
    (HigherHurewicz.simplexStraighteningHomotopy_face 3 x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 4 x)

@[simp] theorem fourFiveSimplexHomotopy_const :
    fourFiveSimplexHomotopy x (ContinuousMap.const (Simplex 5) x) =
      ContinuousMap.const (I × Simplex 5) x :=
  ThirdHurewicz.extendCoherentSimplexHomotopy_const (stationarySimplexHomotopy 3)
    (HigherHurewicz.simplexStraighteningHomotopy 4 x)
    (HigherHurewicz.simplexStraighteningHomotopy_face 3 x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 4 x) x
    (HigherHurewicz.simplexStraighteningHomotopy_const 4 x)

/-- Extend that same compatible five-simplex family over original six-simplices. -/
def fourSixSimplexHomotopy (smp : SingularSimplex X 6) : C(I × Simplex 6, X) :=
  extendCoherentSimplexHomotopy (HigherHurewicz.simplexStraighteningHomotopy 4 x)
    (fourFiveSimplexHomotopy x) (fourFiveSimplexHomotopy_face x)
    (fourFiveSimplexHomotopy_zero x) smp

@[simp] theorem fourSixSimplexHomotopy_zero (smp : SingularSimplex X 6)
    (s : Simplex 6) : fourSixSimplexHomotopy x smp (0, s) = smp s :=
  extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

theorem fourSixSimplexHomotopy_face :
    FaceCompatibleHomotopies 5 (fourFiveSimplexHomotopy x) (fourSixSimplexHomotopy x) :=
  extendCoherentSimplexHomotopy_face (HigherHurewicz.simplexStraighteningHomotopy 4 x)
    (fourFiveSimplexHomotopy x) (fourFiveSimplexHomotopy_face x)
    (fourFiveSimplexHomotopy_zero x)

@[simp] theorem fourSixSimplexHomotopy_const :
    fourSixSimplexHomotopy x (ContinuousMap.const (Simplex 6) x) =
      ContinuousMap.const (I × Simplex 6) x :=
  ThirdHurewicz.extendCoherentSimplexHomotopy_const
    (HigherHurewicz.simplexStraighteningHomotopy 4 x) (fourFiveSimplexHomotopy x)
    (fourFiveSimplexHomotopy_face x) (fourFiveSimplexHomotopy_zero x) x
    (fourFiveSimplexHomotopy_const x)

end Wikipedia.HopfProblem.FifthHurewicz
