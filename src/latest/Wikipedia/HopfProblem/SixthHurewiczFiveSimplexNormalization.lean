import Wikipedia.HopfProblem.HigherHurewiczSimplexStraightening
import Wikipedia.HopfProblem.ThirdHurewiczCoherentHomotopyConstants

/-!
# Coherent native fifth-homotopy contraction through degree seven

The proved dimension-independent nullhomotopy construction contracts
actual based five-simplices from trivial native fifth homotopy. Genuine
coherent extensions propagate these homotopies over six- and seven-
simplices, retaining all literal face restrictions.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SixthHurewicz

open FirstHurewicz SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X]
variable (x : X) [Subsingleton (π_ 5 X x)]

/-- Extend the actual five-simplex contractions over original six-simplices. -/
def fiveSixSimplexHomotopy (smp : SingularSimplex X 6) : C(I × Simplex 6, X) :=
  extendCoherentSimplexHomotopy (stationarySimplexHomotopy 4)
    (HigherHurewicz.simplexStraighteningHomotopy 5 x)
    (HigherHurewicz.simplexStraighteningHomotopy_face 4 x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 5 x) smp

@[simp] theorem fiveSixSimplexHomotopy_zero (smp : SingularSimplex X 6)
    (s : Simplex 6) : fiveSixSimplexHomotopy x smp (0, s) = smp s :=
  extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

theorem fiveSixSimplexHomotopy_face :
    FaceCompatibleHomotopies 5 (HigherHurewicz.simplexStraighteningHomotopy 5 x)
      (fiveSixSimplexHomotopy x) :=
  extendCoherentSimplexHomotopy_face (stationarySimplexHomotopy 4)
    (HigherHurewicz.simplexStraighteningHomotopy 5 x)
    (HigherHurewicz.simplexStraighteningHomotopy_face 4 x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 5 x)

@[simp] theorem fiveSixSimplexHomotopy_const :
    fiveSixSimplexHomotopy x (ContinuousMap.const (Simplex 6) x) =
      ContinuousMap.const (I × Simplex 6) x :=
  ThirdHurewicz.extendCoherentSimplexHomotopy_const (stationarySimplexHomotopy 4)
    (HigherHurewicz.simplexStraighteningHomotopy 5 x)
    (HigherHurewicz.simplexStraighteningHomotopy_face 4 x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 5 x) x
    (HigherHurewicz.simplexStraighteningHomotopy_const 5 x)

/-- Extend that same compatible six-simplex family over original seven-simplices. -/
def fiveSevenSimplexHomotopy (smp : SingularSimplex X 7) : C(I × Simplex 7, X) :=
  extendCoherentSimplexHomotopy (HigherHurewicz.simplexStraighteningHomotopy 5 x)
    (fiveSixSimplexHomotopy x) (fiveSixSimplexHomotopy_face x)
    (fiveSixSimplexHomotopy_zero x) smp

@[simp] theorem fiveSevenSimplexHomotopy_zero (smp : SingularSimplex X 7)
    (s : Simplex 7) : fiveSevenSimplexHomotopy x smp (0, s) = smp s :=
  extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

theorem fiveSevenSimplexHomotopy_face :
    FaceCompatibleHomotopies 6 (fiveSixSimplexHomotopy x) (fiveSevenSimplexHomotopy x) :=
  extendCoherentSimplexHomotopy_face (HigherHurewicz.simplexStraighteningHomotopy 5 x)
    (fiveSixSimplexHomotopy x) (fiveSixSimplexHomotopy_face x)
    (fiveSixSimplexHomotopy_zero x)

@[simp] theorem fiveSevenSimplexHomotopy_const :
    fiveSevenSimplexHomotopy x (ContinuousMap.const (Simplex 7) x) =
      ContinuousMap.const (I × Simplex 7) x :=
  ThirdHurewicz.extendCoherentSimplexHomotopy_const
    (HigherHurewicz.simplexStraighteningHomotopy 5 x) (fiveSixSimplexHomotopy x)
    (fiveSixSimplexHomotopy_face x) (fiveSixSimplexHomotopy_zero x) x
    (fiveSixSimplexHomotopy_const x)

end Wikipedia.HopfProblem.SixthHurewicz
