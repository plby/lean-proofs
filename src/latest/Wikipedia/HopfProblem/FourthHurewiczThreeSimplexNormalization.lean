import Wikipedia.HopfProblem.HigherHurewiczSimplexStraightening
import Wikipedia.HopfProblem.ThirdHurewiczCoherentHomotopyConstants

/-!
# Coherent native third-homotopy contraction through degree five

Trivial native third homotopy supplies genuine relative contractions of
based three-simplices. The proved coherent simplex-cylinder extension
propagates that family over four- and five-simplices while preserving
literal face restrictions and constant-input stationarity.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.FourthHurewicz

open FirstHurewicz SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X]
variable (x : X) [Subsingleton (π_ 3 X x)]

/-- Extend the actual three-simplex contractions over an original four-simplex. -/
def threeFourSimplexHomotopy (smp : SingularSimplex X 4) : C(I × Simplex 4, X) :=
  extendCoherentSimplexHomotopy (stationarySimplexHomotopy 2)
    (HigherHurewicz.simplexStraighteningHomotopy 3 x)
    (HigherHurewicz.simplexStraighteningHomotopy_face 2 x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 3 x) smp

@[simp] theorem threeFourSimplexHomotopy_zero (smp : SingularSimplex X 4)
    (s : Simplex 4) : threeFourSimplexHomotopy x smp (0, s) = smp s :=
  extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

theorem threeFourSimplexHomotopy_face :
    FaceCompatibleHomotopies 3 (HigherHurewicz.simplexStraighteningHomotopy 3 x)
      (threeFourSimplexHomotopy x) :=
  extendCoherentSimplexHomotopy_face (stationarySimplexHomotopy 2)
    (HigherHurewicz.simplexStraighteningHomotopy 3 x)
    (HigherHurewicz.simplexStraighteningHomotopy_face 2 x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 3 x)

@[simp] theorem threeFourSimplexHomotopy_const :
    threeFourSimplexHomotopy x (ContinuousMap.const (Simplex 4) x) =
      ContinuousMap.const (I × Simplex 4) x :=
  ThirdHurewicz.extendCoherentSimplexHomotopy_const (stationarySimplexHomotopy 2)
    (HigherHurewicz.simplexStraighteningHomotopy 3 x)
    (HigherHurewicz.simplexStraighteningHomotopy_face 2 x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 3 x) x
    (HigherHurewicz.simplexStraighteningHomotopy_const 3 x)

/-- Extend that same compatible four-simplex family over an original five-simplex. -/
def threeFiveSimplexHomotopy (smp : SingularSimplex X 5) : C(I × Simplex 5, X) :=
  extendCoherentSimplexHomotopy (HigherHurewicz.simplexStraighteningHomotopy 3 x)
    (threeFourSimplexHomotopy x) (threeFourSimplexHomotopy_face x)
    (threeFourSimplexHomotopy_zero x) smp

@[simp] theorem threeFiveSimplexHomotopy_zero (smp : SingularSimplex X 5)
    (s : Simplex 5) : threeFiveSimplexHomotopy x smp (0, s) = smp s :=
  extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

theorem threeFiveSimplexHomotopy_face :
    FaceCompatibleHomotopies 4 (threeFourSimplexHomotopy x)
      (threeFiveSimplexHomotopy x) :=
  extendCoherentSimplexHomotopy_face (HigherHurewicz.simplexStraighteningHomotopy 3 x)
    (threeFourSimplexHomotopy x) (threeFourSimplexHomotopy_face x)
    (threeFourSimplexHomotopy_zero x)

@[simp] theorem threeFiveSimplexHomotopy_const :
    threeFiveSimplexHomotopy x (ContinuousMap.const (Simplex 5) x) =
      ContinuousMap.const (I × Simplex 5) x :=
  ThirdHurewicz.extendCoherentSimplexHomotopy_const
    (HigherHurewicz.simplexStraighteningHomotopy 3 x) (threeFourSimplexHomotopy x)
    (threeFourSimplexHomotopy_face x) (threeFourSimplexHomotopy_zero x) x
    (threeFourSimplexHomotopy_const x)

end Wikipedia.HopfProblem.FourthHurewicz
