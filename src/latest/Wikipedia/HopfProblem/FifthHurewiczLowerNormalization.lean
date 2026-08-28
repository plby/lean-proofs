import Wikipedia.HopfProblem.FourthHurewiczNormalization

/-!
# Extending the actual lower-dimensional normalization through degree six

The degree-four construction already supplies compatible homotopies on
four- and five-simplices. The proved simplex-cylinder extension gives
their degree-six companion, retaining the original face maps and
literal constant-input stationarity.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.FifthHurewicz

open FirstHurewicz SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]

/-- The genuine degree-six extension of the already constructed lower stages. -/
def lowerSixSimplexHomotopy (smp : SingularSimplex X 6) : C(I × Simplex 6, X) :=
  extendCoherentSimplexHomotopy (FourthHurewicz.normalizationFourSimplexHomotopy x)
    (FourthHurewicz.normalizationFiveSimplexHomotopy x)
    (FourthHurewicz.normalizationFiveHomotopy_face x)
    (FourthHurewicz.normalizationFiveSimplexHomotopy_zero x) smp

@[simp] theorem lowerSixSimplexHomotopy_zero (smp : SingularSimplex X 6)
    (s : Simplex 6) : lowerSixSimplexHomotopy x smp (0, s) = smp s :=
  extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

theorem lowerSixSimplexHomotopy_face :
    FaceCompatibleHomotopies 5 (FourthHurewicz.normalizationFiveSimplexHomotopy x)
      (lowerSixSimplexHomotopy x) :=
  extendCoherentSimplexHomotopy_face (FourthHurewicz.normalizationFourSimplexHomotopy x)
    (FourthHurewicz.normalizationFiveSimplexHomotopy x)
    (FourthHurewicz.normalizationFiveHomotopy_face x)
    (FourthHurewicz.normalizationFiveSimplexHomotopy_zero x)

@[simp] theorem lowerSixSimplexHomotopy_const :
    lowerSixSimplexHomotopy x (ContinuousMap.const (Simplex 6) x) =
      ContinuousMap.const (I × Simplex 6) x :=
  ThirdHurewicz.extendCoherentSimplexHomotopy_const
    (FourthHurewicz.normalizationFourSimplexHomotopy x)
    (FourthHurewicz.normalizationFiveSimplexHomotopy x)
    (FourthHurewicz.normalizationFiveHomotopy_face x)
    (FourthHurewicz.normalizationFiveSimplexHomotopy_zero x) x
    (FourthHurewicz.normalizationFiveSimplexHomotopy_const x)

end Wikipedia.HopfProblem.FifthHurewicz
