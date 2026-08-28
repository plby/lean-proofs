import Wikipedia.HopfProblem.FifthHurewiczNormalization

/-!
# Extending the actual lower-dimensional normalization through degree seven

The degree-five construction already supplies compatible homotopies on
five- and six-simplices. The proved simplex-cylinder extension gives
their degree-seven companion, retaining the original face maps and
literal constant-input stationarity.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SixthHurewicz

open FirstHurewicz SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
  [Subsingleton (π_ 4 X x)]

/-- The genuine degree-seven extension of the already constructed lower stages. -/
def lowerSevenSimplexHomotopy (smp : SingularSimplex X 7) : C(I × Simplex 7, X) :=
  extendCoherentSimplexHomotopy (FifthHurewicz.normalizationFiveSimplexHomotopy x)
    (FifthHurewicz.normalizationSixSimplexHomotopy x)
    (FifthHurewicz.normalizationSixHomotopy_face x)
    (FifthHurewicz.normalizationSixSimplexHomotopy_zero x) smp

@[simp] theorem lowerSevenSimplexHomotopy_zero (smp : SingularSimplex X 7)
    (s : Simplex 7) : lowerSevenSimplexHomotopy x smp (0, s) = smp s :=
  extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

theorem lowerSevenSimplexHomotopy_face :
    FaceCompatibleHomotopies 6 (FifthHurewicz.normalizationSixSimplexHomotopy x)
      (lowerSevenSimplexHomotopy x) :=
  extendCoherentSimplexHomotopy_face (FifthHurewicz.normalizationFiveSimplexHomotopy x)
    (FifthHurewicz.normalizationSixSimplexHomotopy x)
    (FifthHurewicz.normalizationSixHomotopy_face x)
    (FifthHurewicz.normalizationSixSimplexHomotopy_zero x)

@[simp] theorem lowerSevenSimplexHomotopy_const :
    lowerSevenSimplexHomotopy x (ContinuousMap.const (Simplex 7) x) =
      ContinuousMap.const (I × Simplex 7) x :=
  ThirdHurewicz.extendCoherentSimplexHomotopy_const
    (FifthHurewicz.normalizationFiveSimplexHomotopy x)
    (FifthHurewicz.normalizationSixSimplexHomotopy x)
    (FifthHurewicz.normalizationSixHomotopy_face x)
    (FifthHurewicz.normalizationSixSimplexHomotopy_zero x) x
    (FifthHurewicz.normalizationSixSimplexHomotopy_const x)

end Wikipedia.HopfProblem.SixthHurewicz
