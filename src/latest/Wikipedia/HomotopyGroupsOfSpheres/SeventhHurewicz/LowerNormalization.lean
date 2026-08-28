import Wikipedia.HopfProblem.SixthHurewiczNormalization

/-!
# Extending the actual lower-dimensional normalization through degree eight

The degree-six construction already supplies compatible homotopies on
six- and seven-simplices. The proved simplex-cylinder extension gives
their degree-eight companion, retaining the original face maps and
literal constant-input stationarity.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz

open Wikipedia.HopfProblem

open FirstHurewicz SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
  [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)]

/-- The genuine degree-eight extension of the already constructed lower stages. -/
def lowerEightSimplexHomotopy (smp : SingularSimplex X 8) : C(I × Simplex 8, X) :=
  extendCoherentSimplexHomotopy (SixthHurewicz.normalizationSixSimplexHomotopy x)
    (SixthHurewicz.normalizationSevenSimplexHomotopy x)
    (SixthHurewicz.normalizationSevenHomotopy_face x)
    (SixthHurewicz.normalizationSevenSimplexHomotopy_zero x) smp

@[simp] theorem lowerEightSimplexHomotopy_zero (smp : SingularSimplex X 8)
    (s : Simplex 8) : lowerEightSimplexHomotopy x smp (0, s) = smp s :=
  extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

theorem lowerEightSimplexHomotopy_face :
    FaceCompatibleHomotopies 7 (SixthHurewicz.normalizationSevenSimplexHomotopy x)
      (lowerEightSimplexHomotopy x) :=
  extendCoherentSimplexHomotopy_face (SixthHurewicz.normalizationSixSimplexHomotopy x)
    (SixthHurewicz.normalizationSevenSimplexHomotopy x)
    (SixthHurewicz.normalizationSevenHomotopy_face x)
    (SixthHurewicz.normalizationSevenSimplexHomotopy_zero x)

@[simp] theorem lowerEightSimplexHomotopy_const :
    lowerEightSimplexHomotopy x (ContinuousMap.const (Simplex 8) x) =
      ContinuousMap.const (I × Simplex 8) x :=
  ThirdHurewicz.extendCoherentSimplexHomotopy_const
    (SixthHurewicz.normalizationSixSimplexHomotopy x)
    (SixthHurewicz.normalizationSevenSimplexHomotopy x)
    (SixthHurewicz.normalizationSevenHomotopy_face x)
    (SixthHurewicz.normalizationSevenSimplexHomotopy_zero x) x
    (SixthHurewicz.normalizationSevenSimplexHomotopy_const x)

end Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz
