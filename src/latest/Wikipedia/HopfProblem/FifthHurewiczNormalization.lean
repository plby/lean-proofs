import Wikipedia.HopfProblem.FifthHurewiczNormalizationHomotopies
import Wikipedia.HopfProblem.FifthHurewiczFiveSimplexBasic
import Wikipedia.HopfProblem.HigherHurewiczSimplexEndpointBoundary

/-!
# Actual whole-boundary normalization of five-simplices

The complete geometric homotopy ends at an actual based five-simplex.
The six-dimensional companion restricts to exactly these normalized
original faces. Only actual simple connectedness and trivial native
second, third, and fourth homotopy at the base point are used.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.FifthHurewicz

open FirstHurewicz SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
  [Subsingleton (π_ 4 X x)]

/-- The actual terminal five-simplex, based on its entire original boundary. -/
def normalizedFiveSimplex (smp : SingularSimplex X 5) : BasedFiveSimplex x :=
  ⟨timeSlice (normalizationFiveSimplexHomotopy x smp) 1,
    HigherHurewicz.simplexEndpoint_boundary (normalizationFourSimplexHomotopy x)
      (normalizationFiveSimplexHomotopy x) (normalizationHomotopy_face x) x
      (normalizationFourSimplexHomotopy_endpoint x) smp⟩

@[simp] theorem normalizedFiveSimplex_val (smp : SingularSimplex X 5) :
    (normalizedFiveSimplex x smp).val =
      timeSlice (normalizationFiveSimplexHomotopy x smp) 1 := rfl

theorem normalizationFiveSimplexHomotopy_endpoint (smp : SingularSimplex X 5) :
    timeSlice (normalizationFiveSimplexHomotopy x smp) 1 =
      (normalizedFiveSimplex x smp).val := rfl

@[simp] theorem normalizedFiveSimplex_const :
    normalizedFiveSimplex x (ContinuousMap.const (Simplex 5) x) =
      constantBasedFiveSimplex x := by
  apply Subtype.ext
  rw [normalizedFiveSimplex_val, normalizationFiveSimplexHomotopy_const]
  rfl

/-- The actual degree-six endpoint of the complete coherent homotopy. -/
def normalizedSixSimplexMap (smp : SingularSimplex X 6) : SingularSimplex X 6 :=
  timeSlice (normalizationSixSimplexHomotopy x smp) 1

/-- Every terminal six-simplex face is the normalized original face, literally. -/
theorem normalizedSixSimplexMap_face (smp : SingularSimplex X 6) (i : Fin 7) :
    (normalizedSixSimplexMap x smp).comp (simplexFace 5 i) =
      (normalizedFiveSimplex x (smp.comp (simplexFace 5 i))).val :=
  timeSlice_face (normalizationSixHomotopy_face x) smp i 1

theorem normalizedSixSimplexMap_face_boundary (smp : SingularSimplex X 6)
    (i : Fin 7) (s : Simplex 5) (hs : s ∈ fiveSimplexBoundary) :
    normalizedSixSimplexMap x smp (simplexFace 5 i s) = x := by
  have hf := congrArg (fun f : C(Simplex 5, X) => f s)
    (normalizedSixSimplexMap_face x smp i)
  exact hf.trans ((normalizedFiveSimplex x (smp.comp (simplexFace 5 i))).property s hs)

@[simp] theorem normalizedSixSimplexMap_const :
    normalizedSixSimplexMap x (ContinuousMap.const (Simplex 6) x) =
      ContinuousMap.const (Simplex 6) x := by
  unfold normalizedSixSimplexMap
  rw [normalizationSixSimplexHomotopy_const]
  rfl

end Wikipedia.HopfProblem.FifthHurewicz
