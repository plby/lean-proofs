import Wikipedia.HopfProblem.FourthHurewiczNormalizationHomotopies
import Wikipedia.HopfProblem.FourthHurewiczLowerNormalizationMaps
import Wikipedia.HopfProblem.FourthHurewiczFourSimplexBasic
import Wikipedia.HopfProblem.HigherHurewiczSimplexEndpointBoundary

/-!
# Actual whole-boundary normalization of four-simplices

The complete geometric homotopy ends at an actual based four-simplex.
Its degree-five companion restricts to these very same endpoints on all
six original faces. The construction uses only the proved lower stages
and triviality of the original native second and third homotopy groups.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.FourthHurewicz

open FirstHurewicz SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]

/-- The actual terminal four-simplex, based on its entire original boundary. -/
def normalizedFourSimplex (smp : SingularSimplex X 4) : BasedFourSimplex x :=
  ⟨timeSlice (normalizationFourSimplexHomotopy x smp) 1,
    HigherHurewicz.simplexEndpoint_boundary (normalizationThreeSimplexHomotopy x)
      (normalizationFourSimplexHomotopy x) (normalizationHomotopy_face x) x
      (normalizationThreeSimplexHomotopy_endpoint x) smp⟩

@[simp] theorem normalizedFourSimplex_val (smp : SingularSimplex X 4) :
    (normalizedFourSimplex x smp).val =
      timeSlice (normalizationFourSimplexHomotopy x smp) 1 := rfl

theorem normalizationFourSimplexHomotopy_endpoint (smp : SingularSimplex X 4) :
    timeSlice (normalizationFourSimplexHomotopy x smp) 1 =
      (normalizedFourSimplex x smp).val := rfl

/-- This endpoint runs the genuine third-homotopy contraction after the lower stages. -/
theorem normalizedFourSimplex_val_stages (smp : SingularSimplex X 4) :
    (normalizedFourSimplex x smp).val =
      timeSlice (threeFourSimplexHomotopy x (lowerNormalizedFourSimplexMap x smp)) 1 := by
  rw [normalizedFourSimplex_val, normalizationFourSimplexHomotopy,
    ThirdHurewicz.timeSlice_composeSimplexHomotopies_one]
  rfl

@[simp] theorem normalizedFourSimplex_const :
    normalizedFourSimplex x (ContinuousMap.const (Simplex 4) x) =
      constantBasedFourSimplex x := by
  apply Subtype.ext
  rw [normalizedFourSimplex_val, normalizationFourSimplexHomotopy_const]
  rfl

/-- The actual degree-five endpoint of the same coherent geometric homotopy. -/
def normalizedFiveSimplexMap (smp : SingularSimplex X 5) : SingularSimplex X 5 :=
  timeSlice (normalizationFiveSimplexHomotopy x smp) 1

/-- Every terminal five-simplex face is the normalized original face, literally. -/
theorem normalizedFiveSimplexMap_face (smp : SingularSimplex X 5) (i : Fin 6) :
    (normalizedFiveSimplexMap x smp).comp (simplexFace 4 i) =
      (normalizedFourSimplex x (smp.comp (simplexFace 4 i))).val :=
  timeSlice_face (normalizationFiveHomotopy_face x) smp i 1

theorem normalizedFiveSimplexMap_face_boundary (smp : SingularSimplex X 5)
    (i : Fin 6) (s : Simplex 4) (hs : s ∈ fourSimplexBoundary) :
    normalizedFiveSimplexMap x smp (simplexFace 4 i s) = x := by
  have hf := congrArg (fun f : C(Simplex 4, X) => f s)
    (normalizedFiveSimplexMap_face x smp i)
  exact hf.trans ((normalizedFourSimplex x (smp.comp (simplexFace 4 i))).property s hs)

@[simp] theorem normalizedFiveSimplexMap_const :
    normalizedFiveSimplexMap x (ContinuousMap.const (Simplex 5) x) =
      ContinuousMap.const (Simplex 5) x := by
  unfold normalizedFiveSimplexMap
  rw [normalizationFiveSimplexHomotopy_const]
  rfl

end Wikipedia.HopfProblem.FourthHurewicz
