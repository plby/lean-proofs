import Wikipedia.HopfProblem.SixthHurewiczNormalizationHomotopies
import Wikipedia.HopfProblem.SixthHurewiczSixSimplexBasic
import Wikipedia.HopfProblem.HigherHurewiczSimplexEndpointBoundary

/-!
# Actual whole-boundary normalization of six-simplices

The complete geometric homotopy ends at an actual based six-simplex.
The seven-dimensional companion restricts to exactly these normalized
original faces. Only actual simple connectedness and trivial native
second through fifth homotopy at the base point are used.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SixthHurewicz

open FirstHurewicz SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
  [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)]

/-- The actual terminal six-simplex, based on its entire original boundary. -/
def normalizedSixSimplex (smp : SingularSimplex X 6) : BasedSixSimplex x :=
  ⟨timeSlice (normalizationSixSimplexHomotopy x smp) 1,
    HigherHurewicz.simplexEndpoint_boundary (normalizationFiveSimplexHomotopy x)
      (normalizationSixSimplexHomotopy x) (normalizationHomotopy_face x) x
      (normalizationFiveSimplexHomotopy_endpoint x) smp⟩

@[simp] theorem normalizedSixSimplex_val (smp : SingularSimplex X 6) :
    (normalizedSixSimplex x smp).val =
      timeSlice (normalizationSixSimplexHomotopy x smp) 1 := rfl

theorem normalizationSixSimplexHomotopy_endpoint (smp : SingularSimplex X 6) :
    timeSlice (normalizationSixSimplexHomotopy x smp) 1 =
      (normalizedSixSimplex x smp).val := rfl

@[simp] theorem normalizedSixSimplex_const :
    normalizedSixSimplex x (ContinuousMap.const (Simplex 6) x) =
      constantBasedSixSimplex x := by
  apply Subtype.ext
  rw [normalizedSixSimplex_val, normalizationSixSimplexHomotopy_const]
  rfl

/-- The actual degree-seven endpoint of the complete coherent homotopy. -/
def normalizedSevenSimplexMap (smp : SingularSimplex X 7) : SingularSimplex X 7 :=
  timeSlice (normalizationSevenSimplexHomotopy x smp) 1

/-- Every terminal seven-simplex face is the normalized original face, literally. -/
theorem normalizedSevenSimplexMap_face (smp : SingularSimplex X 7) (i : Fin 8) :
    (normalizedSevenSimplexMap x smp).comp (simplexFace 6 i) =
      (normalizedSixSimplex x (smp.comp (simplexFace 6 i))).val :=
  timeSlice_face (normalizationSevenHomotopy_face x) smp i 1

theorem normalizedSevenSimplexMap_face_boundary (smp : SingularSimplex X 7)
    (i : Fin 8) (s : Simplex 6) (hs : s ∈ sixSimplexBoundary) :
    normalizedSevenSimplexMap x smp (simplexFace 6 i s) = x := by
  have hf := congrArg (fun f : C(Simplex 6, X) => f s)
    (normalizedSevenSimplexMap_face x smp i)
  exact hf.trans ((normalizedSixSimplex x (smp.comp (simplexFace 6 i))).property s hs)

@[simp] theorem normalizedSevenSimplexMap_const :
    normalizedSevenSimplexMap x (ContinuousMap.const (Simplex 7) x) =
      ContinuousMap.const (Simplex 7) x := by
  unfold normalizedSevenSimplexMap
  rw [normalizationSevenSimplexHomotopy_const]
  rfl

end Wikipedia.HopfProblem.SixthHurewicz
