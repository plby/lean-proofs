import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.NormalizationHomotopies
import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.SevenSimplexBasic
import Wikipedia.HopfProblem.HigherHurewiczSimplexEndpointBoundary

/-!
# Actual whole-boundary normalization of seven-simplices

The complete geometric homotopy ends at an actual based seven-simplex.
The eight-dimensional companion restricts to exactly these normalized
original faces. Only actual simple connectedness and trivial native
second through sixth homotopy at the base point are used.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz

open Wikipedia.HopfProblem

open FirstHurewicz SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
  [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] [Subsingleton (π_ 6 X x)]

/-- The actual terminal seven-simplex, based on its entire original boundary. -/
def normalizedSevenSimplex (smp : SingularSimplex X 7) : BasedSevenSimplex x :=
  ⟨timeSlice (normalizationSevenSimplexHomotopy x smp) 1,
    HigherHurewicz.simplexEndpoint_boundary (normalizationSixSimplexHomotopy x)
      (normalizationSevenSimplexHomotopy x) (normalizationHomotopy_face x) x
      (normalizationSixSimplexHomotopy_endpoint x) smp⟩

@[simp] theorem normalizedSevenSimplex_val (smp : SingularSimplex X 7) :
    (normalizedSevenSimplex x smp).val =
      timeSlice (normalizationSevenSimplexHomotopy x smp) 1 := rfl

theorem normalizationSevenSimplexHomotopy_endpoint (smp : SingularSimplex X 7) :
    timeSlice (normalizationSevenSimplexHomotopy x smp) 1 =
      (normalizedSevenSimplex x smp).val := rfl

@[simp] theorem normalizedSevenSimplex_const :
    normalizedSevenSimplex x (ContinuousMap.const (Simplex 7) x) =
      constantBasedSevenSimplex x := by
  apply Subtype.ext
  rw [normalizedSevenSimplex_val, normalizationSevenSimplexHomotopy_const]
  rfl

/-- The actual degree-eight endpoint of the complete coherent homotopy. -/
def normalizedEightSimplexMap (smp : SingularSimplex X 8) : SingularSimplex X 8 :=
  timeSlice (normalizationEightSimplexHomotopy x smp) 1

/-- Every terminal eight-simplex face is the normalized original face, literally. -/
theorem normalizedEightSimplexMap_face (smp : SingularSimplex X 8) (i : Fin 9) :
    (normalizedEightSimplexMap x smp).comp (simplexFace 7 i) =
      (normalizedSevenSimplex x (smp.comp (simplexFace 7 i))).val :=
  timeSlice_face (normalizationEightHomotopy_face x) smp i 1

theorem normalizedEightSimplexMap_face_boundary (smp : SingularSimplex X 8)
    (i : Fin 9) (s : Simplex 7) (hs : s ∈ sevenSimplexBoundary) :
    normalizedEightSimplexMap x smp (simplexFace 7 i s) = x := by
  have hf := congrArg (fun f : C(Simplex 7, X) => f s)
    (normalizedEightSimplexMap_face x smp i)
  exact hf.trans ((normalizedSevenSimplex x (smp.comp (simplexFace 7 i))).property s hs)

@[simp] theorem normalizedEightSimplexMap_const :
    normalizedEightSimplexMap x (ContinuousMap.const (Simplex 8) x) =
      ContinuousMap.const (Simplex 8) x := by
  unfold normalizedEightSimplexMap
  rw [normalizationEightSimplexHomotopy_const]
  rfl

end Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz
