import Wikipedia.HopfProblem.FourthHurewiczLowerNormalization

/-!
# Actual endpoints of the coherent lower-dimensional normalization

The four-simplex endpoint has the already constructed based three-simplices
as its literal faces. The five-simplex endpoint restricts to those same
four-simplex maps, so the subsequent native third-homotopy contraction
can be attached coherently.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.FourthHurewicz

open FirstHurewicz SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)]

def lowerNormalizedFourSimplexMap (smp : SingularSimplex X 4) : SingularSimplex X 4 :=
  timeSlice (lowerFourSimplexHomotopy x smp) 1

theorem lowerNormalizedFourSimplexMap_face (smp : SingularSimplex X 4) (i : Fin 5) :
    (lowerNormalizedFourSimplexMap x smp).comp (simplexFace 3 i) =
      (ThirdHurewicz.normalizedThreeSimplex x (smp.comp (simplexFace 3 i))).val := by
  change (timeSlice (lowerFourSimplexHomotopy x smp) 1).comp (simplexFace 3 i) = _
  rw [timeSlice_face (lowerFourSimplexHomotopy_face x)]
  exact ThirdHurewicz.normalizationThreeSimplexHomotopy_endpoint x _

theorem lowerNormalizedFourSimplexMap_face_boundary (smp : SingularSimplex X 4)
    (i : Fin 5) (s : Simplex 3) (hs : s ∈ ThirdHurewicz.threeSimplexBoundary) :
    lowerNormalizedFourSimplexMap x smp (simplexFace 3 i s) = x := by
  have hf := congrArg (fun f : C(Simplex 3, X) => f s)
    (lowerNormalizedFourSimplexMap_face x smp i)
  exact hf.trans ((ThirdHurewicz.normalizedThreeSimplex x
    (smp.comp (simplexFace 3 i))).property s hs)

@[simp] theorem lowerNormalizedFourSimplexMap_const :
    lowerNormalizedFourSimplexMap x (ContinuousMap.const (Simplex 4) x) =
      ContinuousMap.const (Simplex 4) x := by
  unfold lowerNormalizedFourSimplexMap
  rw [lowerFourSimplexHomotopy_const]
  rfl

def lowerNormalizedFiveSimplexMap (smp : SingularSimplex X 5) : SingularSimplex X 5 :=
  timeSlice (lowerFiveSimplexHomotopy x smp) 1

theorem lowerNormalizedFiveSimplexMap_face (smp : SingularSimplex X 5) (i : Fin 6) :
    (lowerNormalizedFiveSimplexMap x smp).comp (simplexFace 4 i) =
      lowerNormalizedFourSimplexMap x (smp.comp (simplexFace 4 i)) :=
  timeSlice_face (lowerFiveSimplexHomotopy_face x) smp i 1

@[simp] theorem lowerNormalizedFiveSimplexMap_const :
    lowerNormalizedFiveSimplexMap x (ContinuousMap.const (Simplex 5) x) =
      ContinuousMap.const (Simplex 5) x := by
  unfold lowerNormalizedFiveSimplexMap
  rw [lowerFiveSimplexHomotopy_const]
  rfl

end Wikipedia.HopfProblem.FourthHurewicz
