import Wikipedia.HopfProblem.ThirdHurewiczTriangleNormalizationBasic
import Wikipedia.HopfProblem.ThirdHurewiczCoherentHomotopyConstants
import Wikipedia.HopfProblem.ThirdHurewiczThreeSimplexBasic

/-!
# Coherent triangle contraction through dimension four

Actual boundary-fixed triangle nullhomotopies extend over three- and
four-simplices by the proved simplex-cylinder retraction. The resulting
families retain exact face compatibility and constant-input stationarity.
Only trivial native second homotopy is used to construct this stage.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)]

/-- The genuine extension of the triangle-contraction stage over a three-simplex. -/
def triangleThreeSimplexHomotopy (smp : SingularSimplex X 3) : C(I × Simplex 3, X) :=
  extendCoherentSimplexHomotopy (stationarySimplexHomotopy 1)
    (triangleStraighteningHomotopy x) (triangleStraighteningHomotopy_face x)
    (triangleStraighteningHomotopy_zero x) smp

@[simp] theorem triangleThreeSimplexHomotopy_zero (smp : SingularSimplex X 3)
    (s : Simplex 3) : triangleThreeSimplexHomotopy x smp (0, s) = smp s :=
  extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

theorem triangleThreeSimplexHomotopy_face :
    FaceCompatibleHomotopies 2 (triangleStraighteningHomotopy x)
      (triangleThreeSimplexHomotopy x) :=
  extendCoherentSimplexHomotopy_face (stationarySimplexHomotopy 1)
    (triangleStraighteningHomotopy x) (triangleStraighteningHomotopy_face x)
    (triangleStraighteningHomotopy_zero x)

@[simp] theorem triangleThreeSimplexHomotopy_const :
    triangleThreeSimplexHomotopy x (ContinuousMap.const (Simplex 3) x) =
      ContinuousMap.const (I × Simplex 3) x :=
  extendCoherentSimplexHomotopy_const (stationarySimplexHomotopy 1)
    (triangleStraighteningHomotopy x) (triangleStraighteningHomotopy_face x)
    (triangleStraighteningHomotopy_zero x) x (triangleStraighteningHomotopy_const x)

/-- Extending the coherent three-simplex homotopies over actual four-simplices. -/
def triangleFourSimplexHomotopy (smp : SingularSimplex X 4) : C(I × Simplex 4, X) :=
  extendCoherentSimplexHomotopy (triangleStraighteningHomotopy x)
    (triangleThreeSimplexHomotopy x) (triangleThreeSimplexHomotopy_face x)
    (triangleThreeSimplexHomotopy_zero x) smp

@[simp] theorem triangleFourSimplexHomotopy_zero (smp : SingularSimplex X 4)
    (s : Simplex 4) : triangleFourSimplexHomotopy x smp (0, s) = smp s :=
  extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

theorem triangleFourSimplexHomotopy_face :
    FaceCompatibleHomotopies 3 (triangleThreeSimplexHomotopy x)
      (triangleFourSimplexHomotopy x) :=
  extendCoherentSimplexHomotopy_face (triangleStraighteningHomotopy x)
    (triangleThreeSimplexHomotopy x) (triangleThreeSimplexHomotopy_face x)
    (triangleThreeSimplexHomotopy_zero x)

@[simp] theorem triangleFourSimplexHomotopy_const :
    triangleFourSimplexHomotopy x (ContinuousMap.const (Simplex 4) x) =
      ContinuousMap.const (I × Simplex 4) x :=
  extendCoherentSimplexHomotopy_const (triangleStraighteningHomotopy x)
    (triangleThreeSimplexHomotopy x) (triangleThreeSimplexHomotopy_face x)
    (triangleThreeSimplexHomotopy_zero x) x (triangleThreeSimplexHomotopy_const x)

/-- If the original two-dimensional faces have based boundaries, their
terminal maps are constant on each entire face. -/
theorem triangleThreeSimplexHomotopy_one_face (smp : SingularSimplex X 3)
    (h : ∀ i : Fin 4, ∀ s ∈ triangleBoundary, (smp.comp (simplexFace 2 i)) s = x)
    (i : Fin 4) :
    (timeSlice (triangleThreeSimplexHomotopy x smp) 1).comp (simplexFace 2 i) =
      ContinuousMap.const (Simplex 2) x := by
  rw [timeSlice_face (triangleThreeSimplexHomotopy_face x)]
  ext s
  exact triangleStraighteningHomotopy_one x (smp.comp (simplexFace 2 i)) (h i) s

theorem triangleThreeSimplexHomotopy_one_boundary (smp : SingularSimplex X 3)
    (h : ∀ i : Fin 4, ∀ s ∈ triangleBoundary, (smp.comp (simplexFace 2 i)) s = x)
    (s : Simplex 3) (hs : s ∈ threeSimplexBoundary) :
    timeSlice (triangleThreeSimplexHomotopy x smp) 1 s = x := by
  obtain ⟨i, t, ht⟩ := simplexBoundary_exists_face 2 (⟨s, hs⟩ : SimplexBoundary 3)
  have he : simplexFace 2 i t = s := congrArg Subtype.val ht
  rw [← he]
  exact congrArg (fun f : C(Simplex 2, X) => f t)
    (triangleThreeSimplexHomotopy_one_face x smp h i)

/-- The endpoint as an actual whole-boundary-based three-simplex. -/
def triangleStraightenedThreeSimplex (smp : SingularSimplex X 3)
    (h : ∀ i : Fin 4, ∀ s ∈ triangleBoundary, (smp.comp (simplexFace 2 i)) s = x) :
    BasedThreeSimplex x :=
  ⟨timeSlice (triangleThreeSimplexHomotopy x smp) 1,
    triangleThreeSimplexHomotopy_one_boundary x smp h⟩

@[simp] theorem triangleStraightenedThreeSimplex_val (smp : SingularSimplex X 3)
    (h : ∀ i : Fin 4, ∀ s ∈ triangleBoundary, (smp.comp (simplexFace 2 i)) s = x) :
    (triangleStraightenedThreeSimplex x smp h).val =
      timeSlice (triangleThreeSimplexHomotopy x smp) 1 := rfl

end Wikipedia.HopfProblem.ThirdHurewicz
