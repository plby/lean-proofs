import Wikipedia.HopfProblem.ThirdHurewiczTriangleNullhomotopy
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedEdgeBasic

/-!
# Boundary-fixed contraction of singular triangles

Triviality of the actual native second homotopy group supplies a genuine
relative nullhomotopy of a whole-boundary-based singular triangle. Other
triangles are kept stationary. This total family therefore fixes every
original edge and is literally compatible with all singular face maps.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)]

/-- An actual total triangle homotopy, contracting exactly the triangles
whose whole boundary is already at the chosen base point. -/
def triangleStraighteningHomotopy (smp : SingularSimplex X 2) : C(I × Simplex 2, X) := by
  classical
  exact if h : ∀ s ∈ triangleBoundary, smp s = x then
    (triangleNullHomotopy (⟨smp, h⟩ : BasedTriangle x)).toContinuousMap
  else stationarySimplexHomotopy 2 smp

@[simp] theorem triangleStraighteningHomotopy_zero (smp : SingularSimplex X 2)
    (s : Simplex 2) : triangleStraighteningHomotopy x smp (0, s) = smp s := by
  classical
  unfold triangleStraighteningHomotopy
  split
  · rename_i h
    exact triangleNullHomotopy_zero (⟨smp, h⟩ : BasedTriangle x) s
  · rfl

theorem triangleStraighteningHomotopy_one (smp : SingularSimplex X 2)
    (h : ∀ s ∈ triangleBoundary, smp s = x) (s : Simplex 2) :
    triangleStraighteningHomotopy x smp (1, s) = x := by
  classical
  rw [triangleStraighteningHomotopy, dif_pos h]
  exact triangleNullHomotopy_one (⟨smp, h⟩ : BasedTriangle x) s

/-- Every original boundary point stays fixed, whether or not it is based. -/
theorem triangleStraighteningHomotopy_boundary (smp : SingularSimplex X 2)
    (r : I) (s : Simplex 2) (hs : s ∈ triangleBoundary) :
    triangleStraighteningHomotopy x smp (r, s) = smp s := by
  classical
  unfold triangleStraighteningHomotopy
  split
  · rename_i h
    exact (triangleNullHomotopy (⟨smp, h⟩ : BasedTriangle x)).eq_fst r hs
  · rfl

@[simp] theorem triangleStraighteningHomotopy_const :
    triangleStraighteningHomotopy x (ContinuousMap.const (Simplex 2) x) =
      ContinuousMap.const (I × Simplex 2) x := by
  classical
  have h : ∀ s ∈ triangleBoundary, (ContinuousMap.const (Simplex 2) x) s = x :=
    fun _ _ => rfl
  rw [triangleStraighteningHomotopy, dif_pos h]
  exact triangleNullHomotopy_constant_toContinuousMap x

/-- Boundary fixing is exact compatibility with the stationary edge homotopies. -/
theorem triangleStraighteningHomotopy_face :
    FaceCompatibleHomotopies 1 (stationarySimplexHomotopy 1)
      (triangleStraighteningHomotopy x) := by
  intro smp i
  ext u
  change triangleStraighteningHomotopy x smp (u.1, simplexFace 1 i u.2) =
    smp (simplexFace 1 i u.2)
  exact triangleStraighteningHomotopy_boundary x smp u.1 _
    ⟨i, simplexFace_apply_self 1 i u.2⟩

@[simp] theorem triangleStraighteningHomotopy_timeSlice_zero (smp : SingularSimplex X 2) :
    timeSlice (triangleStraighteningHomotopy x smp) 0 = smp := by
  ext s
  exact triangleStraighteningHomotopy_zero x smp s

end Wikipedia.HopfProblem.ThirdHurewicz
