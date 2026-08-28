import Wikipedia.HopfProblem.HigherHurewiczSimplexNullhomotopy
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedEdgeBasic

/-!
# Genuine simplex contraction families from native homotopy vanishing

In each dimension, the proved relative nullhomotopy contracts every
whole-boundary-based simplex. Other simplices remain stationary. This
total family fixes every original boundary point and is therefore exactly
compatible with stationary homotopies on the lower-dimensional faces.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz

open FirstHurewicz SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X]

/-- Contract actual based simplices using native homotopy vanishing, fixing other inputs. -/
def simplexStraighteningHomotopy (n : ℕ) (x : X) [Subsingleton (π_ n X x)]
    (smp : SingularSimplex X n) : C(I × Simplex n, X) := by
  classical
  exact if h : ∀ s ∈ simplexBoundary n, smp s = x then
    (simplexNullHomotopy (⟨smp, h⟩ : BasedSimplex n x)).toContinuousMap
  else stationarySimplexHomotopy n smp

variable (n : ℕ) (x : X) [Subsingleton (π_ n X x)]

@[simp] theorem simplexStraighteningHomotopy_zero (smp : SingularSimplex X n)
    (s : Simplex n) : simplexStraighteningHomotopy n x smp (0, s) = smp s := by
  classical
  unfold simplexStraighteningHomotopy
  split
  · rename_i h
    exact simplexNullHomotopy_zero (⟨smp, h⟩ : BasedSimplex n x) s
  · rfl

/-- Every based simplex is genuinely contracted over its full interior. -/
theorem simplexStraighteningHomotopy_one (smp : SingularSimplex X n)
    (h : ∀ s ∈ simplexBoundary n, smp s = x) (s : Simplex n) :
    simplexStraighteningHomotopy n x smp (1, s) = x := by
  classical
  rw [simplexStraighteningHomotopy, dif_pos h]
  exact simplexNullHomotopy_one (⟨smp, h⟩ : BasedSimplex n x) s

/-- Each original boundary point stays fixed, whether its value is the base point or not. -/
theorem simplexStraighteningHomotopy_boundary (smp : SingularSimplex X n)
    (r : I) (s : Simplex n) (hs : s ∈ simplexBoundary n) :
    simplexStraighteningHomotopy n x smp (r, s) = smp s := by
  classical
  unfold simplexStraighteningHomotopy
  split
  · rename_i h
    exact (simplexNullHomotopy (⟨smp, h⟩ : BasedSimplex n x)).eq_fst r hs
  · rfl

@[simp] theorem simplexStraighteningHomotopy_const :
    simplexStraighteningHomotopy n x (ContinuousMap.const (Simplex n) x) =
      ContinuousMap.const (I × Simplex n) x := by
  classical
  have h : ∀ s ∈ simplexBoundary n, (ContinuousMap.const (Simplex n) x) s = x :=
    fun _ _ => rfl
  rw [simplexStraighteningHomotopy, dif_pos h]
  exact simplexNullHomotopy_constant_toContinuousMap n x

@[simp] theorem simplexStraighteningHomotopy_timeSlice_zero (smp : SingularSimplex X n) :
    timeSlice (simplexStraighteningHomotopy n x smp) 0 = smp := by
  ext s
  exact simplexStraighteningHomotopy_zero n x smp s

omit [Subsingleton (π_ n X x)] in
/-- Relative boundary fixing gives literal compatibility with every actual simplex face. -/
theorem simplexStraighteningHomotopy_face [Subsingleton (π_ (n + 1) X x)] :
    FaceCompatibleHomotopies n (stationarySimplexHomotopy n)
      (simplexStraighteningHomotopy (n + 1) x) := by
  intro smp i
  ext u
  change simplexStraighteningHomotopy (n + 1) x smp (u.1, simplexFace n i u.2) =
    smp (simplexFace n i u.2)
  exact simplexStraighteningHomotopy_boundary (n + 1) x smp u.1 _
    ⟨i, simplexFace_apply_self n i u.2⟩

end Wikipedia.HopfProblem.HigherHurewicz
