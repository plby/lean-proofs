import Wikipedia.HopfProblem.ThirdHurewiczTriangleNullhomotopyInterpolation
import Wikipedia.HopfProblem.ThirdHurewiczTriangleNullhomotopyCube

/-!
# Actual based-triangle nullhomotopies from trivial native second homotopy

The triangle is first deformed, relative to its boundary, to its explicit
square round trip. Triviality of Mathlib's native second homotopy group
then supplies a genuine square nullhomotopy, which is pulled back along
the boundary-preserving return map. A literal constant triangle is assigned
the literal constant homotopy.

No simple-connectedness, extension property, Hurewicz isomorphism, or
higher-connectivity theorem is assumed in this construction.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X] {x : X} [Subsingleton (π_ 2 X x)]

/-- The constructed nullhomotopy before imposing the constant-input normalization. -/
def triangleNullHomotopyUnnormalized (τ : BasedTriangle x) :
    τ.val.HomotopyRel (ContinuousMap.const (Simplex 2) x) triangleBoundary :=
  ContinuousMap.HomotopyRel.trans (triangleReturnHomotopy τ)
    (nativeSquareNullHomotopy_comp (basedTriangleLoop τ) triangleCubicalReturn
      triangleBoundary (fun _ hs => triangleCubicalReturn_boundary _ hs))

/-- A genuine relative nullhomotopy of the actual triangle, normalized
to be stationary on the literal constant triangle. -/
def triangleNullHomotopy (τ : BasedTriangle x) :
    τ.val.HomotopyRel (ContinuousMap.const (Simplex 2) x) triangleBoundary := by
  classical
  exact if h : τ = constantBasedTriangle x then
    ContinuousMap.HomotopyRel.cast
      (ContinuousMap.HomotopyRel.refl (ContinuousMap.const (Simplex 2) x) triangleBoundary)
      (congrArg (fun υ : BasedTriangle x => υ.val) h).symm rfl
  else triangleNullHomotopyUnnormalized τ

@[simp] theorem triangleNullHomotopy_zero (τ : BasedTriangle x) (s : Simplex 2) :
    triangleNullHomotopy τ (0, s) = τ.val s :=
  (triangleNullHomotopy τ).apply_zero s

@[simp] theorem triangleNullHomotopy_one (τ : BasedTriangle x) (s : Simplex 2) :
    triangleNullHomotopy τ (1, s) = x :=
  (triangleNullHomotopy τ).apply_one s

/-- Every point of the whole original boundary stays at the base point. -/
theorem triangleNullHomotopy_boundary (τ : BasedTriangle x) (t : I) (s : Simplex 2)
    (hs : s ∈ triangleBoundary) : triangleNullHomotopy τ (t, s) = x :=
  (triangleNullHomotopy τ).eq_snd t hs

@[simp] theorem triangleNullHomotopy_constant (x : X) [Subsingleton (π_ 2 X x)] :
    triangleNullHomotopy (constantBasedTriangle x) =
      ContinuousMap.HomotopyRel.refl (ContinuousMap.const (Simplex 2) x) triangleBoundary := by
  classical
  unfold triangleNullHomotopy
  rw [dif_pos rfl]
  rfl

@[simp] theorem triangleNullHomotopy_constant_toContinuousMap (x : X)
    [Subsingleton (π_ 2 X x)] :
    (triangleNullHomotopy (constantBasedTriangle x)).toContinuousMap =
      ContinuousMap.const (I × Simplex 2) x := by
  rw [triangleNullHomotopy_constant]
  rfl

/-- Equality of the underlying triangle with the constant map also gives
literal stationarity; proof fields do not affect the construction. -/
theorem triangleNullHomotopy_stationary_of_val_eq_const (τ : BasedTriangle x)
    (hτ : τ.val = ContinuousMap.const (Simplex 2) x) :
    (triangleNullHomotopy τ).toContinuousMap = ContinuousMap.const (I × Simplex 2) x := by
  have h : τ = constantBasedTriangle x := Subtype.ext hτ
  rw [h, triangleNullHomotopy_constant_toContinuousMap]

end Wikipedia.HopfProblem.ThirdHurewicz
