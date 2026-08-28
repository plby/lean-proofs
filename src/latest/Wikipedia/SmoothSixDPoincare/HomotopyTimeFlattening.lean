import Mathlib.Topology.Homotopy.Basic
import Mathlib.Tactic.Linarith

/-!
# Flattening a continuous homotopy near its endpoints

The piecewise-linear time change is continuous and constant on endpoint
collars. No smoothness of the original homotopy is required. The resulting
collars will be kept fixed by the relative smoothing theorem.
-/

noncomputable section

open Set ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.ManifoldSmoothing

/-- A continuous time change, zero up to one third and one after two thirds. -/
def flattenTime (t : unitInterval) : unitInterval :=
  ⟨max 0 (min 1 (3 * (t : ℝ) - 1)), le_max_left _ _,
    max_le zero_le_one (min_le_left _ _)⟩

theorem continuous_flattenTime : Continuous flattenTime :=
  (continuous_const.max
    (continuous_const.min ((continuous_const.mul continuous_subtype_val).sub continuous_const)))
    |>.subtype_mk _

theorem flattenTime_eq_zero (t : unitInterval) (ht : (t : ℝ) ≤ 1 / 3) : flattenTime t = 0 := by
  apply Subtype.ext
  change max 0 (min 1 (3 * (t : ℝ) - 1)) = 0
  exact max_eq_left ((min_le_right _ _).trans (by linarith))

theorem flattenTime_eq_one (t : unitInterval) (ht : 2 / 3 ≤ (t : ℝ)) : flattenTime t = 1 := by
  apply Subtype.ext
  change max 0 (min 1 (3 * (t : ℝ) - 1)) = 1
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

variable {X N : Type*} [TopologicalSpace X] [TopologicalSpace N]
  {f g : C(X, N)} (H : f.Homotopy g)

/-- The original homotopy after the explicit time change. -/
def flattenedHomotopyMap : C(unitInterval × X, N) where
  toFun q := H (flattenTime q.1, q.2)
  continuous_toFun := H.continuous.comp
    ((continuous_flattenTime.comp continuous_fst).prodMk continuous_snd)

theorem flattenedHomotopyMap_lower (t : unitInterval) (x : X) (ht : (t : ℝ) ≤ 1 / 3) :
    flattenedHomotopyMap H (t, x) = f x := by
  change H (flattenTime t, x) = f x
  rw [flattenTime_eq_zero t ht, H.apply_zero]

theorem flattenedHomotopyMap_upper (t : unitInterval) (x : X) (ht : 2 / 3 ≤ (t : ℝ)) :
    flattenedHomotopyMap H (t, x) = g x := by
  change H (flattenTime t, x) = g x
  rw [flattenTime_eq_one t ht, H.apply_one]

variable (X) in
/-- The closed endpoint collars to remain fixed in the smoothing. -/
def homotopyCollars : Set (unitInterval × X) :=
  {q | (q.1 : ℝ) ≤ 1 / 4 ∨ 3 / 4 ≤ (q.1 : ℝ)}

variable (X) in
/-- A larger open neighborhood on which the flattened homotopy already equals its endpoints. -/
def homotopyCollarNeighborhood : Set (unitInterval × X) :=
  {q | (q.1 : ℝ) < 1 / 3 ∨ 2 / 3 < (q.1 : ℝ)}

theorem isClosed_homotopyCollars : IsClosed (homotopyCollars X) :=
  (isClosed_le (continuous_subtype_val.comp continuous_fst) continuous_const).union
    (isClosed_le continuous_const (continuous_subtype_val.comp continuous_fst))

theorem isOpen_homotopyCollarNeighborhood : IsOpen (homotopyCollarNeighborhood X) :=
  (isOpen_lt (continuous_subtype_val.comp continuous_fst) continuous_const).union
    (isOpen_lt continuous_const (continuous_subtype_val.comp continuous_fst))

omit [TopologicalSpace X] in
theorem homotopyCollars_subset : homotopyCollars X ⊆ homotopyCollarNeighborhood X := by
  rintro q (hl | hu)
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

end Wikipedia.SmoothSixDPoincare.ManifoldSmoothing
