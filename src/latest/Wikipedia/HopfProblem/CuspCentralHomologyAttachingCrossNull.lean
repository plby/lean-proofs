import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCirclePoint

/-!
# Positive-degree singular homology maps of nullhomotopic attaching maps

A constant continuous map factors through the actual one-point space. Its
positive-degree integral singular homology map therefore vanishes. Actual
singular homotopy invariance gives the same conclusion for a nullhomotopic map.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspCentralHomology

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The actual singular homology map of a constant map vanishes in positive degree. -/
theorem singularHomologyMap_const_eq_zero (X : Type) [TopologicalSpace X]
    (y : Y) (n : ℕ) (hn : n ≠ 0) :
    singularHomologyMap (ContinuousMap.const X y) n = 0 := by
  let := point_homology_subsingleton n hn
  change singularHomologyMap
    ((ContinuousMap.const Unit y).comp (ContinuousMap.const X ())) n = 0
  rw [singularHomologyMap_comp]
  ext a
  change singularHomologyMap (ContinuousMap.const Unit y) n
    (singularHomologyMap (ContinuousMap.const X ()) n a) = 0
  rw [Subsingleton.elim
    (singularHomologyMap (ContinuousMap.const X ()) n a) (0 : SingularHomology Unit n),
    map_zero]

/-- A genuine nullhomotopy kills the actual singular homology map in every
nonzero degree. -/
theorem singularHomologyMap_eq_zero_of_nullhomotopic (f : C(X, Y))
    (hf : f.Nullhomotopic) (n : ℕ) (hn : n ≠ 0) :
    singularHomologyMap f n = 0 := by
  obtain ⟨y, hy⟩ := hf
  rw [homotopic_homologyMap hy n]
  exact singularHomologyMap_const_eq_zero X y n hn

end Wikipedia.HopfProblem.CuspCentralHomology
