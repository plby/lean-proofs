import Wikipedia.NoExoticSixSphere.Topology.SimplyConnectedSphere
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Homotopy.Lifting

/-!
# Circle-valued families on simply connected spaces

The actual exponential covering lifts the family to a real-valued function.
Scaling that lift gives a nullhomotopy to the identity of the circle.
-/

open unitInterval

namespace NoExoticSixSphere

variable {X : Type*} [TopologicalSpace X] [SimplyConnectedSpace X]
  [LocallyPathConnectedSpace X]

theorem exists_circleLog (f : C(X, Circle)) :
    ∃ g : C(X, ℝ), ∀ x, Circle.exp (g x) = f x := by
  classical
  let x₀ : X := Classical.choice (inferInstance : Nonempty X)
  obtain ⟨r, hr⟩ := Circle.exp_surjective (f x₀)
  obtain ⟨g, ⟨_, hg⟩, _⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts f x₀ r hr
  exact ⟨g, fun x ↦ congrFun hg x⟩

theorem circleMap_nullhomotopic (f : C(X, Circle)) :
    f.Homotopic (ContinuousMap.const X 1) := by
  obtain ⟨g, hg⟩ := exists_circleLog f
  refine ⟨{
    toFun := fun p ↦ Circle.exp ((1 - (p.1 : ℝ)) * g p.2)
    continuous_toFun := Circle.exp.continuous.comp
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        (g.continuous.comp continuous_snd))
    map_zero_left := ?_
    map_one_left := ?_ }⟩
  · intro x
    change Circle.exp ((1 - (0 : ℝ)) * g x) = f x
    simpa only [sub_zero, one_mul] using hg x
  · intro x
    change Circle.exp ((1 - (1 : ℝ)) * g x) = 1
    simp only [sub_self, zero_mul, Circle.exp_zero]

end NoExoticSixSphere
