import Mathlib.Algebra.Module.LinearMap.Basic

/-!
# Detecting a nonzero linear map by its actual value

This elementary helper keeps the categorical coefficient structures
opaque when it is applied to the genuine holomorphic exterior cup.
-/

namespace Wikipedia.HopfProblem.CuspHolomorphicCupNonvanishing

/-- An actual nonzero value proves that the original linear map is nonzero. -/
theorem linearMap_ne_zero_of_nonzero_value
    {R V W : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    [AddCommMonoid W] [Module R W] (f : V →ₗ[R] W) (v : V) (w : W)
    (he : f v = w) (hw : w ≠ 0) : f ≠ 0 := by
  intro hf
  apply hw
  exact he.symm.trans (congrArg (fun g : V →ₗ[R] W => g v) hf)

end Wikipedia.HopfProblem.CuspHolomorphicCupNonvanishing
