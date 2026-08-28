import Wikipedia.HopfProblem.HigherHurewiczSimplexNullhomotopy
import Wikipedia.HopfProblem.ThirdHurewiczThreeSimplexBasic

/-!
# Nullhomotopies of the original based three-simplices

This specialization accepts the already defined `ThirdHurewicz.BasedThreeSimplex`
without changing its map or boundary predicate. The only homotopical input
is triviality of Mathlib's native third homotopy group at the base point.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.FourthHurewicz

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] {x : X} [Subsingleton (π_ 3 X x)]

/-- A genuine nullhomotopy of the original three-simplex, relative to its entire boundary. -/
def threeSimplexNullHomotopy (τ : ThirdHurewicz.BasedThreeSimplex x) :
    τ.val.HomotopyRel (ContinuousMap.const (Simplex 3) x) ThirdHurewicz.threeSimplexBoundary :=
  HigherHurewicz.simplexNullHomotopy (n := 3) τ

@[simp] theorem threeSimplexNullHomotopy_zero (τ : ThirdHurewicz.BasedThreeSimplex x)
    (s : Simplex 3) : threeSimplexNullHomotopy τ (0, s) = τ.val s :=
  (threeSimplexNullHomotopy τ).apply_zero s

@[simp] theorem threeSimplexNullHomotopy_one (τ : ThirdHurewicz.BasedThreeSimplex x)
    (s : Simplex 3) : threeSimplexNullHomotopy τ (1, s) = x :=
  (threeSimplexNullHomotopy τ).apply_one s

theorem threeSimplexNullHomotopy_boundary (τ : ThirdHurewicz.BasedThreeSimplex x)
    (t : I) (s : Simplex 3) (hs : s ∈ ThirdHurewicz.threeSimplexBoundary) :
    threeSimplexNullHomotopy τ (t, s) = x :=
  (threeSimplexNullHomotopy τ).eq_snd t hs

@[simp] theorem threeSimplexNullHomotopy_constant (x : X) [Subsingleton (π_ 3 X x)] :
    threeSimplexNullHomotopy (ThirdHurewicz.constantBasedThreeSimplex x) =
      ContinuousMap.HomotopyRel.refl (ContinuousMap.const (Simplex 3) x)
        ThirdHurewicz.threeSimplexBoundary :=
  HigherHurewicz.simplexNullHomotopy_constant 3 x

@[simp] theorem threeSimplexNullHomotopy_constant_toContinuousMap (x : X)
    [Subsingleton (π_ 3 X x)] :
    (threeSimplexNullHomotopy (ThirdHurewicz.constantBasedThreeSimplex x)).toContinuousMap =
      ContinuousMap.const (I × Simplex 3) x :=
  HigherHurewicz.simplexNullHomotopy_constant_toContinuousMap 3 x

theorem threeSimplexNullHomotopy_stationary_of_val_eq_const
    (τ : ThirdHurewicz.BasedThreeSimplex x)
    (hτ : τ.val = ContinuousMap.const (Simplex 3) x) :
    (threeSimplexNullHomotopy τ).toContinuousMap = ContinuousMap.const (I × Simplex 3) x :=
  HigherHurewicz.simplexNullHomotopy_stationary_of_val_eq_const τ hτ

end Wikipedia.HopfProblem.FourthHurewicz
