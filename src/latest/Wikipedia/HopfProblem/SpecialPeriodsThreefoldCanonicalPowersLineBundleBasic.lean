import Wikipedia.HopfProblem.HolomorphicCharacterBundleCoreSections
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Powers of actual holomorphic line-bundle transition functions

The power cocycle retains the original open cover and preferred charts.
Its native vector-bundle core is constructed by the existing transition
data interface.  Companion files identify its fibres with full algebraic
tensor powers and its section powers with actual holomorphic bundle maps.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicCharacterBundle.TransitionData

variable {M ι : Type*} [TopologicalSpace M]

/-- The genuine power cocycle on the unchanged original open cover. -/
def power (A : TransitionData M ι) (n : ℕ) : TransitionData M ι where
  baseSet := A.baseSet
  isOpen_baseSet := A.isOpen_baseSet
  indexAt := A.indexAt
  mem_baseSet_at := A.mem_baseSet_at
  transition i j x := A.transition i j x ^ n
  transition_self i x hx := by rw [A.transition_self i x hx, one_pow]
  transition_comp i j k x hx := by
    rw [← mul_pow, A.transition_comp i j k x hx]
  continuousOn_transition i j := by
    apply ((A.continuousOn_transition i j).pow n).congr
    intro x _
    simp only [Units.val_pow_eq_pow_val, Pi.pow_apply]

variable (A : TransitionData M ι) (n : ℕ)

@[simp] theorem power_baseSet (i : ι) : (A.power n).baseSet i = A.baseSet i := rfl

@[simp] theorem power_indexAt (x : M) : (A.power n).indexAt x = A.indexAt x := rfl

@[simp] theorem power_transition (i j : ι) (x : M) :
    (A.power n).transition i j x = A.transition i j x ^ n := rfl

theorem power_transition_val (i j : ι) (x : M) :
    ((A.power n).transition i j x : ℂ) = (A.transition i j x : ℂ) ^ n := rfl

@[simp] theorem power_zero_transition (i j : ι) (x : M) :
    (A.power 0).transition i j x = 1 := pow_zero _

@[simp] theorem power_one_transition (i j : ι) (x : M) :
    (A.power 1).transition i j x = A.transition i j x := pow_one _

theorem power_add_transition (m : ℕ) (i j : ι) (x : M) :
    (A.power (m + n)).transition i j x =
      (A.power m).transition i j x * (A.power n).transition i j x := pow_add _ m n

theorem power_mul_transition (m : ℕ) (i j : ι) (x : M) :
    ((A.power m).power n).transition i j x = (A.power (m * n)).transition i j x :=
  (pow_mul _ m n).symm

theorem power_core_coordChange_apply (i j : ι) (x : M) (v : ℂ) :
    (A.power n).core.coordChange i j x v = (A.transition i j x : ℂ) ^ n * v := rfl

theorem power_core_localTriv_apply (i : ι) (p : (A.power n).core.TotalSpace) :
    (A.power n).core.localTriv i p =
      (p.proj, (A.transition (A.indexAt p.proj) i p.proj : ℂ) ^ n * id (α := ℂ) p.2) := rfl

section Holomorphic

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  [ChartedSpace H M] (I : ModelWithCorners ℂ E H)

/-- The actual variable power transitions are holomorphic on the original overlaps. -/
instance power_isHolomorphic [A.IsHolomorphic I] : (A.power n).IsHolomorphic I where
  contMDiffOn_transition i j := by
    simpa only [power_transition_val, power_baseSet] using
      (A.transition_holomorphic I i j).pow n

theorem power_holomorphicVectorBundle [A.IsHolomorphic I] :
    ContMDiffVectorBundle ω ℂ (A.power n).core.Fiber I := inferInstance

theorem power_totalSpace_isManifold [A.IsHolomorphic I] [IsManifold I ω M] :
    IsManifold (I.prod (modelWithCornersSelf ℂ ℂ)) ω (A.power n).core.TotalSpace :=
  inferInstance

end Holomorphic

end Wikipedia.HopfProblem.HolomorphicCharacterBundle.TransitionData
