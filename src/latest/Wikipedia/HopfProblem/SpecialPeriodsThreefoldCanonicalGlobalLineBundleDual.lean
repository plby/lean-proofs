import Wikipedia.HopfProblem.HolomorphicCharacterBundleCore
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Duals of the existing holomorphic cocycle line bundles

This file reuses `HolomorphicCharacterBundle.TransitionData` and its native
`VectorBundleCore`. Inverting the variable transition functions constructs
the dual bundle, and its fibres are identified with the full continuous
complex-linear duals of the original fibres. The identification respects
the actual local trivializations.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.CanonicalGlobalLineBundle

open HolomorphicCharacterBundle

variable {M ι : Type*} [TopologicalSpace M] (A : TransitionData M ι)

theorem transition_reverse_mul (i j : ι) {x : M}
    (hx : x ∈ A.baseSet i ∩ A.baseSet j) :
    A.transition j i x * A.transition i j x = 1 :=
  (A.transition_comp i j i x ⟨⟨hx.1, hx.2⟩, hx.1⟩).trans
    (A.transition_self i x hx.1)

theorem transition_reverse (i j : ι) {x : M}
    (hx : x ∈ A.baseSet i ∩ A.baseSet j) :
    A.transition j i x = (A.transition i j x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (transition_reverse_mul A i j hx)

/-- Inverse transition functions on the original open cover define the
dual native line bundle. -/
def dual : TransitionData M ι where
  baseSet := A.baseSet
  isOpen_baseSet := A.isOpen_baseSet
  indexAt := A.indexAt
  mem_baseSet_at := A.mem_baseSet_at
  transition i j x := (A.transition i j x)⁻¹
  transition_self i x hx := by rw [A.transition_self i x hx, inv_one]
  transition_comp i j k x hx := by
    rw [← mul_inv, A.transition_comp i j k x hx]
  continuousOn_transition i j := by
    intro x hx
    have h : ContinuousWithinAt (fun y => (A.transition i j y : ℂ)⁻¹)
        (A.baseSet i ∩ A.baseSet j) x :=
      (continuousAt_inv₀ (A.transition_ne_zero i j x)).comp_continuousWithinAt
        (f := fun y : M => (A.transition i j y : ℂ))
        (A.continuousOn_transition i j x hx)
    simpa only [Units.val_inv_eq_inv_val] using h

@[simp] theorem dual_baseSet (i : ι) : (dual A).baseSet i = A.baseSet i := rfl

@[simp] theorem dual_indexAt (x : M) : (dual A).indexAt x = A.indexAt x := rfl

@[simp] theorem dual_transition (i j : ι) (x : M) :
    (dual A).transition i j x = (A.transition i j x)⁻¹ := rfl

@[simp] theorem dual_core_coordChange_apply (i j : ι) (x : M) (c : ℂ) :
    (dual A).core.coordChange i j x c = (A.transition i j x : ℂ)⁻¹ * c := by
  simp only [TransitionData.core_coordChange_apply, dual_transition, Units.val_inv_eq_inv_val]

/-- Each dual-bundle fibre is the full continuous complex-linear dual of
the corresponding original fibre, not a formal inverse line label. -/
def dualFiberEquiv (x : M) :
    (dual A).core.Fiber x ≃L[ℂ] (A.core.Fiber x →L[ℂ] ℂ) :=
  (ContinuousLinearMap.toSpanSingletonCLE : ℂ ≃L[ℂ] (ℂ →L[ℂ] ℂ))

@[simp] theorem dualFiberEquiv_apply (x : M) (c : (dual A).core.Fiber x)
    (v : A.core.Fiber x) :
    dualFiberEquiv A x c v = id (α := ℂ) c * id (α := ℂ) v := by
  change id (α := ℂ) v * id (α := ℂ) c = _
  exact mul_comm _ _

/-- The actual dual coordinate change is precomposition by the inverse
primal coordinate change, on the full space of continuous linear maps. -/
theorem dualFiberEquiv_coordChange (i j : ι) {x : M}
    (hx : x ∈ A.baseSet i ∩ A.baseSet j) (c : ℂ) :
    dualFiberEquiv A x ((dual A).core.coordChange i j x c) =
      (dualFiberEquiv A x c).comp (A.core.coordChange j i x) := by
  apply ContinuousLinearMap.ext
  intro v
  change id (α := ℂ) v * (((A.transition i j x)⁻¹ : ℂˣ) * c) =
    ((A.transition j i x : ℂ) * id (α := ℂ) v) * c
  rw [transition_reverse A i j hx]
  exact (mul_left_comm _ _ _).trans (mul_assoc _ _ _).symm

/-- In every native bundle chart, evaluation is multiplication of the
dual and primal scalar coordinates. -/
theorem dualFiberEquiv_localTriv (i : ι) (x : M) (c : (dual A).core.Fiber x)
    (v : A.core.Fiber x) :
    dualFiberEquiv A x c v =
      ((dual A).core.localTriv i ⟨x, c⟩).2 * (A.core.localTriv i ⟨x, v⟩).2 := by
  rw [dualFiberEquiv_apply, TransitionData.core_localTriv_apply,
    TransitionData.core_localTriv_apply]
  simp only [dual_indexAt, dual_transition, Units.val_inv_eq_inv_val]
  rw [mul_mul_mul_comm, inv_mul_cancel₀ (A.transition_ne_zero _ _ _), one_mul]

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
    [ChartedSpace H M] (I : ModelWithCorners ℂ E H)

instance dual_isHolomorphic [A.IsHolomorphic I] : (dual A).IsHolomorphic I where
  contMDiffOn_transition i j := by
    simpa only [dual_transition, Units.val_inv_eq_inv_val, dual_baseSet] using
      (A.transition_holomorphic I i j).inv₀ (fun x _ => A.transition_ne_zero i j x)

theorem dual_contMDiffVectorBundle [A.IsHolomorphic I] :
    ContMDiffVectorBundle ω ℂ (dual A).core.Fiber I := inferInstance

end Wikipedia.HopfProblem.CanonicalGlobalLineBundle
