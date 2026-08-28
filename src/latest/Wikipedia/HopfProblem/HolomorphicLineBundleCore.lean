import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Holomorphic line bundles with constant transition coefficients

An open cover and a nonzero scalar coefficient in each chart define an
actual complex line bundle.  Its transition from chart `i` to chart `j`
is multiplication by `coefficient j / coefficient i`.  The standard
`VectorBundleCore` construction supplies its total-space topology and its
local trivializations.  The constant transitions are analytic for any
complex manifold structure on the base.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicLineBundle

structure ConstantTransitionData (M : Type*) [TopologicalSpace M] (ι : Type*) where
  baseSet : ι → Set M
  isOpen_baseSet : ∀ i, IsOpen (baseSet i)
  indexAt : M → ι
  mem_baseSet_at : ∀ x, x ∈ baseSet (indexAt x)
  coefficient : ι → ℂ
  coefficient_ne_zero : ∀ i, coefficient i ≠ 0

namespace ConstantTransitionData

variable {M ι : Type*} [TopologicalSpace M] (A : ConstantTransitionData M ι)

def core : VectorBundleCore ℂ M ℂ ι where
  baseSet := A.baseSet
  isOpen_baseSet := A.isOpen_baseSet
  indexAt := A.indexAt
  mem_baseSet_at := A.mem_baseSet_at
  coordChange i j _ := (A.coefficient j / A.coefficient i) • ContinuousLinearMap.id ℂ ℂ
  coordChange_self i _ _ v := by
    simp [A.coefficient_ne_zero i]
  continuousOn_coordChange _ _ := continuousOn_const
  coordChange_comp i j k _ _ v := by
    simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    field_simp [A.coefficient_ne_zero i, A.coefficient_ne_zero j]

@[simp] theorem core_baseSet (i : ι) : A.core.baseSet i = A.baseSet i := rfl

@[simp] theorem core_indexAt (x : M) : A.core.indexAt x = A.indexAt x := rfl

@[simp] theorem core_coordChange (i j : ι) (x : M) :
    A.core.coordChange i j x =
      (A.coefficient j / A.coefficient i) • ContinuousLinearMap.id ℂ ℂ := rfl

@[simp] theorem core_coordChange_apply (i j : ι) (x : M) (v : ℂ) :
    A.core.coordChange i j x v = (A.coefficient j / A.coefficient i) * v := rfl

@[simp] theorem core_localTriv_apply (i : ι) (p : A.core.TotalSpace) :
    A.core.localTriv i p =
      (p.1, (A.coefficient i / A.coefficient (A.indexAt p.1)) * id (α := ℂ) p.2) := rfl

@[simp] theorem core_localTriv_symm_apply (i : ι) (x : M) (v : ℂ) :
    (A.core.localTriv i).toOpenPartialHomeomorph.symm (x, v) =
      ⟨x, (A.coefficient (A.indexAt x) / A.coefficient i) * v⟩ := rfl

theorem core_localTriv_fiber_symm (i : ι) {x : M} (hx : x ∈ A.baseSet i) (v : ℂ) :
    (A.core.localTriv i).symm x v =
      (A.coefficient (A.indexAt x) / A.coefficient i) * v := by
  rw [VectorBundleCore.localTriv_symm_apply A.core i hx v]
  rfl

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
    [ChartedSpace H M] (I : ModelWithCorners ℂ E H)

instance core_isContMDiff : A.core.IsContMDiff I ω where
  contMDiffOn_coordChange _ _ := contMDiffOn_const

theorem core_contMDiffVectorBundle : ContMDiffVectorBundle ω ℂ A.core.Fiber I :=
  inferInstance

end ConstantTransitionData

end Wikipedia.HopfProblem.HolomorphicLineBundle
