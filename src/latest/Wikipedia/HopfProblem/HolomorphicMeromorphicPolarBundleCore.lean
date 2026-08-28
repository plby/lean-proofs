import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# A native holomorphic line bundle from a scalar cocycle

An open cover and holomorphic scalar transition functions satisfying the
actual overlap cocycle identities construct a `VectorBundleCore`. Its native
total-space topology and atlas make it a holomorphic vector bundle with
one-dimensional complex fibers. No line bundle or global trivialization is
assumed as input.
-/

open Set Topology Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]

/-- Holomorphic scalar transition functions on an actual open cover.
The convention is that `transition i j` sends chart `i` coordinates to chart
`j` coordinates. Nonvanishing follows from the cocycle identities. -/
structure ScalarCocycle (I : ModelWithCorners ℂ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] (ι : Type*) where
  baseSet : ι → Set M
  isOpen_baseSet : ∀ i, IsOpen (baseSet i)
  cover : ∀ x, ∃ i, x ∈ baseSet i
  transition : ι → ι → M → ℂ
  holomorphic_transition : ∀ i j,
    ContMDiffOn I (modelWithCornersSelf ℂ ℂ) ω (transition i j) (baseSet i ∩ baseSet j)
  transition_self : ∀ i x, x ∈ baseSet i → transition i i x = 1
  transition_comp : ∀ i j k x, x ∈ baseSet i ∩ baseSet j ∩ baseSet k →
    transition j k x * transition i j x = transition i k x

namespace ScalarCocycle

variable {I : ModelWithCorners ℂ E H} {M ι : Type*}
  [TopologicalSpace M] [ChartedSpace H M] (A : ScalarCocycle I M ι)

/-- Choose a chart containing each base point, only to implement the standard
bundle-core fiber model. -/
noncomputable def indexAt (x : M) : ι := Classical.choose (A.cover x)

theorem mem_baseSet_at (x : M) : x ∈ A.baseSet (A.indexAt x) :=
  Classical.choose_spec (A.cover x)

theorem transition_reverse_mul (i j : ι) {x : M}
    (hx : x ∈ A.baseSet i ∩ A.baseSet j) :
    A.transition j i x * A.transition i j x = 1 := by
  rw [A.transition_comp i j i x ⟨hx, hx.1⟩, A.transition_self i x hx.1]

theorem transition_ne_zero (i j : ι) {x : M}
    (hx : x ∈ A.baseSet i ∩ A.baseSet j) : A.transition i j x ≠ 0 := by
  intro hzero
  have h := A.transition_reverse_mul i j hx
  rw [hzero, mul_zero] at h
  exact zero_ne_one h

/-- The actual bundle core associated to the scalar cocycle. Its topology and
trivialization atlas are supplied by the native `VectorBundleCore` construction. -/
noncomputable def core : VectorBundleCore ℂ M ℂ ι where
  baseSet := A.baseSet
  isOpen_baseSet := A.isOpen_baseSet
  indexAt := A.indexAt
  mem_baseSet_at := A.mem_baseSet_at
  coordChange i j x := A.transition i j x • ContinuousLinearMap.id ℂ ℂ
  coordChange_self i x hx v := by
    simp [A.transition_self i x hx]
  continuousOn_coordChange i j :=
    (A.holomorphic_transition i j).continuousOn.smul continuousOn_const
  coordChange_comp i j k x hx v := by
    simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    rw [← mul_assoc, A.transition_comp i j k x hx]

@[simp] theorem core_baseSet (i : ι) : A.core.baseSet i = A.baseSet i := rfl

@[simp] theorem core_indexAt (x : M) : A.core.indexAt x = A.indexAt x := rfl

@[simp] theorem core_coordChange (i j : ι) (x : M) :
    A.core.coordChange i j x = A.transition i j x • ContinuousLinearMap.id ℂ ℂ := rfl

@[simp] theorem core_coordChange_apply (i j : ι) (x : M) (v : ℂ) :
    A.core.coordChange i j x v = A.transition i j x * v := rfl

@[simp] theorem core_localTriv_apply (i : ι) (p : A.core.TotalSpace) :
    A.core.localTriv i p =
      (p.1, A.transition (A.indexAt p.1) i p.1 * id (α := ℂ) p.2) := rfl

@[simp] theorem core_localTriv_baseSet (i : ι) :
    (A.core.localTriv i).baseSet = A.baseSet i := rfl

/-- The transition in the native trivialization atlas is precisely the
supplied scalar transition on every overlap. -/
theorem core_localTriv_coordChange (i j : ι) {x : M}
    (hx : x ∈ A.baseSet i ∩ A.baseSet j) (v : ℂ) :
    (A.core.localTriv i).coordChangeL ℂ (A.core.localTriv j) x v =
      A.transition i j x * v :=
  A.core.localTriv_coordChange_eq i j hx v

instance core_isContMDiff : A.core.IsContMDiff I ω where
  contMDiffOn_coordChange i j :=
    (A.holomorphic_transition i j).smul contMDiffOn_const

/-- Native holomorphic vector-bundle structure for the constructed core. -/
theorem core_contMDiffVectorBundle : ContMDiffVectorBundle ω ℂ A.core.Fiber I :=
  inferInstance

instance core_finiteDimensional (x : M) : FiniteDimensional ℂ (A.core.Fiber x) :=
  inferInstanceAs (FiniteDimensional ℂ ℂ)

/-- Every fiber of the constructed native bundle has complex dimension one. -/
theorem core_finrank (x : M) : Module.finrank ℂ (A.core.Fiber x) = 1 :=
  Module.finrank_self ℂ

end ScalarCocycle

end Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarBundle
