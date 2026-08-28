import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Analysis.Complex.Basic

/-!
# Holomorphic line bundles from general multiplicative cocycles

An open cover and nonzero scalar transition functions satisfying the
cocycle identities define an actual complex line bundle. No expression of
the transition functions as a coboundary is assumed. `VectorBundleCore`
supplies the bundle topology, fibres, and linear local trivializations.
Holomorphic transition functions give the resulting bundle its analytic
vector-bundle structure.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicCharacterBundle

structure TransitionData (M : Type*) [TopologicalSpace M] (ι : Type*) where
  baseSet : ι → Set M
  isOpen_baseSet : ∀ i, IsOpen (baseSet i)
  indexAt : M → ι
  mem_baseSet_at : ∀ x, x ∈ baseSet (indexAt x)
  transition : ι → ι → M → ℂˣ
  transition_self : ∀ i x, x ∈ baseSet i → transition i i x = 1
  transition_comp : ∀ i j k x, x ∈ baseSet i ∩ baseSet j ∩ baseSet k →
    transition j k x * transition i j x = transition i k x
  continuousOn_transition : ∀ i j,
    ContinuousOn (fun x => (transition i j x : ℂ)) (baseSet i ∩ baseSet j)

namespace TransitionData

variable {M ι : Type*} [TopologicalSpace M] (A : TransitionData M ι)

theorem transition_ne_zero (i j : ι) (x : M) : (A.transition i j x : ℂ) ≠ 0 :=
  (A.transition i j x).ne_zero

def core : VectorBundleCore ℂ M ℂ ι where
  baseSet := A.baseSet
  isOpen_baseSet := A.isOpen_baseSet
  indexAt := A.indexAt
  mem_baseSet_at := A.mem_baseSet_at
  coordChange i j x := (A.transition i j x : ℂ) • ContinuousLinearMap.id ℂ ℂ
  coordChange_self i x hx v := by
    simp [A.transition_self i x hx]
  continuousOn_coordChange i j := (A.continuousOn_transition i j).smul continuousOn_const
  coordChange_comp i j k x hx v := by
    change (A.transition j k x : ℂ) * ((A.transition i j x : ℂ) * v) =
      (A.transition i k x : ℂ) * v
    rw [← mul_assoc, ← Units.val_mul, A.transition_comp i j k x hx]

@[simp] theorem core_baseSet (i : ι) : A.core.baseSet i = A.baseSet i := rfl

@[simp] theorem core_indexAt (x : M) : A.core.indexAt x = A.indexAt x := rfl

@[simp] theorem core_coordChange (i j : ι) (x : M) :
    A.core.coordChange i j x = (A.transition i j x : ℂ) • ContinuousLinearMap.id ℂ ℂ := rfl

@[simp] theorem core_coordChange_apply (i j : ι) (x : M) (v : ℂ) :
    A.core.coordChange i j x v = (A.transition i j x : ℂ) * v := rfl

@[simp] theorem core_localTriv_apply (i : ι) (p : A.core.TotalSpace) :
    A.core.localTriv i p =
      (p.1, (A.transition (A.indexAt p.1) i p.1 : ℂ) * id (α := ℂ) p.2) := rfl

@[simp] theorem core_localTriv_symm_apply (i : ι) (x : M) (v : ℂ) :
    (A.core.localTriv i).toOpenPartialHomeomorph.symm (x, v) =
      ⟨x, (A.transition i (A.indexAt x) x : ℂ) * v⟩ := rfl

instance core_localTriv_memTrivializationAtlas (i : ι) :
    MemTrivializationAtlas (A.core.localTriv i) where
  out := ⟨i, rfl⟩

theorem core_localTriv_fiber_symm (i : ι) {x : M} (hx : x ∈ A.baseSet i) (v : ℂ) :
    (A.core.localTriv i).symm x v = (A.transition i (A.indexAt x) x : ℂ) * v := by
  rw [VectorBundleCore.localTriv_symm_apply A.core i hx v]
  rfl

theorem core_localTriv_coordChange (i j : ι) {x : M}
    (hx : x ∈ A.baseSet i ∩ A.baseSet j) (v : ℂ) :
    (A.core.localTriv i).coordChangeL ℂ (A.core.localTriv j) x v =
      (A.transition i j x : ℂ) * v :=
  A.core.localTriv_coordChange_eq i j hx v

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
    [ChartedSpace H M] (I : ModelWithCorners ℂ E H)

class IsHolomorphic : Prop where
  contMDiffOn_transition : ∀ i j,
    ContMDiffOn I (modelWithCornersSelf ℂ ℂ) ω
      (fun x => (A.transition i j x : ℂ)) (A.baseSet i ∩ A.baseSet j)

theorem transition_holomorphic [hA : A.IsHolomorphic I] (i j : ι) :
    ContMDiffOn I (modelWithCornersSelf ℂ ℂ) ω
      (fun x => (A.transition i j x : ℂ)) (A.baseSet i ∩ A.baseSet j) :=
  hA.contMDiffOn_transition i j

instance core_isContMDiff [A.IsHolomorphic I] : A.core.IsContMDiff I ω where
  contMDiffOn_coordChange i j := (A.transition_holomorphic I i j).smul contMDiffOn_const

theorem core_contMDiffVectorBundle [A.IsHolomorphic I] :
    ContMDiffVectorBundle ω ℂ A.core.Fiber I := inferInstance

theorem core_totalSpace_isManifold [A.IsHolomorphic I] [IsManifold I ω M] :
    IsManifold (I.prod (modelWithCornersSelf ℂ ℂ)) ω A.core.TotalSpace := inferInstance

theorem isHolomorphic_of_locally_constant
    (h : ∀ i j x, x ∈ A.baseSet i ∩ A.baseSet j →
      (fun y => (A.transition i j y : ℂ)) =ᶠ[𝓝 x] fun _ => (A.transition i j x : ℂ)) :
    A.IsHolomorphic I where
  contMDiffOn_transition i j x hx :=
    (contMDiffAt_const.congr_of_eventuallyEq (h i j x hx)).contMDiffWithinAt

end TransitionData

end Wikipedia.HopfProblem.HolomorphicCharacterBundle
