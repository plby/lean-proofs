import Wikipedia.HopfProblem.HolomorphicPicardNativeGluingTransition

/-!
# The actual native holomorphic line bundle glued from a unit Čech cocycle

The original open cover and unit sections supply genuine scalar transition
data. The cocycle identities and holomorphicity are proved, after which
the existing `VectorBundleCore` construction gives the native bundle, its
topology, vector-space fibres, and holomorphic local trivializations.
The resulting bundle is not a subtype of presentations.
-/

noncomputable section

open Set TopologicalSpace Bundle
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicPicardNative

open HolomorphicExponentialSheaf HolomorphicCharacterBundle
open HolomorphicFunctionSheaf.SphereH1

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  {ι : Type} (U : ι → Opens M) (hcover : ∀ x : M, ∃ i : ι, x ∈ U i)
  (c : CechOneCocycle (unitsSheaf I M) U)

/-- Actual scalar transition data from an actual unit-valued Čech cocycle.
Only the chart index is chosen; every transition and every bundle identity
comes from the supplied genuine section and its proved cocycle equation. -/
def cocycleTransitionData : TransitionData M ι where
  baseSet i := U i
  isOpen_baseSet i := (U i).isOpen
  indexAt x := Classical.choose (hcover x)
  mem_baseSet_at x := Classical.choose_spec (hcover x)
  transition := cocycleTransition I M U c
  transition_self i x hx := by
    apply Units.ext
    change (cocycleTransition I M U c i i x : ℂ) = 1
    rw [cocycleTransition_apply I M U c i i x ⟨hx, hx⟩]
    exact cocycle_unit_eval_self I M U c i x hx
  transition_comp i j k x hx := by
    apply Units.ext
    change (cocycleTransition I M U c j k x : ℂ) *
      (cocycleTransition I M U c i j x : ℂ) = (cocycleTransition I M U c i k x : ℂ)
    rw [cocycleTransition_apply I M U c j k x ⟨hx.1.2, hx.2⟩,
      cocycleTransition_apply I M U c i j x hx.1,
      cocycleTransition_apply I M U c i k x ⟨hx.1.1, hx.2⟩]
    exact cocycle_unit_eval_comp I M U c i j k x hx.1.1 hx.1.2 hx.2
  continuousOn_transition i j := (cocycleTransition_contMDiffOn I M U c i j).continuousOn

@[simp]
theorem cocycleTransitionData_baseSet (i : ι) :
    (cocycleTransitionData I M U hcover c).baseSet i = (U i : Set M) := rfl

@[simp]
theorem cocycleTransitionData_indexAt (x : M) :
    (cocycleTransitionData I M U hcover c).indexAt x = Classical.choose (hcover x) := rfl

/-- The constructed bundle's transition on an original overlap is the
pointwise value of the original unit section, without a change of sign. -/
theorem cocycleTransitionData_transition (i j : ι) (x : M) (hx : x ∈ U i ⊓ U j) :
    ((cocycleTransitionData I M U hcover c).transition i j x : ℂ) =
      unitSectionEval (c.value i j) ⟨x, hx⟩ :=
  cocycleTransition_apply I M U c i j x hx

/-- The actual transition data are holomorphic in the original charts. -/
instance cocycleTransitionData_isHolomorphic :
    (cocycleTransitionData I M U hcover c).IsHolomorphic I where
  contMDiffOn_transition i j := cocycleTransition_contMDiffOn I M U c i j

/-- The genuine native vector-bundle core obtained from the original
unit-valued cocycle. Its fibres and total-space topology are mathlib's
actual `VectorBundleCore` fibres and topology. -/
abbrev cocycleCore : VectorBundleCore ℂ M ℂ ι :=
  (cocycleTransitionData I M U hcover c).core

@[simp]
theorem cocycleCore_baseSet (i : ι) :
    (cocycleCore I M U hcover c).baseSet i = (U i : Set M) := rfl

/-- The constructed native fibres form an actual topological fibre bundle. -/
def cocycleCore_fiberBundle : FiberBundle ℂ (cocycleCore I M U hcover c).Fiber :=
  inferInstance

/-- The constructed native bundle is an actual complex vector bundle. -/
theorem cocycleCore_vectorBundle : VectorBundle ℂ ℂ (cocycleCore I M U hcover c).Fiber :=
  inferInstance

/-- The native vector-bundle structure has analytic-order transition maps
in the original complex charts on the base. -/
theorem cocycleCore_contMDiffVectorBundle :
    ContMDiffVectorBundle ω ℂ (cocycleCore I M U hcover c).Fiber I :=
  (cocycleTransitionData I M U hcover c).core_contMDiffVectorBundle I

/-- The actual native local trivializations have exactly the original
unit-cocycle values as their scalar coordinate changes. -/
theorem cocycleCore_localTriv_coordChange (i j : ι) {x : M}
    (hx : x ∈ U i ⊓ U j) (v : ℂ) :
    ((cocycleCore I M U hcover c).localTriv i).coordChangeL ℂ
      ((cocycleCore I M U hcover c).localTriv j) x v =
        unitSectionEval (c.value i j) ⟨x, hx⟩ * v := by
  calc
    _ = ((cocycleTransitionData I M U hcover c).transition i j x : ℂ) * v :=
      (cocycleTransitionData I M U hcover c).core_localTriv_coordChange i j hx v
    _ = _ := by rw [cocycleTransitionData_transition I M U hcover c i j x hx]

end Wikipedia.HopfProblem.HolomorphicPicardNative
