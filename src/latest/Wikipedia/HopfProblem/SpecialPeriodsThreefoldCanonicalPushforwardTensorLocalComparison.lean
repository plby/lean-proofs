import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardTensorLocalSections
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardTensorLocalModules

/-!
# The actual local projection-formula section comparison

Over a base open contained in a genuine base-line chart, contraction
identifies sections of the native tensor bundle with native sections of
the first factor. The comparison is linear over the base's actual
holomorphic functions, acting by actual pullback. Its forward base-chart
transition and compatibility with literal restriction are explicit.
-/

noncomputable section

open Set Topology TopologicalSpace Bundle
open scoped ContDiff TensorProduct

namespace Wikipedia.HopfProblem.CanonicalGlobalLineBundle.TensorLocal

open HolomorphicCharacterBundle

variable {M N : Type} {ι κ : Type*} [TopologicalSpace M] [TopologicalSpace N]
  (A : TransitionData M ι) (B : TransitionData N κ)
  {E H F K : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace K] [ChartedSpace K N]
  (I : ModelWithCorners ℂ E H) (J : ModelWithCorners ℂ F K)
  (f : M → N) (hf : ContMDiff I J ω f)
  [A.IsHolomorphic I] [B.IsHolomorphic J]

/-- The genuine comparison is linear over actual base holomorphic functions. -/
def sectionLinearEquiv (j : κ) (U : Opens N) (hU : (U : Set N) ⊆ B.baseSet j) :
    letI : (pullback B f hf.continuous).IsHolomorphic I :=
      pullback_isHolomorphic B f hf.continuous I J hf
    letI := baseModule (tensor A (pullback B f hf.continuous)).core I J f hf U
    letI := baseModule A.core I J f hf U
    NativeBundleSections.Section (tensor A (pullback B f hf.continuous)).core I
        (preimageOpen f hf.continuous U)
      ≃ₗ[HolomorphicFunctionSheaf.Section J N U]
        NativeBundleSections.Section A.core I (preimageOpen f hf.continuous U) := by
  let : (pullback B f hf.continuous).IsHolomorphic I :=
    pullback_isHolomorphic B f hf.continuous I J hf
  letI := baseModule (tensor A (pullback B f hf.continuous)).core I J f hf U
  letI := baseModule A.core I J f hf U
  let e := sectionEquivOn A B I J f hf j (preimageOpen f hf.continuous U) (fun _ hx => hU hx)
  exact
    { toFun := e
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply
      map_add' := e.map_add
      map_smul' g s := e.map_smul (scalarPullback I J f hf U g) s }

/-- The forward section map is the already proved genuine fibre contraction. -/
@[simp] theorem sectionLinearEquiv_apply (j : κ) (U : Opens N)
    (hU : (U : Set N) ⊆ B.baseSet j)
    (s : NativeBundleSections.Section (tensor A (pullback B f hf.continuous)).core I
      (preimageOpen f hf.continuous U)) (x : preimageOpen f hf.continuous U) :
    sectionLinearEquiv A B I J f hf j U hU s x =
      unTensorFiberEquiv A B f hf.continuous j x.val (s x) := rfl

@[simp] theorem sectionLinearEquiv_symm_apply (j : κ) (U : Opens N)
    (hU : (U : Set N) ⊆ B.baseSet j)
    (s : NativeBundleSections.Section A.core I (preimageOpen f hf.continuous U))
    (x : preimageOpen f hf.continuous U) :
    letI : (pullback B f hf.continuous).IsHolomorphic I :=
      pullback_isHolomorphic B f hf.continuous I J hf
    letI := baseModule (tensor A (pullback B f hf.continuous)).core I J f hf U
    letI := baseModule A.core I J f hf U
    (sectionLinearEquiv A B I J f hf j U hU).symm s x =
      (unTensorFiberEquiv A B f hf.continuous j x.val).symm (s x) := rfl

/-- The actual inverse tensors with the base chart's original unit frame in every fibre. -/
theorem sectionLinearEquiv_symm_fibreTensor (j : κ) (U : Opens N)
    (hU : (U : Set N) ⊆ B.baseSet j)
    (s : NativeBundleSections.Section A.core I (preimageOpen f hf.continuous U))
    (x : preimageOpen f hf.continuous U) :
    letI : (pullback B f hf.continuous).IsHolomorphic I :=
      pullback_isHolomorphic B f hf.continuous I J hf
    letI := baseModule (tensor A (pullback B f hf.continuous)).core I J f hf U
    letI := baseModule A.core I J f hf U
    (sectionLinearEquiv A B I J f hf j U hU).symm s x =
      fibreTensorEquiv A (pullback B f hf.continuous) x.val
        (s x ⊗ₜ[ℂ] pulledFrame B f hf.continuous j x.val) :=
  unTensorFiberEquiv_symm A B f hf.continuous j x.val (hU x.property) (s x)

/-- The original base transition as an actual holomorphic scalar function on the overlap open. -/
def chartTransition (j k : κ) (U : Opens N)
    (hj : (U : Set N) ⊆ B.baseSet j) (hk : (U : Set N) ⊆ B.baseSet k) :
    HolomorphicFunctionSheaf.Section J N U :=
  ⟨fun p => (B.transition j k p.val : ℂ), by
    intro p
    exact ((B.transition_holomorphic J j k).contMDiffAt
      (((B.isOpen_baseSet j).inter (B.isOpen_baseSet k)).mem_nhds
        ⟨hj p.property, hk p.property⟩)).comp p contMDiff_subtype_val.contMDiffAt⟩

@[simp] theorem chartTransition_apply (j k : κ) (U : Opens N)
    (hj : (U : Set N) ⊆ B.baseSet j) (hk : (U : Set N) ⊆ B.baseSet k) (p : U) :
    chartTransition B J j k U hj hk p = (B.transition j k p.val : ℂ) := rfl

theorem chartTransition_ne_zero (j k : κ) (U : Opens N)
    (hj : (U : Set N) ⊆ B.baseSet j) (hk : (U : Set N) ⊆ B.baseSet k) (p : U) :
    chartTransition B J j k U hj hk p ≠ 0 := (B.transition j k p.val).ne_zero

/-- The exact change of base frame, with the forward transition and actual base scalar action. -/
theorem sectionLinearEquiv_change (j k : κ) (U : Opens N)
    (hj : (U : Set N) ⊆ B.baseSet j) (hk : (U : Set N) ⊆ B.baseSet k)
    (s : NativeBundleSections.Section (tensor A (pullback B f hf.continuous)).core I
      (preimageOpen f hf.continuous U)) :
    letI : (pullback B f hf.continuous).IsHolomorphic I :=
      pullback_isHolomorphic B f hf.continuous I J hf
    letI := baseModule A.core I J f hf U
    sectionLinearEquiv A B I J f hf k U hk s =
      chartTransition B J j k U hj hk • sectionLinearEquiv A B I J f hf j U hj s := by
  let : (pullback B f hf.continuous).IsHolomorphic I :=
    pullback_isHolomorphic B f hf.continuous I J hf
  let := baseModule A.core I J f hf U
  apply NativeBundleSections.Section.ext A.core I
  intro x
  exact unTensorFiberEquiv_change A B f hf.continuous j k x.val
    (hj x.property) (hk x.property) (s x)

/-- Local comparison commutes with actual restriction on the base and on its full preimage. -/
theorem sectionLinearEquiv_restrict (j : κ) {U V : Opens N} (hUV : U ≤ V)
    (hU : (U : Set N) ⊆ B.baseSet j) (hV : (V : Set N) ⊆ B.baseSet j)
    (s : NativeBundleSections.Section (tensor A (pullback B f hf.continuous)).core I
      (preimageOpen f hf.continuous V)) :
    NativeBundleSections.Section.restrict A.core I (preimageOpen_mono f hf.continuous hUV)
        (sectionLinearEquiv A B I J f hf j V hV s) =
      sectionLinearEquiv A B I J f hf j U hU
        (NativeBundleSections.Section.restrict (tensor A (pullback B f hf.continuous)).core I
          (preimageOpen_mono f hf.continuous hUV) s) := by
  apply NativeBundleSections.Section.ext A.core I
  intro x
  rfl

theorem sectionLinearEquiv_symm_restrict (j : κ) {U V : Opens N} (hUV : U ≤ V)
    (hU : (U : Set N) ⊆ B.baseSet j) (hV : (V : Set N) ⊆ B.baseSet j)
    (s : NativeBundleSections.Section A.core I (preimageOpen f hf.continuous V)) :
    letI : (pullback B f hf.continuous).IsHolomorphic I :=
      pullback_isHolomorphic B f hf.continuous I J hf
    letI := baseModule (tensor A (pullback B f hf.continuous)).core I J f hf U
    letI := baseModule A.core I J f hf U
    letI := baseModule (tensor A (pullback B f hf.continuous)).core I J f hf V
    letI := baseModule A.core I J f hf V
    NativeBundleSections.Section.restrict (tensor A (pullback B f hf.continuous)).core I
        (preimageOpen_mono f hf.continuous hUV)
        ((sectionLinearEquiv A B I J f hf j V hV).symm s) =
      (sectionLinearEquiv A B I J f hf j U hU).symm
        (NativeBundleSections.Section.restrict A.core I
          (preimageOpen_mono f hf.continuous hUV) s) := by
  let : (pullback B f hf.continuous).IsHolomorphic I :=
    pullback_isHolomorphic B f hf.continuous I J hf
  let := baseModule (tensor A (pullback B f hf.continuous)).core I J f hf U
  let := baseModule A.core I J f hf U
  let := baseModule (tensor A (pullback B f hf.continuous)).core I J f hf V
  let := baseModule A.core I J f hf V
  apply NativeBundleSections.Section.ext (tensor A (pullback B f hf.continuous)).core I
  intro x
  rfl

end Wikipedia.HopfProblem.CanonicalGlobalLineBundle.TensorLocal
