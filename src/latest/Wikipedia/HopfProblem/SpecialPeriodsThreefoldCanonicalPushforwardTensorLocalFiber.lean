import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundleTensor
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundlePullback
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundleOpenMaps

/-!
# Actual local contraction of a pulled-back line factor

The contraction reads the original base line in one of its genuine
native local trivializations. The input is the original native tensor
cocycle, and the full fibre tensor equivalence identifies contraction
with evaluation on that factor. Its inverse tensors with the actual
unit frame obtained from the original local trivialization.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff TensorProduct

namespace Wikipedia.HopfProblem.CanonicalGlobalLineBundle.TensorLocal

open HolomorphicCharacterBundle

variable {M N : Type} {ι κ : Type*} [TopologicalSpace M] [TopologicalSpace N]
  (A : TransitionData M ι) (B : TransitionData N κ) (f : M → N) (hf : Continuous f)

/-- This is the actual coefficient multiplier of the original base chart. -/
def contractionMultiplier (j : κ) (x : M) : ℂˣ :=
  B.transition (B.indexAt (f x)) j (f x)

/-- Contraction on the original native tensor fibre is complex-linearly invertible. -/
def unTensorFiberEquiv (j : κ) (x : M) :
    (tensor A (pullback B f hf)).core.Fiber x ≃L[ℂ] A.core.Fiber x :=
  OpenMaps.fiberEquiv (tensor A (pullback B f hf)) A (contractionMultiplier B f j) x

@[simp] theorem unTensorFiberEquiv_apply (j : κ) (x : M)
    (v : (tensor A (pullback B f hf)).core.Fiber x) :
    unTensorFiberEquiv A B f hf j x v =
      (contractionMultiplier B f j x : ℂ) * id (α := ℂ) v := rfl

/-- The native total-space contraction map, without changing either atlas. -/
def unTensorMap (j : κ) (p : (tensor A (pullback B f hf)).core.TotalSpace) :
    A.core.TotalSpace := ⟨p.proj, unTensorFiberEquiv A B f hf j p.proj p.2⟩

/-- The inverse map on the same original native fibres. -/
def tensorMap (j : κ) (p : A.core.TotalSpace) :
    (tensor A (pullback B f hf)).core.TotalSpace :=
  ⟨p.proj, (unTensorFiberEquiv A B f hf j p.proj).symm p.2⟩

@[simp] theorem unTensorMap_proj (j : κ)
    (p : (tensor A (pullback B f hf)).core.TotalSpace) :
    (unTensorMap A B f hf j p).proj = p.proj := rfl

@[simp] theorem tensorMap_proj (j : κ) (p : A.core.TotalSpace) :
    (tensorMap A B f hf j p).proj = p.proj := rfl

@[simp] theorem unTensorMap_mk (j : κ) (x : M)
    (v : (tensor A (pullback B f hf)).core.Fiber x) :
    unTensorMap A B f hf j ⟨x, v⟩ = ⟨x, unTensorFiberEquiv A B f hf j x v⟩ := rfl

@[simp] theorem tensorMap_mk (j : κ) (x : M) (v : A.core.Fiber x) :
    tensorMap A B f hf j ⟨x, v⟩ =
      ⟨x, (unTensorFiberEquiv A B f hf j x).symm v⟩ := rfl

@[simp] theorem unTensorMap_tensorMap (j : κ) (p : A.core.TotalSpace) :
    unTensorMap A B f hf j (tensorMap A B f hf j p) = p := by
  cases p with
  | mk x v =>
    change (⟨x, unTensorFiberEquiv A B f hf j x
      ((unTensorFiberEquiv A B f hf j x).symm v)⟩ : A.core.TotalSpace) = ⟨x, v⟩
    rw [ContinuousLinearEquiv.apply_symm_apply]

@[simp] theorem tensorMap_unTensorMap (j : κ)
    (p : (tensor A (pullback B f hf)).core.TotalSpace) :
    tensorMap A B f hf j (unTensorMap A B f hf j p) = p := by
  cases p with
  | mk x v =>
    change (⟨x, (unTensorFiberEquiv A B f hf j x).symm
      (unTensorFiberEquiv A B f hf j x v)⟩ :
        (tensor A (pullback B f hf)).core.TotalSpace) = ⟨x, v⟩
    rw [ContinuousLinearEquiv.symm_apply_apply]

/-- In the original paired chart `(i,j)` and original chart `i`, the map preserves coefficients. -/
theorem unTensorMap_localTriv (i : ι) (j : κ)
    (p : (tensor A (pullback B f hf)).core.TotalSpace) :
    (A.core.localTriv i (unTensorMap A B f hf j p)).2 =
      ((tensor A (pullback B f hf)).core.localTriv (i, j) p).2 := by
  change (A.transition (A.indexAt p.proj) i p.proj : ℂ) *
      ((B.transition (B.indexAt (f p.proj)) j (f p.proj) : ℂ) * id (α := ℂ) p.2) =
    ((A.transition (A.indexAt p.proj) i p.proj : ℂ) *
      (B.transition (B.indexAt (f p.proj)) j (f p.proj) : ℂ)) * id (α := ℂ) p.2
  exact (mul_assoc _ _ _).symm

theorem tensorMap_localTriv (i : ι) (j : κ) (p : A.core.TotalSpace) :
    ((tensor A (pullback B f hf)).core.localTriv (i, j) (tensorMap A B f hf j p)).2 =
      (A.core.localTriv i p).2 := by
  have h := unTensorMap_localTriv A B f hf i j (tensorMap A B f hf j p)
  rw [unTensorMap_tensorMap] at h
  exact h.symm

/-- The elementary-tensor formula uses the actual full fibre tensor equivalence and base chart. -/
theorem unTensorFiberEquiv_tmul (j : κ) (x : M)
    (a : A.core.Fiber x) (b : (pullback B f hf).core.Fiber x) :
    unTensorFiberEquiv A B f hf j x
      (fibreTensorEquiv A (pullback B f hf) x (a ⊗ₜ[ℂ] b)) =
        (B.core.localTriv j ⟨f x, pullbackFiberEquiv B f hf x b⟩).2 • a := by
  rw [unTensorFiberEquiv_apply, fibreTensorEquiv_tmul]
  change (B.transition (B.indexAt (f x)) j (f x) : ℂ) *
      (id (α := ℂ) a * id (α := ℂ) b) =
    ((B.transition (B.indexAt (f x)) j (f x) : ℂ) * id (α := ℂ) b) * id (α := ℂ) a
  ring

/-- The full tensor-product contraction reads the pulled-back factor in the original chart. -/
def fibreContraction (j : κ) (x : M) :
    A.core.Fiber x ⊗[ℂ] (pullback B f hf).core.Fiber x →ₗ[ℂ] A.core.Fiber x :=
  (TensorProduct.rid ℂ (A.core.Fiber x)).toLinearMap ∘ₗ
    TensorProduct.map (LinearMap.id : A.core.Fiber x →ₗ[ℂ] A.core.Fiber x)
      (((B.core.localTriv j).linearMapAt ℂ (f x)) ∘ₗ
        (pullbackFiberEquiv B f hf x).toLinearEquiv.toLinearMap)

/-- A genuine equality of linear maps on the entire fibre tensor product. -/
theorem unTensorFiberEquiv_fibreTensorEquiv (j : κ) (x : M)
    (hx : f x ∈ B.baseSet j) :
    (unTensorFiberEquiv A B f hf j x).toLinearEquiv.toLinearMap ∘ₗ
      (fibreTensorEquiv A (pullback B f hf) x).toLinearMap =
        fibreContraction A B f hf j x := by
  apply TensorProduct.ext'
  intro a b
  simp only [fibreContraction, LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, LinearEquiv.coe_toLinearMap, TensorProduct.rid_tmul]
  rw [Trivialization.coe_linearMapAt_of_mem _ hx]
  exact unTensorFiberEquiv_tmul A B f hf j x a b

/-- The original base chart's unit vector, pulled back by the genuine fibre identification. -/
def pulledFrame (j : κ) (x : M) : (pullback B f hf).core.Fiber x :=
  (pullbackFiberEquiv B f hf x).symm (OpenMaps.localFrame B j (f x))

/-- The inverse contraction tensors with this actual native unit frame. -/
theorem unTensorFiberEquiv_symm (j : κ) (x : M) (hx : f x ∈ B.baseSet j)
    (a : A.core.Fiber x) :
    (unTensorFiberEquiv A B f hf j x).symm a =
      fibreTensorEquiv A (pullback B f hf) x (a ⊗ₜ[ℂ] pulledFrame B f hf j x) := by
  apply (unTensorFiberEquiv A B f hf j x).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, unTensorFiberEquiv_tmul]
  have hframe : (B.core.localTriv j
      ⟨f x, pullbackFiberEquiv B f hf x (pulledFrame B f hf j x)⟩).2 = 1 := by
    change (B.core.localTriv j (OpenMaps.localFrameMap B j (f x))).2 = 1
    exact congrArg Prod.snd (OpenMaps.localFrame_localTriv B j hx)
  rw [hframe, one_smul]

/-- Changing the original base chart multiplies contraction by the forward transition unit. -/
theorem unTensorFiberEquiv_change (j k : κ) (x : M)
    (hj : f x ∈ B.baseSet j) (hk : f x ∈ B.baseSet k)
    (v : (tensor A (pullback B f hf)).core.Fiber x) :
    unTensorFiberEquiv A B f hf k x v =
      (B.transition j k (f x) : ℂ) • unTensorFiberEquiv A B f hf j x v := by
  have h := B.transition_comp (B.indexAt (f x)) j k (f x)
    ⟨⟨B.mem_baseSet_at (f x), hj⟩, hk⟩
  have hv := congrArg (fun u : ℂˣ => (u : ℂ)) h
  change (B.transition j k (f x) : ℂ) *
    (B.transition (B.indexAt (f x)) j (f x) : ℂ) =
      (B.transition (B.indexAt (f x)) k (f x) : ℂ) at hv
  change (B.transition (B.indexAt (f x)) k (f x) : ℂ) * id (α := ℂ) v =
    (B.transition j k (f x) : ℂ) *
      ((B.transition (B.indexAt (f x)) j (f x) : ℂ) * id (α := ℂ) v)
  rw [← hv, mul_assoc]

end Wikipedia.HopfProblem.CanonicalGlobalLineBundle.TensorLocal
