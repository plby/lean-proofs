import Wikipedia.HopfProblem.HolomorphicCharacterBundleCore
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Tensor products of general holomorphic line-bundle cocycles

Two variable multiplicative cocycles on possibly different open covers
give their tensor cocycle on the intersection cover.  The resulting
`TransitionData.core` is an actual analytic line bundle, and multiplication
of scalar fibre coordinates identifies its fibres with the algebraic
tensor products of the original fibres.  Full linear-map identities show
compatibility with the original transition maps and local trivializations.
Neither factor is required to be flat or globally trivial.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff TensorProduct

namespace Wikipedia.HopfProblem.CanonicalGlobalLineBundle

open HolomorphicCharacterBundle

variable {M ι κ : Type*} [TopologicalSpace M]

/-- The tensor cocycle on the paired intersection cover. -/
def tensor (A : TransitionData M ι) (B : TransitionData M κ) :
    TransitionData M (ι × κ) where
  baseSet i := A.baseSet i.1 ∩ B.baseSet i.2
  isOpen_baseSet i := (A.isOpen_baseSet i.1).inter (B.isOpen_baseSet i.2)
  indexAt x := (A.indexAt x, B.indexAt x)
  mem_baseSet_at x := ⟨A.mem_baseSet_at x, B.mem_baseSet_at x⟩
  transition i j x := A.transition i.1 j.1 x * B.transition i.2 j.2 x
  transition_self i x hx := by
    rw [A.transition_self i.1 x hx.1, B.transition_self i.2 x hx.2, mul_one]
  transition_comp i j k x hx := by
    calc
      (A.transition j.1 k.1 x * B.transition j.2 k.2 x) *
          (A.transition i.1 j.1 x * B.transition i.2 j.2 x) =
          (A.transition j.1 k.1 x * A.transition i.1 j.1 x) *
            (B.transition j.2 k.2 x * B.transition i.2 j.2 x) := by ac_rfl
      _ = A.transition i.1 k.1 x * B.transition i.2 k.2 x := by
        rw [A.transition_comp i.1 j.1 k.1 x ⟨⟨hx.1.1.1, hx.1.2.1⟩, hx.2.1⟩,
          B.transition_comp i.2 j.2 k.2 x ⟨⟨hx.1.1.2, hx.1.2.2⟩, hx.2.2⟩]
  continuousOn_transition i j :=
    ((A.continuousOn_transition i.1 j.1).mono (fun _ hx => ⟨hx.1.1, hx.2.1⟩)).mul
      ((B.continuousOn_transition i.2 j.2).mono (fun _ hx => ⟨hx.1.2, hx.2.2⟩))

variable (A : TransitionData M ι) (B : TransitionData M κ)

@[simp] theorem tensor_baseSet (i : ι × κ) :
    (tensor A B).baseSet i = A.baseSet i.1 ∩ B.baseSet i.2 := rfl

@[simp] theorem tensor_indexAt (x : M) :
    (tensor A B).indexAt x = (A.indexAt x, B.indexAt x) := rfl

@[simp] theorem tensor_transition (i j : ι × κ) (x : M) :
    (tensor A B).transition i j x = A.transition i.1 j.1 x * B.transition i.2 j.2 x :=
  rfl

/-- A full continuous-linear-map identity for the tensor cocycle. -/
theorem tensor_core_coordChange (i j : ι × κ) (x : M) :
    (tensor A B).core.coordChange i j x =
      (A.core.coordChange i.1 j.1 x).comp (B.core.coordChange i.2 j.2 x) := by
  apply ContinuousLinearMap.ext
  intro v
  change ((A.transition i.1 j.1 x : ℂ) * (B.transition i.2 j.2 x : ℂ)) * v =
    (A.transition i.1 j.1 x : ℂ) * ((B.transition i.2 j.2 x : ℂ) * v)
  exact mul_assoc _ _ _

section Holomorphic

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  [ChartedSpace H M] (I : ModelWithCorners ℂ E H)

/-- Restriction to the intersection cover preserves holomorphicity of the
variable transition functions, and their product is holomorphic. -/
instance tensor_isHolomorphic [A.IsHolomorphic I] [B.IsHolomorphic I] :
    (tensor A B).IsHolomorphic I where
  contMDiffOn_transition i j :=
    ((A.transition_holomorphic I i.1 j.1).mono (fun _ hx => ⟨hx.1.1, hx.2.1⟩)).mul
      ((B.transition_holomorphic I i.2 j.2).mono (fun _ hx => ⟨hx.1.2, hx.2.2⟩))

theorem tensor_holomorphicVectorBundle [A.IsHolomorphic I] [B.IsHolomorphic I] :
    ContMDiffVectorBundle ω ℂ (tensor A B).core.Fiber I := inferInstance

theorem tensor_totalSpace_isManifold [A.IsHolomorphic I] [B.IsHolomorphic I]
    [IsManifold I ω M] :
    IsManifold (I.prod (modelWithCornersSelf ℂ ℂ)) ω (tensor A B).core.TotalSpace :=
  inferInstance

end Holomorphic

/-- The tensor-cocycle fibre is the algebraic tensor product of the two
actual original fibres, by multiplication of their scalar coordinates. -/
def fibreTensorEquiv (x : M) :
    A.core.Fiber x ⊗[ℂ] B.core.Fiber x ≃ₗ[ℂ] (tensor A B).core.Fiber x :=
  TensorProduct.lid ℂ ℂ

@[simp] theorem fibreTensorEquiv_tmul (x : M)
    (z : A.core.Fiber x) (w : B.core.Fiber x) :
    fibreTensorEquiv A B x (z ⊗ₜ[ℂ] w) = (id (α := ℂ) z) * (id (α := ℂ) w) :=
  TensorProduct.lid_tmul (R := ℂ) (M := ℂ) w z

/-- Compatibility with tensor products of the original transition maps
on the full tensor product, not only on elementary tensors. -/
theorem fibreTensorEquiv_coordChange (i j : ι × κ) (x : M) :
    (fibreTensorEquiv A B x).toLinearMap ∘ₗ
        TensorProduct.map (A.core.coordChange i.1 j.1 x).toLinearMap
          (B.core.coordChange i.2 j.2 x).toLinearMap =
      ((tensor A B).core.coordChange i j x).toLinearMap ∘ₗ
        (fibreTensorEquiv A B x).toLinearMap := by
  apply TensorProduct.ext'
  intro z w
  change (TensorProduct.lid ℂ ℂ)
      ((A.core.coordChange i.1 j.1 x z) ⊗ₜ[ℂ] (B.core.coordChange i.2 j.2 x w)) =
    (tensor A B).core.coordChange i j x ((TensorProduct.lid ℂ ℂ) (z ⊗ₜ[ℂ] w))
  simp only [TensorProduct.lid_tmul, smul_eq_mul, TransitionData.core_coordChange_apply,
    tensor_transition, Units.val_mul]
  ring

/-- The actual paired local trivialization intertwines the full fibre
tensor equivalence with the tensor product of the original trivializations. -/
theorem fibreTensorEquiv_localTriv (i : ι × κ) (x : M)
    (hx : x ∈ A.baseSet i.1 ∩ B.baseSet i.2) :
    ((tensor A B).core.localTriv i).linearMapAt ℂ x ∘ₗ
        (fibreTensorEquiv A B x).toLinearMap =
      (TensorProduct.lid ℂ ℂ).toLinearMap ∘ₗ
        TensorProduct.map ((A.core.localTriv i.1).linearMapAt ℂ x)
          ((B.core.localTriv i.2).linearMapAt ℂ x) := by
  apply TensorProduct.ext'
  intro z w
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_toLinearMap,
    fibreTensorEquiv_tmul]
  rw [Trivialization.coe_linearMapAt_of_mem _ hx,
    Trivialization.coe_linearMapAt_of_mem _ hx.1,
    Trivialization.coe_linearMapAt_of_mem _ hx.2]
  simp only [TransitionData.core_localTriv_apply, tensor_indexAt, tensor_transition,
    Units.val_mul, TensorProduct.lid_tmul, smul_eq_mul, id_eq]
  ring

end Wikipedia.HopfProblem.CanonicalGlobalLineBundle
