import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundleRefinementGauge
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundleTensor

/-!
# Tensoring genuine cross-cover bundle comparisons

A holomorphic fibre-linear comparison of two native cocycle bundles
induces one after tensoring with another actual line bundle.  Its maps
on the full fibre tensor products are the tensor products of the
original maps.  The construction preserves the original open covers
and their actual chart transition maps.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff TensorProduct

namespace Wikipedia.HopfProblem.CanonicalGlobalLineBundle.CrossGauge

open HolomorphicCharacterBundle

variable {M ι κ ν : Type*} [TopologicalSpace M]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  [ChartedSpace H M] {I : ModelWithCorners ℂ E H}
  {A : TransitionData M ι} {B : TransitionData M κ}
  (G : CrossGauge I A B) (C : TransitionData M ν)

/-- Tensoring an actual comparison on the right factor, without
requiring either cover to be replaced by the other's preferred charts. -/
def tensorLeft [C.IsHolomorphic I] : CrossGauge I (tensor C A) (tensor C B) where
  value i x := C.transition i.1.1 i.2.1 x * G.value (i.1.2, i.2.2) x
  compatible i j x hx := by
    have hC : C.transition i.2.1 j.2.1 x * C.transition i.1.1 i.2.1 x =
        C.transition j.1.1 j.2.1 x * C.transition i.1.1 j.1.1 x :=
      (C.transition_comp i.1.1 i.2.1 j.2.1 x
        ⟨⟨hx.1.1.1, hx.1.2.1⟩, hx.2.2.1⟩).trans
          (C.transition_comp i.1.1 j.1.1 j.2.1 x
            ⟨⟨hx.1.1.1, hx.2.1.1⟩, hx.2.2.1⟩).symm
    have hG := G.compatible (i.1.2, i.2.2) (j.1.2, j.2.2) x
      ⟨⟨hx.1.1.2, hx.1.2.2⟩, ⟨hx.2.1.2, hx.2.2.2⟩⟩
    change (C.transition i.2.1 j.2.1 x * B.transition i.2.2 j.2.2 x) *
        (C.transition i.1.1 i.2.1 x * G.value (i.1.2, i.2.2) x) =
      (C.transition j.1.1 j.2.1 x * G.value (j.1.2, j.2.2) x) *
        (C.transition i.1.1 j.1.1 x * A.transition i.1.2 j.1.2 x)
    calc
      _ = (C.transition i.2.1 j.2.1 x * C.transition i.1.1 i.2.1 x) *
          (B.transition i.2.2 j.2.2 x * G.value (i.1.2, i.2.2) x) := by ac_rfl
      _ = (C.transition j.1.1 j.2.1 x * C.transition i.1.1 j.1.1 x) *
          (G.value (j.1.2, j.2.2) x * A.transition i.1.2 j.1.2 x) := by rw [hC, hG]
      _ = _ := by ac_rfl
  holomorphicOn i := by
    change ContMDiffOn I (modelWithCornersSelf ℂ ℂ) ω
      (fun x => (C.transition i.1.1 i.2.1 x : ℂ) * (G.value (i.1.2, i.2.2) x : ℂ))
      ((C.baseSet i.1.1 ∩ A.baseSet i.1.2) ∩ (C.baseSet i.2.1 ∩ B.baseSet i.2.2))
    exact ((C.transition_holomorphic I i.1.1 i.2.1).mono
      (fun _ hx => ⟨hx.1.1, hx.2.1⟩)).mul
        ((G.holomorphicOn (i.1.2, i.2.2)).mono (fun _ hx => ⟨hx.1.2, hx.2.2⟩))

/-- In the preferred fibres the extra factor is left unchanged. -/
theorem tensorLeft_fiberEquiv_apply [C.IsHolomorphic I] (x : M)
    (v : (tensor C A).core.Fiber x) :
    (G.tensorLeft C).fiberEquiv x v =
      (G.value (A.indexAt x, B.indexAt x) x : ℂ) * id (α := ℂ) v := by
  rw [fiberEquiv_apply]
  change (C.transition (C.indexAt x) (C.indexAt x) x *
      G.value (A.indexAt x, B.indexAt x) x : ℂˣ) * id (α := ℂ) v = _
  rw [C.transition_self _ _ (C.mem_baseSet_at x), one_mul]

/-- The genuine fibre equivalences intertwine the actual map with
the tensor product of the identity and the original fibre map. -/
theorem tensorLeft_fibreTensorEquiv_tmul [C.IsHolomorphic I] (x : M)
    (c : C.core.Fiber x) (a : A.core.Fiber x) :
    (G.tensorLeft C).fiberEquiv x (fibreTensorEquiv C A x (c ⊗ₜ[ℂ] a)) =
      fibreTensorEquiv C B x (c ⊗ₜ[ℂ] G.fiberEquiv x a) := by
  rw [tensorLeft_fiberEquiv_apply, fibreTensorEquiv_tmul, fibreTensorEquiv_tmul,
    G.fiberEquiv_apply]
  change (G.value (A.indexAt x, B.indexAt x) x : ℂ) *
      (id (α := ℂ) c * id (α := ℂ) a) =
    id (α := ℂ) c * ((G.value (A.indexAt x, B.indexAt x) x : ℂ) * id (α := ℂ) a)
  exact mul_left_comm _ _ _

/-- Equality on the full algebraic tensor product, not just the
chosen frame or elementary tensor values. -/
theorem tensorLeft_fibreTensorEquiv [C.IsHolomorphic I] (x : M) :
    ((G.tensorLeft C).fiberEquiv x).toLinearMap ∘ₗ (fibreTensorEquiv C A x).toLinearMap =
      (fibreTensorEquiv C B x).toLinearMap ∘ₗ
        TensorProduct.map (LinearMap.id : C.core.Fiber x →ₗ[ℂ] C.core.Fiber x)
          (G.fiberEquiv x).toLinearMap := by
  apply TensorProduct.ext'
  intro c a
  exact G.tensorLeft_fibreTensorEquiv_tmul C x c a

end Wikipedia.HopfProblem.CanonicalGlobalLineBundle.CrossGauge
