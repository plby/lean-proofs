import Wikipedia.NoExoticSixSphere.PartialFrameBlockExtension
import Wikipedia.NoExoticSixSphere.InjectiveOperatorExtensionCoordinates
import Wikipedia.NoExoticSixSphere.ManifoldFrameBlockCoordinates

/-!
# Identity columns preserve extension of the original injective operators

Normalization gives a homotopy, not an assumed equality of matrices. The
actual block construction transports this homotopy, reducing the extension
comparison to the checked partial-frame stabilization theorem.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.Monomorphism

open GLOrthonormalization DiskBoundary FrameBlockCoordinates

theorem blockOperator_injective {N n : ℕ} (m : ℕ) (A : Space N n) :
    Function.Injective (BlockSum.operator m A.val) := by
  intro v w h
  apply (EuclideanSpace.finAddEquivProd (n := n) (m := m)).injective
  have he := congrArg (EuclideanSpace.finAddEquivProd (n := N) (m := m)) h
  simp only [BlockSum.operator_apply, ContinuousLinearEquiv.apply_symm_apply] at he
  have hf := congrArg (fun p : Vector N × Vector m ↦ p.1) he
  have hs := congrArg (fun p : Vector N × Vector m ↦ p.2) he
  exact Prod.ext (A.property hf) hs

def blockMap {N n : ℕ} (m : ℕ) : C(Space N n, Space (N + m) (n + m)) where
  toFun A := ⟨BlockSum.operator m A.val, blockOperator_injective m A⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_clm_apply.mpr
    intro w
    exact EuclideanSpace.finAddEquivProd.symm.continuous.comp
      ((continuous_subtype_val.clm_apply continuous_const).prodMk continuous_const)

theorem blockMap_inclusion {N n : ℕ} (m : ℕ) (A : Stiefel.Space N n) :
    blockMap m (inclusion N n A) = inclusion (N + m) (n + m) (BlockSum.frame m A) := rfl

theorem extends_blockMap_iff {N n : ℕ} (hn : 2 ≤ n) (hN : N = 3 + n)
    (m : ℕ) (f : C(Sphere 3, Space N n)) : Extends ((blockMap m).comp f) ↔ Extends f := by
  let F := (normalize N n).comp f
  have h : ((blockMap m).comp f).Homotopic
      ((inclusion (N + m) (n + m)).comp ((BlockSum.map m).comp F)) := by
    let H := (normalizationHomotopy N n).compContinuousMap f
    have Hm : ((blockMap m).comp f).Homotopy
        ((blockMap m).comp (((inclusion N n).comp (normalize N n)).comp f)) :=
      (ContinuousMap.Homotopy.refl (blockMap m)).comp H
    have he : (blockMap m).comp (((inclusion N n).comp (normalize N n)).comp f) =
        (inclusion (N + m) (n + m)).comp ((BlockSum.map m).comp F) := by
      apply ContinuousMap.ext
      intro s
      exact blockMap_inclusion m (normalize N n (f s))
    exact ⟨Hm.cast rfl he⟩
  rw [extends_homotopic_iff h, extends_inclusion_iff,
    BlockSum.extends_block_iff hn hN]
  exact extends_normalize_iff f

def frontBlockMap {N n : ℕ} (m : ℕ) : C(Space N n, Space (m + N) (m + n)) where
  toFun A := ⟨identityBlockOperator m A.val, identityBlockOperator_injective m A.val A.property⟩
  continuous_toFun := (continuous_identityBlockOperator m
    (fun A : Space N n ↦ A.val) continuous_subtype_val).subtype_mk _

def blockSwap (n m : ℕ) : Vector (n + m) ≃L[ℝ] Vector (m + n) :=
  EuclideanSpace.finAddEquivProd.trans
    ((ContinuousLinearEquiv.prodComm ℝ (Vector n) (Vector m)).trans
      EuclideanSpace.finAddEquivProd.symm)

theorem blockSwap_apply (n m : ℕ) (v : Vector (n + m)) :
    blockSwap n m v = EuclideanSpace.finAddEquivProd.symm
      ((EuclideanSpace.finAddEquivProd v).2, (EuclideanSpace.finAddEquivProd v).1) := rfl

theorem frontBlockMap_recoordinate {N n : ℕ} (m : ℕ) (A : Space N n) :
    frontBlockMap m A = recoordinate (blockSwap N m) (blockSwap m n) (blockMap m A) := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro v
  change identityBlockOperator m A.val v =
    blockSwap N m (BlockSum.operator m A.val (blockSwap m n v))
  simp only [identityBlockOperator_apply, blockSwap_apply, BlockSum.operator_apply,
    ContinuousLinearEquiv.apply_symm_apply]

theorem extends_frontBlockMap_iff {N n : ℕ} (hn : 2 ≤ n) (hN : N = 3 + n)
    (m : ℕ) (f : C(Sphere 3, Space N n)) : Extends ((frontBlockMap m).comp f) ↔ Extends f := by
  have he : Extends ((frontBlockMap m).comp f) ↔ Extends ((blockMap m).comp f) :=
    extends_recoordinate_iff (fun _ ↦ blockSwap N m) (fun _ ↦ blockSwap m n)
      continuous_const continuous_const continuous_const continuous_const
      ((blockMap m).comp f) ((frontBlockMap m).comp f)
      (fun s ↦ frontBlockMap_recoordinate m (f s))
  exact he.trans (extends_blockMap_iff hn hN m f)

end NoExoticSixSphere.Stiefel.Monomorphism
