import Wikipedia.NoExoticSixSphere.OrthogonalFrameAppendStabilization
import Wikipedia.NoExoticSixSphere.PartialFrameBlockIteration

/-!
# Exact Euclidean block identities for composing framed comparisons

The associator and block extensions are actual linear isometries. These
identities combine two stabilizations while retaining the actual zero
inclusion and every normal-frame column.
-/

noncomputable section

namespace NoExoticSixSphere.FramedBlock

open GLOrthonormalization Stiefel OrthogonalFrameAppend

def coordinates (k a b : ℕ) : Vector ((k + a) + b) ≃L[ℝ] Vector (k + (a + b)) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := k + a) (m := b)).trans
    (((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := k) (m := a)).prodCongr
      (ContinuousLinearEquiv.refl ℝ (Vector b))).trans
        ((ContinuousLinearEquiv.prodAssoc ℝ (Vector k) (Vector a) (Vector b)).trans
          (((ContinuousLinearEquiv.refl ℝ (Vector k)).prodCongr
            (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := a) (m := b)).symm).trans
              EuclideanSpace.finAddEquivProd.symm)))

theorem coordinates_apply (k a b : ℕ) (v : Vector ((k + a) + b)) :
    coordinates k a b v = EuclideanSpace.finAddEquivProd.symm
      ((EuclideanSpace.finAddEquivProd (EuclideanSpace.finAddEquivProd v).1).1,
        EuclideanSpace.finAddEquivProd.symm
          ((EuclideanSpace.finAddEquivProd (EuclideanSpace.finAddEquivProd v).1).2,
            (EuclideanSpace.finAddEquivProd v).2)) := rfl

theorem inner_coordinates (k a b : ℕ) (u v : Vector ((k + a) + b)) :
    inner ℝ (coordinates k a b u) (coordinates k a b v) = inner ℝ u v := by
  rw [coordinates_apply, coordinates_apply, inner_finAdd_symm, inner_finAdd_symm,
    inner_finAdd_split u v,
    inner_finAdd_split (EuclideanSpace.finAddEquivProd u).1
      (EuclideanSpace.finAddEquivProd v).1]
  ring

def associator (k a b : ℕ) : Vector ((k + a) + b) ≃ₗᵢ[ℝ] Vector (k + (a + b)) where
  toLinearEquiv := (coordinates k a b).toLinearEquiv
  norm_map' v := by
    change ‖coordinates k a b v‖ = ‖v‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simpa only [real_inner_self_eq_norm_sq] using inner_coordinates k a b v v

theorem associator_apply (k a b : ℕ) (v : Vector ((k + a) + b)) :
    associator k a b v = coordinates k a b v := rfl

theorem operator_assoc {N k : ℕ} (a b : ℕ) (F : Vector k →L[ℝ] Vector N)
    (v : Vector ((k + a) + b)) :
    associator N a b (BlockSum.operator b (BlockSum.operator a F) v) =
      BlockSum.operator (a + b) F (associator k a b v) := by
  simp only [associator_apply, coordinates_apply, BlockSum.operator_apply,
    ContinuousLinearEquiv.apply_symm_apply]

theorem appendZero_split (N k : ℕ) (v : Vector N) :
    EuclideanSpace.finAddEquivProd (appendZeroMap N k v) = (v, (0 : Vector k)) :=
  EuclideanSpace.finAddEquivProd.apply_symm_apply (v, 0)

theorem appendZero_zero (N : ℕ) (v : Vector N) : appendZeroMap N 0 v = v := by
  ext i
  change EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 0)) (i.castAdd 0) = v i
  exact EuclideanBlocks.symm_castAdd v 0 i

theorem appendZero_assoc (N a b : ℕ) (v : Vector N) :
    associator N a b (appendZeroMap (N + a) b (appendZeroMap N a v)) =
      appendZeroMap N (a + b) v := by
  simp only [associator_apply, coordinates_apply, appendZero_split]
  change EuclideanSpace.finAddEquivProd.symm
    (v, EuclideanSpace.finAddEquivProd.symm ((0 : Vector a), (0 : Vector b))) =
      EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector (a + b)))
  simp

theorem extend_appendZero {N L : ℕ} (J : Vector N ≃ₗᵢ[ℝ] Vector L) (b : ℕ) (v : Vector N) :
    extendColumnChange J b (appendZeroMap N b v) = appendZeroMap L b (J v) := by
  apply (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := L) (m := b)).injective
  rw [extendColumnChange_split, appendZero_split, appendZero_split]

theorem block_natural {N L k l : ℕ} (b : ℕ)
    (F : Vector k →L[ℝ] Vector N) (G : Vector l →L[ℝ] Vector L)
    (J : Vector N ≃ₗᵢ[ℝ] Vector L) (Q : Vector k ≃ₗᵢ[ℝ] Vector l)
    (h : ∀ w, G (Q w) = J (F w)) (v : Vector (k + b)) :
    BlockSum.operator b G (extendColumnChange Q b v) =
      extendColumnChange J b (BlockSum.operator b F v) := by
  apply (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := L) (m := b)).injective
  simp only [BlockSum.operator_apply, ContinuousLinearEquiv.apply_symm_apply,
    extendColumnChange_split]
  rw [h]

end NoExoticSixSphere.FramedBlock
