import Wikipedia.NoExoticSixSphere.ResidualLinkParity
import Wikipedia.NoExoticSixSphere.InjectiveOperatorBlockExtension

/-!
# Exact coordinates for stabilized corank-one residual models

The leading block is enlarged by any number of actual identity columns.
Associating the Euclidean block coordinates identifies the unit residual
model exactly with the checked cusp operator plus those columns. The
proved stabilization theorem therefore detects its failure to extend.
-/

noncomputable section

open Function

namespace NoExoticSixSphere.StabilizedResidual

open GLOrthonormalization CorankOne Stiefel FrameBlockCoordinates DiskBoundary

def leadingSplit (k : ℕ) : Vector (k + 2) ≃L[ℝ] Vector k × Vector 2 :=
  EuclideanSpace.finAddEquivProd

def sourceSplit (k : ℕ) : Vector (k + 3) ≃L[ℝ] Vector (k + 2) × ℝ :=
  (EuclideanSpace.finAddEquivProd (n := k) (m := 3)).trans
    (((ContinuousLinearEquiv.refl ℝ (Vector k)).prodCongr
      CorankOneEuclidean.sourceSplit).trans
        ((ContinuousLinearEquiv.prodAssoc ℝ (Vector k) (Vector 2) ℝ).symm.trans
          ((leadingSplit k).symm.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ))))

def targetSplit (k : ℕ) : Vector (k + 6) ≃L[ℝ] Vector (k + 2) × Vector 4 :=
  (EuclideanSpace.finAddEquivProd (n := k) (m := 6)).trans
    (((ContinuousLinearEquiv.refl ℝ (Vector k)).prodCongr
      CorankOneEuclidean.targetSplit).trans
        ((ContinuousLinearEquiv.prodAssoc ℝ (Vector k) (Vector 2) (Vector 4)).symm.trans
          ((leadingSplit k).symm.prodCongr (ContinuousLinearEquiv.refl ℝ (Vector 4)))))

def toEuclidean (k : ℕ) : BlockMap (Vector (k + 2)) (Vector 4) ≃L[ℝ]
    (Vector (k + 3) →L[ℝ] Vector (k + 6)) :=
  (sourceSplit k).symm.arrowCongr (targetSplit k).symm

theorem toEuclidean_apply (k : ℕ) (L : BlockMap (Vector (k + 2)) (Vector 4))
    (v : Vector (k + 3)) :
    toEuclidean k L v = (targetSplit k).symm (L (sourceSplit k v)) := rfl

theorem injective_toEuclidean (k : ℕ) (L : BlockMap (Vector (k + 2)) (Vector 4))
    (hL : Injective L) : Injective (toEuclidean k L) :=
  (targetSplit k).symm.injective.comp (hL.comp (sourceSplit k).injective)

theorem sourceSplit_apply (k : ℕ) (v : Vector (k + 3)) :
    sourceSplit k v =
      ((leadingSplit k).symm ((EuclideanSpace.finAddEquivProd v).1,
        (CorankOneEuclidean.sourceSplit (EuclideanSpace.finAddEquivProd v).2).1),
        (CorankOneEuclidean.sourceSplit (EuclideanSpace.finAddEquivProd v).2).2) := rfl

theorem targetSplit_symm_apply (k : ℕ) (x : Vector (k + 2)) (z : Vector 4) :
    (targetSplit k).symm (x, z) = EuclideanSpace.finAddEquivProd.symm
      ((leadingSplit k x).1, CorankOneEuclidean.targetSplit.symm ((leadingSplit k x).2, z)) :=
  rfl

theorem simple_diagonal_eq_frontBlock (k : ℕ) (z : Vector 4) :
    toEuclidean k (diagonal (ContinuousLinearMap.id ℝ (Vector (k + 2))) z) =
      identityBlockOperator k
        (CorankOneEuclidean.toEuclidean (diagonal (ContinuousLinearMap.id ℝ (Vector 2)) z)) := by
  apply ContinuousLinearMap.ext
  intro v
  change (targetSplit k).symm ((sourceSplit k v).1, (sourceSplit k v).2 • z) = _
  rw [sourceSplit_apply, targetSplit_symm_apply, (leadingSplit k).apply_symm_apply]
  rfl

def monoMap (k : ℕ) {Y : Type*} [TopologicalSpace Y]
    (L : Y → BlockMap (Vector (k + 2)) (Vector 4)) (hi : ∀ y, Injective (L y))
    (hL : Continuous L) : C(Y, Monomorphism.Space (k + 6) (k + 3)) where
  toFun y := ⟨toEuclidean k (L y), injective_toEuclidean k (L y) (hi y)⟩
  continuous_toFun := ((toEuclidean k).continuous.comp hL).subtype_mk _

def unitModel (k : ℕ) : C(Sphere 3, Monomorphism.Space (k + 6) (k + 3)) :=
  (Monomorphism.frontBlockMap k).comp
    ((Monomorphism.inclusion 6 3).comp WhitneyCusp.simpleFrameMap)

theorem unitModel_value (k : ℕ) (q : Sphere 3) :
    (unitModel k q).val = toEuclidean k
      (diagonal (ContinuousLinearMap.id ℝ (Vector (k + 2)))
        (WhitneyCusp.residualCoordinates q.val)) := by
  change identityBlockOperator k (WhitneyCusp.deformation 0 q.val) = _
  rw [simple_diagonal_eq_frontBlock, CorankOneEuclidean.simple_diagonal_eq]

theorem unitModel_not_extends (k : ℕ) : ¬ Extends (unitModel k) := by
  intro he
  have hb := (Monomorphism.extends_frontBlockMap_iff (by decide) rfl k
    ((Monomorphism.inclusion 6 3).comp WhitneyCusp.simpleFrameMap)).mp he
  have hz := (Monomorphism.sphereParity_zero_iff_extension 1 _).mpr hb
  rw [Monomorphism.sphereParity_inclusion] at hz
  exact one_ne_zero (WhitneyCusp.simpleFrame_parity.symm.trans hz)

end NoExoticSixSphere.StabilizedResidual
