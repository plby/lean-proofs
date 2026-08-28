import Wikipedia.NoExoticSixSphere.CorankOneShears
import Wikipedia.NoExoticSixSphere.WhitneyCuspParity

/-!
# Exact Euclidean coordinates of the residual block model

These fixed continuous linear equivalences use the actual first two and
last coordinates. The simple residual diagonal is identified with the
already checked cusp frame operator by coordinate equalities, without
equating the ordinary product norm with the Euclidean norm.
-/

noncomputable section

open Function

namespace NoExoticSixSphere.CorankOneEuclidean

open GLOrthonormalization CorankOne

def sourceSplit : Vector 3 ≃L[ℝ] Vector 2 × ℝ :=
  (EuclideanSpace.finAddEquivProd (n := 2) (m := 1)).trans
    ((ContinuousLinearEquiv.refl ℝ (Vector 2)).prodCongr
      EuclideanTailCoordinates.scalar.symm.toContinuousLinearEquiv)

def targetSplit : Vector 6 ≃L[ℝ] Vector 2 × Vector 4 :=
  EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 4)

def toEuclidean : BlockMap (Vector 2) (Vector 4) ≃L[ℝ] (Vector 3 →L[ℝ] Vector 6) :=
  sourceSplit.symm.arrowCongr targetSplit.symm

theorem toEuclidean_apply (L : BlockMap (Vector 2) (Vector 4)) (v : Vector 3) :
    toEuclidean L v = targetSplit.symm (L (sourceSplit v)) := rfl

theorem injective_toEuclidean (L : BlockMap (Vector 2) (Vector 4)) (hL : Injective L) :
    Injective (toEuclidean L) :=
  targetSplit.symm.injective.comp (hL.comp sourceSplit.injective)

theorem sourceSplit_fst (v : Vector 3) (i : Fin 2) : (sourceSplit v).1 i = v (i.castAdd 1) := rfl

theorem sourceSplit_snd (v : Vector 3) : (sourceSplit v).2 = v 2 := rfl

theorem targetSplit_symm_fst (x : Vector 2) (z : Vector 4) (i : Fin 2) :
    targetSplit.symm (x, z) (i.castAdd 4) = x i := EuclideanBlocks.symm_castAdd x z i

theorem targetSplit_symm_snd (x : Vector 2) (z : Vector 4) (i : Fin 4) :
    targetSplit.symm (x, z) (i.natAdd 2) = z i := EuclideanBlocks.symm_natAdd x z i

theorem simple_diagonal_eq (q : Vector 4) :
    toEuclidean (diagonal (ContinuousLinearMap.id ℝ (Vector 2))
      (WhitneyCusp.residualCoordinates q)) = WhitneyCusp.deformation 0 q := by
  apply ContinuousLinearMap.ext
  intro v
  ext i
  rw [toEuclidean_apply]
  change targetSplit.symm ((sourceSplit v).1,
    (sourceSplit v).2 • WhitneyCusp.residualCoordinates q) i = _
  refine Fin.addCases (m := 2) (n := 4) (fun j ↦ ?_) (fun j ↦ ?_) i
  · rw [targetSplit_symm_fst, sourceSplit_fst, WhitneyCusp.deformation_apply]
    fin_cases j <;> rfl
  · rw [targetSplit_symm_snd]
    change (sourceSplit v).2 * (WhitneyCusp.residualCoordinates q) j = _
    rw [sourceSplit_snd, WhitneyCusp.deformation_apply, WhitneyCusp.residualCoordinates_apply]
    fin_cases j <;> simp [mul_comm]

end NoExoticSixSphere.CorankOneEuclidean
