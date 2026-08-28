import Wikipedia.NoExoticSixSphere.InjectiveOperatorBlockHomotopy

/-!
# Removing fixed identity normal columns by an actual operator homotopy

An injective operator with identity normal columns is block upper triangular,
but its upper tangent block need not vanish. Scaling that block to zero gives
a homotopy through injective operators. The remaining tangent operator is
injective, and the checked identity-block extension theorem preserves its
three-complement sphere parity.
-/

noncomputable section

namespace NoExoticSixSphere

namespace FrameBlockCoordinates

open GLOrthonormalization

variable (k : ℕ) {n N : ℕ}

def upperTangentBlock (A : Vector (k + n) →L[ℝ] Vector (k + N)) :
    Vector n →L[ℝ] Vector k :=
  (ContinuousLinearMap.fst ℝ (Vector k) (Vector N)).comp
    (EuclideanSpace.finAddEquivProd.toContinuousLinearMap.comp
      (A.comp (EuclideanSpace.finAddEquivProd.symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.inr ℝ (Vector k) (Vector n)))))

def lowerTangentBlock (A : Vector (k + n) →L[ℝ] Vector (k + N)) :
    Vector n →L[ℝ] Vector N :=
  (ContinuousLinearMap.snd ℝ (Vector k) (Vector N)).comp
    (EuclideanSpace.finAddEquivProd.toContinuousLinearMap.comp
      (A.comp (EuclideanSpace.finAddEquivProd.symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.inr ℝ (Vector k) (Vector n)))))

theorem upperTangentBlock_apply (A : Vector (k + n) →L[ℝ] Vector (k + N))
    (w : Vector n) :
    upperTangentBlock k A w = (EuclideanSpace.finAddEquivProd
      (A (EuclideanSpace.finAddEquivProd.symm ((0 : Vector k), w)))).1 := rfl

theorem lowerTangentBlock_apply (A : Vector (k + n) →L[ℝ] Vector (k + N))
    (w : Vector n) :
    lowerTangentBlock k A w = (EuclideanSpace.finAddEquivProd
      (A (EuclideanSpace.finAddEquivProd.symm ((0 : Vector k), w)))).2 := rfl

theorem fixedNormal_apply (A : Vector (k + n) →L[ℝ] Vector (k + N))
    (hA : ∀ v : Vector k, A (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector n))) =
      EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector N)))
    (v : Vector k) (w : Vector n) :
    A (EuclideanSpace.finAddEquivProd.symm (v, w)) =
      EuclideanSpace.finAddEquivProd.symm
        (v + upperTangentBlock k A w, lowerTangentBlock k A w) := by
  have hs : EuclideanSpace.finAddEquivProd.symm (v, w) =
      EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector n)) +
        EuclideanSpace.finAddEquivProd.symm ((0 : Vector k), w) := by
    rw [← map_add]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  apply (EuclideanSpace.finAddEquivProd (n := k) (m := N)).injective
  rw [hs, map_add, hA, map_add, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  exact Prod.ext rfl (zero_add _)

theorem lowerTangentBlock_injective (A : Vector (k + n) →L[ℝ] Vector (k + N))
    (hi : Function.Injective A)
    (hA : ∀ v : Vector k, A (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector n))) =
      EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector N))) :
    Function.Injective (lowerTangentBlock k A) := by
  intro v w h
  have he : A (EuclideanSpace.finAddEquivProd.symm (-upperTangentBlock k A v, v)) =
      A (EuclideanSpace.finAddEquivProd.symm (-upperTangentBlock k A w, w)) := by
    simp only [fixedNormal_apply k A hA, neg_add_cancel, h]
  have hp := congrArg (EuclideanSpace.finAddEquivProd (n := k) (m := n)) (hi he)
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using congrArg Prod.snd hp

theorem continuous_upperTangentBlock {X : Type*} [TopologicalSpace X]
    (A : X → Vector (k + n) →L[ℝ] Vector (k + N)) (hA : Continuous A) :
    Continuous (fun x ↦ upperTangentBlock k (A x)) := by
  apply continuous_clm_apply.mpr
  intro w
  exact (EuclideanSpace.finAddEquivProd.continuous.comp
    (hA.clm_apply continuous_const)).fst

theorem continuous_lowerTangentBlock {X : Type*} [TopologicalSpace X]
    (A : X → Vector (k + n) →L[ℝ] Vector (k + N)) (hA : Continuous A) :
    Continuous (fun x ↦ lowerTangentBlock k (A x)) := by
  apply continuous_clm_apply.mpr
  intro w
  exact (EuclideanSpace.finAddEquivProd.continuous.comp
    (hA.clm_apply continuous_const)).snd

def upperTriangularOperator (B : Vector n →L[ℝ] Vector k)
    (C : Vector n →L[ℝ] Vector N) : Vector (k + n) →L[ℝ] Vector (k + N) :=
  EuclideanSpace.finAddEquivProd.symm.toContinuousLinearMap.comp
    (((ContinuousLinearMap.fst ℝ (Vector k) (Vector n) +
      B.comp (ContinuousLinearMap.snd ℝ (Vector k) (Vector n))).prod
        (C.comp (ContinuousLinearMap.snd ℝ (Vector k) (Vector n)))).comp
          EuclideanSpace.finAddEquivProd.toContinuousLinearMap)

theorem upperTriangularOperator_apply (B : Vector n →L[ℝ] Vector k)
    (C : Vector n →L[ℝ] Vector N) (v : Vector (k + n)) :
    upperTriangularOperator k B C v = EuclideanSpace.finAddEquivProd.symm
      ((EuclideanSpace.finAddEquivProd v).1 + B (EuclideanSpace.finAddEquivProd v).2,
        C (EuclideanSpace.finAddEquivProd v).2) := rfl

theorem upperTriangularOperator_injective (B : Vector n →L[ℝ] Vector k)
    (C : Vector n →L[ℝ] Vector N) (hi : Function.Injective C) :
    Function.Injective (upperTriangularOperator k B C) := by
  intro v w h
  apply (EuclideanSpace.finAddEquivProd (n := k) (m := n)).injective
  have hp := congrArg (EuclideanSpace.finAddEquivProd (n := k) (m := N)) h
  simp only [upperTriangularOperator_apply, ContinuousLinearEquiv.apply_symm_apply] at hp
  have hs := hi (congrArg Prod.snd hp)
  have hf := congrArg Prod.fst hp
  change _ + _ = _ + _ at hf
  rw [hs] at hf
  exact Prod.ext (add_right_cancel hf) hs

theorem continuous_upperTriangularOperator {X : Type*} [TopologicalSpace X]
    (B : X → Vector n →L[ℝ] Vector k) (C : X → Vector n →L[ℝ] Vector N)
    (hB : Continuous B) (hC : Continuous C) :
    Continuous (fun x ↦ upperTriangularOperator k (B x) (C x)) := by
  apply continuous_clm_apply.mpr
  intro v
  exact EuclideanSpace.finAddEquivProd.symm.continuous.comp
    ((continuous_const.add (hB.clm_apply continuous_const)).prodMk
      (hC.clm_apply continuous_const))

theorem upperTriangularOperator_blocks (A : Vector (k + n) →L[ℝ] Vector (k + N))
    (hA : ∀ v : Vector k, A (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector n))) =
      EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector N))) :
    upperTriangularOperator k (upperTangentBlock k A) (lowerTangentBlock k A) = A := by
  apply ContinuousLinearMap.ext
  intro v
  rw [upperTriangularOperator_apply, ← fixedNormal_apply k A hA,
    ContinuousLinearEquiv.symm_apply_apply]

theorem upperTriangularOperator_zero (C : Vector n →L[ℝ] Vector N) :
    upperTriangularOperator k 0 C = identityBlockOperator k C := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [upperTriangularOperator_apply, zero_apply, add_zero,
    identityBlockOperator_apply]

end FrameBlockCoordinates

namespace Stiefel.Monomorphism

open GLOrthonormalization FrameBlockCoordinates DiskBoundary

variable {X : Type*} [TopologicalSpace X] (k : ℕ) {n N : ℕ}
  (A : C(X, Space (k + N) (k + n)))
  (hA : ∀ x v, (A x).val (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector n))) =
    EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector N)))

def fixedNormalReduction : C(X, Space N n) where
  toFun x := ⟨lowerTangentBlock k (A x).val,
    lowerTangentBlock_injective k (A x).val (A x).property (hA x)⟩
  continuous_toFun := (continuous_lowerTangentBlock k _
    (continuous_subtype_val.comp A.continuous)).subtype_mk _

theorem fixedNormalReduction_apply (x : X) (w : Vector n) :
    (fixedNormalReduction k A hA x).val w = (EuclideanSpace.finAddEquivProd
      ((A x).val (EuclideanSpace.finAddEquivProd.symm ((0 : Vector k), w)))).2 := rfl

def fixedNormalReductionHomotopy :
    A.Homotopy ((frontBlockMap k).comp (fixedNormalReduction k A hA)) where
  toFun p := ⟨upperTriangularOperator k ((1 - p.1.val) • upperTangentBlock k (A p.2).val)
    (lowerTangentBlock k (A p.2).val), upperTriangularOperator_injective k _ _
      (lowerTangentBlock_injective k (A p.2).val (A p.2).property (hA p.2))⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_upperTriangularOperator
    · exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        (continuous_upperTangentBlock k _
          (continuous_subtype_val.comp (A.continuous.comp continuous_snd)))
    · exact continuous_lowerTangentBlock k _
        (continuous_subtype_val.comp (A.continuous.comp continuous_snd))
  map_zero_left x := by
    apply Subtype.ext
    change upperTriangularOperator k ((1 - (0 : ℝ)) • upperTangentBlock k (A x).val)
      (lowerTangentBlock k (A x).val) = (A x).val
    simpa only [sub_zero, one_smul] using upperTriangularOperator_blocks k (A x).val (hA x)
  map_one_left x := by
    apply Subtype.ext
    change upperTriangularOperator k ((1 - (1 : ℝ)) • upperTangentBlock k (A x).val)
      (lowerTangentBlock k (A x).val) = identityBlockOperator k (lowerTangentBlock k (A x).val)
    simp only [sub_self, zero_smul, upperTriangularOperator_zero]

theorem sphereParityOfDimension_fixedNormalReduction (r : ℕ)
    (hN : N = 3 + (r + 2)) (hn : n = r + 2)
    (A : C(Sphere 3, Space (k + N) (k + n)))
    (hA : ∀ x v, (A x).val (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector n))) =
      EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector N))) :
    sphereParityOfDimension (k + r) (by omega) (by omega) A =
      sphereParityOfDimension r hN hn (fixedNormalReduction k A hA) := by
  calc
    _ = sphereParityOfDimension (k + r) (by omega) (by omega)
        ((frontBlockMap k).comp (fixedNormalReduction k A hA)) :=
      sphereParityOfDimension_homotopic (k + r) (by omega) (by omega)
        ⟨fixedNormalReductionHomotopy k A hA⟩
    _ = _ := by
      apply zmodTwo_eq_of_zero_iff
      rw [sphereParityOfDimension_zero_iff, sphereParityOfDimension_zero_iff]
      exact extends_frontBlockMap_iff (by omega) (by omega) k _

end Stiefel.Monomorphism

end NoExoticSixSphere
