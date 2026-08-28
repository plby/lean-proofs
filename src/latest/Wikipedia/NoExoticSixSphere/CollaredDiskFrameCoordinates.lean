import Wikipedia.NoExoticSixSphere.SpanningDiskSourceTwist

/-!
# Actual normal-plus-disk operators in the existing stabilized coordinates

The disk lives in the product of the original ambient space and one height
coordinate. Append five fixed graph axes to its normal-plus-derivative
operator. A fixed source shuffle puts this in exactly the coordinates of
the existing sphere obstruction. A calibrated collar derivative then
gives the original sphere-dependent source twist, with its factor two.
-/

noncomputable section

open Function

namespace NoExoticSixSphere.CollaredDiskFrame

open GLOrthonormalization Stiefel StabilizedSpanningDisk
open SphereThreeTangentFrame SpanningDiskFrameCoordinates

variable {N k : ℕ}

def sourceCoordinates (k : ℕ) :
    Vector ((k + 5) + 4) ≃L[ℝ] ((Vector k × Vector 4) × Vector 5) :=
  EuclideanSpace.finAddEquivProd.trans
    ((EuclideanSpace.finAddEquivProd.prodCongr
      (ContinuousLinearEquiv.refl ℝ (Vector 4))).trans
        ((ContinuousLinearEquiv.prodAssoc ℝ (Vector k) (Vector 5) (Vector 4)).trans
          (((ContinuousLinearEquiv.refl ℝ (Vector k)).prodCongr
            (ContinuousLinearEquiv.prodComm ℝ (Vector 5) (Vector 4))).trans
              (ContinuousLinearEquiv.prodAssoc ℝ (Vector k) (Vector 4) (Vector 5)).symm)))

theorem sourceCoordinates_apply (v : Vector ((k + 5) + 4)) :
    sourceCoordinates k v =
      (((EuclideanSpace.finAddEquivProd (n := k) (m := 5)
          (EuclideanSpace.finAddEquivProd v).1).1,
        (EuclideanSpace.finAddEquivProd (n := k + 5) (m := 4) v).2),
        (EuclideanSpace.finAddEquivProd (n := k) (m := 5)
          (EuclideanSpace.finAddEquivProd v).1).2) := rfl

def combined (A : Vector k →L[ℝ] (Vector N × ℝ))
    (D : Vector 4 →L[ℝ] (Vector N × ℝ)) :
    Vector ((k + 5) + 4) →L[ℝ] Vector (N + 6) :=
  (coordinates N 4).toContinuousLinearMap.comp
    (((A.coprod D).prodMap (DiskGraph.extraCoordinates 4).symm.toContinuousLinearMap).comp
      (sourceCoordinates k).toContinuousLinearMap)

theorem combined_apply (A : Vector k →L[ℝ] (Vector N × ℝ))
    (D : Vector 4 →L[ℝ] (Vector N × ℝ)) (v : Vector ((k + 5) + 4)) :
    combined A D v = coordinates N 4
      (A (sourceCoordinates k v).1.1 + D (sourceCoordinates k v).1.2,
        (DiskGraph.extraCoordinates 4).symm (sourceCoordinates k v).2) := rfl

theorem combined_injective_of_coprod (A : Vector k →L[ℝ] (Vector N × ℝ))
    (D : Vector 4 →L[ℝ] (Vector N × ℝ))
    (hAD : Injective (A.coprod D)) :
    Injective (combined A D) := by
  intro v w h
  rw [combined_apply, combined_apply] at h
  have hp := (coordinates N 4).injective h
  apply (sourceCoordinates k).injective
  exact Prod.ext (hAD (congrArg Prod.fst hp))
    ((DiskGraph.extraCoordinates 4).symm.injective (congrArg Prod.snd hp))

theorem combined_injective (A : Vector k →L[ℝ] (Vector N × ℝ))
    (D : Vector 4 →L[ℝ] (Vector N × ℝ))
    (hA : Injective A) (hD : Injective D) (hr : Disjoint A.range D.range) :
    Injective (combined A D) := by
  apply combined_injective_of_coprod
  change Injective (A.toLinearMap.coprod D.toLinearMap)
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_coprod_of_disjoint_range _ _ hr,
    LinearMap.ker_eq_bot.mpr hA, LinearMap.ker_eq_bot.mpr hD, Submodule.prod_bot]

theorem continuous_combined {X : Type*} [TopologicalSpace X]
    (A : X → Vector k →L[ℝ] (Vector N × ℝ))
    (D : X → Vector 4 →L[ℝ] (Vector N × ℝ)) (hA : Continuous A) (hD : Continuous D) :
    Continuous (fun x ↦ combined (A x) (D x)) := by
  apply continuous_clm_apply.mpr
  intro v
  simp only [combined_apply]
  exact (coordinates N 4).continuous.comp
    (((hA.clm_apply continuous_const).add (hD.clm_apply continuous_const)).prodMk continuous_const)

def combinedMap {X : Type*} [TopologicalSpace X]
    (A : C(X, Vector k →L[ℝ] (Vector N × ℝ)))
    (D : C(X, Vector 4 →L[ℝ] (Vector N × ℝ)))
    (hA : ∀ x, Injective (A x)) (hD : ∀ x, Injective (D x))
    (hr : ∀ x, Disjoint (A x).range (D x).range) :
    C(X, Monomorphism.Space (N + 6) ((k + 5) + 4)) where
  toFun x := ⟨combined (A x) (D x), combined_injective (A x) (D x) (hA x) (hD x) (hr x)⟩
  continuous_toFun := (continuous_combined A D A.continuous D.continuous).subtype_mk _

theorem calibrated_comp_sourceSphere (a : Vector k →L[ℝ] Vector N)
    (T : Vector 3 →L[ℝ] Vector N) (D : Vector 4 →L[ℝ] (Vector N × ℝ)) (s : Sphere 3)
    (hD : ∀ v, D (radialCoordinates s v) =
      (T (EuclideanSpace.finAddEquivProd (n := 3) (m := 1) v).1,
        2 * EuclideanTailCoordinates.scalar.symm
          (EuclideanSpace.finAddEquivProd (n := 3) (m := 1) v).2)) :
    (combined ((ContinuousLinearMap.inl ℝ (Vector N) ℝ).comp a) D).comp
      (sourceSphere k s).toContinuousLinearMap =
        (targetCoordinates N).toContinuousLinearMap.comp
          ((BlockSum.operator 6 (OperatorSum.operator a T)).comp
            (sourceShuffle k).toContinuousLinearMap) := by
  apply ContinuousLinearMap.ext
  intro v
  change combined ((ContinuousLinearMap.inl ℝ (Vector N) ℝ).comp a) D
      (sourceSphere k s v) =
    targetCoordinates N (BlockSum.operator 6 (OperatorSum.operator a T) (sourceShuffle k v))
  simp only [combined_apply, sourceCoordinates_apply, sourceSphere_apply, hD,
    sourceShuffle_apply, BlockSum.operator_apply, OperatorSum.operator_apply,
    targetCoordinates_apply, targetExtra_apply, ContinuousLinearEquiv.apply_symm_apply]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    Prod.mk_add_mk, zero_add]

theorem calibrated_factorization (a : Vector k →L[ℝ] Vector N)
    (T : Vector 3 →L[ℝ] Vector N) (D : Vector 4 →L[ℝ] (Vector N × ℝ)) (s : Sphere 3)
    (hD : ∀ v, D (radialCoordinates s v) =
      (T (EuclideanSpace.finAddEquivProd (n := 3) (m := 1) v).1,
        2 * EuclideanTailCoordinates.scalar.symm
          (EuclideanSpace.finAddEquivProd (n := 3) (m := 1) v).2)) :
    combined ((ContinuousLinearMap.inl ℝ (Vector N) ℝ).comp a) D =
      (targetCoordinates N).toContinuousLinearMap.comp
        ((BlockSum.operator 6 (OperatorSum.operator a T)).comp
          (sourceTwist k s).toContinuousLinearMap) := by
  apply ContinuousLinearMap.ext
  intro v
  change combined ((ContinuousLinearMap.inl ℝ (Vector N) ℝ).comp a) D v =
    targetCoordinates N (BlockSum.operator 6 (OperatorSum.operator a T) (sourceTwist k s v))
  rw [sourceTwist_apply]
  have h := congrArg (fun L : Vector ((k + 5) + 4) →L[ℝ] Vector (N + 6) ↦
    L ((sourceSphere k s).symm v)) (calibrated_comp_sourceSphere a T D s hD)
  change combined ((ContinuousLinearMap.inl ℝ (Vector N) ℝ).comp a) D
      (sourceSphere k s ((sourceSphere k s).symm v)) =
    targetCoordinates N (BlockSum.operator 6 (OperatorSum.operator a T)
      (sourceShuffle k ((sourceSphere k s).symm v))) at h
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  exact h

end NoExoticSixSphere.CollaredDiskFrame
