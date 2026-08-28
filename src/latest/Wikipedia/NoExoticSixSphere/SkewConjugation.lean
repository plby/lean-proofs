import Wikipedia.NoExoticSixSphere.OrthogonalInverseDerivative
import Wikipedia.NoExoticSixSphere.OrthogonalCommutator

/-!
# Orthogonal conjugation on actual skew-adjoint operators

Conjugation preserves the skew-adjoint model and the Hilbert--Schmidt form.
The construction remains smooth in ambient operator coordinates and respects
commutation with operators that are fixed by the conjugation.
-/

open scoped ContDiff

namespace NoExoticSixSphere.SkewConjugation

open GLOrthonormalization OrthogonalPaths CayleyTransform OrthogonalVelocity
  HilbertSchmidt OrthogonalCommutator

variable {n : ℕ}

theorem conjugate_mem_skew (a : OrthogonalOperators n) (K : SkewOperators n) :
    a.1.1.comp ((K : Vector n →L[ℝ] Vector n).comp (inverse a).1.1) ∈
      skewAdjoint.submodule ℝ (Vector n →L[ℝ] Vector n) := by
  change (a.1.1.comp ((K : Vector n →L[ℝ] Vector n).comp (inverse a).1.1)).adjoint =
    -(a.1.1.comp ((K : Vector n →L[ℝ] Vector n).comp (inverse a).1.1))
  simp only [ContinuousLinearMap.adjoint_comp, inverse_eq_adjoint,
    ContinuousLinearMap.adjoint_adjoint, adjoint_eq_neg, ContinuousLinearMap.comp_neg,
    ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_assoc]

noncomputable def conjugate (a : OrthogonalOperators n) (K : SkewOperators n) : SkewOperators n :=
  ⟨a.1.1.comp ((K : Vector n →L[ℝ] Vector n).comp (inverse a).1.1), conjugate_mem_skew a K⟩

theorem conjugate_coe (a : OrthogonalOperators n) (K : SkewOperators n) :
    (conjugate a K : Vector n →L[ℝ] Vector n) =
      a.1.1.comp ((K : Vector n →L[ℝ] Vector n).comp (inverse a).1.1) := rfl

theorem innerForm_conjugate (a : OrthogonalOperators n) (K L : SkewOperators n) :
    innerForm (conjugate a K : Vector n →L[ℝ] Vector n)
      (conjugate a L : Vector n →L[ℝ] Vector n) =
        innerForm (K : Vector n →L[ℝ] Vector n) (L : Vector n →L[ℝ] Vector n) := by
  rw [conjugate_coe, conjugate_coe, innerForm_left, innerForm_right]

theorem squareNorm_conjugate (a : OrthogonalOperators n) (K : SkewOperators n) :
    squareNorm (conjugate a K : Vector n →L[ℝ] Vector n) =
      squareNorm (K : Vector n →L[ℝ] Vector n) := innerForm_conjugate a K K

theorem contDiff_conjugate {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {a : P → OrthogonalOperators n} {K : P → SkewOperators n}
    (ha : ContDiff ℝ ∞ (fun p ↦ (a p).1.1)) (hK : ContDiff ℝ ∞ K) :
    ContDiff ℝ ∞ (fun p ↦ conjugate (a p) (K p)) := by
  let L : (Vector n →L[ℝ] Vector n) →L[ℝ] (Vector n →L[ℝ] Vector n) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  have hi : ContDiff ℝ ∞ (fun p ↦ (inverse (a p)).1.1) := by
    simpa only [L, inverse_eq_adjoint] using! L.contDiff.comp ha
  have hk : ContDiff ℝ ∞ (fun p ↦ (K p : Vector n →L[ℝ] Vector n)) :=
    (skewAdjoint.submodule ℝ (Vector n →L[ℝ] Vector n)).subtypeL.contDiff.comp hK
  have hc : ContDiff ℝ ∞ (fun p ↦ (conjugate (a p) (K p) : Vector n →L[ℝ] Vector n)) :=
    ha.clm_comp (hk.clm_comp hi)
  have hp := (CayleyAtlas.skewProjection (n := n)).contDiff.comp hc
  simpa only [Function.comp_def, CayleyAtlas.skewProjection_coe] using hp

theorem commute_inverse (a : OrthogonalOperators n) (K : Vector n →L[ℝ] Vector n)
    (h : a.1.1.comp K = K.comp a.1.1) :
    K.comp (inverse a).1.1 = (inverse a).1.1.comp K := by
  apply ContinuousLinearMap.ext
  intro x
  apply (toEquiv a).injective
  change a.1.1 (K ((inverse a).1.1 x)) = a.1.1 ((inverse a).1.1 (K x))
  rw [self_apply_inverse]
  have hx := DFunLike.congr_fun h ((inverse a).1.1 x)
  simpa only [ContinuousLinearMap.comp_apply, self_apply_inverse] using hx

theorem commutator_conjugate (a : OrthogonalOperators n) (K L : SkewOperators n)
    (h : a.1.1.comp (K : Vector n →L[ℝ] Vector n) =
      (K : Vector n →L[ℝ] Vector n).comp a.1.1) :
    commutator (K : Vector n →L[ℝ] Vector n)
      (conjugate a L : Vector n →L[ℝ] Vector n) =
        a.1.1.comp ((commutator (K : Vector n →L[ℝ] Vector n)
          (L : Vector n →L[ℝ] Vector n)).comp (inverse a).1.1) := by
  have hi := commute_inverse a (K : Vector n →L[ℝ] Vector n) h
  simp only [OrthogonalCommutator.commutator, conjugate_coe,
    ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
  congr 1
  · rw [← ContinuousLinearMap.comp_assoc, ← h]
    rfl
  · rw [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc,
      ← hi, ← ContinuousLinearMap.comp_assoc]
    rfl

end NoExoticSixSphere.SkewConjugation
