import Wikipedia.NoExoticSixSphere.HilbertSchmidt

/-!
# The skew-adjoint commutator and the Hilbert--Schmidt form

Commuting with a skew-adjoint operator is skew-adjoint for the Hilbert--Schmidt
form. In particular, the commutator term vanishes when paired with that same
operator, as needed in the first variation of orthogonal path energy.
-/

namespace NoExoticSixSphere.OrthogonalCommutator

open GLOrthonormalization CayleyTransform HilbertSchmidt

variable {n : ℕ}

def commutator (A B : Vector n →L[ℝ] Vector n) : Vector n →L[ℝ] Vector n :=
  A.comp B - B.comp A

theorem commutator_swap (A B : Vector n →L[ℝ] Vector n) :
    commutator A B = -commutator B A := by
  simp only [commutator, neg_sub]

theorem commutator_smul_left (r : ℝ) (A B : Vector n →L[ℝ] Vector n) :
    commutator (r • A) B = r • commutator A B := by
  simp only [commutator, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul, smul_sub]

theorem commutator_smul_right (r : ℝ) (A B : Vector n →L[ℝ] Vector n) :
    commutator A (r • B) = r • commutator A B := by
  simp only [commutator, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul, smul_sub]

theorem commutator_add_right (A B C : Vector n →L[ℝ] Vector n) :
    commutator A (B + C) = commutator A B + commutator A C := by
  simp only [commutator, ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp]
  abel

theorem commutator_sub_right (A B C : Vector n →L[ℝ] Vector n) :
    commutator A (B - C) = commutator A B - commutator A C := by
  simp only [commutator, ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
  abel

theorem commutator_sum_right {ι : Type*} (s : Finset ι)
    (A : Vector n →L[ℝ] Vector n) (B : ι → Vector n →L[ℝ] Vector n) :
    commutator A (∑ i ∈ s, B i) = ∑ i ∈ s, commutator A (B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [commutator]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, commutator_add_right, ih]

theorem hasDerivAt_commutator {f g : ℝ → Vector n →L[ℝ] Vector n}
    {A B : Vector n →L[ℝ] Vector n} {t : ℝ}
    (hf : HasDerivAt f A t) (hg : HasDerivAt g B t) :
    HasDerivAt (fun r ↦ commutator (f r) (g r))
      (commutator A (g t) + commutator (f t) B) t := by
  have hd := (hf.clm_comp hg).sub (hg.clm_comp hf)
  convert! hd using 1
  unfold commutator
  abel

theorem adjoint_commutator (K : SkewOperators n) (A : Vector n →L[ℝ] Vector n) :
    (commutator (K : Vector n →L[ℝ] Vector n) A).adjoint =
      commutator (K : Vector n →L[ℝ] Vector n) A.adjoint := by
  change star ((K : Vector n →L[ℝ] Vector n) * A - A * (K : Vector n →L[ℝ] Vector n)) =
    (K : Vector n →L[ℝ] Vector n) * star A - star A * (K : Vector n →L[ℝ] Vector n)
  rw [star_sub, star_mul, star_mul, K.2, mul_neg, neg_mul, neg_sub_neg]

theorem commutator_mem_skew (K L : SkewOperators n) :
    commutator (K : Vector n →L[ℝ] Vector n) (L : Vector n →L[ℝ] Vector n) ∈
      skewAdjoint.submodule ℝ (Vector n →L[ℝ] Vector n) := by
  change (commutator (K : Vector n →L[ℝ] Vector n)
    (L : Vector n →L[ℝ] Vector n)).adjoint = -commutator _ _
  rw [adjoint_commutator, adjoint_eq_neg]
  simp only [commutator, ContinuousLinearMap.comp_neg, ContinuousLinearMap.neg_comp,
    neg_sub_neg, neg_sub]

theorem trace_commutator_mul (A B C : Vector n →L[ℝ] Vector n) :
    LinearMap.trace ℝ (Vector n) ((commutator A B).comp C).toLinearMap =
      LinearMap.trace ℝ (Vector n) (A.comp (commutator B C)).toLinearMap := by
  simpa only [Ring.lie_def, commutator] using!
    LinearMap.trace_lie_mul_eq A.toLinearMap B.toLinearMap C.toLinearMap

theorem innerForm_commutator (K : SkewOperators n) (A B : Vector n →L[ℝ] Vector n) :
    innerForm (commutator (K : Vector n →L[ℝ] Vector n) A) B =
      -innerForm A (commutator (K : Vector n →L[ℝ] Vector n) B) := by
  rw [innerForm_eq_trace, adjoint_commutator]
  calc
    LinearMap.trace ℝ (Vector n)
        ((commutator (K : Vector n →L[ℝ] Vector n) A.adjoint).comp B).toLinearMap =
        -LinearMap.trace ℝ (Vector n)
          ((commutator A.adjoint (K : Vector n →L[ℝ] Vector n)).comp B).toLinearMap := by
      rw [commutator_swap (K : Vector n →L[ℝ] Vector n) A.adjoint,
        ContinuousLinearMap.neg_comp]
      exact map_neg _ _
    _ = -LinearMap.trace ℝ (Vector n)
        (A.adjoint.comp (commutator (K : Vector n →L[ℝ] Vector n) B)).toLinearMap := by
      rw [trace_commutator_mul]
    _ = -innerForm A (commutator (K : Vector n →L[ℝ] Vector n) B) := by
      rw [innerForm_eq_trace]

theorem innerForm_self_commutator (K : SkewOperators n) (A : Vector n →L[ℝ] Vector n) :
    innerForm (K : Vector n →L[ℝ] Vector n)
      (commutator (K : Vector n →L[ℝ] Vector n) A) = 0 := by
  have h := innerForm_commutator K (K : Vector n →L[ℝ] Vector n) A
  have hz : commutator (K : Vector n →L[ℝ] Vector n) (K : Vector n →L[ℝ] Vector n) = 0 :=
    sub_self _
  rw [hz] at h
  have hzero : innerForm (0 : Vector n →L[ℝ] Vector n) A = 0 := by simp [innerForm]
  rw [hzero] at h
  linarith

end NoExoticSixSphere.OrthogonalCommutator
