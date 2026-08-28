import Wikipedia.NoExoticSixSphere.SkewRotationExponential
import Wikipedia.NoExoticSixSphere.OrthogonalCompactness

/-!
# Actual orthogonal complex structures

An orthogonal complex structure is a skew-adjoint real endomorphism whose
square is minus the identity. Orthogonality follows from these equations;
it is not supplied as an unrelated assumption. Its exponential is the
actual sine-cosine operator formula.
-/

namespace NoExoticSixSphere.OrthogonalComplexStructures

open GLOrthonormalization CayleyTransform OrthogonalExponential SkewSpectralPlane
  SkewRotationExponential

def locus (n : ℕ) : Set (SkewOperators n) :=
  {J | (J : Vector n →L[ℝ] Vector n).comp (J : Vector n →L[ℝ] Vector n) =
    -(1 : Vector n →L[ℝ] Vector n)}

abbrev Space (n : ℕ) := locus n

variable {n : ℕ}

theorem square_apply (J : Space n) (x : Vector n) :
    (J.1 : Vector n →L[ℝ] Vector n) ((J.1 : Vector n →L[ℝ] Vector n) x) = -x :=
  DFunLike.congr_fun J.2 x

theorem gram_eq_one (J : Space n) : gram J.1 = (1 : Vector n →L[ℝ] Vector n) := by
  rw [gram, adjoint_eq_neg, ContinuousLinearMap.neg_comp, J.2, neg_neg]

theorem norm_apply (J : Space n) (x : Vector n) :
    ‖(J.1 : Vector n →L[ℝ] Vector n) x‖ = ‖x‖ := by
  have he : gram J.1 x = (1 : ℝ) • x := by rw [gram_eq_one]; simp
  have hs := norm_apply_sq_of_eigenvector J.1 he
  rw [one_mul] at hs
  nlinarith [norm_nonneg ((J.1 : Vector n →L[ℝ] Vector n) x), norm_nonneg x]

noncomputable def toOrthogonal (J : Space n) : OrthogonalOperators n :=
  ⟨⟨J.1, OrthogonalCompactness.normPreserving_isInvertible (n := n)
    (J.1 : Vector n →L[ℝ] Vector n) (norm_apply J)⟩,
    norm_apply J⟩

theorem continuous_toOrthogonal : Continuous (toOrthogonal (n := n)) :=
  ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

theorem exp_smul (J : Space n) (t : ℝ) :
    (exp (t • J.1)).1.1 = Real.cos t • (1 : Vector n →L[ℝ] Vector n) +
      Real.sin t • (J.1 : Vector n →L[ℝ] Vector n) := by
  apply ContinuousLinearMap.ext
  intro x
  change (exp (t • J.1)).1.1 x = Real.cos t • x + Real.sin t •
    (J.1 : Vector n →L[ℝ] Vector n) x
  have hx : (J.1 : Vector n →L[ℝ] Vector n) x =
      (1 : ℝ) • (J.1 : Vector n →L[ℝ] Vector n) x := (one_smul _ _).symm
  have hy : (J.1 : Vector n →L[ℝ] Vector n)
      ((J.1 : Vector n →L[ℝ] Vector n) x) = (-(1 : ℝ)) • x := by
    simpa only [neg_smul, one_smul] using square_apply J x
  simpa only [one_mul] using exp_apply_rotation J.1 hx hy t

theorem exp_pi (J : Space n) :
    (exp (Real.pi • J.1)).1.1 = -(1 : Vector n →L[ℝ] Vector n) := by
  rw [exp_smul, Real.cos_pi, Real.sin_pi, zero_smul, add_zero, neg_one_smul]

theorem isClosed_locus (n : ℕ) : IsClosed (locus n) := by
  change IsClosed {J : SkewOperators n |
    (J : Vector n →L[ℝ] Vector n).comp (J : Vector n →L[ℝ] Vector n) =
      -(1 : Vector n →L[ℝ] Vector n)}
  apply isClosed_eq _ continuous_const
  exact continuous_subtype_val.clm_comp continuous_subtype_val

theorem norm_le_one (J : Space n) : ‖J.1‖ ≤ 1 :=
  OrthogonalCompactness.norm_le_one (n := n)
    (J.1 : Vector n →L[ℝ] Vector n) (norm_apply J)

theorem isCompact_locus (n : ℕ) : IsCompact (locus n) := by
  apply (isCompact_closedBall (0 : SkewOperators n) 1).of_isClosed_subset (isClosed_locus n)
  intro J hJ
  simpa only [Metric.mem_closedBall, dist_zero_right] using norm_le_one ⟨J, hJ⟩

instance compactSpace (n : ℕ) : CompactSpace (Space n) :=
  isCompact_iff_compactSpace.mp (isCompact_locus n)

end NoExoticSixSphere.OrthogonalComplexStructures
