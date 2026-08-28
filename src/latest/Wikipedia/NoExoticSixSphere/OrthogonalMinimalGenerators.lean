import Wikipedia.NoExoticSixSphere.OrthogonalComplexStructures
import Wikipedia.NoExoticSixSphere.SkewGram

/-!
# The minimal Gram locus and orthogonal complex structures

Multiplication by `π` is a homeomorphism from the actual complex-structure
space to the locus `K†K = π² I`. Every generator in this locus has antipodal
exponential. Energy minimality is proved separately, not built into this locus.
-/

namespace NoExoticSixSphere.OrthogonalComplexStructures

open GLOrthonormalization CayleyTransform SkewSpectralPlane OrthogonalExponential

def minimumLocus (n : ℕ) : Set (SkewOperators n) :=
  {K | gram K = Real.pi ^ 2 • (1 : Vector n →L[ℝ] Vector n)}

variable {n : ℕ}

noncomputable def toMinimum (J : Space n) : minimumLocus n :=
  ⟨Real.pi • J.1, by
    change gram (Real.pi • J.1) = _
    rw [gram_smul, gram_eq_one]⟩

theorem normalized_gram (K : minimumLocus n) :
    gram (Real.pi⁻¹ • K.1) = (1 : Vector n →L[ℝ] Vector n) := by
  rw [gram_smul, K.2, smul_smul]
  have hc : Real.pi⁻¹ ^ 2 * Real.pi ^ 2 = 1 := by field_simp [Real.pi_ne_zero]
  rw [hc, one_smul]

noncomputable def ofMinimum (K : minimumLocus n) : Space n :=
  ⟨Real.pi⁻¹ • K.1, by
    have hg := normalized_gram K
    rw [gram, adjoint_eq_neg, ContinuousLinearMap.neg_comp] at hg
    exact neg_eq_iff_eq_neg.mp hg⟩

noncomputable def minimumHomeomorph (n : ℕ) : Space n ≃ₜ minimumLocus n where
  toFun := toMinimum
  invFun := ofMinimum
  left_inv J := by
    apply Subtype.ext
    change Real.pi⁻¹ • (Real.pi • J.1) = J.1
    rw [smul_smul, inv_mul_cancel₀ Real.pi_ne_zero, one_smul]
  right_inv K := by
    apply Subtype.ext
    change Real.pi • (Real.pi⁻¹ • K.1) = K.1
    rw [smul_smul, mul_inv_cancel₀ Real.pi_ne_zero, one_smul]
  continuous_toFun := (continuous_subtype_val.const_smul Real.pi).subtype_mk _
  continuous_invFun := (continuous_subtype_val.const_smul Real.pi⁻¹).subtype_mk _

theorem exp_of_minimum (K : minimumLocus n) :
    (exp K.1).1.1 = -(1 : Vector n →L[ℝ] Vector n) := by
  have he := exp_pi (ofMinimum K)
  have hscale : Real.pi • (ofMinimum K).1 = K.1 := by
    change Real.pi • (Real.pi⁻¹ • K.1) = K.1
    rw [smul_smul, mul_inv_cancel₀ Real.pi_ne_zero, one_smul]
  rw [hscale] at he
  exact he

theorem gram_minimum_iff (K : SkewOperators n) :
    gram K = Real.pi ^ 2 • (1 : Vector n →L[ℝ] Vector n) ↔
      ∃ J : Space n, Real.pi • J.1 = K := by
  constructor
  · intro h
    refine ⟨ofMinimum ⟨K, h⟩, ?_⟩
    change Real.pi • (Real.pi⁻¹ • K) = K
    rw [smul_smul, mul_inv_cancel₀ Real.pi_ne_zero, one_smul]
  · rintro ⟨J, rfl⟩
    rw [gram_smul, gram_eq_one]

end NoExoticSixSphere.OrthogonalComplexStructures
