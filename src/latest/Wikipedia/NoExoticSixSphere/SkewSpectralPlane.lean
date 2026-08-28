import Wikipedia.NoExoticSixSphere.CayleyTransform
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# A real rotation plane for a nonzero skew-adjoint operator

The real spectral theorem is applied to the positive Gram operator `K†K`.
A positive eigenvalue gives two orthogonal unit vectors on which `K` acts
as a genuine planar rotation generator. These are actual ambient vectors,
not a formal diagonalization model.
-/

namespace NoExoticSixSphere.SkewSpectralPlane

open GLOrthonormalization CayleyTransform

variable {n : ℕ}

noncomputable def gram (K : SkewOperators n) : Vector n →L[ℝ] Vector n :=
  (K : Vector n →L[ℝ] Vector n).adjoint.comp (K : Vector n →L[ℝ] Vector n)

theorem gram_isSymmetric (K : SkewOperators n) : (gram K).toLinearMap.IsSymmetric := by
  intro x y
  change inner ℝ ((K : Vector n →L[ℝ] Vector n).adjoint
    ((K : Vector n →L[ℝ] Vector n) x)) y =
      inner ℝ x ((K : Vector n →L[ℝ] Vector n).adjoint
        ((K : Vector n →L[ℝ] Vector n) y))
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]

theorem norm_apply_sq_of_eigenvector (K : SkewOperators n) {x : Vector n} {μ : ℝ}
    (hx : gram K x = μ • x) :
    ‖(K : Vector n →L[ℝ] Vector n) x‖ ^ 2 = μ * ‖x‖ ^ 2 := by
  calc
    _ = inner ℝ x (gram K x) := by
      rw [gram, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
        real_inner_self_eq_norm_sq]
    _ = μ * ‖x‖ ^ 2 := by rw [hx, inner_smul_right, real_inner_self_eq_norm_sq]

theorem square_apply_of_eigenvector (K : SkewOperators n) {x : Vector n} {μ : ℝ}
    (hx : gram K x = μ • x) :
    (K : Vector n →L[ℝ] Vector n) ((K : Vector n →L[ℝ] Vector n) x) = (-μ) • x := by
  have he : -((K : Vector n →L[ℝ] Vector n)
      ((K : Vector n →L[ℝ] Vector n) x)) = μ • x := by
    simpa only [gram, adjoint_eq_neg, ContinuousLinearMap.comp_apply, neg_apply] using hx
  have hn := congrArg Neg.neg he
  simpa only [neg_neg, neg_smul] using hn

/-- A nonzero skew operator has a unit Gram eigenvector with positive eigenvalue. -/
theorem exists_positive_eigenvector (K : SkewOperators n)
    (hK : (K : Vector n →L[ℝ] Vector n) ≠ 0) :
    ∃ (μ : ℝ) (x : Vector n), 0 < μ ∧ ‖x‖ = 1 ∧ gram K x = μ • x := by
  let hS := gram_isSymmetric K
  let b := hS.eigenvectorBasis finrank_euclideanSpace_fin
  have hex : ∃ i : Fin n, (K : Vector n →L[ℝ] Vector n) (b i) ≠ 0 := by
    by_contra h
    push Not at h
    apply hK
    have he : (K : Vector n →L[ℝ] Vector n).toLinearMap = 0 := by
      apply b.toBasis.ext
      intro i
      exact h i
    apply ContinuousLinearMap.ext
    intro x
    exact LinearMap.congr_fun he x
  obtain ⟨i, hi⟩ := hex
  let μ := hS.eigenvalues finrank_euclideanSpace_fin i
  have he : gram K (b i) = μ • b i := hS.apply_eigenvectorBasis _ i
  have hn : ‖b i‖ = 1 := b.orthonormal.norm_eq_one i
  have hnorm := norm_apply_sq_of_eigenvector K he
  rw [hn, one_pow, mul_one] at hnorm
  refine ⟨μ, b i, ?_, hn, he⟩
  rw [← hnorm]
  exact sq_pos_of_pos (norm_pos_iff.mpr hi)

/-- A positive unit Gram eigenvector extends to a rotation plane at the matching speed. -/
theorem exists_rotationPartner (K : SkewOperators n) {μ : ℝ} {x : Vector n}
    (hμ : 0 < μ) (hx : ‖x‖ = 1) (he : gram K x = μ • x) :
    ∃ (α : ℝ) (y : Vector n), 0 < α ∧ ‖y‖ = 1 ∧ inner ℝ x y = 0 ∧
      (K : Vector n →L[ℝ] Vector n) x = α • y ∧
      (K : Vector n →L[ℝ] Vector n) y = (-α) • x ∧ α ^ 2 = μ := by
  let α := ‖(K : Vector n →L[ℝ] Vector n) x‖
  have hnorm : α ^ 2 = μ := by
    simpa only [hx, one_pow, mul_one] using norm_apply_sq_of_eigenvector K he
  have hα : 0 < α := by
    have hn : 0 ≤ α := norm_nonneg _
    nlinarith
  let y : Vector n := α⁻¹ • (K : Vector n →L[ℝ] Vector n) x
  have hy : ‖y‖ = 1 := by
    change ‖α⁻¹ • (K : Vector n →L[ℝ] Vector n) x‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hα)]
    exact inv_mul_cancel₀ hα.ne'
  have hxy : inner ℝ x y = 0 := by
    change inner ℝ x (α⁻¹ • (K : Vector n →L[ℝ] Vector n) x) = 0
    rw [inner_smul_right, inner_skew_self, mul_zero]
  refine ⟨α, y, hα, hy, hxy, ?_, ?_, hnorm⟩
  · change (K : Vector n →L[ℝ] Vector n) x =
      α • (α⁻¹ • (K : Vector n →L[ℝ] Vector n) x)
    rw [smul_smul, mul_inv_cancel₀ hα.ne', one_smul]
  · change (K : Vector n →L[ℝ] Vector n)
      (α⁻¹ • (K : Vector n →L[ℝ] Vector n) x) = (-α) • x
    rw [map_smul, square_apply_of_eigenvector K he, smul_smul]
    have hcoeff : α⁻¹ * (-μ) = -α := by
      rw [← hnorm]
      field_simp
    rw [hcoeff]

/-- A genuine invariant orthonormal two-plane with a strictly positive rotation speed. -/
theorem exists_rotationPlane (K : SkewOperators n)
    (hK : (K : Vector n →L[ℝ] Vector n) ≠ 0) :
    ∃ (α : ℝ) (x y : Vector n), 0 < α ∧ ‖x‖ = 1 ∧ ‖y‖ = 1 ∧ inner ℝ x y = 0 ∧
      (K : Vector n →L[ℝ] Vector n) x = α • y ∧
      (K : Vector n →L[ℝ] Vector n) y = (-α) • x := by
  obtain ⟨μ, x, hμ, hx, he⟩ := exists_positive_eigenvector K hK
  obtain ⟨α, y, hα, hy, hxy, hKx, hKy, _⟩ := exists_rotationPartner K hμ hx he
  exact ⟨α, x, y, hα, hx, hy, hxy, hKx, hKy⟩

theorem inner_skew (K : SkewOperators n) (x y : Vector n) :
    inner ℝ ((K : Vector n →L[ℝ] Vector n) x) y =
      -inner ℝ x ((K : Vector n →L[ℝ] Vector n) y) := by
  simpa only [adjoint_eq_neg, neg_apply, inner_neg_right] using
    ((K : Vector n →L[ℝ] Vector n).adjoint_inner_right x y).symm

/-- The orthogonal complement of a rotation plane is also invariant under `K`. -/
theorem rotationPlane_complement_invariant (K : SkewOperators n)
    {α : ℝ} {x y z : Vector n}
    (hx : (K : Vector n →L[ℝ] Vector n) x = α • y)
    (hy : (K : Vector n →L[ℝ] Vector n) y = (-α) • x)
    (hxz : inner ℝ x z = 0) (hyz : inner ℝ y z = 0) :
    inner ℝ x ((K : Vector n →L[ℝ] Vector n) z) = 0 ∧
      inner ℝ y ((K : Vector n →L[ℝ] Vector n) z) = 0 := by
  have h₁ := inner_skew K x z
  have h₂ := inner_skew K y z
  rw [hx] at h₁
  rw [hy] at h₂
  simp only [inner_smul_left, RCLike.conj_to_real, hxz, hyz, mul_zero] at h₁ h₂
  constructor <;> linarith

end NoExoticSixSphere.SkewSpectralPlane
