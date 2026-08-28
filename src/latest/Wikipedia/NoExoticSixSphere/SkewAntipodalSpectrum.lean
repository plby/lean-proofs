import Wikipedia.NoExoticSixSphere.SkewRotationExponential

/-!
# Spectral restrictions imposed by the antipodal endpoint

When the actual exponential of `K` is minus the identity, `K` has no kernel.
Every Gram eigenvalue is the square of a positive odd multiple of `π`.
If `K†K` is not `π²` times the identity, one of its actual rotation planes
therefore has speed at least `3π`.
-/

namespace NoExoticSixSphere.SkewAntipodalSpectrum

open GLOrthonormalization CayleyTransform OrthogonalExponential SkewVectorODE
  SkewSpectralPlane SkewRotationExponential

variable {n : ℕ} (K : SkewOperators n)
  (hexp : (exp K).1.1 = -(1 : Vector n →L[ℝ] Vector n))

include hexp

theorem ker_eq_zero {x : Vector n} (hx : (K : Vector n →L[ℝ] Vector n) x = 0) : x = 0 := by
  have he := exp_apply_of_zero K hx 1
  rw [one_smul, hexp] at he
  change -x = x at he
  have hz : x + x = 0 := eq_neg_iff_add_eq_zero.mp he.symm
  have htwo : (2 : ℝ) • x = 0 := by simpa only [two_smul] using hz
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

theorem gram_eigenvalue_pos {μ : ℝ} {x : Vector n} (hn : ‖x‖ = 1)
    (hx : gram K x = μ • x) : 0 < μ := by
  have hnorm : ‖(K : Vector n →L[ℝ] Vector n) x‖ ^ 2 = μ := by
    simpa only [hn, one_pow, mul_one] using norm_apply_sq_of_eigenvector K hx
  have hx0 : x ≠ 0 := by
    intro h
    simp only [h, norm_zero, zero_ne_one] at hn
  have hKx : (K : Vector n →L[ℝ] Vector n) x ≠ 0 := fun h ↦ hx0 (ker_eq_zero K hexp h)
  rw [← hnorm]
  exact sq_pos_of_pos (norm_pos_iff.mpr hKx)

theorem gram_eigenvalue_odd_pi {μ : ℝ} {x : Vector n} (hn : ‖x‖ = 1)
    (hx : gram K x = μ • x) : ∃ m : ℕ, μ = ((2 * (m : ℝ) + 1) * Real.pi) ^ 2 := by
  have hμ := gram_eigenvalue_pos K hexp hn hx
  obtain ⟨α, y, hα, _, hxy, hKx, hKy, hsq⟩ := exists_rotationPartner K hμ hn hx
  obtain ⟨m, hm⟩ := speed_eq_odd_pi hα (cos_speed_eq_neg_one K hKx hKy hn hxy hexp)
  exact ⟨m, by rw [← hsq, hm]⟩

theorem gram_eigenvalue_ge_pi_sq {μ : ℝ} {x : Vector n} (hn : ‖x‖ = 1)
    (hx : gram K x = μ • x) : Real.pi ^ 2 ≤ μ := by
  obtain ⟨m, hm⟩ := gram_eigenvalue_odd_pi K hexp hn hx
  rw [hm]
  have hspeed : Real.pi ≤ (2 * (m : ℝ) + 1) * Real.pi := by
    nlinarith [Real.pi_pos, Nat.cast_nonneg' (α := ℝ) m]
  exact (sq_le_sq₀ Real.pi_pos.le (Real.pi_pos.le.trans hspeed)).mpr hspeed

/-- A generator outside the minimal Gram locus has an actual high-speed rotation plane. -/
theorem exists_fast_rotationPlane
    (hnot : gram K ≠ Real.pi ^ 2 • (1 : Vector n →L[ℝ] Vector n)) :
    ∃ (α : ℝ) (x y : Vector n), 3 * Real.pi ≤ α ∧ ‖x‖ = 1 ∧ ‖y‖ = 1 ∧
      inner ℝ x y = 0 ∧ (K : Vector n →L[ℝ] Vector n) x = α • y ∧
        (K : Vector n →L[ℝ] Vector n) y = (-α) • x := by
  let hS := gram_isSymmetric K
  let b := hS.eigenvectorBasis finrank_euclideanSpace_fin
  let μ := hS.eigenvalues finrank_euclideanSpace_fin
  have hex : ∃ i : Fin n, μ i ≠ Real.pi ^ 2 := by
    by_contra h
    push Not at h
    apply hnot
    have he : (gram K).toLinearMap =
        (Real.pi ^ 2 • (1 : Vector n →L[ℝ] Vector n)).toLinearMap := by
      apply b.toBasis.ext
      intro i
      have hi := hS.apply_eigenvectorBasis finrank_euclideanSpace_fin i
      change gram K (b i) = μ i • b i at hi
      rw [h i] at hi
      exact hi
    apply ContinuousLinearMap.ext
    intro x
    exact LinearMap.congr_fun he x
  obtain ⟨i, hi⟩ := hex
  have he : gram K (b i) = μ i • b i := hS.apply_eigenvectorBasis _ i
  have hn : ‖b i‖ = 1 := b.orthonormal.norm_eq_one i
  obtain ⟨α, y, hα, hy, hxy, hKx, hKy, hsq⟩ :=
    exists_rotationPartner K (gram_eigenvalue_pos K hexp hn he) hn he
  have hgap := speed_gap hα (cos_speed_eq_neg_one K hKx hKy hn hxy hexp)
  refine ⟨α, b i, y, ?_, hn, hy, hxy, hKx, hKy⟩
  rcases hgap with h | h
  · exact False.elim (hi (by rw [← hsq, h]))
  · exact h

end NoExoticSixSphere.SkewAntipodalSpectrum
