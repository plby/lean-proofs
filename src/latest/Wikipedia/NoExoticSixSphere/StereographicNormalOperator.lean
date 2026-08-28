import Wikipedia.NoExoticSixSphere.StereographicEquationDifferential
import Wikipedia.NoExoticSixSphere.SphereSuspensionNormalOperator

/-!
# Canonical normal operators in the actual compactification coordinates

Conformality and radial orthogonality identify the orthogonal right
inverse of the full block derivative. This is an equality of canonical
operators, not a choice of an unrelated frame with the same dimension.
-/

noncomputable section

namespace NoExoticSixSphere.StereographicEquator

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] {n : ℕ}

omit [FiniteDimensional ℝ F] in
theorem surjective_augmented_equation_block (x : V n)
    (D : V n →L[ℝ] F) (D' : V (n + 1) →L[ℝ] WithLp 2 (ℝ × F))
    (hD : Function.Surjective D)
    (hblock : ∀ w t, D' (augmentedEquiv n x (w, t)) = WithLp.toLp 2 (2 * t, D w)) :
    Function.Surjective D' := by
  intro p
  obtain ⟨w, hw⟩ := hD p.snd
  refine ⟨augmentedEquiv n x (w, p.fst / 2), ?_⟩
  rw [hblock, hw]
  apply WithLp.ofLp_injective
  apply Prod.ext
  · change 2 * (p.fst / 2) = p.fst
    ring
  · rfl

theorem normalOperator_of_augmented_equation_block (x : V n)
    (D : V n →L[ℝ] F) (D' : V (n + 1) →L[ℝ] WithLp 2 (ℝ × F))
    (hD : Function.Surjective D)
    (hblock : ∀ w t, D' (augmentedEquiv n x (w, t)) = WithLp.toLp 2 (2 * t, D w))
    (r : ℝ) (z : F) :
    orthogonalRightInverse D' (WithLp.toLp 2 (r, z)) =
      augmentedEquiv n x (orthogonalRightInverse D z, r / 2) := by
  apply orthogonalRightInverse_eq_of_orthogonal_preimage D'
    (surjective_augmented_equation_block x D D' hD hblock)
  · rw [hblock, apply_orthogonalRightInverse D hD]
    congr 2
    ring
  · rw [Submodule.mem_orthogonal']
    intro y hy
    obtain ⟨⟨w, t⟩, rfl⟩ := (augmentedEquiv n x).surjective y
    have hzero : WithLp.toLp 2 (2 * t, D w) = 0 := by
      rw [← hblock]
      exact hy
    have ht' := congrArg (fun p : WithLp 2 (ℝ × F) ↦ p.fst) hzero
    have hw := congrArg (fun p : WithLp 2 (ℝ × F) ↦ p.snd) hzero
    change 2 * t = 0 at ht'
    change D w = 0 at hw
    have ht : t = 0 := (mul_eq_zero.mp ht').resolve_left (by norm_num)
    have hR : orthogonalRightInverse D z ∈ D.kerᗮ := by
      rw [← range_orthogonalRightInverse D hD]
      exact ⟨z, rfl⟩
    rw [Submodule.mem_orthogonal'] at hR
    rw [augmentedEquiv_apply, augmentedEquiv_apply, ht, zero_smul, add_zero,
      inner_add_left, real_inner_smul_left, inner_finiteAmbient_fderiv,
      inner_fderiv_finiteAmbient, hR w hw, mul_zero, mul_zero, add_zero]

end NoExoticSixSphere.StereographicEquator
