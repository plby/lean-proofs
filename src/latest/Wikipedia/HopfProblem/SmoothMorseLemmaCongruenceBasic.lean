import Wikipedia.HopfProblem.SmoothMorseLemmaBilinear

/-!
# The symmetric congruence polynomial and its derivative

The polynomial is defined on the actual subspace of symmetric bilinear
forms. Its linear part is twice the identity and its remaining term is
the literal quadratic congruence term. No matrix normal form is assumed.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.SmoothMorseLemma

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Raising an index on the actual subspace of symmetric forms. -/
def raiseSymmetricIndex (H : E ≃L[ℝ] (E →L[ℝ] ℝ)) :
    SymmetricForm E →L[ℝ] (E →L[ℝ] E) :=
  (raiseIndex H).comp (symmetricForms E).subtypeL

@[simp] theorem raiseSymmetricIndex_apply (H : E ≃L[ℝ] (E →L[ℝ] ℝ))
    (S : SymmetricForm E) (u : E) :
    raiseSymmetricIndex H S u = H.symm (S.val u) := rfl

/-- The derivative of the genuine quadratic congruence operation at zero. -/
theorem hasFDerivAt_congruence_zero (B : Bilinear E) :
    HasFDerivAt (congruence B) (0 : (E →L[ℝ] E) →L[ℝ] Bilinear E) 0 := by
  have h₁ := (hasFDerivAt_const B (0 : E →L[ℝ] E)).clm_comp
    (hasFDerivAt_id (0 : E →L[ℝ] E))
  have h₂ := (flipBilinear E).hasFDerivAt.comp 0 h₁
  have h₃ := h₂.clm_comp (hasFDerivAt_id (0 : E →L[ℝ] E))
  have h₄ := (flipBilinear E).hasFDerivAt.comp 0 h₃
  convert h₄ using 1 <;> first | rfl | simp

/-- The centered symmetric polynomial whose derivative is twice the identity. -/
def congruencePolynomial (H : E ≃L[ℝ] (E →L[ℝ] ℝ))
    (S : SymmetricForm E) : SymmetricForm E :=
  (2 : ℝ) • S + symmetrize E (congruence H.toContinuousLinearMap (raiseSymmetricIndex H S))

@[simp] theorem congruencePolynomial_zero (H : E ≃L[ℝ] (E →L[ℝ] ℝ)) :
    congruencePolynomial H 0 = 0 := by
  simp [congruencePolynomial]

theorem contDiff_congruencePolynomial (H : E ≃L[ℝ] (E →L[ℝ] ℝ)) :
    ContDiff ℝ ∞ (congruencePolynomial H) :=
  (contDiff_id.const_smul (2 : ℝ)).add
    ((symmetrize E).contDiff.comp
      ((contDiff_congruence H.toContinuousLinearMap).comp (raiseSymmetricIndex H).contDiff))

theorem hasFDerivAt_congruencePolynomial_zero (H : E ≃L[ℝ] (E →L[ℝ] ℝ)) :
    HasFDerivAt (congruencePolynomial H)
      ((2 : ℝ) • ContinuousLinearMap.id ℝ (SymmetricForm E)) 0 := by
  have hc : HasFDerivAt (congruence H.toContinuousLinearMap)
      (0 : (E →L[ℝ] E) →L[ℝ] Bilinear E)
      (raiseSymmetricIndex H (0 : SymmetricForm E)) := by
    simpa only [map_zero] using hasFDerivAt_congruence_zero H.toContinuousLinearMap
  have hq := hc.comp
    (0 : SymmetricForm E) (raiseSymmetricIndex H).hasFDerivAt
  have hs := (symmetrize E).hasFDerivAt.comp (0 : SymmetricForm E) hq
  have h := ((hasFDerivAt_id (0 : SymmetricForm E)).const_smul (2 : ℝ)).add hs
  convert h using 1 <;> first | rfl | simp

/-- The reference form as an element of the genuine symmetric subspace. -/
def referenceSymmetricForm (H : E ≃L[ℝ] (E →L[ℝ] ℝ))
    (hH : ∀ u v, H u v = H v u) : SymmetricForm E :=
  ⟨H.toContinuousLinearMap, hH⟩

@[simp] theorem referenceSymmetricForm_apply (H : E ≃L[ℝ] (E →L[ℝ] ℝ))
    (hH : ∀ u v, H u v = H v u) (u v : E) :
    (referenceSymmetricForm H hH).val u v = H u v := rfl

/-- Expanding the actual congruence proves the polynomial's defining geometric
identity. Symmetry is used only for the two equal linear cross terms. -/
theorem congruencePolynomial_add_reference (H : E ≃L[ℝ] (E →L[ℝ] ℝ))
    (hH : ∀ u v, H u v = H v u) (S : SymmetricForm E) :
    (congruencePolynomial H S + referenceSymmetricForm H hH).val =
      congruence H.toContinuousLinearMap
        (ContinuousLinearMap.id ℝ E + raiseSymmetricIndex H S) := by
  ext u v
  have hcross : H u (H.symm (S.val v)) = S.val u v := by
    rw [hH, H.apply_symm_apply, S.property v u]
  have hquad : H (H.symm (S.val v)) (H.symm (S.val u)) =
      H (H.symm (S.val u)) (H.symm (S.val v)) := hH _ _
  have hquad' : S.val v (H.symm (S.val u)) = S.val u (H.symm (S.val v)) := by
    simpa only [H.apply_symm_apply] using hquad
  simp only [congruencePolynomial, Submodule.coe_add, Submodule.coe_smul,
    add_apply, smul_apply, smul_eq_mul,
    symmetrize_apply, congruence_apply, raiseSymmetricIndex_apply,
    referenceSymmetricForm_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe, map_add, hcross, H.apply_symm_apply, hquad']
  ring

end Wikipedia.HopfProblem.SmoothMorseLemma
