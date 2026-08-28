import Wikipedia.HopfProblem.SmoothMorseLemmaCongruenceBasic
import Wikipedia.HopfProblem.SmoothMorseLemmaInverse

/-!
# Smooth local congruence of genuine symmetric bilinear forms

Applying the smooth inverse-function theorem to the explicit congruence
polynomial gives a smooth operator factor for every symmetric form in an
open neighborhood of the nondegenerate reference form. The operator at
the reference form is exactly the identity, and the factorization holds
as equality of the original continuous bilinear maps.
-/

noncomputable section

open Set
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SmoothMorseLemma

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Twice the identity, as a genuine continuous linear equivalence. -/
def congruenceDoubleEquiv (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    SymmetricForm E ≃L[ℝ] SymmetricForm E :=
  ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := SymmetricForm E)
    (Units.mk0 (2 : ℝ) (by norm_num))

@[simp] theorem congruenceDoubleEquiv_apply (S : SymmetricForm E) :
    congruenceDoubleEquiv E S = (2 : ℝ) • S := rfl

theorem congruenceDoubleEquiv_toContinuousLinearMap :
    (congruenceDoubleEquiv E).toContinuousLinearMap =
      (2 : ℝ) • ContinuousLinearMap.id ℝ (SymmetricForm E) := by
  ext S
  rfl

variable [FiniteDimensional ℝ E]

/-- The explicit congruence polynomial has a genuine smooth local inverse
at zero. No preexisting congruence or normal form is a hypothesis. -/
theorem exists_congruencePolynomial_partialDiffeomorph
    (H : E ≃L[ℝ] (E →L[ℝ] ℝ)) :
    ∃ e : PartialDiffeomorph 𝓘(ℝ, SymmetricForm E) 𝓘(ℝ, SymmetricForm E)
        (SymmetricForm E) (SymmetricForm E) ∞,
      (0 : SymmetricForm E) ∈ e.source ∧ ∀ S, e S = congruencePolynomial H S := by
  apply exists_partialDiffeomorph_of_contDiff (contDiff_congruencePolynomial H)
    0 (congruenceDoubleEquiv E)
  rw [congruenceDoubleEquiv_toContinuousLinearMap]
  exact hasFDerivAt_congruencePolynomial_zero H

/-- A genuine smooth local factorization of symmetric bilinear forms near a
nondegenerate symmetric reference form. The reference factor is literally
the identity, and the factorization is equality of the actual bilinear maps. -/
theorem exists_smooth_congruence_factor
    (H : E ≃L[ℝ] (E →L[ℝ] ℝ)) (hH : ∀ u v, H u v = H v u) :
    ∃ U : Set (SymmetricForm E), IsOpen U ∧ referenceSymmetricForm H hH ∈ U ∧
      ∃ L : SymmetricForm E → (E →L[ℝ] E),
        ContDiffOn ℝ ∞ L U ∧
        L (referenceSymmetricForm H hH) = ContinuousLinearMap.id ℝ E ∧
        ∀ A ∈ U, congruence H.toContinuousLinearMap (L A) = A.val := by
  obtain ⟨e, he0, he⟩ := exists_congruencePolynomial_partialDiffeomorph H
  have he_zero : e (0 : SymmetricForm E) = 0 := by
    rw [he, congruencePolynomial_zero]
  have hzero_target : (0 : SymmetricForm E) ∈ e.target := by
    simpa only [he_zero] using e.toPartialEquiv.map_source he0
  have he_symm_zero : e.invFun (0 : SymmetricForm E) = 0 := by
    have h := e.toPartialEquiv.left_inv he0
    change e.invFun (e.toFun 0) = 0 at h
    change e.toFun 0 = 0 at he_zero
    rwa [he_zero] at h
  let U : Set (SymmetricForm E) :=
    (fun A => A - referenceSymmetricForm H hH) ⁻¹' e.target
  let L : SymmetricForm E → (E →L[ℝ] E) := fun A =>
    ContinuousLinearMap.id ℝ E +
      raiseSymmetricIndex H (e.invFun (A - referenceSymmetricForm H hH))
  have hU : IsOpen U := e.open_target.preimage (continuous_id.sub continuous_const)
  have hHU : referenceSymmetricForm H hH ∈ U := by
    simpa only [U, mem_preimage, sub_self] using hzero_target
  have hinv : ContDiffOn ℝ ∞
      (fun A => e.invFun (A - referenceSymmetricForm H hH)) U :=
    e.contMDiffOn_invFun.contDiffOn.comp
      (contDiff_id.sub contDiff_const).contDiffOn (fun _ hA => hA)
  refine ⟨U, hU, hHU, L, ?_, ?_, ?_⟩
  · exact contDiffOn_const.add ((raiseSymmetricIndex H).contDiff.comp_contDiffOn hinv)
  · simp only [L, sub_self, he_symm_zero, map_zero, add_zero]
  · intro A hA
    have hq : congruencePolynomial H (e.invFun (A - referenceSymmetricForm H hH)) =
        A - referenceSymmetricForm H hH := by
      rw [← he]
      exact e.toPartialEquiv.right_inv hA
    change congruence H.toContinuousLinearMap
      (ContinuousLinearMap.id ℝ E +
        raiseSymmetricIndex H (e.invFun (A - referenceSymmetricForm H hH))) = A.val
    rw [← congruencePolynomial_add_reference H hH, hq, sub_add_cancel]

/-- Pointwise spelling of the native bilinear factorization for direct use
in the Morse coordinate identity. -/
theorem exists_smooth_congruence_factor_apply
    (H : E ≃L[ℝ] (E →L[ℝ] ℝ)) (hH : ∀ u v, H u v = H v u) :
    ∃ U : Set (SymmetricForm E), IsOpen U ∧ referenceSymmetricForm H hH ∈ U ∧
      ∃ L : SymmetricForm E → (E →L[ℝ] E),
        ContDiffOn ℝ ∞ L U ∧
        L (referenceSymmetricForm H hH) = ContinuousLinearMap.id ℝ E ∧
        ∀ A ∈ U, ∀ u v, H (L A u) (L A v) = A.val u v := by
  obtain ⟨U, hU, hHU, L, hL, hLH, hfactor⟩ := exists_smooth_congruence_factor H hH
  refine ⟨U, hU, hHU, L, hL, hLH, ?_⟩
  intro A hA u v
  exact congrArg (fun B : Bilinear E => B u v) (hfactor A hA)

end Wikipedia.HopfProblem.SmoothMorseLemma
