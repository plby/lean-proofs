import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicDiagonalIndex
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicConjugation
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicAntipodalDiagonalization

/-!
# A rank-growing negative-direction estimate inside the symplectic Lie algebra

For `Sp(n+1)`, the explicit construction gives `n` independent real directions
with a strict commutator bound at every nonminimal antipodal exponential.
This conservative bound grows with rank and suffices for a stable Bott
comparison. It is a pointwise estimate, not yet a Morse deformation theorem.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.HilbertSchmidt
open NoExoticSixSphere.OrthogonalCommutator NoExoticSixSphere.SkewSpectralPlane

variable {n : ℕ}

theorem transported_mixing_commutator_norm (K : SkewSpace n)
    (U : SpGroup (Fin (n + 1))) (α : Fin (n + 1) → ℝ)
    (hd : conjugateMatrix U (coefficients n K.val) =
      Matrix.diagonal (fun a => α a • QuaternionicScalars.i)) (c : Fin n → ℝ) :
    squareNorm (commutator K.val (transportedMixingLinear U c).val) =
      squareNorm (commutator (realAction n (Matrix.diagonal (fun a => α a • QuaternionicScalars.i)))
        (mixingSkewLinear n c).val) := by
  have hcancel : conjugateMatrix U
      (conjugateMatrix U⁻¹ (mixingMatrix QuaternionicScalars.j c)) =
        mixingMatrix QuaternionicScalars.j c := by
    simpa only [inv_inv] using
      conjugateMatrix_inv_cancel U⁻¹ (mixingMatrix QuaternionicScalars.j c)
  have h := squareNorm_commutator_conjugateMatrix U (coefficients n K.val)
    (conjugateMatrix U⁻¹ (mixingMatrix QuaternionicScalars.j c))
  rw [hd, hcancel, realAction_coefficients n K.val K.property.2] at h
  exact h.symm

/-- A nonminimal antipodal symplectic generator has a linear family of `n`
independent quaternionic directions with strictly negative index-form criterion. -/
theorem exists_negativeFamily (K : SkewSpace n)
    (hexp : (Exponential.exp K).val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (hnot : gram (toOrthogonalSkew n K) ≠
      Real.pi ^ 2 • (1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4))) :
    ∃ T : (Fin n → ℝ) →ₗ[ℝ] SkewSpace n, Function.Injective T ∧
      ∀ c, c ≠ 0 → 4 * Real.pi ^ 2 * squareNorm (T c).val <
        squareNorm (commutator K.val (T c).val) := by
  obtain ⟨U, m, hm, hd⟩ := exists_fast_antipodal_diagonalization K hexp hnot
  let α : Fin (n + 1) → ℝ := fun a => (2 * (m a : ℝ) + 1) * Real.pi
  have hfast : 3 * Real.pi ≤ α 0 := by
    have hm' : (1 : ℝ) ≤ m 0 := by exact_mod_cast hm
    dsimp [α]
    nlinarith [Real.pi_pos]
  have hslow (a : Fin n) : Real.pi ≤ α a.succ := by
    dsimp [α]
    nlinarith [Real.pi_pos, Nat.cast_nonneg' (α := ℝ) (m a.succ)]
  refine ⟨transportedMixingLinear U, transportedMixingLinear_injective U, fun c hc => ?_⟩
  rw [squareNorm_transportedMixing, transported_mixing_commutator_norm K U α hd]
  exact diagonal_mixing_commutator_strict α hfast hslow c hc

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
