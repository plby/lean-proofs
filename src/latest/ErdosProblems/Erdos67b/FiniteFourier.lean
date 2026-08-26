import ErdosProblems.Erdos67b.FourierReduction

/-!
# Normalized finite Fourier transform for the Erdős discrepancy proof

This file packages the finite Fourier calculation in the normalization used in Tao's Section 2.
The results hold for every finite abelian group and are specialized at the end to `(ZMod M)^r`.
-/

open Finset
open scoped BigOperators ComplexConjugate

namespace Erdos67b

noncomputable section

section NormalizedFiniteFourier

variable {G E : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The finite Fourier coefficient normalized by `|G|`, i.e. by uniform averaging. -/
def fourierCoeff (F : G → E) (psi : AddChar G ℂ) : E :=
  (Fintype.card G : ℂ)⁻¹ • rawCoeff F psi

/-- Polarized Plancherel for the normalized vector-valued finite Fourier transform. -/
theorem sum_inner_fourierCoeff (F K : G → E) :
    ∑ psi : AddChar G ℂ, inner ℂ (fourierCoeff F psi) (fourierCoeff K psi) =
      (Fintype.card G : ℂ)⁻¹ * ∑ x : G, inner ℂ (F x) (K x) := by
  classical
  let c : ℂ := (Fintype.card G : ℂ)⁻¹
  have hcstar : (starRingEnd ℂ) c = c := by simp [c]
  calc
    (∑ psi : AddChar G ℂ, inner ℂ (fourierCoeff F psi) (fourierCoeff K psi)) =
        c * c * ∑ psi : AddChar G ℂ,
          inner ℂ (rawCoeff F psi) (rawCoeff K psi) := by
      change (∑ psi : AddChar G ℂ,
        inner ℂ (c • rawCoeff F psi) (c • rawCoeff K psi)) = _
      simp only [inner_smul_left, inner_smul_right, hcstar]
      simp only [Finset.mul_sum, mul_assoc]
    _ = c * c * ((Fintype.card G : ℂ) *
        ∑ x : G, inner ℂ (F x) (K x)) := by rw [sum_inner_rawCoeff]
    _ = (Fintype.card G : ℂ)⁻¹ * ∑ x : G, inner ℂ (F x) (K x) := by
      have hn : (Fintype.card G : ℂ) ≠ 0 := by
        exact_mod_cast Fintype.card_ne_zero
      have hcn : c * (Fintype.card G : ℂ) = 1 := inv_mul_cancel₀ hn
      rw [mul_assoc c c, ← mul_assoc c (Fintype.card G : ℂ), hcn]
      simp [c]

/-- Vector-valued finite Plancherel in squared-norm form. -/
theorem sum_norm_sq_fourierCoeff (F : G → E) :
    ∑ psi : AddChar G ℂ, ‖fourierCoeff F psi‖ ^ 2 =
      (Fintype.card G : ℝ)⁻¹ * ∑ x : G, ‖F x‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  simpa [inner_self_eq_norm_sq_to_K] using (sum_inner_fourierCoeff F F)

/-- The same Plancherel identity with the uniform average written as division by `|G|`. -/
theorem sum_norm_sq_fourierCoeff_eq_average (F : G → E) :
    ∑ psi : AddChar G ℂ, ‖fourierCoeff F psi‖ ^ 2 =
      (∑ x : G, ‖F x‖ ^ 2) / Fintype.card G := by
  simpa only [div_eq_inv_mul] using (sum_norm_sq_fourierCoeff F)

omit [DecidableEq G] in
private lemma char_mul_conj_ff (psi : AddChar G ℂ) (x y : G) :
    psi x * conj (psi y) = psi (x - y) := by
  calc
    psi x * conj (psi y) = psi x * (psi y)⁻¹ := by rw [psi.inv_apply_eq_conj]
    _ = psi x * psi (-y) := by rw [psi.map_neg_eq_inv]
    _ = psi (x + -y) := (psi.map_add_eq_mul x (-y)).symm
    _ = psi (x - y) := by rw [sub_eq_add_neg]

private lemma sum_char_mul_conj_ff (x y : G) :
    ∑ psi : AddChar G ℂ, psi x * conj (psi y) =
      if x = y then (Fintype.card G : ℂ) else 0 := by
  simp_rw [char_mul_conj_ff]
  simpa only [sub_eq_zero] using (AddChar.sum_apply_eq_ite (a := x - y))

/-- Orthogonality gives the unnormalized Fourier synthesis formula. -/
theorem sum_character_smul_rawCoeff (F : G → E) (x : G) :
    ∑ psi : AddChar G ℂ, psi x • rawCoeff F psi =
      (Fintype.card G : ℂ) • F x := by
  classical
  simp only [rawCoeff, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, sum_char_mul_conj_ff]
  simp

/-- Fourier synthesis (inversion) for the normalized coefficients. -/
theorem fourier_inversion (F : G → E) (x : G) :
    ∑ psi : AddChar G ℂ, psi x • fourierCoeff F psi = F x := by
  classical
  let c : ℂ := (Fintype.card G : ℂ)⁻¹
  calc
    (∑ psi : AddChar G ℂ, psi x • fourierCoeff F psi) =
        c • ∑ psi : AddChar G ℂ, psi x • rawCoeff F psi := by
      change (∑ psi : AddChar G ℂ, psi x • (c • rawCoeff F psi)) = _
      simp only [Finset.smul_sum, smul_smul, mul_comm]
    _ = c • ((Fintype.card G : ℂ) • F x) := by
      rw [sum_character_smul_rawCoeff]
    _ = F x := by
      have hn : (Fintype.card G : ℂ) ≠ 0 := by
        exact_mod_cast Fintype.card_ne_zero
      rw [smul_smul]
      simp [c, hn]

end NormalizedFiniteFourier

section PiZMod

variable (M r : ℕ) [NeZero M]

/-- The cardinality of `(ZMod M)^r`. -/
theorem card_pi_zmod : Fintype.card (Fin r → ZMod M) = M ^ r := by
  simp [ZMod.card]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Vector-valued Plancherel on `(ZMod M)^r`, in Tao's normalization. -/
theorem sum_norm_sq_fourierCoeff_piZMod (F : (Fin r → ZMod M) → E) :
    ∑ psi : AddChar (Fin r → ZMod M) ℂ, ‖fourierCoeff F psi‖ ^ 2 =
      (M ^ r : ℝ)⁻¹ * ∑ x : Fin r → ZMod M, ‖F x‖ ^ 2 := by
  simpa [card_pi_zmod] using (sum_norm_sq_fourierCoeff F)

end PiZMod

end


end Erdos67b
