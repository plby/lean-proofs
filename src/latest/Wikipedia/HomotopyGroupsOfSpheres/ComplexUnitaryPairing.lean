import Wikipedia.HomotopyGroupsOfSpheres.ComplexUnitaryEntryNorm

/-! # Preservation of the actual complex Hermitian pairing by unitary matrices -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexUnitaryEntryNorm

variable {N : Type*} [Fintype N] [DecidableEq N]

def hermitianPairing (v w : N → ℂ) : ℂ := star v ⬝ᵥ w

theorem pairing_mulVec (U : unitary (Matrix N N ℂ)) (v w : N → ℂ) :
    hermitianPairing (U.val *ᵥ v) (U.val *ᵥ w) = hermitianPairing v w := by
  unfold hermitianPairing
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  change (star v ᵥ* (star U.val * U.val)) ⬝ᵥ w = _
  rw [Unitary.coe_star_mul_self, Matrix.vecMul_one]

omit [DecidableEq N] in
theorem pairing_smul (a b : ℂ) (v w : N → ℂ) :
    hermitianPairing (a • v) (b • w) = star a * b * hermitianPairing v w := by
  simp only [hermitianPairing, dotProduct, Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

omit [DecidableEq N] in
theorem pairing_self (v : N → ℂ) :
    hermitianPairing v v = ((∑ r, Complex.normSq (v r) : ℝ) : ℂ) := by
  simp [hermitianPairing, dotProduct, ← Complex.normSq_eq_conj_mul_self]

theorem sum_normSq_mulVec (U : unitary (Matrix N N ℂ)) (v : N → ℂ) :
    ∑ r, Complex.normSq ((U.val *ᵥ v) r) = ∑ r, Complex.normSq (v r) := by
  have h := pairing_mulVec U v v
  rw [pairing_self, pairing_self] at h
  exact_mod_cast h

end Wikipedia.HomotopyGroupsOfSpheres.ComplexUnitaryEntryNorm
