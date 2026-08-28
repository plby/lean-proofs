import Wikipedia.HomotopyGroupsOfSpheres.BalancedCommutatorFamily

/-!
# Imaginary symmetric matrices and the constrained commutator estimate

Multiplication by `i` identifies real symmetric trace-zero directions with
complex symmetric skew-adjoint trace-zero directions. The matrix square
norm and the norm of the commutator are preserved by this passage.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres

namespace ImaginarySymmetricMatrices

open RealUnitaryMatrices

variable {N : Type*} [Fintype N] [DecidableEq N]

def imaginary : Matrix N N ℝ →ₗ[ℝ] Matrix N N ℂ where
  toFun A := Complex.I • complexification A
  map_add' A B := by rw [map_add, smul_add]
  map_smul' c A := by rw [map_smul, smul_comm]; rfl

theorem imaginary_apply (A : Matrix N N ℝ) (i j : N) :
    imaginary A i j = Complex.I * (A i j : ℂ) := rfl

theorem imaginary_im (A : Matrix N N ℝ) (i j : N) :
    (imaginary A i j).im = A i j := by
  rw [imaginary_apply]
  simp

theorem imaginary_injective :
    Function.Injective (imaginary : Matrix N N ℝ → Matrix N N ℂ) := by
  intro A B h
  apply Matrix.ext
  intro i j
  simpa only [imaginary_im] using congrArg (fun C : Matrix N N ℂ ↦ (C i j).im) h

theorem imaginary_transpose (A : Matrix N N ℝ) :
    (imaginary A).transpose = imaginary A.transpose := rfl

theorem imaginary_star (A : Matrix N N ℝ) :
    star (imaginary A) = -imaginary A.transpose := by
  apply Matrix.ext
  intro i j
  change star (Complex.I * (A j i : ℂ)) = -(Complex.I * (A j i : ℂ))
  simp only [star_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem imaginary_trace (A : Matrix N N ℝ) :
    (imaginary A).trace = Complex.I * (A.trace : ℂ) := by
  change (∑ i, Complex.I * (A i i : ℂ)) = Complex.I * ((∑ i, A i i : ℝ) : ℂ)
  rw [Complex.ofReal_sum, Finset.mul_sum]

theorem imaginary_relations (A : RealSymmetricMixing.DirectionSpace N) :
    (imaginary A.val).transpose = imaginary A.val ∧
      star (imaginary A.val) = -imaginary A.val ∧ (imaginary A.val).trace = 0 := by
  exact ⟨by rw [imaginary_transpose, A.property.1],
    by rw [imaginary_star, A.property.1],
    by rw [imaginary_trace, A.property.2, Complex.ofReal_zero, mul_zero]⟩

def squareNorm (A : Matrix N N ℂ) : ℝ := ∑ i, ∑ j, Complex.normSq (A i j)

theorem squareNorm_complexification (A : Matrix N N ℝ) :
    squareNorm (complexification A) = RealMatrixSquareNorm.squareNorm A := by
  change (∑ i, ∑ j, Complex.normSq (A i j : ℂ)) = ∑ i, ∑ j, A i j ^ 2
  simp only [Complex.normSq_ofReal, pow_two]

theorem squareNorm_imaginary (A : Matrix N N ℝ) :
    squareNorm (imaginary A) = RealMatrixSquareNorm.squareNorm A := by
  simp only [squareNorm, imaginary_apply, Complex.normSq_mul, Complex.normSq_I,
    one_mul, Complex.normSq_ofReal, RealMatrixSquareNorm.squareNorm, pow_two]

omit [DecidableEq N] in
theorem squareNorm_neg (A : Matrix N N ℂ) : squareNorm (-A) = squareNorm A := by
  simp only [squareNorm, Matrix.neg_apply, Complex.normSq_neg]

def commutator (A B : Matrix N N ℂ) : Matrix N N ℂ := A * B - B * A

theorem imaginary_mul (A B : Matrix N N ℝ) :
    imaginary A * imaginary B = -complexification (A * B) := by
  change (Complex.I • complexification A) * (Complex.I • complexification B) = _
  rw [smul_mul_smul_comm, Complex.I_mul_I, neg_one_smul, map_mul]

theorem commutator_imaginary (A B : Matrix N N ℝ) :
    commutator (imaginary A) (imaginary B) =
      -complexification (RealMatrixSquareNorm.commutator A B) := by
  rw [commutator, imaginary_mul, imaginary_mul, RealMatrixSquareNorm.commutator, map_sub]
  abel

theorem squareNorm_commutator_imaginary (A B : Matrix N N ℝ) :
    squareNorm (commutator (imaginary A) (imaginary B)) =
      RealMatrixSquareNorm.squareNorm (RealMatrixSquareNorm.commutator A B) := by
  rw [commutator_imaginary, squareNorm_neg, squareNorm_complexification]

def directionMap : RealSymmetricMixing.DirectionSpace N →ₗ[ℝ] Matrix N N ℂ :=
  imaginary.comp (RealSymmetricMixing.symmetricTraceZero N).subtype

theorem directionMap_injective :
    Function.Injective (directionMap : RealSymmetricMixing.DirectionSpace N → Matrix N N ℂ) :=
  imaginary_injective.comp Subtype.val_injective

end ImaginarySymmetricMatrices

namespace BalancedRealInvolutions

open ImaginarySymmetricMatrices

theorem exists_balanced_imaginary_commutator_family (n : ℕ) (m : Index n → ℤ)
    (hsum : ∑ a, (2 * (m a : ℝ) + 1) = 0) (hfast : ∃ a, m a ≠ 0 ∧ m a ≠ -1)
    (U : unitary (Matrix (Index n) (Index n) ℝ)) :
    ∃ L : (Fin n → ℝ) →ₗ[ℝ] Matrix (Index n) (Index n) ℂ, Function.Injective L ∧
      (∀ c, (L c).transpose = L c ∧ star (L c) = -L c ∧ (L c).trace = 0) ∧
      ∀ c, c ≠ 0 → 4 * Real.pi ^ 2 * squareNorm (L c) <
        squareNorm (commutator (imaginary (RealMatrixSquareNorm.conjugate U
          (Matrix.diagonal (fun a ↦ Real.pi * (2 * (m a : ℝ) + 1))))) (L c)) := by
  obtain ⟨L, hL, _, hstrict⟩ := exists_balanced_commutator_family n m hsum hfast U
  refine ⟨directionMap.comp L, directionMap_injective.comp hL, ?_, ?_⟩
  · intro c
    exact imaginary_relations (L c)
  · intro c hc
    change 4 * Real.pi ^ 2 * squareNorm (imaginary (L c).val) <
      squareNorm (commutator (imaginary _) (imaginary (L c).val))
    rw [squareNorm_imaginary, squareNorm_commutator_imaginary]
    exact hstrict c hc

end BalancedRealInvolutions

end Wikipedia.HomotopyGroupsOfSpheres
