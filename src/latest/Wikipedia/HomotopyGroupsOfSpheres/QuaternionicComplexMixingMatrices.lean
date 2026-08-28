import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicDiagonalIndex

/-!
# Mixing directions compatible with a diagonal quaternionic complex structure

Using `k` for the mixing entries makes every direction anticommute with
diagonal `j`. Its commutator with diagonal `α i` has the same norm estimate
as the first symplectic mixing family.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres

namespace QuaternionicScalars

theorem i_mul_k : i * k = -j := by
  have h : (QuaternionAlgebra.mk 0 1 0 0 : QuaternionAlgebra ℝ (-1) 0 (-1)) *
      QuaternionAlgebra.mk 0 0 0 1 = -QuaternionAlgebra.mk 0 0 1 0 := by ext <;> norm_num
  exact h

theorem k_mul_i : k * i = j := by
  have h : (QuaternionAlgebra.mk 0 0 0 1 : QuaternionAlgebra ℝ (-1) 0 (-1)) *
      QuaternionAlgebra.mk 0 1 0 0 = QuaternionAlgebra.mk 0 0 1 0 := by ext <;> norm_num
  exact h

theorem j_mul_k_eq_neg_k_mul_j : j * k = -(k * j) := by
  have h : (QuaternionAlgebra.mk 0 0 1 0 : QuaternionAlgebra ℝ (-1) 0 (-1)) *
      QuaternionAlgebra.mk 0 0 0 1 =
        -(QuaternionAlgebra.mk 0 0 0 1 * QuaternionAlgebra.mk 0 0 1 0) := by ext <;> norm_num
  exact h

theorem k_ne_zero : k ≠ 0 := by
  intro h
  have he := congrArg QuaternionAlgebra.imK h
  change (1 : ℝ) = 0 at he
  exact one_ne_zero he

theorem scalar_commutator_ik (a b c : ℝ) :
    (a • i) * (c • k) - (c • k) * (b • i) = ((a + b) * c) • (-j) := by
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, i_mul_k, k_mul_i,
    smul_neg, sub_eq_add_neg, ← neg_add, ← add_smul]
  congr 2
  ring

end QuaternionicScalars

namespace QuaternionicColumns

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.HilbertSchmidt
open NoExoticSixSphere.OrthogonalCommutator

local notation "ℍ" => Quaternion ℝ

variable {n : ℕ}

def complexMixingLinear (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] SkewSpace n where
  toFun c := skewOfMatrix n (mixingMatrix QuaternionicScalars.k c)
    (mixingMatrix_skew _ QuaternionicScalars.star_k c)
  map_add' c d := by
    apply Subtype.ext
    exact (congrArg (realAction n) (mixingMatrix_add QuaternionicScalars.k c d)).trans
      (realAction_add n _ _)
  map_smul' r c := by
    apply Subtype.ext
    exact (congrArg (realAction n) (mixingMatrix_smul QuaternionicScalars.k r c)).trans
      (realAction_smul n r _)

theorem complexMixingLinear_injective (n : ℕ) : Function.Injective (complexMixingLinear n) := by
  intro c d h
  apply mixingMatrix_injective QuaternionicScalars.k QuaternionicScalars.k_ne_zero
  exact realAction_injective n (congrArg Subtype.val h)

theorem j_complexMixing_anticommute (c : Fin n → ℝ) :
    Matrix.diagonal (fun _ : Fin (n + 1) ↦ QuaternionicScalars.j) *
      mixingMatrix QuaternionicScalars.k c =
        -(mixingMatrix QuaternionicScalars.k c *
          Matrix.diagonal (fun _ : Fin (n + 1) ↦ QuaternionicScalars.j)) := by
  apply Matrix.ext
  intro a b
  simp only [Matrix.diagonal_mul, Matrix.neg_apply, Matrix.mul_diagonal]
  cases a using Fin.cases <;> cases b using Fin.cases <;>
    simp [mixingMatrix,
      QuaternionicScalars.j_mul_k_eq_neg_k_mul_j, smul_neg]

theorem diagonal_commutator_complexMixing (α : Fin (n + 1) → ℝ) (c : Fin n → ℝ) :
    Matrix.diagonal (fun a ↦ α a • QuaternionicScalars.i) * mixingMatrix QuaternionicScalars.k c -
      mixingMatrix QuaternionicScalars.k c *
        Matrix.diagonal (fun a ↦ α a • QuaternionicScalars.i) =
      mixingMatrix (-QuaternionicScalars.j) (fun b ↦ (α 0 + α b.succ) * c b) := by
  apply Matrix.ext
  intro a b
  simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  cases a using Fin.cases <;> cases b using Fin.cases
  · simp [mixingMatrix]
  · exact QuaternionicScalars.scalar_commutator_ik _ _ _
  · rename_i a
    change (α a.succ • QuaternionicScalars.i) * (c a • QuaternionicScalars.k) -
      (c a • QuaternionicScalars.k) * (α 0 • QuaternionicScalars.i) =
        ((α 0 + α a.succ) * c a) • (-QuaternionicScalars.j)
    rw [QuaternionicScalars.scalar_commutator_ik, add_comm]
  · simp [mixingMatrix]

theorem squareNorm_complexMixing (c : Fin n → ℝ) :
    squareNorm (complexMixingLinear n c).val = 8 * ∑ a, c a ^ 2 :=
  squareNorm_realAction_mixing QuaternionicScalars.k QuaternionicScalars.norm_k c

theorem squareNorm_diagonal_commutator_complexMixing (α : Fin (n + 1) → ℝ) (c : Fin n → ℝ) :
    squareNorm (commutator (realAction n (Matrix.diagonal (fun a ↦ α a • QuaternionicScalars.i)))
      (complexMixingLinear n c).val) = 8 * ∑ a, ((α 0 + α a.succ) * c a) ^ 2 := by
  change squareNorm (commutator (realAction n _)
    (realAction n (mixingMatrix QuaternionicScalars.k c))) = _
  rw [realAction_commutator, diagonal_commutator_complexMixing,
    squareNorm_realAction_mixing (-QuaternionicScalars.j)
      (by rw [norm_neg, QuaternionicScalars.norm_j])]

theorem diagonal_complexMixing_commutator_strict (α : Fin (n + 1) → ℝ)
    (hfast : 3 * Real.pi ≤ α 0) (hslow : ∀ a : Fin n, Real.pi ≤ α a.succ)
    (c : Fin n → ℝ) (hc : c ≠ 0) :
    4 * Real.pi ^ 2 * squareNorm (complexMixingLinear n c).val <
      squareNorm (commutator (realAction n (Matrix.diagonal (fun a ↦ α a • QuaternionicScalars.i)))
        (complexMixingLinear n c).val) := by
  have h := diagonal_mixing_commutator_strict α hfast hslow c hc
  rw [squareNorm_diagonal_commutator_mixing] at h
  change 4 * Real.pi ^ 2 * squareNorm (realAction n (mixingMatrix QuaternionicScalars.j c)) < _ at h
  rw [squareNorm_realAction_mixing QuaternionicScalars.j QuaternionicScalars.norm_j] at h
  rw [squareNorm_complexMixing, squareNorm_diagonal_commutator_complexMixing]
  exact h

end QuaternionicColumns
end Wikipedia.HomotopyGroupsOfSpheres
