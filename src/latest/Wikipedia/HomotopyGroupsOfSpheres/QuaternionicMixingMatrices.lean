import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicHilbertSchmidt
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSpectralSplitting
import Wikipedia.NoExoticSixSphere.OrthogonalCommutator

/-!
# Explicit quaternionic mixing directions

The matrices mix the first quaternionic axis with each other axis using
the scalar `j`. They form an injective real-linear family of skew-adjoint
matrices. Commutation with a diagonal imaginary matrix rotates `j` to `k`
and multiplies the corresponding coefficient by the sum of the two speeds.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.HilbertSchmidt
open NoExoticSixSphere.OrthogonalCommutator

local notation "ℍ" => Quaternion ℝ

variable {n : ℕ}

def mixingMatrix (q : ℍ) (c : Fin n → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ :=
  Matrix.of (Fin.cons (Fin.cons 0 (fun b => c b • q))
    (fun a => Fin.cons (c a • q) (fun _ => 0)))

theorem mixingMatrix_add (q : ℍ) (c d : Fin n → ℝ) :
    mixingMatrix q (c + d) = mixingMatrix q c + mixingMatrix q d := by
  apply Matrix.ext
  intro a b
  cases a using Fin.cases <;> cases b using Fin.cases <;>
    simp [mixingMatrix, add_smul]

theorem mixingMatrix_smul (q : ℍ) (r : ℝ) (c : Fin n → ℝ) :
    mixingMatrix q (r • c) = r • mixingMatrix q c := by
  apply Matrix.ext
  intro a b
  cases a using Fin.cases <;> cases b using Fin.cases <;>
    simp [mixingMatrix, smul_smul]

theorem mixingMatrix_skew (q : ℍ) (hq : star q = -q) (c : Fin n → ℝ) :
    star (mixingMatrix q c) = -(mixingMatrix q c) := by
  apply Matrix.ext
  intro a b
  cases a using Fin.cases <;> cases b using Fin.cases <;>
    simp [mixingMatrix, Matrix.star_apply, hq, smul_neg]

theorem mixingMatrix_injective (q : ℍ) (hq : q ≠ 0) :
    Function.Injective (mixingMatrix (n := n) q) := by
  intro c d h
  funext a
  have ha : c a • q = d a • q :=
    congrArg (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ => A 0 a.succ) h
  exact smul_left_injective ℝ hq ha

def mixingSkewLinear (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] SkewSpace n where
  toFun c := skewOfMatrix n (mixingMatrix QuaternionicScalars.j c)
    (mixingMatrix_skew _ QuaternionicScalars.star_j c)
  map_add' c d := by
    apply Subtype.ext
    exact (congrArg (realAction n) (mixingMatrix_add QuaternionicScalars.j c d)).trans
      (realAction_add n _ _)
  map_smul' r c := by
    apply Subtype.ext
    exact (congrArg (realAction n) (mixingMatrix_smul QuaternionicScalars.j r c)).trans
      (realAction_smul n r _)

theorem mixingSkewLinear_injective (n : ℕ) : Function.Injective (mixingSkewLinear n) := by
  intro c d h
  apply mixingMatrix_injective QuaternionicScalars.j QuaternionicScalars.j_ne_zero
  exact realAction_injective n (congrArg Subtype.val h)

theorem squareNorm_realAction_mixing (q : ℍ) (hq : ‖q‖ = 1) (c : Fin n → ℝ) :
    squareNorm (realAction n (mixingMatrix q c)) = 8 * ∑ a, c a ^ 2 := by
  rw [squareNorm_realAction]
  simp only [Fin.sum_univ_succ, mixingMatrix, Matrix.of_apply, Fin.cons_zero, Fin.cons_succ,
    norm_zero, zero_pow (by decide : 2 ≠ 0), norm_smul, hq, mul_one, Real.norm_eq_abs,
    sq_abs, Finset.sum_const_zero, add_zero, zero_add]
  ring

theorem diagonal_commutator_mixing (α : Fin (n + 1) → ℝ) (c : Fin n → ℝ) :
    Matrix.diagonal (fun a => α a • QuaternionicScalars.i) * mixingMatrix QuaternionicScalars.j c -
      mixingMatrix QuaternionicScalars.j c *
        Matrix.diagonal (fun a => α a • QuaternionicScalars.i) =
    mixingMatrix QuaternionicScalars.k (fun b => (α 0 + α b.succ) * c b) := by
  apply Matrix.ext
  intro a b
  simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  cases a using Fin.cases <;> cases b using Fin.cases
  · simp [mixingMatrix]
  · exact QuaternionicScalars.scalar_commutator_ij _ _ _
  · rename_i a
    change (α a.succ • QuaternionicScalars.i) * (c a • QuaternionicScalars.j) -
      (c a • QuaternionicScalars.j) * (α 0 • QuaternionicScalars.i) =
        ((α 0 + α a.succ) * c a) • QuaternionicScalars.k
    rw [QuaternionicScalars.scalar_commutator_ij, add_comm]
  · simp [mixingMatrix]

theorem realAction_commutator (n : ℕ)
    (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ) :
    commutator (realAction n A) (realAction n B) = realAction n (A * B - B * A) := by
  change realRepresentation n A * realRepresentation n B -
    realRepresentation n B * realRepresentation n A = realRepresentation n (A * B - B * A)
  rw [map_sub, map_mul, map_mul]

theorem squareNorm_diagonal_commutator_mixing (α : Fin (n + 1) → ℝ) (c : Fin n → ℝ) :
    squareNorm (commutator (realAction n (Matrix.diagonal (fun a => α a • QuaternionicScalars.i)))
      (mixingSkewLinear n c).val) = 8 * ∑ a, ((α 0 + α a.succ) * c a) ^ 2 := by
  change squareNorm (commutator (realAction n _)
    (realAction n (mixingMatrix QuaternionicScalars.j c))) = _
  rw [realAction_commutator, diagonal_commutator_mixing,
    squareNorm_realAction_mixing QuaternionicScalars.k QuaternionicScalars.norm_k]

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
