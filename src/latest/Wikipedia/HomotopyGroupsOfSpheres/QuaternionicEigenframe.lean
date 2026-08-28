import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicRotationEigenvector
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumnAction

/-!
# Quaternionic unitary frames containing a fast eigenvector

The eigenvector is expressed as an actual unit quaternionic column and
completed to a unitary matrix. Conjugating by that matrix isolates its
eigenvalue in the first coordinate; skew-adjointness also eliminates the
corresponding off-diagonal row. This is a spectral splitting of the original
matrix, not a change of its topology or homotopy groups.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

open QuaternionicRankOne NoExoticSixSphere.GLOrthonormalization
open NoExoticSixSphere.SkewSpectralPlane

local notation "ℍ" => Quaternion ℝ

theorem coefficients_mulVec (n : ℕ)
    (T : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) (hT : T ∈ commutant n)
    (v : QuaternionSpace n) :
    coefficients n T *ᵥ WithLp.ofLp v = WithLp.ofLp (coordinateOperator n T v) := by
  have he := congrArg (fun L : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4) =>
    WithLp.ofLp ((quaternionCoordinates n).symm (L (quaternionCoordinates n v))))
      (realAction_coefficients n T hT)
  simpa only [realAction_apply, coordinateOperator_apply,
    (quaternionCoordinates n).symm_apply_apply, WithLp.ofLp_toLp] using he

theorem coefficients_skew {n : ℕ} (K : SkewSpace n) :
    star (coefficients n K.val) = -(coefficients n K.val) := by
  apply realAction_injective n
  rw [realAction_star, realAction_coefficients n K.val K.property.2]
  have hn : realAction n (-(coefficients n K.val)) = -(realAction n (coefficients n K.val)) :=
    (realRepresentation n).map_neg _
  rw [hn, realAction_coefficients n K.val K.property.2]
  exact K.property.1

theorem unit_column_of_i_eigenvector {n : ℕ} (K : SkewSpace n)
    {α : ℝ} {v : Vector (4 * n + 4)} (hv : ‖v‖ = 1)
    (he : K.val v = α • rightAction n QuaternionicScalars.i v) :
    ∃ u : UnitColumn (Fin (n + 1)),
      coefficients n K.val *ᵥ u.val = fun a => u.val a * (α • QuaternionicScalars.i) := by
  let w := (quaternionCoordinates n).symm v
  have hw : pairing (WithLp.ofLp w) (WithLp.ofLp w) = 1 := by
    apply (pairing_self_eq_one_iff_norm _).mpr
    change ‖w‖ = 1
    exact ((quaternionCoordinates n).symm.norm_map v).trans hv
  refine ⟨⟨WithLp.ofLp w, hw⟩, ?_⟩
  rw [coefficients_mulVec n K.val K.property.2 w]
  have hew : coordinateOperator n K.val w = α • rightMulLinear n QuaternionicScalars.i w := by
    change (quaternionCoordinates n).symm (K.val (quaternionCoordinates n w)) = _
    rw [(quaternionCoordinates n).apply_symm_apply, he, map_smul, rightAction_apply,
      (quaternionCoordinates n).symm_apply_apply]
  rw [hew]
  funext a
  change α • (WithLp.ofLp w a * QuaternionicScalars.i) =
    WithLp.ofLp w a * (α • QuaternionicScalars.i)
  exact (mul_smul_comm _ _ _).symm

section MatrixSplitting

variable {N : Type*} [Fintype N] [DecidableEq N]

def conjugateMatrix (U : SpGroup N) (A : Matrix N N ℍ) : Matrix N N ℍ :=
  star U.val * A * U.val

theorem conjugateMatrix_skew (U : SpGroup N) (A : Matrix N N ℍ) (hA : star A = -A) :
    star (conjugateMatrix U A) = -(conjugateMatrix U A) := by
  simp only [conjugateMatrix, star_mul, star_star, hA, mul_neg, neg_mul, mul_assoc]

theorem conjugateMatrix_column (U : SpGroup N) (A : Matrix N N ℍ) (a : N) (q : ℍ)
    (he : A *ᵥ (column a U).val = fun b => (column a U).val b * q) (b : N) :
    conjugateMatrix U A b a = if b = a then q else 0 := by
  calc
    conjugateMatrix U A b a =
        ((star U.val) *ᵥ (A *ᵥ (column a U).val)) b := by
      rw [Matrix.mulVec_mulVec]
      rfl
    _ = ((star U.val) *ᵥ (fun c => (column a U).val c * q)) b := by rw [he]
    _ = (star U.val * U.val) b a * q := by
      simp only [Matrix.mulVec, Matrix.mul_apply, dotProduct, column,
        ContinuousMap.coe_mk, Finset.sum_mul, mul_assoc]
    _ = (1 : Matrix N N ℍ) b a * q := by rw [Unitary.star_mul_self_of_mem U.property]
    _ = if b = a then q else 0 := by
      by_cases h : b = a <;> simp [Matrix.one_apply, h]

theorem conjugateMatrix_row_zero (U : SpGroup N) (A : Matrix N N ℍ)
    (hA : star A = -A) {a b : N} (hcol : conjugateMatrix U A b a = 0) :
    conjugateMatrix U A a b = 0 := by
  have h := congrArg (fun M : Matrix N N ℍ => M b a) (conjugateMatrix_skew U A hA)
  change star (conjugateMatrix U A a b) = -(conjugateMatrix U A b a) at h
  rw [hcol, neg_zero] at h
  exact star_eq_zero.mp h

end MatrixSplitting

/-- A unitary change of coordinates separates a genuine fast quaternionic eigenline. -/
theorem exists_fast_eigenframe {n : ℕ} (K : SkewSpace n)
    (hexp : (Exponential.exp K).val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (hnot : gram (toOrthogonalSkew n K) ≠
      Real.pi ^ 2 • (1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4))) :
    ∃ (α : ℝ) (U : SpGroup (Fin (n + 1))), 3 * Real.pi ≤ α ∧
      conjugateMatrix U (coefficients n K.val) 0 0 = α • QuaternionicScalars.i ∧
      ∀ b : Fin (n + 1), b ≠ 0 →
        conjugateMatrix U (coefficients n K.val) b 0 = 0 ∧
        conjugateMatrix U (coefficients n K.val) 0 b = 0 := by
  obtain ⟨α, v, hα, hv, he⟩ := exists_fast_i_eigenvector K hexp hnot
  obtain ⟨u, hu⟩ := unit_column_of_i_eigenvector K hv he
  obtain ⟨U, hU⟩ := column_surjective (0 : Fin (n + 1)) u
  rw [← hU] at hu
  refine ⟨α, U, hα, ?_, ?_⟩
  · simpa only [ite_true] using
      conjugateMatrix_column U (coefficients n K.val) 0 (α • QuaternionicScalars.i) hu 0
  · intro b hb
    have hcol : conjugateMatrix U (coefficients n K.val) b 0 = 0 := by
      simpa only [hb, ite_false] using
        conjugateMatrix_column U (coefficients n K.val) 0 (α • QuaternionicScalars.i) hu b
    exact ⟨hcol, conjugateMatrix_row_zero U _ (coefficients_skew K) hcol⟩

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
