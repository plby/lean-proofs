import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicJointEigenvector
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSpectralTheorem

/-!
# A unitary frame containing an actual joint quaternionic eigenline

Both eigenvector equations are transported through the same unit quaternionic
column. Completing that column gives a common block splitting for the skew
generator and the anticommuting complex structure.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

open NoExoticSixSphere.GLOrthonormalization ComplexStructures

local notation "ℍ" => Quaternion ℝ

variable {n : ℕ}

def unitColumnOfVector (v : Vector (4 * n + 4)) (hv : ‖v‖ = 1) :
    UnitColumn (Fin (n + 1)) :=
  ⟨WithLp.ofLp ((quaternionCoordinates n).symm v), by
    apply (pairing_self_eq_one_iff_norm _).mpr
    exact ((quaternionCoordinates n).symm.norm_map v).trans hv⟩

theorem unitColumnOfVector_eigen (T : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4))
    (hT : T ∈ commutant n) (v : Vector (4 * n + 4)) (hv : ‖v‖ = 1) (q : ℍ) (α : ℝ)
    (he : T v = α • rightAction n q v) :
    coefficients n T *ᵥ (unitColumnOfVector v hv).val =
      fun a ↦ (unitColumnOfVector v hv).val a * (α • q) := by
  let w := (quaternionCoordinates n).symm v
  change coefficients n T *ᵥ WithLp.ofLp w = fun a ↦ WithLp.ofLp w a * (α • q)
  rw [coefficients_mulVec n T hT w]
  have hew : coordinateOperator n T w = α • rightMulLinear n q w := by
    change (quaternionCoordinates n).symm (T (quaternionCoordinates n w)) = _
    rw [(quaternionCoordinates n).apply_symm_apply, he, map_smul, rightAction_apply,
      (quaternionCoordinates n).symm_apply_apply]
  rw [hew]
  funext a
  change α • (WithLp.ofLp w a * q) = WithLp.ofLp w a * (α • q)
  exact (mul_smul_comm _ _ _).symm

theorem conjugateMatrix_split_of_eigenColumn (U : SpGroup (Fin (n + 1)))
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ) (hA : star A = -A) (q : ℍ)
    (he : A *ᵥ (column 0 U).val = fun b ↦ (column 0 U).val b * q) :
    conjugateMatrix U A = splitMatrix q (lowerBlock (conjugateMatrix U A)) := by
  apply splitMatrix_eq_of_entries
  · simpa only [ite_true] using conjugateMatrix_column U A 0 q he 0
  · intro b hb
    have hc : conjugateMatrix U A b 0 = 0 := by
      simpa only [hb, ite_false] using conjugateMatrix_column U A 0 q he b
    exact ⟨hc, conjugateMatrix_row_zero U A hA hc⟩

theorem exists_joint_eigenframe (J : Space n) (K : SkewSpace n) (α : ℝ)
    (v : Vector (4 * n + 4)) (hv : ‖v‖ = 1)
    (hKv : K.val v = α • rightAction n QuaternionicScalars.i v)
    (hJv : J.val.val v = rightAction n QuaternionicScalars.j v) :
    ∃ U : SpGroup (Fin (n + 1)),
      conjugateMatrix U (coefficients n K.val) = splitMatrix (α • QuaternionicScalars.i)
        (lowerBlock (conjugateMatrix U (coefficients n K.val))) ∧
      conjugateMatrix U (coefficients n J.val.val) = splitMatrix QuaternionicScalars.j
        (lowerBlock (conjugateMatrix U (coefficients n J.val.val))) := by
  let u := unitColumnOfVector v hv
  have hKu := unitColumnOfVector_eigen K.val K.property.2 v hv QuaternionicScalars.i α hKv
  have hJu : coefficients n J.val.val *ᵥ u.val = fun a ↦ u.val a * QuaternionicScalars.j := by
    simpa only [one_smul] using unitColumnOfVector_eigen J.val.val J.val.property.2 v hv
      QuaternionicScalars.j 1 (by simpa only [one_smul] using hJv)
  obtain ⟨U, hU⟩ := column_surjective (0 : Fin (n + 1)) u
  change coefficients n K.val *ᵥ u.val = fun a ↦ u.val a * (α • QuaternionicScalars.i) at hKu
  rw [← hU] at hKu hJu
  exact ⟨U, conjugateMatrix_split_of_eigenColumn U _ (coefficients_skew K) _ hKu,
    conjugateMatrix_split_of_eigenColumn U _ (coefficients_skew J.val) _ hJu⟩

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
