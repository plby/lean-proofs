import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicEigenframe
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumnFiber

/-! # A one-dimensional quaternionic spectral splitting for every skew-adjoint matrix -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.SkewSpectralPlane

local notation "ℍ" => Quaternion ℝ

def skewOfMatrix (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ)
    (hA : star A = -A) : SkewSpace n :=
  ⟨realAction n A, ⟨by
    change (realAction n A).adjoint = -(realAction n A)
    rw [← realAction_star, hA]
    exact (realRepresentation n).map_neg _, realAction_mem_commutant n A⟩⟩

theorem exists_nonnegative_eigenframe (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ) (hA : star A = -A) :
    ∃ (α : ℝ) (U : SpGroup (Fin (n + 1))), 0 ≤ α ∧
      conjugateMatrix U A 0 0 = α • QuaternionicScalars.i ∧
      ∀ b : Fin (n + 1), b ≠ 0 →
        conjugateMatrix U A b 0 = 0 ∧ conjugateMatrix U A 0 b = 0 := by
  by_cases hzero : A = 0
  · subst A
    refine ⟨0, 1, le_rfl, ?_, ?_⟩ <;> simp [conjugateMatrix]
  · let K := skewOfMatrix n A hA
    have hK : K.val ≠ 0 := by
      intro h
      apply hzero
      apply realAction_injective n
      exact h.trans (realRepresentation n).map_zero.symm
    obtain ⟨α, x, y, hα, hx, _, _, hKx, hKy⟩ :=
      exists_rotationPlane (toOrthogonalSkew n K) hK
    have hx0 : x ≠ 0 := by
      intro he
      exact zero_ne_one (by simpa only [he, norm_zero] using hx)
    obtain ⟨v, hv, he⟩ := exists_unit_i_eigenvector_of_rotation K hx0 hKx hKy
    obtain ⟨u, hu⟩ := unit_column_of_i_eigenvector K hv he
    have hcoeff : coefficients n K.val = A := coefficients_realAction n A
    rw [hcoeff] at hu
    obtain ⟨U, hU⟩ := column_surjective (0 : Fin (n + 1)) u
    rw [← hU] at hu
    refine ⟨α, U, hα.le, ?_, ?_⟩
    · simpa only [ite_true] using
        conjugateMatrix_column U A 0 (α • QuaternionicScalars.i) hu 0
    · intro b hb
      have hcol : conjugateMatrix U A b 0 = 0 := by
        simpa only [hb, ite_false] using
          conjugateMatrix_column U A 0 (α • QuaternionicScalars.i) hu b
      exact ⟨hcol, conjugateMatrix_row_zero U A hA hcol⟩

/-- A scalar diagonal block followed by an arbitrary quaternionic matrix. -/
def splitMatrix {n : ℕ} (q : ℍ) (B : Matrix (Fin n) (Fin n) ℍ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ :=
  Matrix.of (Fin.cons (Fin.cons q (fun _ => 0)) (fun i => Fin.cons 0 (fun j => B i j)))

theorem splitMatrix_eq_of_entries {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ) (q : ℍ)
    (h00 : A 0 0 = q) (hc : ∀ b : Fin (n + 1), b ≠ 0 → A b 0 = 0 ∧ A 0 b = 0) :
    A = splitMatrix q (lowerBlock A) := by
  apply Matrix.ext
  intro i j
  cases i using Fin.cases <;> cases j using Fin.cases
  · exact h00
  · exact (hc _ (Fin.succ_ne_zero _)).2
  · exact (hc _ (Fin.succ_ne_zero _)).1
  · rfl

theorem lowerBlock_skew {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ)
    (hA : star A = -A) : star (lowerBlock A) = -(lowerBlock A) := by
  apply Matrix.ext
  intro i j
  exact congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ => M i.succ j.succ) hA

/-- Every skew-adjoint quaternionic matrix splits off a nonnegative imaginary eigenvalue. -/
theorem exists_spectral_split (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ) (hA : star A = -A) :
    ∃ (α : ℝ) (U : SpGroup (Fin (n + 1))) (B : Matrix (Fin n) (Fin n) ℍ),
      0 ≤ α ∧ star B = -B ∧ conjugateMatrix U A = splitMatrix (α • QuaternionicScalars.i) B := by
  obtain ⟨α, U, hα, h00, hc⟩ := exists_nonnegative_eigenframe n A hA
  exact ⟨α, U, lowerBlock (conjugateMatrix U A), hα,
    lowerBlock_skew _ (conjugateMatrix_skew U A hA),
    splitMatrix_eq_of_entries _ _ h00 hc⟩

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
