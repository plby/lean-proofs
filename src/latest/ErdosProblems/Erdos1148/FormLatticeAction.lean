import ErdosProblems.Erdos1148.FormEmbeddingAction
import ErdosProblems.Erdos1148.ProperFormLattice

/-! # Integral changes of form rescale the associated lattice -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma integralSL_preserves_standardRationalLattice (γ : SL(2, ℤ)) :
    ∀ v ∈ standardRationalLattice,
      ((γ : SL(2, ℚ)) : Matrix (Fin 2) (Fin 2) ℚ).mulVec v ∈ standardRationalLattice :=
  (matrix_preserves_standardRationalLattice_iff _).mpr ⟨γ.1, rfl⟩

lemma integralSL_mulVec_mem_iff (γ : SL(2, ℤ)) (v : Fin 2 → ℚ) :
    ((γ : SL(2, ℚ)) : Matrix (Fin 2) (Fin 2) ℚ).mulVec v ∈ standardRationalLattice ↔
      v ∈ standardRationalLattice := by
  constructor
  · intro hv
    have hi := integralSL_preserves_standardRationalLattice γ⁻¹ _ hv
    have hγ : ((γ⁻¹ : SL(2, ℤ)) : SL(2, ℚ)) * (γ : SL(2, ℚ)) = 1 := by simp
    simpa only [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, hγ,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec] using hi
  · exact integralSL_preserves_standardRationalLattice γ v

noncomputable def formActionScale {d : ℤ} (t : ℤ × ℤ × ℤ) (ha : t.1 ≠ 0)
    (γ : SL(2, ℤ)) : QuadraticDiscrAlgebra d :=
  (formLatticeCoordinates t ha).symm (fun i => ((γ : SL(2, ℚ))⁻¹ : SL(2, ℚ)) i 0)

lemma formLatticeCoordinates_action {d : ℤ} {t : ℤ × ℤ × ℤ}
    (ht : discr t = d) (ha : t.1 ≠ 0) (γ : SL(2, ℤ))
    (ha' : (formAction γ t).1 ≠ 0) (w : QuadraticDiscrAlgebra d) :
    formLatticeCoordinates (formAction γ t) ha' w =
      ((γ : SL(2, ℚ)) : Matrix (Fin 2) (Fin 2) ℚ).mulVec
        (formLatticeCoordinates t ha (w * formActionScale t ha γ)) := by
  rw [formLatticeCoordinates_eq_firstColumn ((discr_formAction γ t).trans ht),
    integralFormFieldEmbedding_action ht, formLatticeCoordinates_mul ht]
  simp only [formActionScale, LinearEquiv.apply_symm_apply, Matrix.mulVec_mulVec]
  rfl

lemma formActionScale_ne_zero {d : ℤ} {t : ℤ × ℤ × ℤ}
    (ht : discr t = d) (ha : t.1 ≠ 0) (γ : SL(2, ℤ))
    (ha' : (formAction γ t).1 ≠ 0) : formActionScale (d := d) t ha γ ≠ 0 := by
  intro hzero
  have h := formLatticeCoordinates_action ht ha γ ha' (1 : QuadraticDiscrAlgebra d)
  rw [hzero, mul_zero, map_zero, Matrix.mulVec_zero] at h
  exact one_ne_zero ((formLatticeCoordinates (formAction γ t) ha').map_eq_zero_iff.mp h)

theorem formIdealLattice_action_mem_iff {d : ℤ} {t : ℤ × ℤ × ℤ}
    (ht : discr t = d) (ha : t.1 ≠ 0) (γ : SL(2, ℤ))
    (ha' : (formAction γ t).1 ≠ 0) (w : QuadraticDiscrAlgebra d) :
    w ∈ formIdealLattice (formAction γ t) ha' ↔
      w * formActionScale t ha γ ∈ formIdealLattice t ha := by
  rw [mem_formIdealLattice, mem_formIdealLattice, formLatticeCoordinates_action ht,
    integralSL_mulVec_mem_iff]

end Erdos1148.DukeArithmetic
