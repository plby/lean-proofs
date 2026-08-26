import ErdosProblems.Erdos1148.QuadraticOrderFractionField

/-! # Two explicit integral generators of the form ideal -/

namespace Erdos1148.DukeArithmetic

open scoped nonZeroDivisors

noncomputable def formIdealGenerator {d : ℤ} (t : ℤ × ℤ × ℤ) : QuadraticDiscrAlgebra d :=
  ⟨(t.2.1 : ℚ) / (2 * (t.1 : ℚ)), 1 / (2 * (t.1 : ℚ))⟩

lemma formIdealGenerator_eq_symm {d : ℤ} (t : ℤ × ℤ × ℤ) (ha : t.1 ≠ 0) :
    formIdealGenerator (d := d) t = (formLatticeCoordinates t ha).symm ![0, 1] := by
  ext <;> simp [formIdealGenerator, formLatticeCoordinates, div_eq_mul_inv]

lemma formIdealGenerator_mem {d : ℤ} (t : ℤ × ℤ × ℤ) (ha : t.1 ≠ 0) :
    formIdealGenerator (d := d) t ∈ formIdealLattice t ha := by
  rw [mem_formIdealLattice, formIdealGenerator_eq_symm t ha, LinearEquiv.apply_symm_apply]
  refine ⟨![0, 1], ?_⟩
  ext i
  fin_cases i <;> simp [intVectorCast]

theorem formIdealLattice_int_coordinates {d : ℤ} (t : ℤ × ℤ × ℤ) (ha : t.1 ≠ 0)
    {z : QuadraticDiscrAlgebra d} (hz : z ∈ formIdealLattice t ha) :
    ∃ x y : ℤ, z = (x : QuadraticDiscrAlgebra d) +
      (y : QuadraticDiscrAlgebra d) * formIdealGenerator t := by
  obtain ⟨v, hv⟩ := hz
  have hz' : z = (formLatticeCoordinates t ha).symm (intVectorCast v) := by
    apply (formLatticeCoordinates t ha).injective
    rw [LinearEquiv.apply_symm_apply]
    exact hv.symm
  refine ⟨v 0, v 1, ?_⟩
  rw [hz']
  ext <;> simp [formLatticeCoordinates, intVectorCast, formIdealGenerator] <;> ring

theorem formIdealLattice_int_coordinates_iff {d : ℤ} (t : ℤ × ℤ × ℤ) (ha : t.1 ≠ 0)
    (z : QuadraticDiscrAlgebra d) :
    z ∈ formIdealLattice t ha ↔ ∃ x y : ℤ, z = (x : QuadraticDiscrAlgebra d) +
      (y : QuadraticDiscrAlgebra d) * formIdealGenerator t := by
  constructor
  · exact formIdealLattice_int_coordinates t ha
  · rintro ⟨x, y, rfl⟩
    apply (formIdealLattice t ha).add_mem
    · simpa only [zsmul_eq_mul, mul_one] using
        (formIdealLattice t ha).smul_mem x (one_mem_formIdealLattice t ha)
    · simpa only [zsmul_eq_mul] using
        (formIdealLattice t ha).smul_mem y (formIdealGenerator_mem t ha)

lemma leading_mul_formIdealGenerator_mem_order {d : ℤ} {t : ℤ × ℤ × ℤ}
    (ht : discr t = d) (ha : t.1 ≠ 0) :
    (t.1 : QuadraticDiscrAlgebra d) * formIdealGenerator t ∈ quadraticOrder d := by
  obtain ⟨k, hk⟩ := ht ▸ even_middle_sub_discr t
  have hkQ : (t.2.1 : ℚ) - d = (k : ℚ) + k := by exact_mod_cast hk
  have haQ : (t.1 : ℚ) ≠ 0 := by exact_mod_cast ha
  have heq : (t.1 : QuadraticDiscrAlgebra d) * formIdealGenerator t =
      (k : QuadraticDiscrAlgebra d) + quadraticOrderGenerator d := by
    ext <;> simp [formIdealGenerator, quadraticOrderGenerator] <;> field_simp
    linear_combination hkQ
  rw [heq]
  exact (quadraticOrder d).add_mem (intCast_mem (quadraticOrder d) k)
    (quadraticOrderGenerator_mem d)

end Erdos1148.DukeArithmetic
