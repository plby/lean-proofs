import ErdosProblems.Erdos1148.ProperFormLattice

/-! # An integral basis and a common denominator for the form lattice -/

namespace Erdos1148.DukeArithmetic

noncomputable def formIdealLatticeParam {d : ℤ} (t : ℤ × ℤ × ℤ) (ha : t.1 ≠ 0) :
    (Fin 2 → ℤ) →ₗ[ℤ] formIdealLattice (d := d) t ha :=
  let f := ((formLatticeCoordinates (d := d) t ha).symm.toLinearMap.restrictScalars ℤ).comp
    intVectorCast
  f.codRestrict (formIdealLattice t ha) (by
    intro v
    change formLatticeCoordinates t ha
      ((formLatticeCoordinates (d := d) t ha).symm (intVectorCast v)) ∈ standardRationalLattice
    rw [LinearEquiv.apply_symm_apply]
    exact ⟨v, rfl⟩)

lemma formIdealLatticeParam_apply {d : ℤ} (t : ℤ × ℤ × ℤ) (ha : t.1 ≠ 0) (v : Fin 2 → ℤ) :
    ((formIdealLatticeParam (d := d) t ha v) : QuadraticDiscrAlgebra d) =
      (formLatticeCoordinates t ha).symm (intVectorCast v) := rfl

lemma formIdealLatticeParam_bijective {d : ℤ} (t : ℤ × ℤ × ℤ) (ha : t.1 ≠ 0) :
    Function.Bijective (formIdealLatticeParam (d := d) t ha) := by
  constructor
  · intro v w hvw
    have heq := congrArg (fun z : formIdealLattice (d := d) t ha =>
      formLatticeCoordinates t ha z.1) hvw
    simp only [formIdealLatticeParam_apply, LinearEquiv.apply_symm_apply] at heq
    ext i
    exact Int.cast_injective (congrFun heq i)
  · intro z
    obtain ⟨v, hv⟩ := z.2
    refine ⟨v, Subtype.ext ?_⟩
    rw [formIdealLatticeParam_apply]
    apply (formLatticeCoordinates t ha).injective
    rw [LinearEquiv.apply_symm_apply]
    exact hv

noncomputable def formIdealLatticeBasis {d : ℤ} (t : ℤ × ℤ × ℤ) (ha : t.1 ≠ 0) :
    Module.Basis (Fin 2) ℤ (formIdealLattice (d := d) t ha) :=
  (Pi.basisFun ℤ (Fin 2)).map
    (LinearEquiv.ofBijective (formIdealLatticeParam t ha) (formIdealLatticeParam_bijective t ha))

instance formIdealLattice_finite {d : ℤ} (t : ℤ × ℤ × ℤ) (ha : t.1 ≠ 0) :
    Module.Finite ℤ (formIdealLattice (d := d) t ha) :=
  Module.Finite.of_basis (formIdealLatticeBasis t ha)

instance formIdealLattice_free {d : ℤ} (t : ℤ × ℤ × ℤ) (ha : t.1 ≠ 0) :
    Module.Free ℤ (formIdealLattice (d := d) t ha) :=
  Module.Free.of_basis (formIdealLatticeBasis t ha)

lemma one_mem_formIdealLattice {d : ℤ} (t : ℤ × ℤ × ℤ) (ha : t.1 ≠ 0) :
    (1 : QuadraticDiscrAlgebra d) ∈ formIdealLattice t ha := by
  refine ⟨![1, 0], ?_⟩
  ext i
  fin_cases i <;> simp [intVectorCast, formLatticeCoordinates,
    QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

theorem formIdealLattice_clear_denominator {d : ℤ} (t : ℤ × ℤ × ℤ) (ha : t.1 ≠ 0)
    {z : QuadraticDiscrAlgebra d} (hz : z ∈ formIdealLattice t ha) :
    ((2 * t.1 : ℤ) : QuadraticDiscrAlgebra d) * z ∈ quadraticOrder d := by
  obtain ⟨v, hv⟩ := hz
  have hv₀ := congrFun hv 0
  have hv₁ := congrFun hv 1
  change (v 0 : ℚ) = z.re - (t.2.1 : ℚ) * z.im at hv₀
  change (v 1 : ℚ) = 2 * (t.1 : ℚ) * z.im at hv₁
  have heq : ((2 * t.1 : ℤ) : QuadraticDiscrAlgebra d) * z =
      ((2 * t.1 * v 0 + (t.2.1 - d) * v 1 : ℤ) : QuadraticDiscrAlgebra d) +
        ((2 * v 1 : ℤ) : QuadraticDiscrAlgebra d) * quadraticOrderGenerator d := by
    ext
    · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_add,
        QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast,
        quadraticOrderGenerator, zero_mul, mul_zero, add_zero]
      push_cast
      linear_combination -(2 * (t.1 : ℚ)) * hv₀ - (t.2.1 : ℚ) * hv₁
    · simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.im_add,
        QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast,
        quadraticOrderGenerator, zero_mul, mul_zero, add_zero, zero_add]
      push_cast
      linear_combination -hv₁
  rw [heq]
  exact int_combination_mem_quadraticOrder _ _ _

end Erdos1148.DukeArithmetic
