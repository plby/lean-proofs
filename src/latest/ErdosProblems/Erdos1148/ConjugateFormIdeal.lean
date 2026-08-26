import ErdosProblems.Erdos1148.FormIdealGenerators

/-! # Products with the conjugate form ideal -/

namespace Erdos1148.DukeArithmetic

def conjugateForm (t : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ := (t.1, -t.2.1, t.2.2)

lemma discr_conjugateForm (t : ℤ × ℤ × ℤ) : discr (conjugateForm t) = discr t := by
  dsimp [conjugateForm, discr]
  ring

lemma leading_mul_generator_difference {d : ℤ} (t : ℤ × ℤ × ℤ) (ha : t.1 ≠ 0) :
    (t.1 : QuadraticDiscrAlgebra d) *
        (formIdealGenerator t - formIdealGenerator (conjugateForm t)) =
      (t.2.1 : QuadraticDiscrAlgebra d) := by
  have haQ : (t.1 : ℚ) ≠ 0 := by exact_mod_cast ha
  ext <;> simp [formIdealGenerator, conjugateForm] <;> field_simp <;> ring

lemma leading_mul_generator_product {d : ℤ} {t : ℤ × ℤ × ℤ}
    (ht : discr t = d) (ha : t.1 ≠ 0) :
    (t.1 : QuadraticDiscrAlgebra d) * formIdealGenerator t *
        formIdealGenerator (conjugateForm t) = (-t.2.2 : QuadraticDiscrAlgebra d) := by
  have haQ : (t.1 : ℚ) ≠ 0 := by exact_mod_cast ha
  have hdQ : (t.2.1 : ℚ) ^ 2 - 4 * (t.1 : ℚ) * t.2.2 = d := by
    exact_mod_cast ht
  ext <;> simp [formIdealGenerator, conjugateForm] <;> field_simp
  · linear_combination -hdQ
  · ring

theorem leading_mul_formIdeal_product_mem_order {d : ℤ} {t : ℤ × ℤ × ℤ}
    (ht : discr t = d) (ha : t.1 ≠ 0) {v w : QuadraticDiscrAlgebra d}
    (hv : v ∈ formIdealLattice t ha)
    (hw : w ∈ formIdealLattice (conjugateForm t) ha) :
    (t.1 : QuadraticDiscrAlgebra d) * v * w ∈ quadraticOrder d := by
  obtain ⟨x, y, rfl⟩ := formIdealLattice_int_coordinates t ha hv
  obtain ⟨z, r, rfl⟩ := formIdealLattice_int_coordinates (conjugateForm t) ha hw
  have heq : (t.1 : QuadraticDiscrAlgebra d) *
      ((x : QuadraticDiscrAlgebra d) + (y : QuadraticDiscrAlgebra d) * formIdealGenerator t) *
      ((z : QuadraticDiscrAlgebra d) + (r : QuadraticDiscrAlgebra d) *
        formIdealGenerator (conjugateForm t)) =
      ((x * z : ℤ) : QuadraticDiscrAlgebra d) * (t.1 : QuadraticDiscrAlgebra d) +
      ((x * r : ℤ) : QuadraticDiscrAlgebra d) *
        ((t.1 : QuadraticDiscrAlgebra d) * formIdealGenerator (conjugateForm t)) +
      ((y * z : ℤ) : QuadraticDiscrAlgebra d) *
        ((t.1 : QuadraticDiscrAlgebra d) * formIdealGenerator t) +
      ((y * r : ℤ) : QuadraticDiscrAlgebra d) *
        ((t.1 : QuadraticDiscrAlgebra d) * formIdealGenerator t *
          formIdealGenerator (conjugateForm t)) := by push_cast; ring
  rw [heq, leading_mul_generator_product ht ha]
  have hβ := leading_mul_formIdealGenerator_mem_order ht ha
  have hβ' := leading_mul_formIdealGenerator_mem_order ((discr_conjugateForm t).trans ht) ha
  exact (quadraticOrder d).add_mem
    ((quadraticOrder d).add_mem
      ((quadraticOrder d).add_mem
        ((quadraticOrder d).mul_mem (intCast_mem _ _) (intCast_mem _ _))
        ((quadraticOrder d).mul_mem (intCast_mem _ _) hβ'))
      ((quadraticOrder d).mul_mem (intCast_mem _ _) hβ))
    ((quadraticOrder d).mul_mem (intCast_mem _ _) ((quadraticOrder d).neg_mem (intCast_mem _ _)))

end Erdos1148.DukeArithmetic
