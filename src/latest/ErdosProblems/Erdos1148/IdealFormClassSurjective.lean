import ErdosProblems.Erdos1148.IdealBasisLattice
import ErdosProblems.Erdos1148.PrimitiveOfInvertible
import ErdosProblems.Erdos1148.IntegralIdealClass
import ErdosProblems.Erdos1148.FormOrbitClass

/-! # Every invertible order ideal class comes from a primitive form -/

namespace Erdos1148.DukeArithmetic

open scoped nonZeroDivisors

theorem primitive_formOfIdealBasis {d : ℤ} [Fact (¬IsSquare d)]
    (I : Ideal (quadraticOrder d)) (b : Module.Basis (Fin 2) ℤ I)
    (hI : IsUnit (I : FractionalIdeal (quadraticOrder d)⁰ (QuadraticDiscrAlgebra d))) :
    PrimitiveIntegralForm (formOfIdealBasis I b) := by
  apply primitiveIntegralForm_of_formFractionalIdeal_isUnit
    (formOfIdealBasis_discr I b) (formOfIdealBasis_fst_ne_zero I b)
  rw [coeIdeal_eq_span_mul_formFractionalIdeal I b] at hI
  exact isUnit_of_mul_isUnit_right hI

theorem primitiveFormClass_formOfIdealBasis {d : ℤ} [Fact (¬IsSquare d)]
    (I : Ideal (quadraticOrder d)) (b : Module.Basis (Fin 2) ℤ I)
    (u : (FractionalIdeal (quadraticOrder d)⁰ (QuadraticDiscrAlgebra d))ˣ)
    (hu : (u : FractionalIdeal (quadraticOrder d)⁰ (QuadraticDiscrAlgebra d)) = I) :
    primitiveFormClass (formOfIdealBasis_discr I b)
        (primitive_formOfIdealBasis I b (hu ▸ u.isUnit)) (formOfIdealBasis_fst_ne_zero I b) =
      ClassGroup.mk (QuadraticDiscrAlgebra d) u := by
  let v := Units.mk0 (idealBasisValue I b 0) (idealBasisValue_ne_zero I b 0)
  have heq : u = toPrincipalIdeal (quadraticOrder d) (QuadraticDiscrAlgebra d) v *
      primitiveFormIdealUnit (formOfIdealBasis_discr I b)
        (primitive_formOfIdealBasis I b (hu ▸ u.isUnit)) (formOfIdealBasis_fst_ne_zero I b) := by
    apply Units.ext
    simp only [Units.val_mul, coe_toPrincipalIdeal, primitiveFormIdealUnit_val]
    rw [hu]
    exact coeIdeal_eq_span_mul_formFractionalIdeal I b
  conv_rhs => rw [heq, map_mul, classGroup_mk_principal, one_mul]
  rfl

theorem primitiveFormOrbitClass_surjective {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    Function.Surjective (primitiveFormOrbitClass (d := d)) := by
  intro c
  obtain ⟨I, hI, u, hu, huc⟩ :=
    classGroup_exists_integral_representative (K := QuadraticDiscrAlgebra d) c
  let b := Ideal.selfBasis (quadraticOrderBasis ht) I hI
  let f : IntegralDiscrForm d := ⟨formOfIdealBasis I b, formOfIdealBasis_discr I b⟩
  have hp : PrimitiveIntegralForm f.val := primitive_formOfIdealBasis I b (hu ▸ u.isUnit)
  refine ⟨primitiveIntegralFormOrbitMk f hp, ?_⟩
  rw [primitiveFormOrbitClass_mk]
  exact (primitiveFormClass_formOfIdealBasis I b u hu).trans huc

end Erdos1148.DukeArithmetic
