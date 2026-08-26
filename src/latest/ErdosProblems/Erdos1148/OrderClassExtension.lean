import ErdosProblems.Erdos1148.OrderFractionalExtension
import ErdosProblems.Erdos1148.PrimitiveFormClass

/-! # Extension of ideal classes to the full ring of integers -/

namespace Erdos1148.DukeArithmetic

open NumberField
open scoped nonZeroDivisors

noncomputable def orderIdealUnitClass {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    (FractionalIdeal (quadraticOrder d)⁰ (QuadraticDiscrAlgebra d))ˣ →*
      ClassGroup (𝓞 (QuadraticDiscrAlgebra d)) :=
  (ClassGroup.mk (QuadraticDiscrAlgebra d)).comp
    (Units.map (orderFractionalExtension ht).toMonoidHom)

theorem orderIdealUnitClass_principal {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) (u : (QuadraticDiscrAlgebra d)ˣ) :
    orderIdealUnitClass ht
      (toPrincipalIdeal (quadraticOrder d) (QuadraticDiscrAlgebra d) u) = 1 := by
  have heq : Units.map (orderFractionalExtension ht).toMonoidHom
      (toPrincipalIdeal (quadraticOrder d) (QuadraticDiscrAlgebra d) u) =
      toPrincipalIdeal (𝓞 (QuadraticDiscrAlgebra d)) (QuadraticDiscrAlgebra d) u := by
    apply Units.ext
    simp only [Units.coe_map, coe_toPrincipalIdeal]
    exact orderFractionalExtension_spanSingleton ht (u : QuadraticDiscrAlgebra d)
  change ClassGroup.mk (QuadraticDiscrAlgebra d) _ = 1
  rw [heq, classGroup_mk_principal]

noncomputable def orderClassExtension {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    ClassGroup (quadraticOrder d) →* ClassGroup (𝓞 (QuadraticDiscrAlgebra d)) :=
  (QuotientGroup.lift (toPrincipalIdeal (quadraticOrder d) (QuadraticDiscrAlgebra d)).range
    (orderIdealUnitClass ht) (by
      rintro I ⟨u, rfl⟩
      exact orderIdealUnitClass_principal ht u)).comp
    (ClassGroup.equiv (QuadraticDiscrAlgebra d)).toMonoidHom

theorem orderClassExtension_mk {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d)
    (I : (FractionalIdeal (quadraticOrder d)⁰ (QuadraticDiscrAlgebra d))ˣ) :
    orderClassExtension ht (ClassGroup.mk (QuadraticDiscrAlgebra d) I) =
      ClassGroup.mk (QuadraticDiscrAlgebra d)
        (Units.map (orderFractionalExtension ht).toMonoidHom I) := by
  simp [orderClassExtension, ClassGroup.equiv_mk, FractionalIdeal.canonicalEquiv_self,
    orderIdealUnitClass]
  rfl

end Erdos1148.DukeArithmetic
