import ErdosProblems.Erdos1148.OrderClassExtension
import ErdosProblems.Erdos1148.ConductorClassMap

/-! # Conductor-glued ideals become principal over the full ring of integers -/

namespace Erdos1148.DukeArithmetic

open NumberField
open scoped nonZeroDivisors

lemma extended_gluedIdeal_le_one {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d)
    (u : (𝓞 (QuadraticDiscrAlgebra d) ⧸ quadraticOrderConductor d)ˣ) :
    orderFractionalExtension ht (conductorGluedIdeal ht u) ≤ 1 := by
  change (orderFractionalExtension ht (conductorGluedIdeal ht u) :
      Submodule (𝓞 (QuadraticDiscrAlgebra d)) (QuadraticDiscrAlgebra d)) ≤
    (1 : FractionalIdeal (𝓞 (QuadraticDiscrAlgebra d))⁰ (QuadraticDiscrAlgebra d))
  rw [coe_orderFractionalExtension]
  apply Submodule.span_le.mpr
  rintro _ ⟨x, rfl, _⟩
  exact (FractionalIdeal.mem_one_iff (𝓞 (QuadraticDiscrAlgebra d))⁰).mpr ⟨x, rfl⟩

theorem orderFractionalExtension_gluedIdeal {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d)
    (u : (𝓞 (QuadraticDiscrAlgebra d) ⧸ quadraticOrderConductor d)ˣ) :
    orderFractionalExtension ht (conductorGluedIdeal ht u) = 1 := by
  apply le_antisymm (extended_gluedIdeal_le_one ht u)
  have hp : orderFractionalExtension ht (conductorGluedIdeal ht u) *
      orderFractionalExtension ht (conductorGluedIdeal ht u⁻¹) = 1 := by
    rw [← map_mul, conductorGluedIdeal_mul_inverse, map_one]
  have hm := mul_le_mul' (le_refl (orderFractionalExtension ht (conductorGluedIdeal ht u)))
    (extended_gluedIdeal_le_one ht u⁻¹)
  simpa only [hp, mul_one] using hm

theorem orderClassExtension_conductorClassMap {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d)
    (u : (𝓞 (QuadraticDiscrAlgebra d) ⧸ quadraticOrderConductor d)ˣ) :
    orderClassExtension ht (conductorClassMap ht u) = 1 := by
  change orderClassExtension ht (ClassGroup.mk (QuadraticDiscrAlgebra d)
    (conductorGluedIdealHom ht u)) = 1
  rw [orderClassExtension_mk]
  have hu : Units.map (orderFractionalExtension ht).toMonoidHom (conductorGluedIdealHom ht u) = 1 := by
    apply Units.ext
    exact orderFractionalExtension_gluedIdeal ht u
  rw [hu, map_one]

theorem conductorClassMap_range_le_orderClassExtension_ker {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    (conductorClassMap ht).range ≤ (orderClassExtension ht).ker := by
  rintro _ ⟨u, rfl⟩
  exact orderClassExtension_conductorClassMap ht u

end Erdos1148.DukeArithmetic
