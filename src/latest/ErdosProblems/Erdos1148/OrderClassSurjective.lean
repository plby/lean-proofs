import ErdosProblems.Erdos1148.ConductorContractInvertible
import ErdosProblems.Erdos1148.CoprimeClassRepresentative
import ErdosProblems.Erdos1148.QuadraticOrderConductor

/-! # Surjectivity of extension to the maximal-order class group -/

namespace Erdos1148.DukeArithmetic

open NumberField
open scoped nonZeroDivisors

lemma conductor_mem_quadraticOrderToIntegers_range {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    ∀ c ∈ quadraticOrderConductor d, c ∈ (quadraticOrderToIntegers ht).range := by
  intro c hc
  exact ⟨⟨(c : QuadraticDiscrAlgebra d), quadraticOrderConductor_mem_order hc⟩, rfl⟩

theorem orderClassExtension_surjective {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) : Function.Surjective (orderClassExtension ht) := by
  intro c
  obtain ⟨J, hJ₀, v, hv, hvc, hJC⟩ :=
    classGroup_exists_coprime_representative (K := QuadraticDiscrAlgebra d)
      (quadraticOrderConductor d) (quadraticOrderConductor_ne_bot ht) c
  have hC := conductor_mem_quadraticOrderToIntegers_range ht
  have hunit := isUnit_comap_of_conductor_coprime (K := QuadraticDiscrAlgebra d)
    (quadraticOrderToIntegers ht) (quadraticOrderToIntegers_injective ht)
    (quadraticOrderConductor d) hC J hJ₀ hJC
  obtain ⟨u, hu⟩ := hunit
  refine ⟨ClassGroup.mk (QuadraticDiscrAlgebra d) u, ?_⟩
  rw [orderClassExtension_mk]
  have hext : Units.map (orderFractionalExtension ht).toMonoidHom u = v := by
    apply Units.ext
    change orderFractionalExtension ht (u : FractionalIdeal (quadraticOrder d)⁰
      (QuadraticDiscrAlgebra d)) = (v : FractionalIdeal
        (𝓞 (QuadraticDiscrAlgebra d))⁰ (QuadraticDiscrAlgebra d))
    rw [hu, orderFractionalExtension_coeIdeal,
      map_comap_eq_of_conductor_coprime (quadraticOrderToIntegers ht)
        (quadraticOrderConductor d) hC J hJC, hv]
  rw [hext, hvc]

end Erdos1148.DukeArithmetic
