import ErdosProblems.Erdos1148.ConductorGluedIdealProduct
import ErdosProblems.Erdos1148.PrimitiveFormClass

/-! # The class-group map supplied by conductor residue units -/

namespace Erdos1148.DukeArithmetic

open NumberField
open scoped nonZeroDivisors

theorem conductorGluedIdeal_mul {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d)
    (u v : (𝓞 (QuadraticDiscrAlgebra d) ⧸ quadraticOrderConductor d)ˣ) :
    conductorGluedIdeal ht u * conductorGluedIdeal ht v = conductorGluedIdeal ht (u * v) := by
  apply le_antisymm (conductorGluedIdeal_mul_le ht u v)
  have h := conductorGluedIdeal_mul_le ht (u * v) v⁻¹
  rw [mul_assoc, mul_inv_cancel, mul_one] at h
  have hi : conductorGluedIdeal ht v⁻¹ * conductorGluedIdeal ht v = 1 := by
    rw [mul_comm]
    exact conductorGluedIdeal_mul_inverse ht v
  have hmul := mul_le_mul' h (le_refl (conductorGluedIdeal ht v))
  simpa only [mul_assoc, hi, mul_one] using hmul

noncomputable def conductorGluedIdealUnit {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d)
    (u : (𝓞 (QuadraticDiscrAlgebra d) ⧸ quadraticOrderConductor d)ˣ) :
    (FractionalIdeal (quadraticOrder d)⁰ (QuadraticDiscrAlgebra d))ˣ where
  val := conductorGluedIdeal ht u
  inv := conductorGluedIdeal ht u⁻¹
  val_inv := conductorGluedIdeal_mul_inverse ht u
  inv_val := by rw [mul_comm]; exact conductorGluedIdeal_mul_inverse ht u

noncomputable def conductorGluedIdealHom {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    (𝓞 (QuadraticDiscrAlgebra d) ⧸ quadraticOrderConductor d)ˣ →*
      (FractionalIdeal (quadraticOrder d)⁰ (QuadraticDiscrAlgebra d))ˣ where
  toFun := conductorGluedIdealUnit ht
  map_one' := Units.ext (conductorGluedIdeal_one ht)
  map_mul' u v := Units.ext (conductorGluedIdeal_mul ht u v).symm

noncomputable def conductorClassMap {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    (𝓞 (QuadraticDiscrAlgebra d) ⧸ quadraticOrderConductor d)ˣ →*
      ClassGroup (quadraticOrder d) :=
  (ClassGroup.mk (QuadraticDiscrAlgebra d)).comp (conductorGluedIdealHom ht)

end Erdos1148.DukeArithmetic
