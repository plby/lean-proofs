import ErdosProblems.Erdos1148.QuadraticOrderIntegers
import Mathlib.RingTheory.FractionalIdeal.Extended

/-! # Extending order fractional ideals inside the same quadratic field -/

namespace Erdos1148.DukeArithmetic

open NumberField
open scoped nonZeroDivisors

lemma quadraticOrderToIntegers_nonZeroDivisors {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    (quadraticOrder d)⁰ ≤ (𝓞 (QuadraticDiscrAlgebra d))⁰.comap (quadraticOrderToIntegers ht) :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (quadraticOrderToIntegers_injective ht)

theorem orderLocalizationMap_eq_id {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    IsLocalization.map (S := QuadraticDiscrAlgebra d) (QuadraticDiscrAlgebra d)
      (quadraticOrderToIntegers ht) (quadraticOrderToIntegers_nonZeroDivisors ht) =
        RingHom.id (QuadraticDiscrAlgebra d) := by
  apply IsLocalization.ringHom_ext (quadraticOrder d)⁰
  apply RingHom.ext
  intro a
  rw [RingHom.comp_apply, IsLocalization.map_eq]
  rfl

noncomputable def orderFractionalExtension {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    FractionalIdeal (quadraticOrder d)⁰ (QuadraticDiscrAlgebra d) →+*
      FractionalIdeal (𝓞 (QuadraticDiscrAlgebra d))⁰ (QuadraticDiscrAlgebra d) :=
  FractionalIdeal.extendedHom' (QuadraticDiscrAlgebra d)
    (quadraticOrderToIntegers_nonZeroDivisors ht)

theorem coe_orderFractionalExtension {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d)
    (I : FractionalIdeal (quadraticOrder d)⁰ (QuadraticDiscrAlgebra d)) :
    (orderFractionalExtension ht I : Submodule (𝓞 (QuadraticDiscrAlgebra d))
      (QuadraticDiscrAlgebra d)) =
      Submodule.span (𝓞 (QuadraticDiscrAlgebra d)) (I : Set (QuadraticDiscrAlgebra d)) := by
  change (FractionalIdeal.extended (QuadraticDiscrAlgebra d)
    (quadraticOrderToIntegers_nonZeroDivisors ht) I :
      Submodule (𝓞 (QuadraticDiscrAlgebra d)) (QuadraticDiscrAlgebra d)) = _
  rw [FractionalIdeal.coe_extended_eq_span, orderLocalizationMap_eq_id]
  simp

theorem orderFractionalExtension_spanSingleton {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) (x : QuadraticDiscrAlgebra d) :
    orderFractionalExtension ht (FractionalIdeal.spanSingleton (quadraticOrder d)⁰ x) =
      FractionalIdeal.spanSingleton (𝓞 (QuadraticDiscrAlgebra d))⁰ x := by
  change FractionalIdeal.extended (QuadraticDiscrAlgebra d)
    (quadraticOrderToIntegers_nonZeroDivisors ht) _ = _
  rw [FractionalIdeal.extended_spanSingleton, orderLocalizationMap_eq_id]
  rfl

theorem orderFractionalExtension_coeIdeal {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) (I : Ideal (quadraticOrder d)) :
    orderFractionalExtension ht
        (I : FractionalIdeal (quadraticOrder d)⁰ (QuadraticDiscrAlgebra d)) =
      (I.map (quadraticOrderToIntegers ht) :
        FractionalIdeal (𝓞 (QuadraticDiscrAlgebra d))⁰ (QuadraticDiscrAlgebra d)) :=
  FractionalIdeal.extended_coeIdeal_eq_map _ _ I

end Erdos1148.DukeArithmetic
