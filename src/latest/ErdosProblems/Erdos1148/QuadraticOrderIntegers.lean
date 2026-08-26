import ErdosProblems.Erdos1148.QuadraticOrderBasis

/-! # The discriminant order embeds into the ring of integers -/

namespace Erdos1148.DukeArithmetic

open scoped NumberField

theorem quadraticOrder_isIntegral {d : ℤ} {t : ℤ × ℤ × ℤ} (ht : discr t = d)
    (w : quadraticOrder d) : IsIntegral ℤ (w : QuadraticDiscrAlgebra d) := by
  let := quadraticOrder_moduleFinite ht
  exact IsIntegral.map (IsScalarTower.toAlgHom ℤ (quadraticOrder d) (QuadraticDiscrAlgebra d))
    (IsIntegral.of_finite ℤ w)

noncomputable def quadraticOrderToIntegers {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) : quadraticOrder d →+* 𝓞 (QuadraticDiscrAlgebra d) where
  toFun w := ⟨(w : QuadraticDiscrAlgebra d), quadraticOrder_isIntegral ht w⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

lemma quadraticOrderToIntegers_val {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) (w : quadraticOrder d) :
    (quadraticOrderToIntegers ht w : QuadraticDiscrAlgebra d) = w := rfl

theorem quadraticOrderToIntegers_injective {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) : Function.Injective (quadraticOrderToIntegers ht) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun w : 𝓞 (QuadraticDiscrAlgebra d) => (w : QuadraticDiscrAlgebra d)) h

end Erdos1148.DukeArithmetic
