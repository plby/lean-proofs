import ErdosProblems.Erdos1123.WeightedQuotient

/-! # Transport between weighted presentations of the same null ideal -/

namespace Erdos1123
namespace WeightSequence

variable {α : Type*} (W V : WeightSequence α)

/-- Equality of null predicates gives an isomorphism of the actual Boolean quotients. -/
noncomputable def algebraEquivOfNull (h : ∀ A, W.IsNull A ↔ V.IsNull A) : W.Algebra ≃o V.Algebra := by
  have hI : W.nullIdeal = V.nullIdeal := by
    ext A
    exact h (ofBoolRing A)
  let e := Ideal.quotEquivOfEq hI
  let f : W.Algebra ≃ V.Algebra := ofBoolAlg.trans (e.toEquiv.trans toBoolAlg)
  exact f.toOrderIso (OrderHomClass.monotone e.toRingHom.asBoolAlg)
    (OrderHomClass.monotone e.symm.toRingHom.asBoolAlg)

end WeightSequence
end Erdos1123
