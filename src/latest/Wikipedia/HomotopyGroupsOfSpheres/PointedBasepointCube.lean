import Wikipedia.HomotopyGroupsOfSpheres.PointedMaps

/-! # Base-point equality transport on actual native cube representatives -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres

variable {N X : Type} [TopologicalSpace X] [DecidableEq N] [Nonempty N]

theorem basepointEqMulEquiv_mk {x y : X} (h : x = y) (p : GenLoop N X x) :
    basepointEqMulEquiv h (⟦p⟧ : HomotopyGroup N X x) =
      (⟦(⟨p.val, fun u hu ↦ (p.property u hu).trans h⟩ : GenLoop N X y)⟧ :
        HomotopyGroup N X y) := by
  cases h
  rfl

end Wikipedia.HomotopyGroupsOfSpheres
