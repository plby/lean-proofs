import Wikipedia.HopfProblem.FundamentalGroupBasepointNaturality
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-!
# Basepoint change along an actual homotopy trajectory

The homotopy square for a loop identifies its two endpoint images after
changing the basepoint along the actual path traced by the homotopy.
No endpoint identifications or hypotheses on a quotient family are needed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DiagonalQuotient

/-- Changing basepoint along the homotopy trajectory carries the induced
map at its initial endpoint to the induced map at its terminal endpoint. -/
theorem fundamentalGroup_basepointChange_of_homotopy
    {F E : Type*} [TopologicalSpace F] [TopologicalSpace E]
    (f₀ f₁ : C(F, E)) (H : f₀.Homotopy f₁)
    (c : F) (v : FundamentalGroup F c) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath (H.evalAt c)
        (FundamentalGroup.map f₀ c v) =
      FundamentalGroup.map f₁ c v := by
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective v
  rw [fundamentalGroup_basepoint_change_apply]
  change (Path.Homotopic.Quotient.mk (H.evalAt c)).symm.trans
      ((Path.Homotopic.Quotient.mk (p.map f₀.continuous)).trans
        (Path.Homotopic.Quotient.mk (H.evalAt c))) =
    Path.Homotopic.Quotient.mk (p.map f₁.continuous)
  have hsquare :
      (Path.Homotopic.Quotient.mk (p.map f₀.continuous)).trans
          (Path.Homotopic.Quotient.mk (H.evalAt c)) =
        (Path.Homotopic.Quotient.mk (H.evalAt c)).trans
          (Path.Homotopic.Quotient.mk (p.map f₁.continuous)) := by
    rw [← Path.Homotopic.Quotient.mk_trans, ← Path.Homotopic.Quotient.mk_trans]
    exact Path.Homotopic.Quotient.eq.mpr (Path.Homotopic.map_trans_evalAt H p)
  rw [hsquare, ← Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]

end Wikipedia.HopfProblem.DiagonalQuotient
