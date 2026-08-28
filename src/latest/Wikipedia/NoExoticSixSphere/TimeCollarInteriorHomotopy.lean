import Wikipedia.HopfProblem.DegreeCollapseTimeCollarInterior

/-!
# An exact interior homotopy from a homotopy in the collared half

Push the given homotopy into the positive interior and attach the actual
collar slides at its two ends. The original interior endpoint maps are
restored exactly. No smoothness of the topological collar is asserted.
-/

noncomputable section

namespace NoExoticSixSphere

open Wikipedia.HopfProblem.DegreeCollapse

def interiorHomotopyOfHalfHomotopy
    {X M B : Type} [TopologicalSpace X] [TopologicalSpace M] [TopologicalSpace B]
    {t : M → ℝ} (C : TimeCollar t B)
    (f₀ f₁ : C(X, C.positiveInterior))
    (H : (C.interiorToHalf.comp f₀).Homotopy (C.interiorToHalf.comp f₁)) :
    f₀.Homotopy f₁ :=
  ((C.interiorHalfSlide.compContinuousMap f₀).trans
    ((ContinuousMap.Homotopy.refl C.halfToInterior).comp H)).trans
      (C.interiorHalfSlide.symm.compContinuousMap f₁)

end NoExoticSixSphere
