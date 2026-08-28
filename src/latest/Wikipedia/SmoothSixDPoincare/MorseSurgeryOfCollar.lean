import Wikipedia.SmoothSixDPoincare.MorseSurgerySmoothExterior
import Wikipedia.SmoothSixDPoincare.FlowCollarAttachmentRealization
import Wikipedia.SmoothSixDPoincare.SmoothSublevelCollarExterior

/-!
# The same collar realization as a native Morse surgery record

The constructor retains the original frontier, fixed points, quadratic
boundary orbits, native exterior maps, whole pieces, and belt sphere.
Smoothness of the two collar exteriors transfers to those exact recorded
maps, without adding a smoothness axiom to the general surgery structure.
-/

noncomputable section

open Set Metric Manifold
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
  {f : M → ℝ} {p : M} (c : SignedMorseChart (E := E) f p)
  (ρ : ℝ) (hρ : 0 < ρ)
  (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
    closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
  [CompactSpace ↥({x : M | f x ≤ f p + ρ ^ 2})]
  {F : Flow ℝ M}
  (R : FlowConstruction.FlowCollarData F
    ({x | f x ≤ f p - ρ ^ 2} ∪ range (c.attachingHandleMap ρ hρ hblock))
    {x | f x ≤ f p + ρ ^ 2})
  (hfronta : frontier {x | f x ≤ f p - ρ ^ 2} = {x | f x = f p - ρ ^ 2})
  (hfrontb : frontier {x | f x ≤ f p + ρ ^ 2} = {x | f x = f p + ρ ^ 2})
  (hlower : ∀ x, f x = f p - ρ ^ 2 → x ∉ criticalPoints E f)
  (hupper : ∀ x, f x = f p + ρ ^ 2 → x ∉ criticalPoints E f)
  (hmodel : c.FollowsModelBoundaryOrbits ρ hρ hblock R.sublevelRealization)

def surgeryDataOfCollar (hc : Continuous f) : MorseSurgeryData E f p where
  radius := ρ
  radius_pos := hρ
  chart := c
  block := hblock
  attachmentHomeomorph := R.sublevelRealization
  attachment_frontier := R.sublevelRealization_frontier hfrontb
  attachment_fixed := R.sublevelRealization_fixed hfrontb
  attachment_model_orbits := hmodel
  surgery := c.levelSurgeryBoundaryPair hc ρ hρ hblock hfronta R.sublevelRealization
    (R.sublevelRealization_frontier hfrontb)
  oldExterior_eq := fun _ => rfl
  newExterior_eq := fun _ => rfl
  oldPiece_eq := fun _ => rfl
  newPiece_eq := fun _ => rfl
  belt_eq := c.beltSphere_eq_beltCoreMap hc ρ hρ hblock hfronta R.sublevelRealization
    (R.sublevelRealization_frontier hfrontb) (R.sublevelRealization_fixed hfrontb)
  lower_regular := hlower
  upper_regular := hupper

theorem surgeryDataOfCollar_radius (hc : Continuous f) :
    (c.surgeryDataOfCollar ρ hρ hblock R hfronta hfrontb hlower hupper hmodel hc).radius = ρ := rfl

theorem surgeryDataOfCollar_attachmentHomeomorph (hc : Continuous f) :
    (c.surgeryDataOfCollar ρ hρ hblock R hfronta hfrontb
      hlower hupper hmodel hc).attachmentHomeomorph = R.sublevelRealization := rfl

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem surgeryDataOfCollar_hasSmoothExterior
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hforward : letI := RegularLevel.chartedSpace hf hlower;
      ContMDiffOn 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, E) ∞ R.lowerExteriorMap
        {x | x.val ∉ range (c.attachingHandleMap ρ hρ hblock)})
    (hbackward : letI := RegularLevel.chartedSpace hf hupper;
      ContMDiffOn 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, E) ∞ R.upperExteriorMap
        {x | R.upperExteriorMap x ∉ range (c.attachingHandleMap ρ hρ hblock)}) :
    (c.surgeryDataOfCollar ρ hρ hblock R hfronta hfrontb
      hlower hupper hmodel hf.continuous).HasSmoothExterior hf := by
  constructor
  · exact hforward
  · exact hbackward

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart
