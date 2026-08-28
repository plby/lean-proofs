import Wikipedia.SmoothSixDPoincare.MorseCriticalHomeomorph

/-!
# Computable boundary orbits for the actual Morse attachment

The boundary map agrees with the exact quadratic flow whenever the full
backward trajectory stays in the controlled Morse block and ends on the
upper level. The predicate records this formula; it is proved from the
constructed native flow, not assumed of an arbitrary attachment.
-/

noncomputable section

open Set Metric Manifold Filter
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {p : M} (c : SignedMorseChart (E := E) f p)

open Classical in
/-- The boundary-orbit formula on the full controlled product block. -/
def FollowsModelBoundaryOrbits (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (e : ↥({x | f x ≤ f p - ρ ^ 2} ∪ range (c.attachingHandleMap ρ hρ hblock)) ≃ₜ
      {x : M // f x ≤ f p + ρ ^ 2}) : Prop :=
  ∀ x, x.val ∈ frontier ({y | f y ≤ f p - ρ ^ 2} ∪
      range (c.attachingHandleMap ρ hρ hblock)) → x.val ∈ c.splitChart.source →
    ∀ t : ℝ, t ≤ 0 →
      (∀ s ∈ uIcc 0 t, MorseHandle.descentFlow s (c.splitChart x.val) ∈
        closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          closedBall (0 : c.PositiveCoordinates) (2 * ρ)) →
      f (c.splitChart.symm (MorseHandle.descentFlow t (c.splitChart x.val))) = f p + ρ ^ 2 →
      (e x).val = c.splitChart.symm (MorseHandle.descentFlow t (c.splitChart x.val))

variable [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

open Classical in
/-- Agreement of the native field on the whole block computes all of the
corresponding attachment-boundary endpoints. -/
theorem followsModelBoundaryOrbits_of_flow
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (heq : ∀ z ∈ closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
        closedBall (0 : c.PositiveCoordinates) (2 * ρ),
      ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    (e : ↥({x | f x ≤ f p - ρ ^ 2} ∪ range (c.attachingHandleMap ρ hρ hblock)) ≃ₜ
      {x : M // f x ≤ f p + ρ ^ 2})
    (horbit : ∀ x, x.val ∈ frontier ({y | f y ≤ f p - ρ ^ 2} ∪
        range (c.attachingHandleMap ρ hρ hblock)) →
      ∀ t : ℝ, t ≤ 0 → f (F t x.val) = f p + ρ ^ 2 → (e x).val = F t x.val) :
    c.FollowsModelBoundaryOrbits ρ hρ hblock e := by
  intro x hx hsource t ht hpath hlevel
  have hmodel := c.flow_eq_descentModel_of_mem_uIcc hV F hcurve hsource
    (fun s hs => hblock (hpath s hs)) (fun s hs => heq _ (hpath s hs))
  exact (horbit x hx t ht (hmodel ▸ hlevel)).trans hmodel

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart
