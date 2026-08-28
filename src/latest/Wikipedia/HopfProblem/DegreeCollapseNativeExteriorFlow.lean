import Wikipedia.HopfProblem.DegreeCollapseNativeFlowSegment
import Wikipedia.HopfProblem.DegreeCollapseAdaptedHeightField
import Wikipedia.HopfProblem.DegreeCollapseFlowBarrier

/-!
# Exact exterior flow tails after a supported band perturbation

Native uniqueness on closed segments identifies whole positive and
negative half-orbits wherever the fields agree. Strict boundary barriers
construct the required exterior invariance, even without monotonicity
inside the perturbed band.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M]
  {V W : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- An entire forward half-orbit in the agreement region is the original half-orbit. -/
theorem native_flow_eq_on_positive_halfline
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F G : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hG : ∀ x, IsMIntegralCurve (fun t => G t x) W)
    {x : M} (hagrees : ∀ t : ℝ, 0 ≤ t → W (G t x) = V (G t x)) :
    ∀ t : ℝ, 0 ≤ t → G t x = F t x := by
  intro t ht
  rcases ht.eq_or_lt with ht | ht
  · subst t
    rw [G.map_zero_apply, F.map_zero_apply]
  · have hc : IsMIntegralCurveOn (fun s => G s x) V (Ioo (0 : ℝ) t) := by
      intro s hs
      have hd := hG x s
      rw [hagrees s hs.1.le] at hd
      exact hd.hasMFDerivWithinAt
    have hh := FlowSuspension.native_flow_segment_endpoints hV F hF ht
      (hG x).continuous.continuousOn hc
    simpa only [sub_zero, G.map_zero_apply] using hh.symm

/-- An entire backward half-orbit in the agreement region is the original half-orbit. -/
theorem native_flow_eq_on_negative_halfline
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F G : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hG : ∀ x, IsMIntegralCurve (fun t => G t x) W)
    {x : M} (hagrees : ∀ t : ℝ, t ≤ 0 → W (G t x) = V (G t x)) :
    ∀ t : ℝ, t ≤ 0 → G t x = F t x := by
  intro t ht
  rcases ht.lt_or_eq with ht | ht
  · have hc : IsMIntegralCurveOn (fun s => G s x) V (Ioo t (0 : ℝ)) := by
      intro s hs
      have hd := hG x s
      rw [hagrees s hs.2.le] at hd
      exact hd.hasMFDerivWithinAt
    have hh := FlowSuspension.native_flow_segment_endpoints hV F hF ht
      (hG x).continuous.continuousOn hc
    have he := congrArg (F t) hh
    simpa only [zero_sub, ← F.map_add, add_neg_cancel, F.map_zero_apply,
      G.map_zero_apply] using he
  · subst t
    rw [G.map_zero_apply, F.map_zero_apply]

/-- A strict descending level barrier also gives backward invariance of its superlevel. -/
theorem backwardInvariant_superlevel_of_boundary {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t)
    {c : ℝ} (hboundary : ∀ x, f x = c → D x < 0) :
    ∀ x, c ≤ f x → ∀ t : ℝ, t ≤ 0 → c ≤ f (F t x) := by
  intro x hx t ht
  rcases ht.lt_or_eq with ht | ht
  · by_contra hn
    have hh := strict_sublevel_entry_of_boundary F hf hD hder hboundary
      (F t x) (le_of_not_ge hn) (-t) (neg_pos.mpr ht)
    rw [← F.map_add, neg_add_cancel, F.map_zero_apply] at hh
    exact (not_lt_of_ge hx) hh
  · subst t
    simpa only [F.map_zero_apply] using hx

variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Agreement outside a band and strict boundary derivatives preserve both
complete exterior tails of the original native flow. -/
theorem native_exterior_flow_tails {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hW : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F G : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hG : ∀ x, IsMIntegralCurve (fun t => G t x) W)
    {a b : ℝ} (hagrees : ∀ x, f x ≤ a ∨ b ≤ f x → W x = V x)
    (hboundary : ∀ x, f x = a ∨ f x = b → mvfderiv 𝓘(ℝ, E) f x (W x) < 0) :
    (∀ x, f x ≤ a → ∀ t : ℝ, 0 ≤ t → G t x = F t x) ∧
    (∀ x, b ≤ f x → ∀ t : ℝ, t ≤ 0 → G t x = F t x) := by
  have hD := (MorseCancellation.contMDiff_directionalDerivative hf hW).continuous
  have hder (x : M) (t : ℝ) := FlowConstruction.hasDerivAt_comp_integralCurve hf (hG x) t
  constructor
  · intro x hx
    apply native_flow_eq_on_positive_halfline hV F G hF hG
    intro t ht
    apply hagrees
    exact Or.inl (forwardInvariant_sublevel_of_boundary G hf.continuous hD hder
      (fun y hy => hboundary y (Or.inl hy)) x hx t ht)
  · intro x hx
    apply native_flow_eq_on_negative_halfline hV F G hF hG
    intro t ht
    apply hagrees
    exact Or.inr (backwardInvariant_superlevel_of_boundary G hf.continuous hD hder
      (fun y hy => hboundary y (Or.inr hy)) x hx t ht)

end Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation
