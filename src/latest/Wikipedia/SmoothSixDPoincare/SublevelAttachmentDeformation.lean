import Wikipedia.SmoothSixDPoincare.FlowDeformation
import Wikipedia.SmoothSixDPoincare.DescentResidence

/-!
# Deformation onto an actual absorbing attachment across a critical band

The previously proved uniform residence estimate supplies finite hitting
times. The continuous first-entry construction then gives a strong
deformation retraction, once trapping and critical-neighborhood coverage
have been verified for the actual attachment.
-/

noncomputable section

open Set Manifold ContinuousMap
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] {f : M → ℝ} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- A closed absorbing attachment containing the band's critical neighborhoods is reached by
every trajectory from the upper sublevel. -/
theorem exists_uniform_absorbing_entry
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x)))
    {a b : ℝ} {A : Set M} (hlower : {x | f x ≤ a} ⊆ A)
    (hcover : ∀ x ∈ ManifoldMorse.criticalPoints E f, f x ∈ Icc a b → x ∈ interior A) :
    ∃ T > (0 : ℝ), ∀ x, f x ≤ b → ∃ t ∈ Icc 0 T, F t x ∈ A := by
  obtain ⟨T, hT, hentry⟩ := exists_uniform_criticalNeighborhood_entry hf hV hdesc F hcurve hmono
    isOpen_interior hcover
  refine ⟨T, hT, ?_⟩
  intro x hx
  obtain ⟨t, ht, hlow | hint⟩ := hentry x hx
  · exact ⟨t, ht, hlower (show f (F t x) ≤ a from le_of_lt hlow)⟩
  · exact ⟨t, ht, interior_subset hint⟩

/-- The actual attachment's inclusion into the upper sublevel is a homotopy equivalence. -/
theorem exists_absorbingSublevelHomotopyEquiv
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x)))
    {a b : ℝ} {A : Set M} (hA : IsClosed A)
    (hlower : {x | f x ≤ a} ⊆ A) (hupper : A ⊆ {x | f x ≤ b})
    (hcover : ∀ x ∈ ManifoldMorse.criticalPoints E f, f x ∈ Icc a b → x ∈ interior A)
    (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A)
    (hentry : ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A) :
    ∃ e : A ≃ₕ {x : M // f x ≤ b}, ∀ x, (e x).1 = x.1 := by
  obtain ⟨T, _, hhit⟩ := exists_uniform_absorbing_entry hf hV hdesc F hcurve hmono hlower hcover
  have hfinite : ∀ x ∈ {x | f x ≤ b}, ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A := by
    intro x hx
    obtain ⟨t, ht, hm⟩ := hhit x hx
    exact ⟨t, ht.1, hm⟩
  have hregion : ∀ x ∈ {x | f x ≤ b}, ∀ t : ℝ, 0 ≤ t → f (F t x) ≤ b := by
    intro x hx t ht
    have hle : f (F t x) ≤ f x := by simpa only [F.map_zero_apply] using hmono x ht
    exact hle.trans hx
  exact ⟨entryHomotopyEquiv F hA hforward hentry hfinite hupper hregion, fun _ => rfl⟩

end Wikipedia.SmoothSixDPoincare.FlowConstruction
