import Wikipedia.HopfProblem.DegreeCollapsePositiveBandNormalization
import Wikipedia.HopfProblem.DegreeCollapseNativeTimeChange
import Wikipedia.SmoothSixDPoincare.CompactFlow

/-!
# Complete orbit-preserving normalization of a native regular band

The normalized field, its complete native flow, and its increasing clocks
are all constructed. Full critical-point germs, zeros, strict descent,
whole orbits, both endpoint limits, and uniqueness of a selected connection
are retained.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowTimeChange

/-- Whole-orbit equality and preservation of both limits retain uniqueness
of a selected connection, with the same actual reference orbit. -/
theorem unique_connection_of_orbit_data {X : Type*} [TopologicalSpace X]
    (F G : Flow ℝ X) {S : Set X} {p q z : X}
    (horbits : ∀ x, range (fun t => G t x) = range (fun t => F t x))
    (htop : ∀ x y, Tendsto (fun t => G t x) atTop (𝓝 y) →
      Tendsto (fun t => F t x) atTop (𝓝 y))
    (hbot : ∀ x y, Tendsto (fun t => G t x) atBot (𝓝 y) →
      Tendsto (fun t => F t x) atBot (𝓝 y))
    (hunique : ∀ x ∉ S, Tendsto (fun t => F t x) atBot (𝓝 p) →
      Tendsto (fun t => F t x) atTop (𝓝 q) → ∃ t, F t z = x) :
    ∀ x ∉ S, Tendsto (fun t => G t x) atBot (𝓝 p) →
      Tendsto (fun t => G t x) atTop (𝓝 q) → ∃ t, G t z = x := by
  intro x hx hp hq
  have hh : x ∈ range (fun t => F t z) := hunique x hx (hbot x p hp) (htop x q hq)
  rw [← horbits z] at hh
  exact hh

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  {f : M → ℝ} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- Normalize the original field and construct its complete flow, with
unit descending height speed and exact orbit equivalence. -/
theorem exists_orbit_preserving_band_normalization
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f →
      mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {a b : ℝ} (hband : ∀ x, f x ∈ Icc a b → x ∉ ManifoldMorse.criticalPoints E f) :
    ∃ (U : Set ℝ) (W : (x : M) → TangentSpace 𝓘(ℝ, E) x) (G : Flow ℝ M),
      IsOpen U ∧ Icc a b ⊆ U ∧
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
        (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      (∀ x, IsMIntegralCurve (fun t => G t x) W) ∧
      (∀ x, W x = 0 ↔ V x = 0) ∧
      (∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (W x) < 0) ∧
      (∀ x, f x ∈ U → mvfderiv 𝓘(ℝ, E) f x (W x) = -1) ∧
      (∀ x ∈ ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 x, W y = V y) ∧
      (∀ x, ∃ c : ℝ ≃o ℝ, c 0 = 0 ∧ ∀ t, G t x = F (c.symm t) x) ∧
      ∀ x, range (fun t => G t x) = range (fun t => F t x) ∧
        (∀ p, Tendsto (fun t => G t x) atTop (𝓝 p) ↔ Tendsto (fun t => F t x) atTop (𝓝 p)) ∧
        ∀ p, Tendsto (fun t => G t x) atBot (𝓝 p) ↔ Tendsto (fun t => F t x) atBot (𝓝 p) := by
  obtain ⟨ρ, U, hU, hAU, hρ, hpos, hW, hzeros, hneg, hspeed, hgerm⟩ :=
    MorseCancellation.exists_positive_band_normalization hf hV hdesc hband
  have hW₁ := hW.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  let W : (x : M) → TangentSpace 𝓘(ℝ, E) x := fun x => ρ x • V x
  let G := FlowConstruction.compactFlow hW₁
  have hG (x : M) : IsMIntegralCurve (fun t => G t x) W :=
    FlowConstruction.isMIntegralCurve_compactFlow hW₁ x
  refine ⟨U, W, G, hU, hAU, hW, hG, hzeros, hneg, hspeed, ?_, ?_, ?_⟩
  · intro x hx
    filter_upwards [hgerm x hx] with y hy
    simp only [W, hy, one_smul]
  · intro x
    obtain ⟨c, hc0, -, -, heq⟩ := exists_native_flow_time_change hρ.continuous hpos hW₁ F G hF hG x
    exact ⟨c, hc0, heq⟩
  · exact native_flow_time_change_orbits hρ.continuous hpos hW₁ F G hF hG

end Wikipedia.HopfProblem.DegreeCollapse.FlowTimeChange
