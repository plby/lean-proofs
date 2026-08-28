import Wikipedia.HopfProblem.DegreeCollapseNativeTimeCollarBounds

/-!
# Boundary germ correction without quantitative collar hypotheses

The native compact time-tube estimates construct the bounds required by
the logarithmic blend. The correction may be confined to any prescribed
signed-time radius. A second, distinct compact level has a uniformly
positive signed-time distance, so its entire germ can be retained.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
  {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- Construct the full boundary germ correction in an arbitrarily small time collar. -/
theorem exists_boundary_germ_correction {U : Set M} (hU : IsOpen U) {f g : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g U)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {c : ℝ} (hlevel : {x | f x = c} ⊆ U) (hbasin : U ⊆ levelBasin F f c)
    (heq : ∀ x, f x = c → g x = f x)
    (hfc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hgneg : ∀ x ∈ U, mvfderiv 𝓘(ℝ, E) g x (V x) < 0)
    {r : ℝ} (hr : 0 < r) :
    ∃ b : M → ℝ, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b U ∧
      (∀ x ∈ U, mvfderiv 𝓘(ℝ, E) b x (V x) < 0) ∧
      (∀ x, f x = c → b =ᶠ[𝓝 x] f) ∧
      ∀ x ∈ U, r ≤ |signedLevelTime F f c x| → b =ᶠ[𝓝 x] g := by
  obtain ⟨ε₀, μ, C, hε₀, hμ, hC, hbounds⟩ := exists_native_time_collar_bounds hU hf hg hV
    F hcurve hlevel hbasin heq hfc (fun x hx => hgneg x (hlevel hx))
  let ε := min ε₀ (r / 2)
  have hε : 0 < ε := lt_min hε₀ (half_pos hr)
  have hεr : ε < r := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨-, hθ, -⟩ := smooth_signed_level_time hf hV F hcurve hfc
  have htime (x : M) (hx : x ∈ U) :
      mvfderiv 𝓘(ℝ, E) (signedLevelTime F f c) x (V x) = -1 :=
    mvfderiv_signedLevelTime hf hV F hcurve hfc (hbasin hx)
  obtain ⟨b, hb, hbneg, hbone, -, hboff⟩ := exists_native_descent_blend hU (hθ.mono hbasin)
    hf.contMDiffOn hg F hcurve htime hgneg hε hμ hC
    (fun x hx ht => hbounds x hx (lt_of_lt_of_le ht (min_le_left _ _)))
  refine ⟨b, hb, hbneg, ?_, fun x hx ht => hboff x hx (hεr.trans_le ht)⟩
  intro x hx
  apply hbone x (hlevel hx)
  let D (y : M) := mvfderiv 𝓘(ℝ, E) f y (V y)
  have hD : Continuous D := (MorseCancellation.contMDiff_directionalDerivative hf hV).continuous
  exact signedLevelTime_eq_zero F hf.continuous hD
    (fun y t => Wikipedia.SmoothSixDPoincare.FlowConstruction.hasDerivAt_comp_integralCurve
      hf (hcurve y) t) hfc hx

/-- A distinct compact level has positive uniform signed-time distance. -/
theorem exists_signedTime_level_separation {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {c d : ℝ} (hcd : c ≠ d)
    (hc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hlevel : {x | f x = d} ⊆ levelBasin F f c) :
    ∃ r : ℝ, 0 < r ∧ ∀ x, f x = d → r < |signedLevelTime F f c x| := by
  obtain ⟨-, hθ, -⟩ := smooth_signed_level_time hf hV F hcurve hc
  have hS : IsCompact {x | f x = d} := (isClosed_eq hf.continuous continuous_const).isCompact
  obtain ⟨r, hr, hmargin⟩ := exists_compact_negative_margin hS
    ((hθ.continuousOn.mono hlevel).abs.neg) (fun x hx => by
      apply neg_neg_of_pos
      apply abs_pos.mpr
      intro hz
      have hhit := signedLevelTime_hits F f c (hlevel hx)
      rw [hz, F.map_zero_apply] at hhit
      exact hcd (hhit.symm.trans hx))
  refine ⟨r, hr, fun x hx => ?_⟩
  have hh : -|signedLevelTime F f c x| < -r := hmargin x hx
  linarith

/-- Restore one entire boundary germ while preserving the entire germ on a
second, distinct level. Every collar radius and derivative bound is constructed. -/
theorem exists_boundary_correction_preserving_level {U : Set M} (hU : IsOpen U) {f g : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g U)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {c d : ℝ} (hcd : c ≠ d) (hcU : {x | f x = c} ⊆ U) (hdU : {x | f x = d} ⊆ U)
    (hbasin : U ⊆ levelBasin F f c) (heq : ∀ x, f x = c → g x = f x)
    (hfc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hgneg : ∀ x ∈ U, mvfderiv 𝓘(ℝ, E) g x (V x) < 0) :
    ∃ b : M → ℝ, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b U ∧
      (∀ x ∈ U, mvfderiv 𝓘(ℝ, E) b x (V x) < 0) ∧
      (∀ x, f x = c → b =ᶠ[𝓝 x] f) ∧ ∀ x, f x = d → b =ᶠ[𝓝 x] g := by
  obtain ⟨r, hr, hsep⟩ := exists_signedTime_level_separation hf hV F hcurve hcd hfc
    (hdU.trans hbasin)
  obtain ⟨b, hb, hbneg, hbc, hboff⟩ := exists_boundary_germ_correction hU hf hg hV F hcurve
    hcU hbasin heq hfc hgneg hr
  exact ⟨b, hb, hbneg, hbc, fun x hx => hboff x (hdU hx) (hsep x hx).le⟩

end Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation
