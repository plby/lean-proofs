import Wikipedia.HopfProblem.DegreeCollapseNativeAttachingBasinImage

/-!
# The entire original forward basin on the belt level is the core image

An actual forward limit supplies a nonzero small positive Morse coordinate.
Normalization and the exact belt-core half-orbit give a common orbit;
uniqueness of the regular-level crossing identifies the original point.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  {f : M → ℝ} {p : M} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

open Classical in
theorem native_forward_basin_mem_belt_core (c : SignedMorseChart (E := E) f p)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (r : ℝ) (hr : 0 < r)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆ c.splitChart.target)
    (hfield : ∀ z ∈ closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * r),
      ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    (hboundary : ∀ x, f x = f p + r ^ 2 → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    {x : M} (hlevel : f x = f p + r ^ 2)
    (hlim : Tendsto (fun t => F t x) atTop (𝓝 p)) :
    ∃ u : PuncturedHandle.UnitSphere c.PositiveCoordinates,
      (c.beltCoreMap r hr hblock u : M) = x := by
  have hV₁ := hV.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  have hcenter : c.splitChart.symm (0 : c.NegativeCoordinates × c.PositiveCoordinates) = p := by
    rw [← c.splitChart_center]
    exact c.splitChart.left_inv' c.splitChart_mem_source
  have heq := hfield (0 : c.NegativeCoordinates × c.PositiveCoordinates)
    ⟨mem_closedBall_self (by positivity), mem_closedBall_self (by positivity)⟩
  rw [hcenter] at heq
  obtain ⟨T, hsource, hplane, -⟩ := exists_incoming_morse_tail c hV₁ F hF x hlim heq
  obtain ⟨hcoord, -⟩ := morse_endpoint_tail_data c F x hlim heq
  have hnorm : Tendsto (fun t => ‖(c.splitChart (F t x)).2‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [comp_def, Prod.snd_zero, norm_zero] using
      (continuous_snd.norm.tendsto (0 : c.NegativeCoordinates × c.PositiveCoordinates)).comp hcoord
  obtain ⟨s, hsmall, hs⟩ :=
    ((hnorm.eventually (eventually_lt_nhds hr)).and (eventually_ge_atTop T)).exists
  have hxp : x ≠ p := by
    intro hh
    rw [hh] at hlevel
    nlinarith [sq_pos_of_pos hr]
  have hnonzero := morse_coordinates_nonzero_on_nonstationary_orbit c hV₁ F hF hxp heq
    (hsource s hs)
  have hn : (c.splitChart (F s x)).2 ≠ 0 :=
    fun hz => hnonzero (Prod.ext (hplane s hs) hz)
  obtain ⟨u, t, ht, hu⟩ := exists_positive_core_ray_parameter hr hn hsmall
  have hmodel : MorseHandle.descentFlow t ((0 : c.NegativeCoordinates),
      r • (u : c.PositiveCoordinates)) = c.splitChart (F s x) := by
    apply Prod.ext
    · change Real.exp t • (0 : c.NegativeCoordinates) = (c.splitChart (F s x)).1
      rw [smul_zero, hplane s hs]
    · exact hu
  have hcore := native_belt_core_flow c hV₁ F hF r hr hblock hfield u ht.le
  rw [hmodel] at hcore
  have hsame : F t (c.beltCoreMap r hr hblock u) = F s x :=
    hcore.trans (c.splitChart.left_inv' (hsource s hs))
  exact ⟨u, native_same_level_orbit_points hf hV F hF hboundary
    (c.beltCoreMap r hr hblock u).property hlevel hsame⟩

open Classical in
theorem native_belt_core_basin_iff (c : SignedMorseChart (E := E) f p)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (r : ℝ) (hr : 0 < r)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆ c.splitChart.target)
    (hfield : ∀ z ∈ closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * r),
      ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    (hboundary : ∀ x, f x = f p + r ^ 2 → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    {x : M} (hlevel : f x = f p + r ^ 2) :
    Tendsto (fun t => F t x) atTop (𝓝 p) ↔
      ∃ u : PuncturedHandle.UnitSphere c.PositiveCoordinates,
        (c.beltCoreMap r hr hblock u : M) = x := by
  constructor
  · exact native_forward_basin_mem_belt_core c hf hV F hF r hr hblock hfield hboundary hlevel
  · rintro ⟨u, rfl⟩
    exact native_belt_core_forward_limit c (hV.of_le (by simp)) F hF r hr hblock hfield u

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
