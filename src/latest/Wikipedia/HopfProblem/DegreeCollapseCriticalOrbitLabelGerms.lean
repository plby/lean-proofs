import Wikipedia.HopfProblem.DegreeCollapseNativeCoreExitNeighborhood
import Wikipedia.HopfProblem.DegreeCollapseNativeMorseBasins
import Wikipedia.HopfProblem.DegreeCollapseSignedLevelTime

/-!
# Constant orbit-label germs at the critical points

An actual orbit crossing a level above a Morse point cannot lie in its
local negative plane: its backward critical limit and monotonicity exclude
that level. The positive-plane statement is dual. Together with controlled
core exits this propagates a constant label weight from an open core
neighborhood to the whole nearby part of the actual level basin.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse
open Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  {f : M → ℝ} {p : M}

open Classical in
theorem eventually_nonzero_positive_coordinate_on_upper_level_basin
    (c : SignedMorseChart (E := E) f p) (hf : Continuous f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x)))
    (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y)
    {a : ℝ} (ha : f p < a) :
    ∀ᶠ x in 𝓝 p, x ∈ levelBasin F f a → (c.splitChart x).2 ≠ 0 := by
  obtain ⟨r, hr, hbox, hfield⟩ := exists_native_morse_field_block c heq
  filter_upwards [morse_coordinate_neighborhood c hr hr] with x hx
  rintro ⟨t, ht⟩ hzero
  have hlim := native_morse_negative_plane_limit c hV F hF hr hbox hfield hx.1 hx.2.1 hzero
  have hheight : Tendsto (fun t => f (F t x)) atBot (𝓝 (f p)) :=
    hf.continuousAt.tendsto.comp hlim
  have hh := (hmono x).ge_of_tendsto hheight t
  rw [ht] at hh
  exact (not_le_of_gt ha) hh

open Classical in
theorem eventually_nonzero_negative_coordinate_on_lower_level_basin
    (c : SignedMorseChart (E := E) f p) (hf : Continuous f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x)))
    (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y)
    {a : ℝ} (ha : a < f p) :
    ∀ᶠ x in 𝓝 p, x ∈ levelBasin F f a → (c.splitChart x).1 ≠ 0 := by
  obtain ⟨r, hr, hbox, hfield⟩ := exists_native_morse_field_block c heq
  filter_upwards [morse_coordinate_neighborhood c hr hr] with x hx
  rintro ⟨t, ht⟩ hzero
  have hlim := native_morse_positive_plane_limit c hV F hF hr hbox hfield hx.1 hx.2.2 hzero
  have hheight : Tendsto (fun t => f (F t x)) atTop (𝓝 (f p)) :=
    hf.continuousAt.tendsto.comp hlim
  have hh := (hmono x).le_of_tendsto hheight t
  rw [ht] at hh
  exact (not_le_of_gt ha) hh

open Classical in
theorem eventually_constant_basin_weight_of_belt_neighborhood
    (c : SignedMorseChart (E := E) f p) (hf : Continuous f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x)))
    {r : ℝ} (hr : 0 < r)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆ c.splitChart.target)
    (hfield : ∀ z ∈ closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * r),
      ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    {a k : ℝ} (ha : f p < a) {w : M → ℝ}
    (hinv : ∀ x ∈ levelBasin F f a, ∀ t : ℝ, w (F t x) = w x)
    {U : Set M} (hU : IsOpen U)
    (hcore : ∀ v : PuncturedHandle.UnitSphere c.PositiveCoordinates,
      (c.beltCoreMap r hr hblock v : M) ∈ U)
    (hplateau : ∀ x ∈ U, f x = f p + r ^ 2 → w x = k) :
    ∀ᶠ x in 𝓝 p, x ∈ levelBasin F f a → w x = k := by
  have hcenter : c.splitChart.symm (0 : c.NegativeCoordinates × c.PositiveCoordinates) = p := by
    rw [← c.splitChart_center]
    exact c.splitChart.left_inv' c.splitChart_mem_source
  have heq := hfield (0 : c.NegativeCoordinates × c.PositiveCoordinates)
    ⟨mem_closedBall_self (by positivity), mem_closedBall_self (by positivity)⟩
  rw [hcenter] at heq
  filter_upwards [eventually_nonzero_positive_coordinate_on_upper_level_basin c hf hV F hF
    hmono heq ha, eventually_backward_exit_in_belt_neighborhood c hV F hF hr hblock hfield hU hcore]
    with x hne hexit
  intro hx
  obtain ⟨T, -, hlevel, hU⟩ := hexit (hne hx)
  exact (hinv x hx T).symm.trans (hplateau _ hU hlevel)

open Classical in
theorem eventually_constant_basin_weight_of_attaching_neighborhood
    (c : SignedMorseChart (E := E) f p) (hf : Continuous f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x)))
    {r : ℝ} (hr : 0 < r)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆ c.splitChart.target)
    (hfield : ∀ z ∈ closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * r),
      ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    {a k : ℝ} (ha : a < f p) {w : M → ℝ}
    (hinv : ∀ x ∈ levelBasin F f a, ∀ t : ℝ, w (F t x) = w x)
    {U : Set M} (hU : IsOpen U)
    (hcore : ∀ v : PuncturedHandle.UnitSphere c.NegativeCoordinates,
      (c.attachingCoreMap r hr hblock v : M) ∈ U)
    (hplateau : ∀ x ∈ U, f x = f p - r ^ 2 → w x = k) :
    ∀ᶠ x in 𝓝 p, x ∈ levelBasin F f a → w x = k := by
  have hcenter : c.splitChart.symm (0 : c.NegativeCoordinates × c.PositiveCoordinates) = p := by
    rw [← c.splitChart_center]
    exact c.splitChart.left_inv' c.splitChart_mem_source
  have heq := hfield (0 : c.NegativeCoordinates × c.PositiveCoordinates)
    ⟨mem_closedBall_self (by positivity), mem_closedBall_self (by positivity)⟩
  rw [hcenter] at heq
  filter_upwards [eventually_nonzero_negative_coordinate_on_lower_level_basin c hf hV F hF
    hmono heq ha, eventually_forward_exit_in_attaching_neighborhood c hV F hF hr hblock hfield hU hcore]
    with x hne hexit
  intro hx
  obtain ⟨T, -, hlevel, hU⟩ := hexit (hne hx)
  exact (hinv x hx T).symm.trans (hplateau _ hU hlevel)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
