import Wikipedia.HopfProblem.DegreeCollapseNativeMorseBlockExit
import Wikipedia.SmoothSixDPoincare.DescendingFlow
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Exact native stable and unstable sets near a Morse critical point

A constructed Morse field block gives both directions. Pure contracting
coordinates stay in the block and converge to the actual critical point.
A nonzero expanding coordinate produces a finite exit on the wrong side
of the critical value, contradicting the original function's monotonicity
if that orbit were to converge to the critical point. No prior assertion
that the actual orbit stays in the chart is assumed.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  {f : M → ℝ} {p : M}

open ManifoldMorse

open Classical in
/-- The actual local positive plane converges to the critical point under
the original complete native flow. -/
theorem native_morse_positive_plane_limit (c : SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {r : ℝ} (hr : 0 < r)
    (hbox : closedBall (0 : c.NegativeCoordinates) r ×ˢ closedBall (0 : c.PositiveCoordinates) r ⊆
      c.splitChart.target)
    (heq : ∀ z ∈ closedBall (0 : c.NegativeCoordinates) r ×ˢ
      closedBall (0 : c.PositiveCoordinates) r, ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    {x : M} (hx : x ∈ c.splitChart.source) (hp : ‖(c.splitChart x).2‖ < r)
    (hzero : (c.splitChart x).1 = 0) : Tendsto (fun t => F t x) atTop (𝓝 p) := by
  have hstay (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) : MorseHandle.descentFlow t (c.splitChart x) ∈
      closedBall (0 : c.NegativeCoordinates) r ×ˢ closedBall (0 : c.PositiveCoordinates) r := by
    constructor
    · rw [mem_closedBall_zero_iff, MorseHandle.norm_descentFlow_fst, hzero, norm_zero, mul_zero]
      exact hr.le
    · exact mem_closedBall_zero_iff.mpr
        ((MorseHandle.norm_snd_descentFlow_le ht (c.splitChart x)).trans hp.le)
  have hflow := c.flow_eqOn_descentModel hV F hF hx isPreconnected_Ici (le_refl (0 : ℝ))
    (fun t ht => hbox (hstay t ht)) (fun t ht => heq _ (hstay t ht))
  have hfirst : Tendsto (fun t : ℝ => Real.exp t • (c.splitChart x).1) atTop
      (𝓝 (0 : c.NegativeCoordinates)) := by
    simp only [hzero, smul_zero]
    exact tendsto_const_nhds
  have hsecond : Tendsto (fun t : ℝ => Real.exp (-t) • (c.splitChart x).2) atTop
      (𝓝 (0 : c.PositiveCoordinates)) := by
    simpa only [comp_def, zero_smul] using
      (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).smul_const (c.splitChart x).2
  have hlim : Tendsto (fun t => MorseHandle.descentFlow t (c.splitChart x)) atTop
      (𝓝 (0 : c.NegativeCoordinates × c.PositiveCoordinates)) := hfirst.prodMk_nhds hsecond
  have h0 : (0 : c.NegativeCoordinates × c.PositiveCoordinates) ∈ c.splitChart.target :=
    hbox ⟨mem_closedBall_self hr.le, mem_closedBall_self hr.le⟩
  have hcenter : c.splitChart.symm 0 = p := by
    rw [← c.splitChart_center]
    exact c.splitChart.left_inv' c.splitChart_mem_source
  have hn : Tendsto (fun t => c.splitChart.symm (MorseHandle.descentFlow t (c.splitChart x)))
      atTop (𝓝 (c.splitChart.symm 0)) :=
    c.splitChart.toOpenPartialHomeomorph.symm.continuousAt h0 |>.tendsto.comp hlim
  rw [hcenter] at hn
  apply hn.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact (hflow ht).symm

open Classical in
/-- The actual local negative plane converges to the critical point in
backward time under the original complete native flow. -/
theorem native_morse_negative_plane_limit (c : SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {r : ℝ} (hr : 0 < r)
    (hbox : closedBall (0 : c.NegativeCoordinates) r ×ˢ closedBall (0 : c.PositiveCoordinates) r ⊆
      c.splitChart.target)
    (heq : ∀ z ∈ closedBall (0 : c.NegativeCoordinates) r ×ˢ
      closedBall (0 : c.PositiveCoordinates) r, ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    {x : M} (hx : x ∈ c.splitChart.source) (hn : ‖(c.splitChart x).1‖ < r)
    (hzero : (c.splitChart x).2 = 0) : Tendsto (fun t => F t x) atBot (𝓝 p) := by
  have hstay (t : ℝ) (ht : t ∈ Iic (0 : ℝ)) : MorseHandle.descentFlow t (c.splitChart x) ∈
      closedBall (0 : c.NegativeCoordinates) r ×ˢ closedBall (0 : c.PositiveCoordinates) r := by
    constructor
    · rw [mem_closedBall_zero_iff, MorseHandle.norm_descentFlow_fst]
      exact (mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr ht)).trans hn.le
    · rw [mem_closedBall_zero_iff, MorseHandle.norm_descentFlow_snd, hzero, norm_zero, mul_zero]
      exact hr.le
  have hflow := c.flow_eqOn_descentModel hV F hF hx isPreconnected_Iic (le_refl (0 : ℝ))
    (fun t ht => hbox (hstay t ht)) (fun t ht => heq _ (hstay t ht))
  have hfirst : Tendsto (fun t : ℝ => Real.exp t • (c.splitChart x).1) atBot
      (𝓝 (0 : c.NegativeCoordinates)) := by
    simpa only [zero_smul] using Real.tendsto_exp_atBot.smul_const (c.splitChart x).1
  have hsecond : Tendsto (fun t : ℝ => Real.exp (-t) • (c.splitChart x).2) atBot
      (𝓝 (0 : c.PositiveCoordinates)) := by
    simp only [hzero, smul_zero]
    exact tendsto_const_nhds
  have hlim : Tendsto (fun t => MorseHandle.descentFlow t (c.splitChart x)) atBot
      (𝓝 (0 : c.NegativeCoordinates × c.PositiveCoordinates)) := hfirst.prodMk_nhds hsecond
  have h0 : (0 : c.NegativeCoordinates × c.PositiveCoordinates) ∈ c.splitChart.target :=
    hbox ⟨mem_closedBall_self hr.le, mem_closedBall_self hr.le⟩
  have hcenter : c.splitChart.symm 0 = p := by
    rw [← c.splitChart_center]
    exact c.splitChart.left_inv' c.splitChart_mem_source
  have hh : Tendsto (fun t => c.splitChart.symm (MorseHandle.descentFlow t (c.splitChart x)))
      atBot (𝓝 (c.splitChart.symm 0)) :=
    c.splitChart.toOpenPartialHomeomorph.symm.continuousAt h0 |>.tendsto.comp hlim
  rw [hcenter] at hh
  apply hh.congr'
  filter_upwards [eventually_le_atBot (0 : ℝ)] with t ht
  exact (hflow ht).symm

open Classical in
/-- Construct one native neighborhood where the actual forward and backward
endpoint basins are exactly the two Morse coordinate planes. -/
theorem exists_native_morse_basin_block (c : SignedMorseChart (E := E) f p)
    (hf : Continuous f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x)))
    (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) :
    ∃ r : ℝ, 0 < r ∧
      closedBall (0 : c.NegativeCoordinates) r ×ˢ closedBall (0 : c.PositiveCoordinates) r ⊆
        c.splitChart.target ∧
      ∀ x ∈ c.splitChart.source, ‖(c.splitChart x).1‖ < r → ‖(c.splitChart x).2‖ < r →
        (Tendsto (fun t => F t x) atTop (𝓝 p) ↔ (c.splitChart x).1 = 0) ∧
        (Tendsto (fun t => F t x) atBot (𝓝 p) ↔ (c.splitChart x).2 = 0) := by
  obtain ⟨r, hr, hbox, hfield⟩ := exists_native_morse_field_block c heq
  refine ⟨r, hr, hbox, ?_⟩
  intro x hx hn hp
  constructor
  · constructor
    · intro hlim
      by_contra hne
      obtain ⟨T, hT, hexit⟩ := exists_native_forward_morse_exit c hV F hF hr hbox hfield hx hn hp hne
      have hheight : Tendsto (fun t => f (F t x)) atTop (𝓝 (f p)) := hf.continuousAt.tendsto.comp hlim
      exact (not_lt_of_ge ((hmono x).le_of_tendsto hheight T)) hexit
    · exact native_morse_positive_plane_limit c hV F hF hr hbox hfield hx hp
  · constructor
    · intro hlim
      by_contra hne
      obtain ⟨T, hT, hexit⟩ := exists_native_backward_morse_exit c hV F hF hr hbox hfield hx hn hp hne
      have hheight : Tendsto (fun t => f (F t x)) atBot (𝓝 (f p)) := hf.continuousAt.tendsto.comp hlim
      exact (not_lt_of_ge ((hmono x).ge_of_tendsto hheight T)) hexit
    · exact native_morse_negative_plane_limit c hV F hF hr hbox hfield hx hn

open Classical in
/-- Strict native descent and vanishing at the critical points supply the
monotonicity used in the exact local endpoint-basin classification. -/
theorem exists_descending_morse_basin_block (c : SignedMorseChart (E := E) f p)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) :
    ∃ r : ℝ, 0 < r ∧
      closedBall (0 : c.NegativeCoordinates) r ×ˢ closedBall (0 : c.PositiveCoordinates) r ⊆
        c.splitChart.target ∧
      ∀ x ∈ c.splitChart.source, ‖(c.splitChart x).1‖ < r → ‖(c.splitChart x).2‖ < r →
        (Tendsto (fun t => F t x) atTop (𝓝 p) ↔ (c.splitChart x).1 = 0) ∧
        (Tendsto (fun t => F t x) atBot (𝓝 p) ↔ (c.splitChart x).2 = 0) :=
  exists_native_morse_basin_block c hf.continuous hV F hF
    (FlowConstruction.antitone_flow_height hf F hF hzero hdesc) heq

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
