import Wikipedia.HopfProblem.DegreeCollapseMorseModelExit
import Wikipedia.SmoothSixDPoincare.MorseChartFlow

/-!
# Constructed native Morse field blocks and actual finite exits

The original Morse field germ constructs a closed product block on which
all native model comparisons are valid. A nonzero expanding coordinate
then gives a finite time on the actual original flow with function value
strictly on the far side of the critical value.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}

open ManifoldMorse

open Classical in
/-- A genuine positive-radius closed product block is constructed from
the native field germ at the Morse critical point. -/
theorem exists_native_morse_field_block (c : SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) :
    ∃ r : ℝ, 0 < r ∧
      closedBall (0 : c.NegativeCoordinates) r ×ˢ closedBall (0 : c.PositiveCoordinates) r ⊆
        c.splitChart.target ∧
      ∀ z ∈ closedBall (0 : c.NegativeCoordinates) r ×ˢ closedBall (0 : c.PositiveCoordinates) r,
        ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y := by
  have h0 : (0 : c.NegativeCoordinates × c.PositiveCoordinates) ∈ c.splitChart.target := by
    rw [← c.splitChart_center]
    exact c.splitChart.map_source' c.splitChart_mem_source
  have hcenter : c.splitChart.symm 0 = p := by
    rw [← c.splitChart_center]
    exact c.splitChart.left_inv' c.splitChart_mem_source
  have hcont : Tendsto c.splitChart.symm (𝓝 (0 : c.NegativeCoordinates × c.PositiveCoordinates))
      (𝓝 p) := by
    have hh : Tendsto c.splitChart.symm (𝓝 (0 : c.NegativeCoordinates × c.PositiveCoordinates))
        (𝓝 (c.splitChart.symm 0)) := c.splitChart.toOpenPartialHomeomorph.symm.continuousAt h0
    rwa [hcenter] at hh
  have htarget : ∀ᶠ z in 𝓝 (0 : c.NegativeCoordinates × c.PositiveCoordinates),
      z ∈ c.splitChart.target := c.splitChart.open_target.mem_nhds h0
  have hgerm : ∀ᶠ y in 𝓝 p, ∀ᶠ x in 𝓝 y, V x = c.descentField x :=
    eventually_eventually_nhds.mpr heq
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (htarget.and (hcont.eventually hgerm))
  have hblock (z) (hz : z ∈ closedBall (0 : c.NegativeCoordinates) r ×ˢ
      closedBall (0 : c.PositiveCoordinates) r) := hsub (by
    rw [closedBall_prod_same] at hz
    convert! hz using 1)
  exact ⟨r, hr, fun z hz => (hblock z hz).1, fun z hz => (hblock z hz).2⟩

variable [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

open Classical in
/-- A nonzero negative coordinate gives an actual forward flow point below
the critical value, with all model-domain hypotheses proved by the block. -/
theorem exists_native_forward_morse_exit (c : SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {r : ℝ} (hr : 0 < r)
    (hbox : closedBall (0 : c.NegativeCoordinates) r ×ˢ closedBall (0 : c.PositiveCoordinates) r ⊆
      c.splitChart.target)
    (heq : ∀ z ∈ closedBall (0 : c.NegativeCoordinates) r ×ˢ
      closedBall (0 : c.PositiveCoordinates) r, ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    {x : M} (hx : x ∈ c.splitChart.source)
    (hn : ‖(c.splitChart x).1‖ < r) (hp : ‖(c.splitChart x).2‖ < r)
    (hne : (c.splitChart x).1 ≠ 0) : ∃ T : ℝ, 0 < T ∧ f (F T x) < f p := by
  obtain ⟨T, hT, hstay, hheight⟩ := exists_forward_morse_model_exit hr hn hp hne
  have hdomain (s : ℝ) (hs : s ∈ uIcc (0 : ℝ) T) :
      MorseHandle.descentFlow s (c.splitChart x) ∈
        closedBall (0 : c.NegativeCoordinates) r ×ˢ closedBall (0 : c.PositiveCoordinates) r :=
    hstay s (by simpa only [uIcc_of_le hT.le] using hs)
  have hflow := c.flow_eq_descentModel_of_mem_uIcc hV F hF hx
    (fun s hs => hbox (hdomain s hs)) (fun s hs => heq _ (hdomain s hs))
  refine ⟨T, hT, ?_⟩
  rw [hflow, c.splitChart_inverse_equation (hbox (hstay T ⟨hT.le, le_rfl⟩))]
  change -‖(MorseHandle.descentFlow T (c.splitChart x)).1‖ ^ 2 +
    ‖(MorseHandle.descentFlow T (c.splitChart x)).2‖ ^ 2 < 0 at hheight
  linarith

open Classical in
/-- A nonzero positive coordinate gives an actual backward flow point above
the critical value. -/
theorem exists_native_backward_morse_exit (c : SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {r : ℝ} (hr : 0 < r)
    (hbox : closedBall (0 : c.NegativeCoordinates) r ×ˢ closedBall (0 : c.PositiveCoordinates) r ⊆
      c.splitChart.target)
    (heq : ∀ z ∈ closedBall (0 : c.NegativeCoordinates) r ×ˢ
      closedBall (0 : c.PositiveCoordinates) r, ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    {x : M} (hx : x ∈ c.splitChart.source)
    (hn : ‖(c.splitChart x).1‖ < r) (hp : ‖(c.splitChart x).2‖ < r)
    (hne : (c.splitChart x).2 ≠ 0) : ∃ T : ℝ, T < 0 ∧ f p < f (F T x) := by
  obtain ⟨T, hT, hstay, hheight⟩ := exists_backward_morse_model_exit hr hn hp hne
  have hdomain (s : ℝ) (hs : s ∈ uIcc (0 : ℝ) T) :
      MorseHandle.descentFlow s (c.splitChart x) ∈
        closedBall (0 : c.NegativeCoordinates) r ×ˢ closedBall (0 : c.PositiveCoordinates) r :=
    hstay s (by simpa only [uIcc_of_ge hT.le] using hs)
  have hflow := c.flow_eq_descentModel_of_mem_uIcc hV F hF hx
    (fun s hs => hbox (hdomain s hs)) (fun s hs => heq _ (hdomain s hs))
  refine ⟨T, hT, ?_⟩
  rw [hflow, c.splitChart_inverse_equation (hbox (hstay T ⟨le_rfl, hT.le⟩))]
  change 0 < -‖(MorseHandle.descentFlow T (c.splitChart x)).1‖ ^ 2 +
    ‖(MorseHandle.descentFlow T (c.splitChart x)).2‖ ^ 2 at hheight
  linarith

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
