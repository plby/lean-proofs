import Wikipedia.HopfProblem.DegreeCollapseMorseQuadraticLevelExit
import Wikipedia.HopfProblem.DegreeCollapseNativeMorseBlockExit

/-!
# Actual native flow exits at the original Morse levels

The fixed quadratic-level exits are transported through the original signed
Morse chart. They concern the same complete field and flow, and retain the
small transverse coordinate in that chart at the actual crossing point.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  {f : M → ℝ} {p : M}

open Classical in
theorem exists_native_backward_morse_level_exit (c : SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {r : ℝ} (hr : 0 < r)
    (hbox : closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆ c.splitChart.target)
    (heq : ∀ z ∈ closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * r),
      ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    {x : M} (hx : x ∈ c.splitChart.source)
    (hn : ‖(c.splitChart x).1‖ < r) (hp : ‖(c.splitChart x).2‖ < r)
    (hne : (c.splitChart x).2 ≠ 0) :
    ∃ T : ℝ, T < 0 ∧ f (F T x) = f p + r ^ 2 ∧
      F T x ∈ c.splitChart.source ∧
      ‖(c.splitChart (F T x)).1‖ ≤ ‖(c.splitChart x).1‖ ∧
      c.splitChart (F T x) ∈ closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
        closedBall (0 : c.PositiveCoordinates) (2 * r) := by
  obtain ⟨T, hT, hlevel, hstay, hsmall⟩ := exists_backward_morse_quadratic_level_exit hr hn hp hne
  have hdomain (s : ℝ) (hs : s ∈ uIcc (0 : ℝ) T) :=
    hstay s (by simpa only [uIcc_of_ge hT.le] using hs)
  have hflow := c.flow_eq_descentModel_of_mem_uIcc hV F hF hx
    (fun s hs => hbox (hdomain s hs)) (fun s hs => heq _ (hdomain s hs))
  have htarget := hbox (hstay T ⟨le_rfl, hT.le⟩)
  have hsource : F T x ∈ c.splitChart.source := by
    rw [hflow]
    exact c.splitChart.map_target' htarget
  have hcoord : c.splitChart (F T x) = MorseHandle.descentFlow T (c.splitChart x) := by
    rw [hflow]
    exact c.splitChart.right_inv' htarget
  refine ⟨T, hT, ?_, hsource, ?_, ?_⟩
  · rw [hflow, c.splitChart_inverse_equation htarget]
    change -‖(MorseHandle.descentFlow T (c.splitChart x)).1‖ ^ 2 +
      ‖(MorseHandle.descentFlow T (c.splitChart x)).2‖ ^ 2 = r ^ 2 at hlevel
    linarith
  · simpa only [hcoord] using hsmall
  · rw [hcoord]
    exact hstay T ⟨le_rfl, hT.le⟩

open Classical in
theorem exists_native_forward_morse_level_exit (c : SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {r : ℝ} (hr : 0 < r)
    (hbox : closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆ c.splitChart.target)
    (heq : ∀ z ∈ closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * r),
      ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    {x : M} (hx : x ∈ c.splitChart.source)
    (hn : ‖(c.splitChart x).1‖ < r) (hp : ‖(c.splitChart x).2‖ < r)
    (hne : (c.splitChart x).1 ≠ 0) :
    ∃ T : ℝ, 0 < T ∧ f (F T x) = f p - r ^ 2 ∧
      F T x ∈ c.splitChart.source ∧
      ‖(c.splitChart (F T x)).2‖ ≤ ‖(c.splitChart x).2‖ ∧
      c.splitChart (F T x) ∈ closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
        closedBall (0 : c.PositiveCoordinates) (2 * r) := by
  obtain ⟨T, hT, hlevel, hstay, hsmall⟩ := exists_forward_morse_quadratic_level_exit hr hn hp hne
  have hdomain (s : ℝ) (hs : s ∈ uIcc (0 : ℝ) T) :=
    hstay s (by simpa only [uIcc_of_le hT.le] using hs)
  have hflow := c.flow_eq_descentModel_of_mem_uIcc hV F hF hx
    (fun s hs => hbox (hdomain s hs)) (fun s hs => heq _ (hdomain s hs))
  have htarget := hbox (hstay T ⟨hT.le, le_rfl⟩)
  have hsource : F T x ∈ c.splitChart.source := by
    rw [hflow]
    exact c.splitChart.map_target' htarget
  have hcoord : c.splitChart (F T x) = MorseHandle.descentFlow T (c.splitChart x) := by
    rw [hflow]
    exact c.splitChart.right_inv' htarget
  refine ⟨T, hT, ?_, hsource, ?_, ?_⟩
  · rw [hflow, c.splitChart_inverse_equation htarget]
    change -‖(MorseHandle.descentFlow T (c.splitChart x)).1‖ ^ 2 +
      ‖(MorseHandle.descentFlow T (c.splitChart x)).2‖ ^ 2 = -(r ^ 2) at hlevel
    linarith
  · simpa only [hcoord] using hsmall
  · rw [hcoord]
    exact hstay T ⟨hT.le, le_rfl⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
