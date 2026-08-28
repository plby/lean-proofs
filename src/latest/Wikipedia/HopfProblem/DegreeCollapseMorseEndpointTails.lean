import Wikipedia.HopfProblem.DegreeCollapseMorseOrbitCoordinates

/-!
# Pure stable and unstable tails of actual native connections

A trajectory converging to a Morse critical point eventually lies in its
actual Morse chart and the field-agreement neighborhood. Local uniqueness
then gives the exact linear model on that entire tail. The norm of an
expanding coordinate cannot converge to zero unless that coordinate is zero.
Thus a forward endpoint has only positive coordinates, and a backward
endpoint has only negative coordinates.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {f : M → ℝ} {p : M}

open ManifoldMorse

open Classical in
/-- Convergence to the critical point supplies actual chart and field-germ
control, as well as convergence of the genuine Morse coordinates to zero. -/
theorem morse_endpoint_tail_data (c : SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (F : Flow ℝ M) (x : M) {l : Filter ℝ}
    (hlim : Tendsto (fun t => F t x) l (𝓝 p))
    (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) :
    Tendsto (fun t => c.splitChart (F t x)) l (𝓝 0) ∧
      ∀ᶠ t in l, F t x ∈ c.splitChart.source ∧
        ∀ᶠ y in 𝓝 (F t x), V y = c.descentField y := by
  have hc := c.splitChart.toOpenPartialHomeomorph.continuousAt c.splitChart_mem_source
  have hcoord : Tendsto (fun t => c.splitChart (F t x)) l (𝓝 0) := by
    have hh : Tendsto (fun t => c.splitChart (F t x)) l (𝓝 (c.splitChart p)) :=
      hc.tendsto.comp hlim
    simpa only [c.splitChart_center] using hh
  have hsource : ∀ᶠ y in 𝓝 p, y ∈ c.splitChart.source :=
    c.splitChart.open_source.mem_nhds c.splitChart_mem_source
  have hgerm : ∀ᶠ y in 𝓝 p, ∀ᶠ z in 𝓝 y, V z = c.descentField z :=
    eventually_eventually_nhds.mpr heq
  exact ⟨hcoord, hlim.eventually (hsource.and hgerm)⟩

open Classical in
/-- The actual incoming tail is entirely in the positive Morse block. -/
theorem exists_incoming_morse_tail (c : SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (x : M) (hlim : Tendsto (fun t => F t x) atTop (𝓝 p))
    (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) :
    ∃ T : ℝ,
      (∀ t ≥ T, F t x ∈ c.splitChart.source) ∧
      (∀ t ≥ T, (c.splitChart (F t x)).1 = 0) ∧
      ∀ t ≥ T, ∀ s ≥ T, c.splitChart (F s x) =
        MorseHandle.descentFlow (s - t) (c.splitChart (F t x)) := by
  obtain ⟨hcoord, htail⟩ := morse_endpoint_tail_data c F x hlim heq
  obtain ⟨T, hT⟩ := eventually_atTop.mp htail
  have hformula (t : ℝ) (ht : T ≤ t) (s : ℝ) (hs : T ≤ s) :
      c.splitChart (F s x) = MorseHandle.descentFlow (s - t) (c.splitChart (F t x)) :=
    morse_coordinates_of_actual_trajectory c hV F hF x isPreconnected_Ici
      (fun u hu => (hT u hu).1) (fun u hu => (hT u hu).2) ht hs
  refine ⟨T, fun t ht => (hT t ht).1, ?_, hformula⟩
  intro t ht
  have hnorm : Tendsto (fun s => ‖(c.splitChart (F s x)).1‖) atTop (𝓝 0) := by
    simpa only [comp_def, Prod.fst_zero, norm_zero] using (continuous_fst.norm.tendsto
      (0 : c.NegativeCoordinates × c.PositiveCoordinates)).comp hcoord
  have hbound : ∀ᶠ s in atTop, ‖(c.splitChart (F t x)).1‖ ≤ ‖(c.splitChart (F s x)).1‖ := by
    filter_upwards [eventually_ge_atTop T, eventually_ge_atTop t] with s hs hst
    rw [hformula t ht s hs]
    exact MorseHandle.norm_fst_le_descentFlow (sub_nonneg.mpr hst) _
  exact norm_eq_zero.mp (le_antisymm (ge_of_tendsto hnorm hbound) (norm_nonneg _))

open Classical in
/-- The actual outgoing tail is entirely in the negative Morse block. -/
theorem exists_outgoing_morse_tail (c : SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (x : M) (hlim : Tendsto (fun t => F t x) atBot (𝓝 p))
    (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) :
    ∃ T : ℝ,
      (∀ t ≤ T, F t x ∈ c.splitChart.source) ∧
      (∀ t ≤ T, (c.splitChart (F t x)).2 = 0) ∧
      ∀ t ≤ T, ∀ s ≤ T, c.splitChart (F s x) =
        MorseHandle.descentFlow (s - t) (c.splitChart (F t x)) := by
  obtain ⟨hcoord, htail⟩ := morse_endpoint_tail_data c F x hlim heq
  obtain ⟨T, hT⟩ := eventually_atBot.mp htail
  have hformula (t : ℝ) (ht : t ≤ T) (s : ℝ) (hs : s ≤ T) :
      c.splitChart (F s x) = MorseHandle.descentFlow (s - t) (c.splitChart (F t x)) :=
    morse_coordinates_of_actual_trajectory c hV F hF x isPreconnected_Iic
      (fun u hu => (hT u hu).1) (fun u hu => (hT u hu).2) ht hs
  refine ⟨T, fun t ht => (hT t ht).1, ?_, hformula⟩
  intro t ht
  have hnorm : Tendsto (fun s => ‖(c.splitChart (F s x)).2‖) atBot (𝓝 0) := by
    simpa only [comp_def, Prod.snd_zero, norm_zero] using (continuous_snd.norm.tendsto
      (0 : c.NegativeCoordinates × c.PositiveCoordinates)).comp hcoord
  have hbound : ∀ᶠ s in atBot, ‖(c.splitChart (F t x)).2‖ ≤ ‖(c.splitChart (F s x)).2‖ := by
    filter_upwards [eventually_le_atBot T, eventually_le_atBot t] with s hs hst
    rw [hformula t ht s hs, MorseHandle.norm_descentFlow_snd]
    exact le_mul_of_one_le_left (norm_nonneg _)
      (Real.one_le_exp_iff.mpr (by linarith))
  exact norm_eq_zero.mp (le_antisymm (ge_of_tendsto hnorm hbound) (norm_nonneg _))

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
