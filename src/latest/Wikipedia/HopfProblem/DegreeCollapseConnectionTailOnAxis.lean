import Wikipedia.HopfProblem.DegreeCollapseMorseRayInCubicChart
import Wikipedia.HopfProblem.DegreeCollapseMorseEndpointTails

/-!
# Actual connection tails on the regular cubic endpoint axis

The endpoint limit puts the whole far tail inside the constructed native
endpoint chart. Its exact Morse trajectory and aligned reference point
give a signed exponential ray coordinate. The domain-controlled inverse
then places every point of that tail on the regular cubic axis.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}

open ManifoldMorse

open Classical in
/-- Every sufficiently late point of the actual incoming orbit is on the
genuine regular axis of the aligned endpoint chart. -/
theorem incoming_tail_on_cubic_axis (c : SignedMorseChart (E := E) f p)
    {m : ℕ} (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates))
    (hcenter : (1 / 2, (0 : Fin m → ℝ)) ∈ Φ.source)
    (hvalue : Φ (1 / 2, 0) = p)
    (hcoord : ∀ q ∈ Φ.source, q.1 ∈ endpointFieldDomain (1 / 2) 1 ∧
      c.splitChart (Φ q) = L (endpointFieldProduct (1 / 2) 1 q))
    (F : Flow ℝ M) (x : M) (hlim : Tendsto (fun t => F t x) atTop (𝓝 p))
    {T r : ℝ} (hr : 0 < r) {v : c.PositiveCoordinates}
    (hL : L (-r, 0) = (0, v)) (hbase : c.splitChart (F T x) = (0, v))
    (hmodel : ∀ t ≥ T, c.splitChart (F t x) =
      MorseHandle.descentFlow (t - T) (c.splitChart (F T x))) :
    ∀ᶠ t in atTop, ∃ s ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2),
      (s, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (s, 0) = F t x := by
  have hp : p ∈ Φ.target := hvalue ▸ Φ.map_source' hcenter
  have htarget : ∀ᶠ t in atTop, F t x ∈ Φ.target :=
    hlim.eventually (Φ.open_target.mem_nhds hp)
  filter_upwards [htarget, eventually_ge_atTop T] with t ht hT
  have hline : c.splitChart (F t x) = L (-r * Real.exp (-(t - T)), 0) := by
    rw [hmodel t hT, hbase, ← hL]
    exact descentFlow_incoming_aligned_ray L hL (t - T)
  have hdir : 0 < -(1 : ℝ) * (-r * Real.exp (-(t - T))) := by
    nlinarith [Real.exp_pos (-(t - T))]
  obtain ⟨s, hs, hsource, hpoint, _⟩ := cubic_axis_of_aligned_morse_ray Φ c.splitChart L
    (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num : (1 : ℝ) ^ 2 = 1)
    hcoord ht hdir hline
  exact ⟨s, hs, hsource, hpoint⟩

open Classical in
/-- Every sufficiently early point of the actual outgoing orbit is on the
genuine regular axis of the aligned endpoint chart. -/
theorem outgoing_tail_on_cubic_axis (c : SignedMorseChart (E := E) f p)
    {m : ℕ} (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates))
    (hcenter : (-(1 / 2 : ℝ), (0 : Fin m → ℝ)) ∈ Φ.source)
    (hvalue : Φ (-(1 / 2 : ℝ), 0) = p)
    (hcoord : ∀ q ∈ Φ.source, q.1 ∈ endpointFieldDomain (1 / 2) (-1) ∧
      c.splitChart (Φ q) = L (endpointFieldProduct (1 / 2) (-1) q))
    (F : Flow ℝ M) (x : M) (hlim : Tendsto (fun t => F t x) atBot (𝓝 p))
    {T r : ℝ} (hr : 0 < r) {v : c.NegativeCoordinates}
    (hL : L (r, 0) = (v, 0)) (hbase : c.splitChart (F T x) = (v, 0))
    (hmodel : ∀ t ≤ T, c.splitChart (F t x) =
      MorseHandle.descentFlow (t - T) (c.splitChart (F T x))) :
    ∀ᶠ t in atBot, ∃ s ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2),
      (s, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (s, 0) = F t x := by
  have hp : p ∈ Φ.target := hvalue ▸ Φ.map_source' hcenter
  have htarget : ∀ᶠ t in atBot, F t x ∈ Φ.target :=
    hlim.eventually (Φ.open_target.mem_nhds hp)
  filter_upwards [htarget, eventually_le_atBot T] with t ht hT
  have hline : c.splitChart (F t x) = L (r * Real.exp (t - T), 0) := by
    rw [hmodel t hT, hbase, ← hL]
    exact descentFlow_outgoing_aligned_ray L hL (t - T)
  have hdir : 0 < -(-1 : ℝ) * (r * Real.exp (t - T)) := by
    simpa using mul_pos hr (Real.exp_pos (t - T))
  obtain ⟨s, hs, hsource, hpoint, _⟩ := cubic_axis_of_aligned_morse_ray Φ c.splitChart L
    (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num : (-1 : ℝ) ^ 2 = 1)
    hcoord ht hdir hline
  exact ⟨s, hs, hsource, hpoint⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
