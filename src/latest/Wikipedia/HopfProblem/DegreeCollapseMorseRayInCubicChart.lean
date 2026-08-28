import Wikipedia.HopfProblem.DegreeCollapseControlledMorseEndpointCharts

/-!
# Recovering the regular cubic axis from actual aligned Morse-ray points

The exact coordinate equation and the constructed positive denominator
domain imply that an actual native point on the correct signed linear ray
belongs to the regular cubic axis. The explicit linear flow retains that
ray with its positive exponential scalar multiplier.
-/

noncomputable section

open Set Function Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {m : ℕ} {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The outgoing aligned ray has the exact positive exponential coordinate. -/
theorem descentFlow_outgoing_aligned_ray
    (L : Model m ≃L[ℝ] (N × P)) {r : ℝ} {v : N}
    (hL : L (r, 0) = (v, 0)) (t : ℝ) :
    MorseHandle.descentFlow t (L (r, 0)) = L (r * Real.exp t, 0) := by
  have he : (r * Real.exp t, (0 : Fin m → ℝ)) = Real.exp t • (r, 0) := by
    apply Prod.ext
    · change r * Real.exp t = Real.exp t * r
      ring
    · simp
  rw [he, L.map_smul, hL]
  change (Real.exp t • v, Real.exp (-t) • (0 : P)) =
    (Real.exp t • v, Real.exp t • (0 : P))
  simp

/-- The incoming aligned ray has the exact negative exponential coordinate. -/
theorem descentFlow_incoming_aligned_ray
    (L : Model m ≃L[ℝ] (N × P)) {r : ℝ} {v : P}
    (hL : L (-r, 0) = (0, v)) (t : ℝ) :
    MorseHandle.descentFlow t (L (-r, 0)) = L (-r * Real.exp (-t), 0) := by
  have he : (-r * Real.exp (-t), (0 : Fin m → ℝ)) = Real.exp (-t) • (-r, 0) := by
    apply Prod.ext
    · change -r * Real.exp (-t) = Real.exp (-t) * -r
      ring
    · simp
  rw [he, L.map_smul, hL]
  change (Real.exp t • (0 : N), Real.exp (-t) • v) =
    (Real.exp (-t) • (0 : N), Real.exp (-t) • v)
  simp

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- An actual native point on the correctly signed Morse ray lies on the
regular cubic axis, with membership in the genuine chart source proved. -/
theorem cubic_axis_of_aligned_morse_ray
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (C : M → N × P) (L : Model m ≃L[ℝ] (N × P))
    {a : ℝ} (ha : 0 < a) {e : ℝ} (he : e ^ 2 = 1)
    (hcoord : ∀ p ∈ Φ.source, p.1 ∈ endpointFieldDomain a e ∧
      C (Φ p) = L (endpointFieldProduct a e p))
    {x : M} (hx : x ∈ Φ.target) {r : ℝ}
    (hr : 0 < -e * r) (hCx : C x = L (r, 0)) :
    ∃ s ∈ Ioo (-a) a, (s, (0 : Fin m → ℝ)) ∈ Φ.source ∧
      Φ (s, 0) = x ∧ endpointFieldCoordinate a e s = r := by
  let p := Φ.symm x
  have hp : p ∈ Φ.source := Φ.map_target' hx
  have hpx : Φ p = x := Φ.right_inv' hx
  obtain ⟨hdom, hCp⟩ := hcoord p hp
  rw [hpx, hCx] at hCp
  have hlin : endpointFieldProduct a e p = (r, 0) := L.injective hCp.symm
  have hscalar : endpointFieldCoordinate a e p.1 = r := congrArg Prod.fst hlin
  have hzero : p.2 = 0 := congrArg Prod.snd hlin
  have haxis : p = (p.1, 0) := Prod.ext rfl hzero
  have hdir : 0 < -e * endpointFieldCoordinate a e p.1 := hscalar.symm ▸ hr
  refine ⟨p.1, endpointFieldCoordinate_mem_open_axis ha he hdom hdir, ?_, ?_, hscalar⟩
  · exact haxis ▸ hp
  · exact (congrArg Φ haxis).symm.trans hpx

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
