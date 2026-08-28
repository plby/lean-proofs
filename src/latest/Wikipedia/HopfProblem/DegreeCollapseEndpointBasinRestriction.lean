import Wikipedia.HopfProblem.DegreeCollapseLinearStablePlanes
import Wikipedia.HopfProblem.DegreeCollapseNativeMorseBasins

/-!
# Restricting actual cubic endpoint charts to exact native basins

The original descending Morse function rules out departure and return
in a constructed Morse block. The actual linear field conjugacy then
identifies that basin with the corresponding signed transverse plane
of the cubic endpoint chart. Both implications hold on the whole
restricted source, not only on trajectories assumed to stay there.
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
/-- Shrinking a genuine endpoint chart still contains the far connection
tail, provided its center and forward coordinate map are retained. -/
theorem endpoint_axis_tail_of_restriction {m : ℕ}
    (Φ Ψ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (hsub : Ψ.source ⊆ Φ.source) (hmap : ∀ z, Ψ z = Φ z)
    {a b c : ℝ} (hc : (c, (0 : Fin m → ℝ)) ∈ Ψ.source)
    (hcenter : Ψ (c, 0) = p) (F : Flow ℝ M) (x : M) {l : Filter ℝ}
    (hlim : Tendsto (fun t => F t x) l (𝓝 p))
    (htail : ∀ᶠ t in l, ∃ s ∈ Ioo a b,
      (s, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (s, 0) = F t x) :
    ∀ᶠ t in l, ∃ s ∈ Ioo a b,
      (s, (0 : Fin m → ℝ)) ∈ Ψ.source ∧ Ψ (s, 0) = F t x := by
  have hp : p ∈ Ψ.target := hcenter ▸ Ψ.map_source' hc
  filter_upwards [htail, hlim.eventually (Ψ.open_target.mem_nhds hp)] with t ht htΨ
  obtain ⟨s, hs, hsΦ, hval⟩ := ht
  have hz : Ψ.symm (F t x) ∈ Ψ.source := Ψ.map_target' htΨ
  have hzval : Ψ (Ψ.symm (F t x)) = F t x := Ψ.right_inv' htΨ
  have heq : Ψ.symm (F t x) = (s, (0 : Fin m → ℝ)) :=
    Φ.toOpenPartialHomeomorph.injOn (hsub hz) hsΦ
      ((hmap _).symm.trans (hzval.trans hval.symm))
  exact ⟨s, hs, heq ▸ hz, (hmap _).trans hval⟩

open Classical in
/-- A constructed restriction of an aligned endpoint chart has the exact
native stable or unstable basin described by its signed transverse plane. -/
theorem exists_cubic_endpoint_basin_restriction (c : SignedMorseChart (E := E) f p)
    (hf : Continuous f) {m : ℕ} (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 1) {e : ℝ}
    (L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates))
    (hL : ∀ z, L (endpointLinearField σ (1 / 2) e z) = MorseHandle.descent (L z))
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x)))
    (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (hc : (e / 2, (0 : Fin m → ℝ)) ∈ Φ.source) (hcenter : Φ (e / 2, 0) = p)
    (hfield : ∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(1 / 2 : ℝ) ^ 2) y)
    (hcoord : ∀ z ∈ Φ.source,
      c.splitChart (Φ z) = L (endpointFieldProduct (1 / 2) e z)) :
    ∃ Ψ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      Ψ.source ⊆ Φ.source ∧ (∀ z, Ψ z = Φ z) ∧
      (e / 2, (0 : Fin m → ℝ)) ∈ Ψ.source ∧ Ψ (e / 2, 0) = p ∧
      Ψ.target ⊆ c.splitChart.source ∧
      (∀ y ∈ Ψ.target, V y = nativeCubicDescent σ Ψ (-(1 / 2 : ℝ) ^ 2) y) ∧
      ∀ z ∈ Ψ.source,
        (e = 1 → (Tendsto (fun t => F t (Ψ z)) atTop (𝓝 p) ↔
          ∀ i, σ i = -1 → z.2 i = 0)) ∧
        (e = -1 → (Tendsto (fun t => F t (Ψ z)) atBot (𝓝 p) ↔
          ∀ i, σ i = 1 → z.2 i = 0)) := by
  obtain ⟨r, hr, _, hbasin⟩ := exists_native_morse_basin_block c hf hV F hF hmono heq
  have hct : ContinuousAt c.splitChart p :=
    c.splitChart.toOpenPartialHomeomorph.continuousAt c.splitChart_mem_source
  have hnear : ∀ᶠ y in 𝓝 p, y ∈ c.splitChart.source ∧
      ‖(c.splitChart y).1‖ < r ∧ ‖(c.splitChart y).2‖ < r := by
    have hB : ball (0 : c.NegativeCoordinates) r ×ˢ
        ball (0 : c.PositiveCoordinates) r ∈ 𝓝 (c.splitChart p) := by
      rw [c.splitChart_center]
      exact (isOpen_ball.prod isOpen_ball).mem_nhds
        ⟨mem_ball_self hr, mem_ball_self hr⟩
    filter_upwards [c.splitChart.open_source.mem_nhds c.splitChart_mem_source,
      hct.eventually hB] with y hy hby
    exact ⟨hy, mem_ball_zero_iff.mp hby.1, mem_ball_zero_iff.mp hby.2⟩
  obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp hnear
  let Ψ := PartialChart.restrictTarget Φ hU
  have hsource : Ψ.source ⊆ Φ.source := fun _ hz => hz.1
  have hΨc : (e / 2, (0 : Fin m → ℝ)) ∈ Ψ.source := by
    change (e / 2, 0) ∈ Φ.source ∧ Φ (e / 2, 0) ∈ U
    exact ⟨hc, hcenter.symm ▸ hpU⟩
  refine ⟨Ψ, hsource, fun _ => rfl, hΨc, hcenter,
    fun y hy => (hUsub hy.2).1, ?_, ?_⟩
  · intro y hy
    exact hfield y hy.1
  · intro z hz
    obtain ⟨hy, hn, hp⟩ := hUsub (Ψ.map_source' hz).2
    have hclass := hbasin (Ψ z) hy hn hp
    have hcz : c.splitChart (Ψ z) = L (endpointFieldProduct (1 / 2) e z) :=
      hcoord z (hsource hz)
    constructor
    · intro he
      subst e
      rw [hclass.1, hcz]
      exact incoming_linear_stable_plane c σ hσ L hL (endpointFieldProduct (1 / 2) 1 z)
    · intro he
      subst e
      rw [hclass.2, hcz]
      exact outgoing_linear_unstable_plane c σ hσ L hL (endpointFieldProduct (1 / 2) (-1) z)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
