import Wikipedia.HopfProblem.DegreeCollapseArbitraryGapCylinder
import Wikipedia.HopfProblem.DegreeCollapseConnectionSections
import Wikipedia.HopfProblem.DegreeCollapseClockNormalizedBasins

/-!
# Constructing the normalized cylinder for an actual isolated connection

The endpoint heights and isolation choose a regular inner band. The
actual orbit meets its middle level. Positive normalization constructs
the full finite-coordinate cylinder and preserves both limits, the unique
connection, all critical germs, and descent of the original function.
Neither a regular band nor a chosen level point is an input.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowTimeChange

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {m : ℕ}

theorem exists_normalized_connection_cylinder {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = m + 1)
    (V : (y : M) → TangentSpace 𝓘(ℝ, E) y)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun y => (⟨y, V y⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hzero : ∀ y ∈ criticalPoints E f, V y = 0)
    (hdesc : ∀ y, y ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) f y (V y) < 0)
    (F : Flow ℝ M) (hF : ∀ y, IsMIntegralCurve (fun t => F t y) V)
    {p q x : M} (hpq : f p < f q)
    {c d : ℝ} (hc : c < f p) (hd : f q < d)
    (hpair : ∀ y ∈ criticalPoints E f, f y ∈ Icc c d → y = p ∨ y = q)
    (hp : Tendsto (fun t => F t x) atTop (𝓝 p))
    (hq : Tendsto (fun t => F t x) atBot (𝓝 q))
    (hunique : ∀ y, Tendsto (fun t => F t y) atBot (𝓝 q) →
      Tendsto (fun t => F t y) atTop (𝓝 p) → ∃ t, F t x = y) :
    ∃ (x₀ : M) (r b : ℝ) (W : (y : M) → TangentSpace 𝓘(ℝ, E) y) (G : Flow ℝ M)
      (U : Set (Fin m → ℝ))
      (A : PartialDiffeomorph 𝓘(ℝ, (Fin m → ℝ) × ℝ) 𝓘(ℝ, E) ((Fin m → ℝ) × ℝ) M ∞),
      x₀ ≠ p ∧ x₀ ≠ q ∧ 0 < r ∧
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
        (fun y => (⟨y, W y⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      (∀ y, IsMIntegralCurve (fun t => G t y) W) ∧
      (∀ y ∈ criticalPoints E f, W y = 0) ∧
      (∀ y, y ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) f y (W y) < 0) ∧
      (∀ y ∈ criticalPoints E f, ∀ᶠ z in 𝓝 y, W z = V z) ∧
      (∀ y, Antitone (fun t => f (G t y))) ∧
      Tendsto (fun t => G t x₀) atTop (𝓝 p) ∧
      Tendsto (fun t => G t x₀) atBot (𝓝 q) ∧
      (∀ y, Tendsto (fun t => G t y) atBot (𝓝 q) →
        Tendsto (fun t => G t y) atTop (𝓝 p) → ∃ t, G t x₀ = y) ∧
      IsOpen U ∧ (0 : Fin m → ℝ) ∈ U ∧ A.source = U ×ˢ univ ∧
      (∀ t : ℝ, A (0, t) = G t x₀) ∧
      (∀ z ∈ A.source, z.2 ∈ Icc (0 : ℝ) 1 → f (A z) = b - r * z.2) ∧
      (∀ y ∈ A.target, W y = FlowConstruction.partialChartField A.symm
        (fun _ : (Fin m → ℝ) × ℝ => (0, 1)) y) ∧
      (∀ y, range (fun t => G t y) = range (fun t => F t y) ∧
        (∀ z, Tendsto (fun t => G t y) atTop (𝓝 z) ↔ Tendsto (fun t => F t y) atTop (𝓝 z)) ∧
        ∀ z, Tendsto (fun t => G t y) atBot (𝓝 z) ↔ Tendsto (fun t => F t y) atBot (𝓝 z)) ∧
      ∃ t, F t x = x₀ := by
  let b : ℝ := (f p + f q) / 2
  let lo : ℝ := (f p + b) / 2
  let hi : ℝ := (b + f q) / 2
  have hpb : f p < b := by dsimp [b]; linarith
  have hbq : b < f q := by dsimp [b]; linarith
  have hplo : f p < lo := by dsimp [lo]; linarith
  have hlob : lo < b := by dsimp [lo]; linarith
  have hbhi : b < hi := by dsimp [hi]; linarith
  have hhiq : hi < f q := by dsimp [hi]; linarith
  have hband : ∀ y, f y ∈ Icc lo hi → y ∉ criticalPoints E f := by
    intro y hy hcrit
    have houter : f y ∈ Icc c d := ⟨by linarith [hy.1], by linarith [hy.2]⟩
    rcases hpair y hcrit houter with he | he
    · rw [he] at hy
      exact (not_le_of_gt hplo) hy.1
    · rw [he] at hy
      exact (not_le_of_gt hhiq) hy.2
  obtain ⟨t₀, ht₀⟩ := FlowCancellation.exists_level_crossing_of_endpoint_limits
    F hf.continuous hq hp hbq hpb
  let x₀ := F t₀ x
  have hxp : x₀ ≠ p := by
    intro hh
    have hv : f p = b := hh ▸ ht₀
    exact hpb.ne hv
  have hxq : x₀ ≠ q := by
    intro hh
    have hv : f q = b := hh ▸ ht₀
    exact hbq.ne hv.symm
  have hp₀ : Tendsto (fun t => F t x₀) atTop (𝓝 p) :=
    (MorseCancellation.flow_time_atTop_limit_iff F t₀ x p).mpr hp
  have hq₀ : Tendsto (fun t => F t x₀) atBot (𝓝 q) :=
    (MorseCancellation.flow_time_atBot_limit_iff F t₀ x q).mpr hq
  have hunique₀ : ∀ y, Tendsto (fun t => F t y) atBot (𝓝 q) →
      Tendsto (fun t => F t y) atTop (𝓝 p) → ∃ t, F t x₀ = y := by
    intro y hyq hyp
    obtain ⟨t, ht⟩ := hunique y hyq hyp
    refine ⟨t - t₀, ?_⟩
    change F (t - t₀) (F t₀ x) = y
    rw [← F.map_add, sub_add_cancel]
    exact ht
  obtain ⟨r, W, G, U, A, hr, hW, hG, hWzero, hWdesc, hgerms, hgeometry,
      hU, h0U, hsource, haxis, hheight, hfield⟩ :=
    exists_arbitrary_gap_flow_cylinder hf hdim hV hdesc F hF hlob hbhi hband ht₀
  have hzeros : ∀ y ∈ criticalPoints E f, W y = 0 :=
    fun y hy => (hWzero y).mpr (hzero y hy)
  have huniqueG : ∀ y, Tendsto (fun t => G t y) atBot (𝓝 q) →
      Tendsto (fun t => G t y) atTop (𝓝 p) → ∃ t, G t x₀ = y := by
    intro y hyq hyp
    have hh : y ∈ range (fun t => F t x₀) :=
      hunique₀ y ((hgeometry y).2.2 q |>.mp hyq) ((hgeometry y).2.1 p |>.mp hyp)
    rw [← (hgeometry x₀).1] at hh
    exact hh
  exact ⟨x₀, r, b, W, G, U, A, hxp, hxq, hr, hW, hG, hzeros, hWdesc, hgerms,
    FlowConstruction.antitone_flow_height hf G hG hzeros hWdesc,
    (hgeometry x₀).2.1 p |>.mpr hp₀, (hgeometry x₀).2.2 q |>.mpr hq₀,
    huniqueG, hU, h0U, hsource, haxis, hheight, hfield, hgeometry, t₀, rfl⟩

end Wikipedia.HopfProblem.DegreeCollapse.FlowTimeChange
