import Wikipedia.SmoothSixDPoincare.MorseCollapseIntersectionSigns

/-!
# Smoothness and regularity of the actual finite collapse at belt crossings

The finite representative is smooth near every belt crossing. Native
transversality makes its actual derivative invertible, without replacing
the original attaching map or normal projection.
-/

noncomputable section

open Set Function Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M} (d : MorseSurgeryData E f p)
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

open Classical in
theorem contMDiffAt_collapseNormal_comp (m : ℕ)
    (g : Hemisphere.Sphere m → d.UpperLevel) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 m) 𝓘(ℝ, RegularLevel.Model E) ∞ g)
      (x : Hemisphere.Sphere m), g x ∈ range d.surgery.beltSphere →
      ContMDiffAt (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) ∞ (d.collapseNormal ∘ g) x := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  intro hg x hx
  obtain ⟨v, hv⟩ := hx
  have hn : ContMDiffAt (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) ∞ (d.beltNormal ∘ g) x := by
    have hnormal := (d.contMDiffOn_beltNormal hf).contMDiffAt
      (d.isOpen_beltNormalDomain.mem_nhds (d.belt_mem_normalDomain v))
    rw [hv] at hnormal
    exact hnormal.comp x hg.contMDiffAt
  have hzero : (d.beltNormal ∘ g) x = 0 := by
    change d.beltNormal (g x) = 0
    rw [← hv, d.beltNormal_belt]
  have hq : ContDiffAt ℝ ∞ (MorseHandle.beltCollapseCoordinate
      (N := d.chart.NegativeCoordinates)) (d.radius⁻¹ • (d.beltNormal ∘ g) x) := by
    rw [hzero, smul_zero]
    exact MorseHandle.contDiffOn_beltCollapseCoordinate.contDiffAt
      (isOpen_ball.mem_nhds (by simp))
  have hs : ContDiffAt ℝ ∞
      (fun u : d.chart.NegativeCoordinates =>
        MorseHandle.beltCollapseCoordinate (d.radius⁻¹ • u)) ((d.beltNormal ∘ g) x) :=
    hq.comp _ (contDiff_id.const_smul d.radius⁻¹).contDiffAt
  exact hs.contMDiffAt.comp x hn

open Classical in
theorem isInvertible_collapseNormal_comp_of_transverse (n m : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m)
    (g : Hemisphere.Sphere m → d.UpperLevel) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 m) 𝓘(ℝ, RegularLevel.Model E) ∞ g)
      (_ht : ∀ x y, NativeTransversality.At (𝓡 m) (𝓡 n) 𝓘(ℝ, RegularLevel.Model E)
        g d.surgery.beltSphere x y)
      (x : Hemisphere.Sphere m), x ∈ d.beltIntersectionPoints m g →
      (mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.collapseNormal ∘ g) x).IsInvertible := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  intro hg ht x hx
  obtain ⟨v, hv⟩ := hx
  have hA := d.bijective_beltNormal_comp_of_transverse hf n m hdim g hg x v hv (ht x v hv)
  let A : EuclideanSpace ℝ (Fin m) →L[ℝ] d.chart.NegativeCoordinates :=
    mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ g) x
  have hAi : A.IsInvertible :=
    ⟨(LinearEquiv.ofBijective A.toLinearMap hA).toContinuousLinearEquiv, rfl⟩
  rw [d.mfderiv_collapseNormal_comp m g x (mdifferentiableAt_of_isInvertible_mfderiv hAi)
    ⟨v, hv⟩]
  exact SphereNormalCoordinates.normalDerivative_smul_isInvertible A hAi _
    (MorseHandle.scaled_beltCollapseCoordinate_factor_pos d.radius d.radius_pos).ne'

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
