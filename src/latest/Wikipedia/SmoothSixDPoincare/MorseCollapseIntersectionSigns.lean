import Wikipedia.SmoothSixDPoincare.MorseCollapseNormalCoordinates
import Wikipedia.SmoothSixDPoincare.MorseSignedIntersections
import Wikipedia.SmoothSixDPoincare.PositiveNormalScaling

/-!
# The actual collapse has the original signed belt crossings

The finite representative of the whole-attachment collapse has, at each
transverse belt crossing, the original normal differential times a fixed
positive scalar. The same outward reference therefore gives exactly the
original intersection sign. This is a local comparison, not yet the global
homology-degree formula for the sum of these signs.
-/

noncomputable section

open Set Function Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

open Classical in
/-- Differential of the actual finite collapse coordinate at a belt crossing. -/
theorem mfderiv_collapseNormal_comp (m : ℕ)
    (g : Hemisphere.Sphere m → d.UpperLevel) (x : Hemisphere.Sphere m)
    (hg : MDifferentiableAt (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ g) x)
    (hx : g x ∈ range d.surgery.beltSphere) :
    mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.collapseNormal ∘ g) x =
      ((Real.sqrt 2)⁻¹ * d.radius⁻¹) •
        mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ g) x := by
  obtain ⟨v, hv⟩ := hx
  have hzero : (d.beltNormal ∘ g) x = 0 := by
    change d.beltNormal (g x) = 0
    rw [← hv, d.beltNormal_belt]
  have hout : HasFDerivAt
      (fun u : d.chart.NegativeCoordinates =>
        MorseHandle.beltCollapseCoordinate (d.radius⁻¹ • u))
      (((Real.sqrt 2)⁻¹ * d.radius⁻¹) • ContinuousLinearMap.id ℝ _)
      ((d.beltNormal ∘ g) x) := by
    rw [hzero]
    exact MorseHandle.hasFDerivAt_scaled_beltCollapseCoordinate_zero d.radius
  have h := (hout.hasMFDerivAt.comp x hg.hasMFDerivAt).mfderiv
  change mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.collapseNormal ∘ g) x = _ at h
  apply h.trans
  apply ContinuousLinearMap.ext
  intro u
  rfl

open Classical in
theorem collapseNormal_comp_sign (m : ℕ)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient (m + 1))
    (g : Hemisphere.Sphere m → d.UpperLevel) (x : Hemisphere.Sphere m)
    (hA : (mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates)
      (d.beltNormal ∘ g) x).IsInvertible)
    (hx : g x ∈ range d.surgery.beltSphere) :
    letI : Fact (Module.finrank ℝ (Hemisphere.Ambient (m + 1)) = m + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    SignType.sign (SphereNormalCoordinates.normalJacobian j x
      (mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.collapseNormal ∘ g) x)) =
        d.beltIntersectionSign m j g x := by
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient (m + 1)) = m + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  rw [d.mfderiv_collapseNormal_comp m g x (mdifferentiableAt_of_isInvertible_mfderiv hA) hx]
  exact SphereNormalCoordinates.sign_normalJacobian_smul_pos j x _ hA _
    (MorseHandle.scaled_beltCollapseCoordinate_factor_pos d.radius d.radius_pos)

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

open Classical in
/-- Native transversality supplies every regularity hypothesis of the sign comparison. -/
theorem collapseNormal_comp_sign_of_transverse (n m : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient (m + 1))
    (g : Hemisphere.Sphere m → d.UpperLevel) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI : Fact (Module.finrank ℝ (Hemisphere.Ambient (m + 1)) = m + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    ∀ (_hg : ContMDiff (𝓡 m) 𝓘(ℝ, RegularLevel.Model E) ∞ g)
      (_ht : ∀ x y, NativeTransversality.At (𝓡 m) (𝓡 n) 𝓘(ℝ, RegularLevel.Model E)
        g d.surgery.beltSphere x y)
      (x : Hemisphere.Sphere m), x ∈ d.beltIntersectionPoints m g →
      SignType.sign (SphereNormalCoordinates.normalJacobian j x
        (mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.collapseNormal ∘ g) x)) =
          d.beltIntersectionSign m j g x := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient (m + 1)) = m + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  intro hg ht x hx
  obtain ⟨v, hv⟩ := hx
  have hA := d.bijective_beltNormal_comp_of_transverse hf n m hdim g hg x v hv (ht x v hv)
  let A : EuclideanSpace ℝ (Fin m) →L[ℝ] d.chart.NegativeCoordinates :=
    mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ g) x
  have hAi : A.IsInvertible :=
    ⟨(LinearEquiv.ofBijective A.toLinearMap hA).toContinuousLinearEquiv, rfl⟩
  exact d.collapseNormal_comp_sign m j g x hAi ⟨v, hv⟩

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
open Classical in
/-- Along any continuous attaching map the same finite representative is a local germ. -/
theorem levelCollapse_comp_eventuallyEq [T2Space M] (hf : Continuous f) (m : ℕ)
    (g : Hemisphere.Sphere m → d.UpperLevel) (x : Hemisphere.Sphere m)
    (hg : ContinuousAt g x) (hx : g x ∈ range d.surgery.beltSphere) :
    (fun y => d.levelCollapseMap hf (g y)) =ᶠ[𝓝 x]
      (fun y => (d.collapseNormal (g y) : OnePoint d.chart.NegativeCoordinates)) := by
  obtain ⟨v, hv⟩ := hx
  have h := d.levelCollapse_eventuallyEq_belt hf v
  rw [hv] at h
  exact h.comp_tendsto hg

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
