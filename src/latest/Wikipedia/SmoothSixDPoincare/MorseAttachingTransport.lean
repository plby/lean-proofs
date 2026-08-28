import Wikipedia.SmoothSixDPoincare.SmoothMorseSurgery
import Wikipedia.SmoothSixDPoincare.RegularBandDiffeomorph
import Wikipedia.SmoothSixDPoincare.SphereLinearDiffeomorph

/-!
# Successive Morse attaching spheres in the same actual regular level

An ambient diffeomorphism across a critical-point-free band identifies the
upper level of one Morse surgery with the lower level of the next. Pulling
back the latter's actual attaching sphere preserves smoothness, its closed
embedding, and its injective native differential. The parametrization by a
standard sphere is a genuine sphere diffeomorphism, not a change of image.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {p q : M} (d : MorseSurgeryData E f p) (d' : MorseSurgeryData E f q)

open Classical in
/-- The next actual attaching sphere, pulled back to the preceding upper level. -/
def transportedAttachingSphere (n : ℕ)
    [Fact (Module.finrank ℝ d'.chart.NegativeCoordinates = n + 1)]
    (e : d.UpperLevel ≃ₜ d'.LowerLevel) : C(Hemisphere.Sphere n, d.UpperLevel) :=
  ⟨fun x => e.symm (d'.surgery.attachingSphere
      (SphereCoordinates.standardParametrization d'.chart.NegativeCoordinates n x)),
    e.symm.continuous.comp (d'.surgery.attachingSphere.continuous.comp
      (SphereCoordinates.standardParametrization d'.chart.NegativeCoordinates n).continuous)⟩

open Classical in
theorem transportedAttachingSphere_apply (n : ℕ)
    [Fact (Module.finrank ℝ d'.chart.NegativeCoordinates = n + 1)]
    (e : d.UpperLevel ≃ₜ d'.LowerLevel) (x : Hemisphere.Sphere n) :
    e (d.transportedAttachingSphere d' n e x) = d'.surgery.attachingSphere
      (SphereCoordinates.standardParametrization d'.chart.NegativeCoordinates n x) :=
  e.apply_symm_apply _

open Classical in
/-- Reparametrization does not change the original attaching image. -/
theorem range_transportedAttachingSphere (n : ℕ)
    [Fact (Module.finrank ℝ d'.chart.NegativeCoordinates = n + 1)]
    (e : d.UpperLevel ≃ₜ d'.LowerLevel) :
    range (d.transportedAttachingSphere d' n e) = e ⁻¹' range d'.surgery.attachingSphere := by
  let s := SphereCoordinates.standardParametrization d'.chart.NegativeCoordinates n
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨s x, (d.transportedAttachingSphere_apply d' n e x).symm⟩
  · rintro ⟨z, hz⟩
    obtain ⟨x, hx⟩ := s.surjective z
    refine ⟨x, e.injective ?_⟩
    rw [d.transportedAttachingSphere_apply d' n e]
    exact (congrArg d'.surgery.attachingSphere hx).trans hz

open Classical in
theorem transportedAttachingSphere_isClosedEmbedding [T2Space M] (n : ℕ)
    [Fact (Module.finrank ℝ d'.chart.NegativeCoordinates = n + 1)]
    (e : d.UpperLevel ≃ₜ d'.LowerLevel) :
    IsClosedEmbedding (d.transportedAttachingSphere d' n e) := by
  apply (d.transportedAttachingSphere d' n e).continuous.isClosedEmbedding
  exact e.symm.injective.comp (d'.attaching_isClosedEmbedding.injective.comp
    (SphereCoordinates.standardParametrization d'.chart.NegativeCoordinates n).injective)

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

open Classical in
theorem transportedAttachingSphere_smooth (n : ℕ)
    [Fact (Module.finrank ℝ d'.chart.NegativeCoordinates = n + 1)] :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI := RegularLevel.chartedSpace hf d'.lower_regular
    ∀ e : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        d.UpperLevel d'.LowerLevel ∞,
      ContMDiff (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) ∞
        (d.transportedAttachingSphere d' n e.toHomeomorph) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ := RegularLevel.chartedSpace hf d'.lower_regular
  intro e
  exact e.symm.contMDiff.comp ((d'.attaching_smooth hf n).comp
    (SphereCoordinates.standardParametrization d'.chart.NegativeCoordinates n).contMDiff)

open Classical in
theorem transportedAttachingSphere_derivative_injective (n : ℕ)
    [Fact (Module.finrank ℝ d'.chart.NegativeCoordinates = n + 1)] :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI := RegularLevel.chartedSpace hf d'.lower_regular
    ∀ (e : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        d.UpperLevel d'.LowerLevel ∞) (x : Hemisphere.Sphere n),
      Injective (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E)
        (d.transportedAttachingSphere d' n e.toHomeomorph) x) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ := RegularLevel.chartedSpace hf d'.lower_regular
  intro e x
  let s := SphereCoordinates.standardParametrization d'.chart.NegativeCoordinates n
  have hs := s.mdifferentiable (by simp)
  have ha := (d'.attaching_smooth hf n).mdifferentiable (by simp)
  have he := e.symm.mdifferentiable (by simp)
  have hiE := (e.symm.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv_injective
    (x := d'.surgery.attachingSphere (s x)) (by trivial)
  have hiS := (s.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv_injective
    (x := x) (by trivial)
  change Injective (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E)
    (e.symm ∘ (d'.surgery.attachingSphere ∘ s)) x)
  rw [mfderiv_comp x (he _) ((ha _).comp x (hs x)),
    mfderiv_comp x (ha _) (hs x)]
  exact hiE.comp ((d'.attaching_derivative_injective hf n (s x)).comp hiS)

variable [T2Space M] [CompactSpace M]

/-- The identification between consecutive surgery levels comes from an actual ambient
diffeomorphism carrying the whole original sublevel sets onto each other. -/
theorem exists_smoothBandBridge
    (hgap : f p + d.radius ^ 2 ≤ f q - d'.radius ^ 2)
    (hband : ∀ x, f x ∈ Icc (f p + d.radius ^ 2) (f q - d'.radius ^ 2) →
      x ∉ criticalPoints E f) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI := RegularLevel.chartedSpace hf d'.lower_regular
    ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      ∃ e : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
          d.UpperLevel d'.LowerLevel ∞,
        D '' {x : M | f x ≤ f p + d.radius ^ 2} = {x : M | f x ≤ f q - d'.radius ^ 2} ∧
        ∀ x : d.UpperLevel, (e x : M) = D x := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ := RegularLevel.chartedSpace hf d'.lower_regular
  obtain ⟨D, hlevel, hsublevel⟩ := RegularLevel.exists_ambient_regularBand_transport hf hgap hband
  obtain ⟨e, he⟩ := RegularLevel.exists_levelDiffeomorph_of_ambient hf
    d.upper_regular d'.lower_regular D hlevel
  exact ⟨D, e, hsublevel, he⟩

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
