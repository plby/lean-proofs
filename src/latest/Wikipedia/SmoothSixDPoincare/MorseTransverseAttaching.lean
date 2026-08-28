import Wikipedia.SmoothSixDPoincare.GlobalAmbientTransversality
import Wikipedia.SmoothSixDPoincare.MorseAttachingTransport
import Wikipedia.SmoothSixDPoincare.FiniteTransverseIntersections

/-!
# The actual index-three attaching sphere transverse to the index-two belt

The original regular band supplies an ambient sublevel identification.
Its restriction transports the next actual attaching sphere to the previous
upper level. A constructed ambient isotopy of that native level makes the
sphere transverse to the actual belt, retaining smooth embedding and native
immersion. The intersection set is consequently finite, not assumed finite.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  {f : M → ℝ} {p q : M} (d : MorseSurgeryData E f p) (d' : MorseSurgeryData E f q)
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

open Classical in
/-- The smooth transverse embedded attaching sphere is constructed from the original Morse data.
The ambient band map, its original sublevel identity, and the subsequent isotopy are retained. -/
theorem exists_transverse_attachingSphere (hdim : Module.finrank ℝ E = 6)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    (hindex' : Module.finrank ℝ d'.chart.NegativeCoordinates = 3)
    (hgap : f p + d.radius ^ 2 ≤ f q - d'.radius ^ 2)
    (hband : ∀ x, f x ∈ Icc (f p + d.radius ^ 2) (f q - d'.radius ^ 2) →
      x ∉ criticalPoints E f) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI := RegularLevel.chartedSpace hf d'.lower_regular
    letI : Fact (Module.finrank ℝ d.chart.PositiveCoordinates = 3 + 1) :=
      ⟨by have hh := d.chart.finrank_negative_add_positive; omega⟩
    letI : Fact (Module.finrank ℝ d'.chart.NegativeCoordinates = 2 + 1) := ⟨hindex'⟩
    ∃ D₀ : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      ∃ b : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
          d.UpperLevel d'.LowerLevel ∞,
        D₀ '' {x : M | f x ≤ f p + d.radius ^ 2} = {x : M | f x ≤ f q - d'.radius ^ 2} ∧
        (∀ x : d.UpperLevel, (b x : M) = D₀ x) ∧
        ∃ e : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
            d.UpperLevel d.UpperLevel ∞,
          ∃ g : C(Hemisphere.Sphere 2, d.UpperLevel),
            SupportedDiffeomorph.IsotopicToIdentity e ∧
            (∀ x, g x = e (d.transportedAttachingSphere d' 2 b.toHomeomorph x)) ∧
            ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ g ∧ IsClosedEmbedding g ∧
            (∀ x, Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) g x)) ∧
            (∀ x y, NativeTransversality.At (𝓡 2) (𝓡 3) 𝓘(ℝ, RegularLevel.Model E)
              g d.surgery.beltSphere x y) ∧
            (range g ∩ range d.surgery.beltSphere).Finite := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ := RegularLevel.chartedSpace hf d'.lower_regular
  let _ := RegularLevel.isManifold hf d.upper_regular
  let _ := RegularLevel.isManifold hf d'.lower_regular
  let _ : CompactSpace d.UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  have hpos : Module.finrank ℝ d.chart.PositiveCoordinates = 3 + 1 := by
    have hh := d.chart.finrank_negative_add_positive
    omega
  let _ : Fact (Module.finrank ℝ d.chart.PositiveCoordinates = 3 + 1) := ⟨hpos⟩
  let _ : Fact (Module.finrank ℝ d'.chart.NegativeCoordinates = 2 + 1) := ⟨hindex'⟩
  obtain ⟨D₀, b, hsublevel, hb⟩ := d.exists_smoothBandBridge d' hf hgap hband
  let f₀ := d.transportedAttachingSphere d' 2 b.toHomeomorph
  have hf₀ : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ f₀ :=
    d.transportedAttachingSphere_smooth d' hf 2 b
  have hclosed₀ : IsClosedEmbedding f₀ := d.transportedAttachingSphere_isClosedEmbedding d' 2 _
  have hi₀ : ∀ x, Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) f₀ x) :=
    d.transportedAttachingSphere_derivative_injective d' hf 2 b
  have hbelt := d.belt_smooth hf 3
  have hdim' : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) +
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = Module.finrank ℝ (RegularLevel.Model E) := by
    simp [RegularLevel.Model, hdim]
  obtain ⟨e, hisotopy, ht⟩ :=
    NativeTransversality.exists_ambient_transverse_diffeomorph hf₀ hbelt hdim'
  let g : C(Hemisphere.Sphere 2, d.UpperLevel) := ⟨e ∘ f₀, e.continuous.comp f₀.continuous⟩
  have hg : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ g := e.contMDiff.comp hf₀
  have hclosed : IsClosedEmbedding g := g.continuous.isClosedEmbedding
    (e.injective.comp hclosed₀.injective)
  have hi : ∀ x, Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) g x) := by
    intro x
    change Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) (e ∘ f₀) x)
    rw [mfderiv_comp x (e.mdifferentiable (by simp) _) (hf₀.mdifferentiable (by simp) x)]
    exact ((e.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv_injective
      (by trivial)).comp (hi₀ x)
  refine ⟨D₀, b, hsublevel, hb, e, g, hisotopy, fun _ => rfl, hg, hclosed, hi, ht, ?_⟩
  exact finite_transverse_intersections hg hbelt hclosed.injective
    d.belt_isClosedEmbedding.injective hdim' (fun x y hxy => ht x y hxy)

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
