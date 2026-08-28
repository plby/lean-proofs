import Wikipedia.SmoothSixDPoincare.MorseSignedWhitneyCancellation

/-!
# A repeatable signed-pair cancellation step on the original Morse level

The actual Whitney move preserves the full map germ at every surviving
crossing. Its endpoint sphere therefore stays smooth, embedded, immersive,
and transverse. Exactly the two selected source points disappear, and all
remaining fixed normal signs are unchanged.
-/

noncomputable section

open Set Function Filter Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  {f : M → ℝ} {p : M} (D : MorseSurgeryData E f p)
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

open Classical in
/-- Construct one actual cancellation step, retaining every hypothesis needed to repeat it. -/
theorem exists_signed_belt_cancellation_step
    (hdim : Module.finrank ℝ E = 6)
    (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    (hnull : ∀ γ : C(Hemisphere.Sphere 1, D.LowerLevel),
      ∃ q, γ.Homotopic (ContinuousMap.const _ q))
    (r : (ℝ × D.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient 3)
    (g : C(Hemisphere.Sphere 2, D.UpperLevel)) :
    letI := RegularLevel.chartedSpace hf D.upper_regular
    letI : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
      ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
    ∀ (_hg : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ g)
      (_hinj : Injective g)
      (_hi : ∀ x, Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) g x))
      (_ht : ∀ x y, NativeTransversality.At (𝓡 2) (𝓡 3) 𝓘(ℝ, RegularLevel.Model E)
        g D.surgery.beltSphere x y)
      (x₀ x₁ : Hemisphere.Sphere 2),
      x₀ ∈ D.beltIntersectionPoints 2 g → x₁ ∈ D.beltIntersectionPoints 2 g →
      D.beltIntersectionSign 2 r g x₀ * D.beltIntersectionSign 2 r g x₁ = -1 →
      ∃ e : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
          D.UpperLevel D.UpperLevel ∞,
        ∃ g' : C(Hemisphere.Sphere 2, D.UpperLevel),
          SupportedDiffeomorph.IsotopicToIdentity e ∧ (∀ x, g' x = e (g x)) ∧
          ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ g' ∧ Injective g' ∧
          (∀ x, Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) g' x)) ∧
          (∀ x y, NativeTransversality.At (𝓡 2) (𝓡 3) 𝓘(ℝ, RegularLevel.Model E)
            g' D.surgery.beltSphere x y) ∧
          D.beltIntersectionPoints 2 g' = D.beltIntersectionPoints 2 g \ {x₀, x₁} ∧
          (∀ x ∈ D.beltIntersectionPoints 2 g',
            (g' : Hemisphere.Sphere 2 → D.UpperLevel) =ᶠ[𝓝 x] g) ∧
          ∀ x ∈ D.beltIntersectionPoints 2 g',
            D.beltIntersectionSign 2 r g' x = D.beltIntersectionSign 2 r g x := by
  let _ := RegularLevel.chartedSpace hf D.upper_regular
  let _ : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient 3) = 2 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  intro hg hinj hi ht x₀ x₁ hx₀ hx₁ hsign
  obtain ⟨K, hK, hdis, A, hA, hA₀, hAt, hfix, hcancel⟩ :=
    D.exists_belt_whitney_cancellation_of_opposite_signs hf hdim hindex hnull r g
      hg hinj hi ht x₀ x₁ hx₀ hx₁ hsign
  obtain ⟨e, he⟩ := hAt 1
  have hisotopy : SupportedDiffeomorph.IsotopicToIdentity e := ⟨A, hA, hA₀, he, hAt⟩
  have hfixe : ∀ y ∉ K, e y = y := fun y hy => (he y).symm.trans (hfix 1 y hy)
  have hfun : (fun y => A (1, y)) = e := funext he
  rw [hfun] at hcancel
  let g' : C(Hemisphere.Sphere 2, D.UpperLevel) := ⟨e ∘ g, e.continuous.comp g.continuous⟩
  have hg' : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ g' := e.contMDiff.comp hg
  have hinj' : Injective g' := e.injective.comp hinj
  have hi' : ∀ x, Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) g' x) := by
    intro x
    change Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) (e ∘ g) x)
    rw [mfderiv_comp x (e.mdifferentiable (by simp) _) (hg.mdifferentiableAt (by simp))]
    exact ((e.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv_injective
      (by trivial)).comp (hi x)
  have hfixR : ∀ y ∈ (range g ∩ range D.surgery.beltSphere) \ {g x₀, g x₁}, e y = y := by
    intro y hy
    exact hfixe y (fun hyK => Set.disjoint_left.mp hdis hyK hy)
  have hpre := SupportedDiffeomorph.preimage_target_eq_diff_of_relative_removal
    e.toEquiv (g : Hemisphere.Sphere 2 → D.UpperLevel) hfixR hcancel
  have hp : (g : Hemisphere.Sphere 2 → D.UpperLevel) ⁻¹' {g x₀, g x₁} = {x₀, x₁} := by
    ext x
    change (g x = g x₀ ∨ g x = g x₁) ↔ (x = x₀ ∨ x = x₁)
    exact or_congr hinj.eq_iff hinj.eq_iff
  have hpoints : D.beltIntersectionPoints 2 g' = D.beltIntersectionPoints 2 g \ {x₀, x₁} :=
    hpre.trans (congrArg (fun s : Set (Hemisphere.Sphere 2) => D.beltIntersectionPoints 2 g \ s) hp)
  have hgerm : ∀ x ∈ D.beltIntersectionPoints 2 g',
      (g' : Hemisphere.Sphere 2 → D.UpperLevel) =ᶠ[𝓝 x] g := by
    intro x hx
    have hxold : x ∈ D.beltIntersectionPoints 2 g \ {x₀, x₁} := hpoints ▸ hx
    have hy : g x ∈ (range g ∩ range D.surgery.beltSphere) \ {g x₀, g x₁} := by
      refine ⟨⟨⟨x, rfl⟩, hxold.1⟩, ?_⟩
      change x ∉ (g : Hemisphere.Sphere 2 → D.UpperLevel) ⁻¹' {g x₀, g x₁}
      rw [hp]
      exact hxold.2
    exact SupportedDiffeomorph.eventuallyEq_comp_of_fixed_off_closed hK.isClosed hfixe
      g.continuous (fun hyK => Set.disjoint_left.mp hdis hyK hy)
  have ht' : ∀ x y, NativeTransversality.At (𝓡 2) (𝓡 3) 𝓘(ℝ, RegularLevel.Model E)
      g' D.surgery.beltSphere x y := by
    intro x y hxy
    have hx : x ∈ D.beltIntersectionPoints 2 g' := ⟨y, hxy⟩
    have hnear := hgerm x hx
    have hpoint : g' x = g x := hnear.eq_of_nhds
    have hder : (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) g' x :
        EuclideanSpace ℝ (Fin 2) →L[ℝ] RegularLevel.Model E) =
        mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) g x := hnear.mfderiv_eq
    change Surjective ((mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) g' x :
        EuclideanSpace ℝ (Fin 2) →L[ℝ] RegularLevel.Model E).coprod
      (mfderiv (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) D.surgery.beltSphere y :
        EuclideanSpace ℝ (Fin 3) →L[ℝ] RegularLevel.Model E))
    rw [hder]
    exact ht x y (hxy.trans hpoint)
  refine ⟨e, g', hisotopy, fun _ => rfl, hg', hinj', hi', ht', hpoints, hgerm, ?_⟩
  intro x hx
  have hnormal : (D.beltNormal ∘ g') =ᶠ[𝓝 x] (D.beltNormal ∘ g) := by
    filter_upwards [hgerm x hx] with z hz
    exact congrArg D.beltNormal hz
  have hder : (mfderiv (𝓡 2) 𝓘(ℝ, D.chart.NegativeCoordinates) (D.beltNormal ∘ g') x :
      EuclideanSpace ℝ (Fin 2) →L[ℝ] D.chart.NegativeCoordinates) =
      mfderiv (𝓡 2) 𝓘(ℝ, D.chart.NegativeCoordinates) (D.beltNormal ∘ g) x :=
    hnormal.mfderiv_eq
  have hjac : D.beltIntersectionJacobian 2 r g' x = D.beltIntersectionJacobian 2 r g x :=
    congrArg (fun L : EuclideanSpace ℝ (Fin 2) →L[ℝ] D.chart.NegativeCoordinates =>
      SphereNormalCoordinates.normalJacobian r x L) hder
  exact congrArg SignType.sign hjac

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
