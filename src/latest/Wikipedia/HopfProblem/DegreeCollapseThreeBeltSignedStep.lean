import Wikipedia.HopfProblem.DegreeCollapseThreeBeltWhitneyCancellation

/-!
# A repeatable native three-belt signed-pair removal

The actual Whitney isotopy retains the full map germ at every surviving
crossing. Its endpoint sphere stays smooth, embedded, immersive, and
transverse. Exactly the two selected source points disappear, and every
surviving original fixed-normal intersection sign is unchanged.
-/

noncomputable section

open Set Function Filter Topology ContinuousMap
open scoped ContDiff Manifold
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}

theorem exists_signed_three_belt_cancellation_step
    (D : MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 7)
    [Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1)]
    (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 3)
    (hnull : ∀ γ : C(Hemisphere.Sphere 1, D.LowerLevel),
      ∃ q, γ.Homotopic (ContinuousMap.const _ q))
    (r : (ℝ × D.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient 4)
    (g : C(Hemisphere.Sphere 3, D.UpperLevel))
    (hgood : IsNativeTransverseBeltSphere D hf 3 3 g)
    (x₀ x₁ : Hemisphere.Sphere 3)
    (hx₀ : x₀ ∈ D.beltIntersectionPoints 3 g) (hx₁ : x₁ ∈ D.beltIntersectionPoints 3 g)
    (hsign : D.beltIntersectionSign 3 r g x₀ * D.beltIntersectionSign 3 r g x₁ = -1) :
    letI := RegularLevel.chartedSpace hf D.upper_regular
    ∃ e : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        D.UpperLevel D.UpperLevel ∞,
      ∃ g' : C(Hemisphere.Sphere 3, D.UpperLevel),
        SupportedDiffeomorph.IsotopicToIdentity e ∧ (∀ x, g' x = e (g x)) ∧
        IsNativeTransverseBeltSphere D hf 3 3 g' ∧
        D.beltIntersectionPoints 3 g' = D.beltIntersectionPoints 3 g \ {x₀, x₁} ∧
        (∀ x ∈ D.beltIntersectionPoints 3 g',
          (g' : Hemisphere.Sphere 3 → D.UpperLevel) =ᶠ[𝓝 x] g) ∧
        ∀ x ∈ D.beltIntersectionPoints 3 g',
          D.beltIntersectionSign 3 r g' x = D.beltIntersectionSign 3 r g x := by
  let _ := RegularLevel.chartedSpace hf D.upper_regular
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient 4) = 3 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  obtain ⟨hg, hinj, hi, ht⟩ := hgood
  obtain ⟨K, hK, hdis, A, hA, hA₀, hAt, hfix, hcancel⟩ :=
    exists_three_belt_whitney_cancellation_of_opposite_signs D hf hdim hindex hnull r g
      ⟨hg, hinj, hi, ht⟩ x₀ x₁ hx₀ hx₁ hsign
  obtain ⟨e, he⟩ := hAt 1
  have hisotopy : SupportedDiffeomorph.IsotopicToIdentity e := ⟨A, hA, hA₀, he, hAt⟩
  have hfixe : ∀ y ∉ K, e y = y := fun y hy => (he y).symm.trans (hfix 1 y hy)
  have hfun : (fun y => A (1, y)) = e := funext he
  rw [hfun] at hcancel
  let g' : C(Hemisphere.Sphere 3, D.UpperLevel) := ⟨e ∘ g, e.continuous.comp g.continuous⟩
  have hg' : ContMDiff (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) ∞ g' := e.contMDiff.comp hg
  have hinj' : Injective g' := e.injective.comp hinj
  have hi' : ∀ x, Injective (mfderiv (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) g' x) := by
    intro x
    change Injective (mfderiv (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) (e ∘ g) x)
    rw [mfderiv_comp x (e.mdifferentiable (by simp) _) (hg.mdifferentiableAt (by simp))]
    exact ((e.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv_injective
      (by trivial)).comp (hi x)
  have hfixR : ∀ y ∈ (range g ∩ range D.surgery.beltSphere) \ {g x₀, g x₁}, e y = y := by
    intro y hy
    exact hfixe y (fun hyK => Set.disjoint_left.mp hdis hyK hy)
  have hpre := SupportedDiffeomorph.preimage_target_eq_diff_of_relative_removal
    e.toEquiv (g : Hemisphere.Sphere 3 → D.UpperLevel) hfixR hcancel
  have hp : (g : Hemisphere.Sphere 3 → D.UpperLevel) ⁻¹' {g x₀, g x₁} = {x₀, x₁} := by
    ext x
    change (g x = g x₀ ∨ g x = g x₁) ↔ (x = x₀ ∨ x = x₁)
    exact or_congr hinj.eq_iff hinj.eq_iff
  have hpoints : D.beltIntersectionPoints 3 g' = D.beltIntersectionPoints 3 g \ {x₀, x₁} :=
    hpre.trans (congrArg (fun s : Set (Hemisphere.Sphere 3) => D.beltIntersectionPoints 3 g \ s) hp)
  have hgerm : ∀ x ∈ D.beltIntersectionPoints 3 g',
      (g' : Hemisphere.Sphere 3 → D.UpperLevel) =ᶠ[𝓝 x] g := by
    intro x hx
    have hxold : x ∈ D.beltIntersectionPoints 3 g \ {x₀, x₁} := hpoints ▸ hx
    have hy : g x ∈ (range g ∩ range D.surgery.beltSphere) \ {g x₀, g x₁} := by
      refine ⟨⟨⟨x, rfl⟩, hxold.1⟩, ?_⟩
      change x ∉ (g : Hemisphere.Sphere 3 → D.UpperLevel) ⁻¹' {g x₀, g x₁}
      rw [hp]
      exact hxold.2
    exact SupportedDiffeomorph.eventuallyEq_comp_of_fixed_off_closed hK.isClosed hfixe
      g.continuous (fun hyK => Set.disjoint_left.mp hdis hyK hy)
  have ht' : ∀ x y, NativeTransversality.At (𝓡 3) (𝓡 3) 𝓘(ℝ, RegularLevel.Model E)
      g' D.surgery.beltSphere x y := by
    intro x y hxy
    have hx : x ∈ D.beltIntersectionPoints 3 g' := ⟨y, hxy⟩
    have hnear := hgerm x hx
    have hpoint : g' x = g x := hnear.eq_of_nhds
    have hder : (mfderiv (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) g' x :
        EuclideanSpace ℝ (Fin 3) →L[ℝ] RegularLevel.Model E) =
        mfderiv (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) g x := hnear.mfderiv_eq
    change Surjective ((mfderiv (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) g' x :
        EuclideanSpace ℝ (Fin 3) →L[ℝ] RegularLevel.Model E).coprod
      (mfderiv (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) D.surgery.beltSphere y :
        EuclideanSpace ℝ (Fin 3) →L[ℝ] RegularLevel.Model E))
    rw [hder]
    exact ht x y (hxy.trans hpoint)
  refine ⟨e, g', hisotopy, fun _ => rfl, ⟨hg', hinj', hi', ht'⟩, hpoints, hgerm, ?_⟩
  intro x hx
  have hnormal : (D.beltNormal ∘ g') =ᶠ[𝓝 x] (D.beltNormal ∘ g) := by
    filter_upwards [hgerm x hx] with z hz
    exact congrArg D.beltNormal hz
  have hder : (mfderiv (𝓡 3) 𝓘(ℝ, D.chart.NegativeCoordinates) (D.beltNormal ∘ g') x :
      EuclideanSpace ℝ (Fin 3) →L[ℝ] D.chart.NegativeCoordinates) =
      mfderiv (𝓡 3) 𝓘(ℝ, D.chart.NegativeCoordinates) (D.beltNormal ∘ g) x :=
    hnormal.mfderiv_eq
  have hjac : D.beltIntersectionJacobian 3 r g' x = D.beltIntersectionJacobian 3 r g x :=
    congrArg (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ] D.chart.NegativeCoordinates =>
      SphereNormalCoordinates.normalJacobian r x L) hder
  exact congrArg SignType.sign hjac

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
