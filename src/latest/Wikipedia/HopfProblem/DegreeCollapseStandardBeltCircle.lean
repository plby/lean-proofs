import Wikipedia.HopfProblem.DegreeCollapseBeltCircleTransversality

/-!
# The belt-crossing circle parametrized by the standard Euclidean sphere

The native linear-isometry sphere diffeomorphism converts the complex unit
circle to the exact circle used by the disk-filling theorems. Smoothness,
immersion, the unique intersection, and transversality are retained.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

theorem surjective_coprod_comp_left
    {A A' B G : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup A'] [NormedSpace ℝ A']
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : A →L[ℝ] G) (R : B →L[ℝ] G) (P : A' →L[ℝ] A)
    (hP : Surjective P) (htrans : Surjective (L.coprod R)) :
    Surjective ((L.comp P).coprod R) := by
  intro y
  obtain ⟨⟨a, b⟩, hab⟩ := htrans y
  obtain ⟨a', ha⟩ := hP a
  refine ⟨(a', b), ?_⟩
  change L (P a') + R b = y
  rw [ha]
  exact hab

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

open Classical in
theorem AdaptedSurgeryWindows.exists_standard_transverse_single_belt_circle
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : criticalPoints E f) (hp : nativeMorseIndex E f p = 0)
    (hq : nativeMorseIndex E f q = 1)
    (n : ℕ) [Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = n + 1)]
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (hbranches : ∀ w : sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
      Tendsto (fun t => S.flow t ((S.data q).surgery.attachingSphere w).val) atTop (𝓝 p.val))
    {d : ℕ} (hlow : ∀ a : criticalPoints E f, f a ≤ S.toSurgeryWindows.upper q →
      nativeMorseIndex E f a ≤ d) (hcut : 1 + d < Module.finrank ℝ E)
    (hdim : 4 ≤ Module.finrank ℝ E) :
    let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
    ∃ γ : C(Hemisphere.Sphere 1, (S.data q).UpperLevel),
      ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γ ∧ Injective γ ∧
      (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ z)) ∧
      ∃ z₀ : Hemisphere.Sphere 1,
        (∀ z w, γ z = (S.data q).surgery.beltSphere w ↔ z = z₀ ∧ v = w) ∧
        Surjective ((mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ z₀ :
          EuclideanSpace ℝ (Fin 1) →L[ℝ] RegularLevel.Model E).coprod
            (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) (S.data q).surgery.beltSphere v)) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ := RegularLevel.isManifold hf (S.data q).upper_regular
  let _ : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨Complex.finrank_real_complex⟩
  obtain ⟨γ, hγ, hγi, hγd, z₀, hsingle, htrans⟩ :=
    S.exists_transverse_single_belt_circle hf p q hp hq n u v hbranches hlow hcut hdim
  let e : Diffeomorph (𝓡 1) (𝓡 1) (Hemisphere.Sphere 1) Circle ∞ :=
    SphereCoordinates.standardParametrization ℂ 1
  let Γ : C(Hemisphere.Sphere 1, (S.data q).UpperLevel) :=
    ⟨γ ∘ e, γ.continuous.comp e.continuous⟩
  have hΓ : ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ Γ := hγ.comp e.contMDiff
  have hΓd : ∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) Γ z) := by
    intro z
    change Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) (γ ∘ e) z)
    rw [mfderiv_comp z (hγ.mdifferentiableAt (by simp)) (e.contMDiff.mdifferentiableAt (by simp))]
    exact (hγd (e z)).comp (e.mfderivToContinuousLinearEquiv (by simp) z).injective
  refine ⟨Γ, hΓ, hγi.comp e.injective, hΓd, e.symm z₀, ?_, ?_⟩
  · intro z w
    change γ (e z) = (S.data q).surgery.beltSphere w ↔ _
    rw [hsingle]
    constructor
    · rintro ⟨hz, hv⟩
      exact ⟨e.injective (hz.trans (e.apply_symm_apply z₀).symm), hv⟩
    · rintro ⟨rfl, hv⟩
      exact ⟨e.apply_symm_apply z₀, hv⟩
  · let B : EuclideanSpace ℝ (Fin n) →L[ℝ] RegularLevel.Model E :=
      mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) (S.data q).surgery.beltSphere v
    let L : EuclideanSpace ℝ (Fin 1) →L[ℝ] RegularLevel.Model E :=
      mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ (e (e.symm z₀))
    have hL : Surjective (L.coprod B) := by
      change Surjective ((mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ (e (e.symm z₀)) :
        EuclideanSpace ℝ (Fin 1) →L[ℝ] RegularLevel.Model E).coprod B)
      rw [e.apply_symm_apply z₀]
      exact htrans
    let P : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
      mfderiv (𝓡 1) (𝓡 1) e (e.symm z₀)
    have hP : Surjective P :=
      (e.mfderivToContinuousLinearEquiv (by simp) (e.symm z₀)).surjective
    change Surjective ((mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) (γ ∘ e)
      (e.symm z₀) : EuclideanSpace ℝ (Fin 1) →L[ℝ] RegularLevel.Model E).coprod B)
    rw [mfderiv_comp (e.symm z₀) (hγ.mdifferentiableAt (by simp))
      (e.contMDiff.mdifferentiableAt (by simp))]
    change Surjective ((L.comp P).coprod B)
    exact surjective_coprod_comp_left L B P hP hL

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
