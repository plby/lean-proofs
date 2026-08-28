import Wikipedia.HopfProblem.DegreeCollapsePositiveLevelSphereIsotopy
import Wikipedia.HopfProblem.DegreeCollapseAttachingSphereLowerTransport
import Wikipedia.HopfProblem.DegreeCollapseNewAttachingCirclePlacement

/-!
# Native two-sphere placement on any retained positive fiber

The new defining function need not be a positive presentation of the
state, and its level value may differ. Equality of the actual fibers
gives an identity-on-points native diffeomorphism. Conjugate the original
positive-level two-sphere isotopy through it, retaining the full two-sphere
parametrization and the whole attaching-basin equality.

This applies to a negated function and its supported births without
reversing the state or imposing index bounds on its negative half.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization MorseCancellation SingularMayerVietoris
open Wikipedia.SmoothSixDPoincare ManifoldMorse SupportedDiffeomorph

variable {B : Type} [TopologicalSpace B] [Subsingleton (SingularHomology B 2)]
  {S : CollaredSevenState B}
  (P : S.ExcellentMorsePresentation)

theorem exists_level_two_sphere_isotopy_of_positive_fiber
    (A : AdaptedSurgeryWindows (Vector 7) P.function) {a : ℝ} (ha : 0 < a)
    (hfr : ∀ y, P.function y = a → y ∉ criticalPoints (Vector 7) P.function)
    (hhigh : ∀ p : criticalPoints (Vector 7) P.function, a ≤ P.function p →
      4 ≤ nativeMorseIndex (Vector 7) P.function p)
    (hlow : ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p → P.function p ≤ a →
      nativeMorseIndex (Vector 7) P.function p ≤ 3)
    {g : S.Space → ℝ} (hg : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ g) {b : ℝ}
    (hgr : ∀ y, g y = b → y ∉ criticalPoints (Vector 7) g)
    (heq : ∀ y, g y = b ↔ P.function y = a)
    (γ δ : C(Hemisphere.Sphere 2, {y : S.Space // g y = b})) :
    let _ := RegularLevel.chartedSpace hg hgr
    ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ γ → Injective γ →
    (∀ z, Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) γ z)) →
    ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ δ → Injective δ →
    (∀ z, Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) δ z)) →
    ∃ D : Diffeomorph 𝓘(ℝ, RegularLevel.Model (Vector 7)) 𝓘(ℝ, RegularLevel.Model (Vector 7))
        {y : S.Space // g y = b} {y : S.Space // g y = b} ∞,
      IsotopicToIdentity D ∧ ∀ z, D (γ z) = δ z := by
  let _ := RegularLevel.chartedSpace P.smooth hfr
  let _ := RegularLevel.chartedSpace hg hgr
  let _ := RegularLevel.isManifold P.smooth hfr
  let _ := RegularLevel.isManifold hg hgr
  change ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ γ → Injective γ →
    (∀ z, Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) γ z)) →
    ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ δ → Injective δ →
    (∀ z, Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) δ z)) → _
  intro hγ hγi hγd hδ hδi hδd
  let L := equalFiberDiffeomorph P.smooth hg hfr hgr heq
  let γ' : C(Hemisphere.Sphere 2, {y : S.Space // P.function y = a}) :=
    ⟨L.symm ∘ γ, L.symm.continuous.comp γ.continuous⟩
  let δ' : C(Hemisphere.Sphere 2, {y : S.Space // P.function y = a}) :=
    ⟨L.symm ∘ δ, L.symm.continuous.comp δ.continuous⟩
  have hγ' : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ γ' := L.symm.contMDiff.comp hγ
  have hδ' : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ δ' := L.symm.contMDiff.comp hδ
  have hderiv (κ : C(Hemisphere.Sphere 2, {y : S.Space // g y = b}))
      (hk : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ κ)
      (hkd : ∀ z, Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) κ z)) (z) :
      Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) (L.symm ∘ κ) z) := by
    rw [mfderiv_comp z (L.symm.contMDiff.mdifferentiableAt (by simp))
      (hk.mdifferentiableAt (by simp))]
    exact (L.symm.mfderivToContinuousLinearEquiv (by simp) (κ z)).injective.comp (hkd z)
  obtain ⟨D, hD, hformula⟩ := P.exists_native_positive_level_two_sphere_isotopy A ha hfr hhigh hlow
    γ' δ' hγ' (L.symm.injective.comp hγi) (hderiv γ hγ hγd)
      hδ' (L.symm.injective.comp hδi) (hderiv δ hδ hδd)
  refine ⟨(L.symm.trans D).trans L, isotopicToIdentity_conj L hD, ?_⟩
  intro z
  change L (D (γ' z)) = δ z
  rw [hformula]
  exact L.apply_symm_apply (δ z)

theorem exists_attaching_two_sphere_placement_of_positive_fiber
    (A : AdaptedSurgeryWindows (Vector 7) P.function) {a : ℝ} (ha : 0 < a)
    (hfr : ∀ y, P.function y = a → y ∉ criticalPoints (Vector 7) P.function)
    (hhigh : ∀ p : criticalPoints (Vector 7) P.function, a ≤ P.function p →
      4 ≤ nativeMorseIndex (Vector 7) P.function p)
    (hlow : ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p → P.function p ≤ a →
      nativeMorseIndex (Vector 7) P.function p ≤ 3)
    {g : S.Space → ℝ} (hg : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ g)
    (T : AdaptedSurgeryWindows (Vector 7) g) {b : ℝ}
    (hgr : ∀ y, g y = b → y ∉ criticalPoints (Vector 7) g)
    (heq : ∀ y, g y = b ↔ P.function y = a)
    (r : criticalPoints (Vector 7) g)
    [Fact (Module.finrank ℝ (T.data r).chart.NegativeCoordinates = 2 + 1)]
    (hbr : b < g r)
    (hgap : ∀ p : criticalPoints (Vector 7) g, g p < g r → g p < b)
    (δ : C(Hemisphere.Sphere 2, {y : S.Space // g y = b})) :
    let _ := RegularLevel.chartedSpace hg hgr
    ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ δ → Injective δ →
    (∀ z, Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) δ z)) →
    ∃ (Γ : C(Hemisphere.Sphere 2, {y : S.Space // g y = b}))
      (D : Diffeomorph 𝓘(ℝ, RegularLevel.Model (Vector 7)) 𝓘(ℝ, RegularLevel.Model (Vector 7))
        {y : S.Space // g y = b} {y : S.Space // g y = b} ∞),
      ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ Γ ∧ Injective Γ ∧
      (∀ z, Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) Γ z)) ∧
      (∀ x, x ∈ range Γ ↔ Tendsto (fun t => T.flow t x.val) atBot (𝓝 r.val)) ∧
      IsotopicToIdentity D ∧ (∀ z, D (Γ z) = δ z) ∧
      ∀ x, Tendsto (fun t => T.flow t x.val) atBot (𝓝 r.val) ↔ D x ∈ range δ := by
  let _ := RegularLevel.chartedSpace hg hgr
  let _ := RegularLevel.chartedSpace hg (T.data r).lower_regular
  let _ := RegularLevel.isManifold hg hgr
  let _ := RegularLevel.isManifold hg (T.data r).lower_regular
  change ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ δ → Injective δ →
    (∀ z, Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) δ z)) → _
  intro hδ hδi hδd
  obtain ⟨σ, _, _, _, Γ, hΓ, hΓi, hΓd, _, _, hflow⟩ :=
    T.exists_attaching_sphere_lower_transport hg r 2 hgr hbr hgap
  have hΓrange (x : {y : S.Space // g y = b}) :
      x ∈ range Γ ↔ Tendsto (fun t => T.flow t x.val) atBot (𝓝 r.val) :=
    T.transported_attaching_range_iff hg r hgr σ σ.surjective Γ hflow x
  obtain ⟨D, hD, hformula⟩ := P.exists_level_two_sphere_isotopy_of_positive_fiber
    A ha hfr hhigh hlow hg hgr heq Γ δ hΓ hΓi hΓd hδ hδi hδd
  refine ⟨Γ, D, hΓ, hΓi, hΓd, hΓrange, hD, hformula, ?_⟩
  intro x
  rw [← hΓrange x]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, (hformula z).symm⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, D.injective ((hformula z).trans hz)⟩

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation
