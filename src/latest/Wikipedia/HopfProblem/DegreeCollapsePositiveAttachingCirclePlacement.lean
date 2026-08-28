import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenPositiveCircleIsotopy
import Wikipedia.HopfProblem.DegreeCollapseNewAttachingCirclePlacement

/-!
# Place a newborn attaching circle at the retained original positive cut

Use the ORIGINAL presentation's constructed disk isotopy, transferred by
the native equal-level diffeomorphism to the new presentation's level.
The newborn two-handle's actual complete-flow attaching circle is then
carried to the prescribed belt loop with its entire parametrization and
whole-level backward-basin identity retained.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization MorseCancellation
open Wikipedia.SmoothSixDPoincare ManifoldMorse SupportedDiffeomorph

variable {B : Type} [TopologicalSpace B] {S : CollaredSevenState B}
  (P Q : S.ExcellentMorsePresentation)

theorem exists_equal_positive_level_circle_isotopy
    (A : AdaptedSurgeryWindows (Vector 7) P.function) {a : ℝ} (ha : 0 < a)
    (hfr : ∀ y, P.function y = a → y ∉ criticalPoints (Vector 7) P.function)
    (hgr : ∀ y, Q.function y = a → y ∉ criticalPoints (Vector 7) Q.function)
    (heq : ∀ y, Q.function y = a ↔ P.function y = a)
    (hhigh : ∀ p : criticalPoints (Vector 7) P.function, a ≤ P.function p →
      3 ≤ nativeMorseIndex (Vector 7) P.function p)
    (hlow : ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p → P.function p ≤ a →
      nativeMorseIndex (Vector 7) P.function p ≤ 4)
    (γ δ : C(Hemisphere.Sphere 1, {y : S.Space // Q.function y = a})) :
    let _ := RegularLevel.chartedSpace Q.smooth hgr
    ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ γ → Injective γ →
    (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model (Vector 7)) γ z)) →
    ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ δ → Injective δ →
    (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model (Vector 7)) δ z)) →
    ∃ D : Diffeomorph 𝓘(ℝ, RegularLevel.Model (Vector 7)) 𝓘(ℝ, RegularLevel.Model (Vector 7))
        {y : S.Space // Q.function y = a} {y : S.Space // Q.function y = a} ∞,
      IsotopicToIdentity D ∧ ∀ z, D (γ z) = δ z := by
  let _ := RegularLevel.chartedSpace P.smooth hfr
  let _ := RegularLevel.chartedSpace Q.smooth hgr
  let _ := RegularLevel.isManifold P.smooth hfr
  let _ := RegularLevel.isManifold Q.smooth hgr
  change ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ γ → Injective γ →
    (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model (Vector 7)) γ z)) →
    ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ δ → Injective δ →
    (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model (Vector 7)) δ z)) → _
  intro hγ hγi hγd hδ hδi hδd
  let L := equalLevelDiffeomorph P.smooth Q.smooth hfr hgr heq
  let γ' : C(Hemisphere.Sphere 1, {y : S.Space // P.function y = a}) :=
    ⟨L.symm ∘ γ, L.symm.continuous.comp γ.continuous⟩
  let δ' : C(Hemisphere.Sphere 1, {y : S.Space // P.function y = a}) :=
    ⟨L.symm ∘ δ, L.symm.continuous.comp δ.continuous⟩
  have hγ' : ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ γ' := L.symm.contMDiff.comp hγ
  have hδ' : ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ δ' := L.symm.contMDiff.comp hδ
  have hderiv (κ : C(Hemisphere.Sphere 1, {y : S.Space // Q.function y = a}))
      (hk : ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ κ)
      (hkd : ∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model (Vector 7)) κ z)) (z) :
      Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model (Vector 7)) (L.symm ∘ κ) z) := by
    rw [mfderiv_comp z (L.symm.contMDiff.mdifferentiableAt (by simp))
      (hk.mdifferentiableAt (by simp))]
    exact (L.symm.mfderivToContinuousLinearEquiv (by simp) (κ z)).injective.comp (hkd z)
  obtain ⟨D, hD, hformula⟩ := P.exists_native_positive_level_circle_isotopy A ha hfr hhigh hlow
    γ' δ' hγ' (L.symm.injective.comp hγi) (hderiv γ hγ hγd)
      hδ' (L.symm.injective.comp hδi) (hderiv δ hδ hδd)
  refine ⟨(L.symm.trans D).trans L, isotopicToIdentity_conj L hD, ?_⟩
  intro z
  change L (D (γ' z)) = δ z
  rw [hformula]
  exact L.apply_symm_apply (δ z)

theorem exists_positive_attaching_circle_placement
    (A : AdaptedSurgeryWindows (Vector 7) P.function)
    (T : AdaptedSurgeryWindows (Vector 7) Q.function) {a : ℝ} (ha : 0 < a)
    (hfr : ∀ y, P.function y = a → y ∉ criticalPoints (Vector 7) P.function)
    (hgr : ∀ y, Q.function y = a → y ∉ criticalPoints (Vector 7) Q.function)
    (heq : ∀ y, Q.function y = a ↔ P.function y = a)
    (hhigh : ∀ p : criticalPoints (Vector 7) P.function, a ≤ P.function p →
      3 ≤ nativeMorseIndex (Vector 7) P.function p)
    (hlow : ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p → P.function p ≤ a →
      nativeMorseIndex (Vector 7) P.function p ≤ 4)
    (r : criticalPoints (Vector 7) Q.function)
    [Fact (Module.finrank ℝ (T.data r).chart.NegativeCoordinates = 1 + 1)]
    (har : a < Q.function r)
    (hgap : ∀ p : criticalPoints (Vector 7) Q.function,
      Q.function p < Q.function r → Q.function p < a)
    (δ : C(Hemisphere.Sphere 1, {y : S.Space // Q.function y = a})) :
    let _ := RegularLevel.chartedSpace Q.smooth hgr
    ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ δ → Injective δ →
    (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model (Vector 7)) δ z)) →
    ∃ Γ : C(Hemisphere.Sphere 1, {y : S.Space // Q.function y = a}),
      ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ Γ ∧ Injective Γ ∧
      (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model (Vector 7)) Γ z)) ∧
      (∀ x, x ∈ range Γ ↔ Tendsto (fun t => T.flow t x.val) atBot (𝓝 r.val)) ∧
      ∃ D : Diffeomorph 𝓘(ℝ, RegularLevel.Model (Vector 7)) 𝓘(ℝ, RegularLevel.Model (Vector 7))
          {y : S.Space // Q.function y = a} {y : S.Space // Q.function y = a} ∞,
        IsotopicToIdentity D ∧ (∀ z, D (Γ z) = δ z) ∧
        ∀ x, Tendsto (fun t => T.flow t x.val) atBot (𝓝 r.val) ↔ D x ∈ range δ := by
  let _ := RegularLevel.chartedSpace Q.smooth hgr
  let _ := RegularLevel.chartedSpace Q.smooth (T.data r).lower_regular
  let _ := RegularLevel.isManifold Q.smooth hgr
  let _ := RegularLevel.isManifold Q.smooth (T.data r).lower_regular
  change ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ δ → Injective δ →
    (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model (Vector 7)) δ z)) → _
  intro hδ hδi hδd
  obtain ⟨σ, _, _, _, Γ, hΓ, hΓi, hΓd, _, _, hflow⟩ :=
    T.exists_attaching_circle_lower_transport Q.smooth r hgr har hgap
  have hrange (x : {y : S.Space // Q.function y = a}) :
      x ∈ range Γ ↔ Tendsto (fun t => T.flow t x.val) atBot (𝓝 r.val) :=
    T.transported_attaching_range_iff Q.smooth r hgr σ σ.surjective Γ hflow x
  obtain ⟨D, hD, hformula⟩ := P.exists_equal_positive_level_circle_isotopy Q A ha
    hfr hgr heq hhigh hlow Γ δ hΓ hΓi hΓd hδ hδi hδd
  refine ⟨Γ, hΓ, hΓi, hΓd, hrange, D, hD, hformula, ?_⟩
  intro x
  rw [← hrange]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, (hformula z).symm⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, D.injective ((hformula z).trans hz)⟩

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation
