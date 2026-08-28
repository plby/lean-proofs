import Wikipedia.HopfProblem.DegreeCollapseMiddleLevelCircleIsotopy
import Wikipedia.HopfProblem.DegreeCollapseEqualNativeLevels
import Wikipedia.HopfProblem.DegreeCollapseNativeIsotopyConjugation

/-!
# Circle comparison after a function change preserving the middle level

The old function supplies disk fillings and path connectedness. The identity
native level diffeomorphism transfers these to circles defined using the
new function, and conjugation retains the actual smooth ambient isotopy.
The new function need not satisfy the old upper index bound.
-/

noncomputable section

open Set Function Manifold ContinuousMap
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f g : M → ℝ}

theorem exists_equal_level_circle_isotopy
    (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (e : M ≃ₕ SixSphere) (hdim : Module.finrank ℝ E = 6)
    {a : ℝ} (hfr : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hgr : ∀ y, g y = a → y ∉ criticalPoints E g)
    (heq : ∀ y, g y = a ↔ f y = a)
    (hhigh : ∀ p : criticalPoints E f, a ≤ f p → 3 ≤ nativeMorseIndex E f p)
    (hlow : ∀ p : criticalPoints E f, f p ≤ a → nativeMorseIndex E f p ≤ 3)
    (γ δ : C(Hemisphere.Sphere 1, {y : M // g y = a})) :
    let _ := RegularLevel.chartedSpace hg hgr
    ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γ → Injective γ →
    (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ z)) →
    ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ δ → Injective δ →
    (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) δ z)) →
    ∃ P : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        {y : M // g y = a} {y : M // g y = a} ∞,
      IsotopicToIdentity P ∧ ∀ z, P (γ z) = δ z := by
  let _ := RegularLevel.chartedSpace hf hfr
  let _ := RegularLevel.chartedSpace hg hgr
  let _ := RegularLevel.isManifold hf hfr
  let _ := RegularLevel.isManifold hg hgr
  change ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γ → Injective γ →
    (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ z)) →
    ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ δ → Injective δ →
    (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) δ z)) → _
  intro hγ hγi hγd hδ hδi hδd
  let L := equalLevelDiffeomorph hf hg hfr hgr heq
  let γ' : C(Hemisphere.Sphere 1, {y : M // f y = a}) :=
    ⟨L.symm ∘ γ, L.symm.continuous.comp γ.continuous⟩
  let δ' : C(Hemisphere.Sphere 1, {y : M // f y = a}) :=
    ⟨L.symm ∘ δ, L.symm.continuous.comp δ.continuous⟩
  have hγ' : ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γ' := L.symm.contMDiff.comp hγ
  have hδ' : ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ δ' := L.symm.contMDiff.comp hδ
  have hderiv (κ : C(Hemisphere.Sphere 1, {y : M // g y = a}))
      (hk : ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ κ)
      (hkd : ∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) κ z)) (z) :
      Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) (L.symm ∘ κ) z) := by
    rw [mfderiv_comp z (L.symm.contMDiff.mdifferentiableAt (by simp))
      (hk.mdifferentiableAt (by simp))]
    exact (L.symm.mfderivToContinuousLinearEquiv (by simp) (κ z)).injective.comp (hkd z)
  obtain ⟨Q, hQ, hformula⟩ := exists_native_middle_level_circle_isotopy S hf e hdim
    hfr hhigh hlow γ' δ' hγ' (L.symm.injective.comp hγi) (hderiv γ hγ hγd)
      hδ' (L.symm.injective.comp hδi) (hderiv δ hδ hδd)
  refine ⟨(L.symm.trans Q).trans L, isotopicToIdentity_conj L hQ, ?_⟩
  intro z
  change L (Q (γ' z)) = δ z
  rw [hformula]
  exact L.apply_symm_apply (δ z)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
