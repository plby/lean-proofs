import Wikipedia.HopfProblem.DegreeCollapseTwoSphereHomotopyIsotopy
import Wikipedia.HopfProblem.DegreeCollapseNativeLevelRetraction
import Wikipedia.HopfProblem.DegreeCollapsePositiveLevelSphereHomotopy

/-!
# Actual native two-sphere placement in the positive three/four level

The positive half's native homology supplies the original sphere
homotopy. The original state embedding and flow cylinder construct the
level embedding and tubular retraction. Actual affine perturbation and
ambient isotopy extension then carry the full first parametrized sphere
to the second. No disk embedding, generic parameter, embedding family,
or ambient isotopy is supplied as an extra hypothesis.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization MorseCancellation SingularMayerVietoris
open Wikipedia.SmoothSixDPoincare ManifoldMorse SupportedDiffeomorph

variable {B : Type} [TopologicalSpace B] [Subsingleton (SingularHomology B 2)]
  {S : CollaredSevenState B} (P : S.ExcellentMorsePresentation)

theorem exists_native_positive_level_two_sphere_isotopy
    (A : AdaptedSurgeryWindows (Vector 7) P.function) {a : ℝ} (ha : 0 < a)
    (hreg : ∀ y, P.function y = a → y ∉ criticalPoints (Vector 7) P.function)
    (hhigh : ∀ p : criticalPoints (Vector 7) P.function, a ≤ P.function p →
      4 ≤ nativeMorseIndex (Vector 7) P.function p)
    (hlow : ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p → P.function p ≤ a →
      nativeMorseIndex (Vector 7) P.function p ≤ 3)
    (γ δ : C(Hemisphere.Sphere 2, {y : S.Space // P.function y = a})) :
    let _ := RegularLevel.chartedSpace P.smooth hreg
    ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ γ → Injective γ →
    (∀ z, Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) γ z)) →
    ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ δ → Injective δ →
    (∀ z, Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) δ z)) →
    ∃ D : Diffeomorph 𝓘(ℝ, RegularLevel.Model (Vector 7)) 𝓘(ℝ, RegularLevel.Model (Vector 7))
        {y : S.Space // P.function y = a} {y : S.Space // P.function y = a} ∞,
      IsotopicToIdentity D ∧ ∀ z, D (γ z) = δ z := by
  let _ := RegularLevel.chartedSpace P.smooth hreg
  let _ := RegularLevel.isManifold P.smooth hreg
  let : CompactSpace {y : S.Space // P.function y = a} :=
    isCompact_iff_compactSpace.mp (isClosed_eq P.function.continuous continuous_const).isCompact
  change ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ γ → Injective γ →
    (∀ z, Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) γ z)) →
    ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ δ → Injective δ →
    (∀ z, Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) δ z)) → _
  intro hγ hγi hγd hδ hδi hδd
  let e := P.nativeLevelEmbedding hreg
  obtain ⟨r⟩ := P.nonempty_nativeLevelRetraction A hreg (γ (SphereCube.point 2))
  exact TwoSpherePerturbation.exists_native_isotopy_of_two_sphere_homotopy e r (by simp)
    γ δ hγ hγi hγd hδ hδi hδd
    (P.positive_level_two_spheres_homotopic A ha hreg hhigh hlow γ δ)

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation
