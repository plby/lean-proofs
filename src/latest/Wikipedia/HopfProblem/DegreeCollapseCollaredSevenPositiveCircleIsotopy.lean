import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenPositiveLevelDisks
import Wikipedia.HopfProblem.DegreeCollapseSimplyConnectedCircleIsotopy
import Wikipedia.HopfProblem.DegreeCollapsePositiveIndexCut

/-!
# Native circle isotopy in the actual positive seven-dimensional level

Both circles bound constructed embedded disks in the original regular
level. Actual path connectedness there and the native disk isotopy theorem
give a level diffeomorphism isotopic to the identity, carrying the entire
first parametrized circle to the second. In a seven-dimensional state the
level dimension is six and the disk has four normal directions.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization MorseCancellation
open Wikipedia.SmoothSixDPoincare ManifoldMorse SupportedDiffeomorph

variable {B : Type} [TopologicalSpace B] {S : CollaredSevenState B}
  (P : S.ExcellentMorsePresentation)

theorem exists_native_positive_level_circle_disk
    (A : AdaptedSurgeryWindows (Vector 7) P.function) {a : ℝ} (ha : 0 < a)
    (hreg : ∀ y, P.function y = a → y ∉ criticalPoints (Vector 7) P.function)
    (hhigh : ∀ p : criticalPoints (Vector 7) P.function, a ≤ P.function p →
      3 ≤ nativeMorseIndex (Vector 7) P.function p)
    (hlow : ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p → P.function p ≤ a →
      nativeMorseIndex (Vector 7) P.function p ≤ 4)
    (γ : C(Hemisphere.Sphere 1, {y : S.Space // P.function y = a})) :
    let _ := RegularLevel.chartedSpace P.smooth hreg
    ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ γ → Injective γ →
    (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model (Vector 7)) γ z)) →
    ∃ g : C(Hemisphere.Ambient 2, {y : S.Space // P.function y = a}),
      ContMDiff 𝓘(ℝ, Hemisphere.Ambient 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ g ∧
      (∀ z : Hemisphere.Sphere 1, g z.val = γ z) ∧
      Topology.IsClosedEmbedding (fun z : Hemisphere.Ball 2 => g z.val) ∧
      ∀ z : Hemisphere.Ball 2, Injective (mfderiv 𝓘(ℝ, Hemisphere.Ambient 2)
        𝓘(ℝ, RegularLevel.Model (Vector 7)) g z.val) := by
  let _ := RegularLevel.chartedSpace P.smooth hreg
  let _ := RegularLevel.isManifold P.smooth hreg
  change ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ γ → Injective γ →
    (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model (Vector 7)) γ z)) → _
  intro hγ hγi hγd
  let γM : C(Hemisphere.Sphere 1, S.Space) :=
    ⟨Subtype.val ∘ γ, continuous_subtype_val.comp γ.continuous⟩
  have hγM : ContMDiff (𝓡 1) (𝓡 7) ∞ γM :=
    (RegularLevel.contMDiff_inclusion P.smooth hreg).comp hγ
  have hγMi : Injective γM := Subtype.val_injective.comp hγi
  have hγMd (z : Hemisphere.Sphere 1) : Injective (mfderiv (𝓡 1) (𝓡 7) γM z) := by
    change Injective (mfderiv (𝓡 1) (𝓡 7) (Subtype.val ∘ γ) z)
    rw [mfderiv_comp z
      ((RegularLevel.contMDiff_inclusion P.smooth hreg).mdifferentiableAt (by simp))
      (hγ.mdifferentiableAt (by simp))]
    exact (RegularLevel.injective_mfderiv_inclusion P.smooth hreg (γ z)).comp (hγd z)
  obtain ⟨g, hg, hb, hemb, hgd⟩ := P.exists_embedded_positive_level_disk A ha hreg
    hhigh hlow γM hγM hγMi hγMd (fun z => (γ z).property)
  exact ⟨g, hg, fun z => Subtype.ext (hb z), hemb, hgd⟩

theorem exists_native_positive_level_circle_isotopy
    (A : AdaptedSurgeryWindows (Vector 7) P.function) {a : ℝ} (ha : 0 < a)
    (hreg : ∀ y, P.function y = a → y ∉ criticalPoints (Vector 7) P.function)
    (hhigh : ∀ p : criticalPoints (Vector 7) P.function, a ≤ P.function p →
      3 ≤ nativeMorseIndex (Vector 7) P.function p)
    (hlow : ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p → P.function p ≤ a →
      nativeMorseIndex (Vector 7) P.function p ≤ 4)
    (γ δ : C(Hemisphere.Sphere 1, {y : S.Space // P.function y = a})) :
    let _ := RegularLevel.chartedSpace P.smooth hreg
    ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ γ → Injective γ →
    (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model (Vector 7)) γ z)) →
    ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ δ → Injective δ →
    (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model (Vector 7)) δ z)) →
    ∃ Q : Diffeomorph 𝓘(ℝ, RegularLevel.Model (Vector 7)) 𝓘(ℝ, RegularLevel.Model (Vector 7))
        {y : S.Space // P.function y = a} {y : S.Space // P.function y = a} ∞,
      IsotopicToIdentity Q ∧ ∀ z, Q (γ z) = δ z := by
  let _ := RegularLevel.chartedSpace P.smooth hreg
  let _ := RegularLevel.isManifold P.smooth hreg
  let _ : CompactSpace {y : S.Space // P.function y = a} :=
    isCompact_iff_compactSpace.mp (isClosed_eq P.function.continuous continuous_const).isCompact
  change ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ γ → Injective γ →
    (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model (Vector 7)) γ z)) →
    ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ δ → Injective δ →
    (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model (Vector 7)) δ z)) → _
  intro hγ hγi hγd hδ hδi hδd
  obtain ⟨g, hg, hgb, hge, hgd⟩ :=
    P.exists_native_positive_level_circle_disk A ha hreg hhigh hlow γ hγ hγi hγd
  obtain ⟨h, hh, hhb, hhe, hhd⟩ :=
    P.exists_native_positive_level_circle_disk A ha hreg hhigh hlow δ hδ hδi hδd
  let _ := P.pathConnectedSpace_positive_level A ha hreg hhigh hlow (g 0)
  have hgi : InjOn g (closedBall (0 : Hemisphere.Ambient 2) 1) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hge.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hhi : InjOn h (closedBall (0 : Hemisphere.Ambient 2) 1) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hhe.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hcodim : Module.finrank ℝ (Hemisphere.Ambient 2) + 4 =
      Module.finrank ℝ (RegularLevel.Model (Vector 7)) := by
    simp [Hemisphere.Ambient, RegularLevel.Model, GLOrthonormalization.Vector]
  have hmodel : 2 ≤ Module.finrank ℝ (RegularLevel.Model (Vector 7)) := by
    simp [RegularLevel.Model, GLOrthonormalization.Vector]
  obtain ⟨Q, hQ, hformula⟩ := DiskShrinking.exists_embedded_disk_isotopy hg hh hgi hhi
    (fun x hx => hgd ⟨x, hx⟩) (fun x hx => hhd ⟨x, hx⟩) 4 (by omega) hcodim hmodel
  refine ⟨Q, hQ, ?_⟩
  intro z
  rw [← hgb z, hformula z.val (sphere_subset_closedBall z.property), hhb z]

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation
