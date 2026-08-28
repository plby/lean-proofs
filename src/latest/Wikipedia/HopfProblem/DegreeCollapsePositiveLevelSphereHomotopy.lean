import Wikipedia.HopfProblem.DegreeCollapsePositiveLevelPiTwo
import Wikipedia.HopfProblem.DegreeCollapseSphereFillingHomotopy

/-!
# Actual sphere homotopies in the original positive three/four level

Smooth approximation, the constructed level disk, and radial contraction
give a nullhomotopy for EVERY continuous two-sphere in this literal level.
Actual connectedness joins the disk centers. Smooth endpoint maps then
admit a jointly smooth homotopy stationary on both endpoint collars.
These are homotopies, not a yet-constructed family of embeddings.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization MorseCancellation SingularMayerVietoris
open Wikipedia.SmoothSixDPoincare ManifoldMorse

variable {B : Type} [TopologicalSpace B] [Subsingleton (SingularHomology B 2)]
  {S : CollaredSevenState B} (P : S.ExcellentMorsePresentation)

theorem positive_level_two_sphere_nullhomotopic
    (A : AdaptedSurgeryWindows (Vector 7) P.function) {a : ℝ} (ha : 0 < a)
    (hreg : ∀ y, P.function y = a → y ∉ criticalPoints (Vector 7) P.function)
    (hhigh : ∀ p : criticalPoints (Vector 7) P.function, a ≤ P.function p →
      4 ≤ nativeMorseIndex (Vector 7) P.function p)
    (hlow : ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p → P.function p ≤ a →
      nativeMorseIndex (Vector 7) P.function p ≤ 3)
    (γ : C(Hemisphere.Sphere 2, {y : S.Space // P.function y = a})) :
    ∃ c, γ.Homotopic (ContinuousMap.const _ c) := by
  let _ := RegularLevel.chartedSpace P.smooth hreg
  let _ := RegularLevel.isManifold P.smooth hreg
  obtain ⟨δ, hδ, hγδ⟩ := ManifoldSmoothing.exists_smooth_map_homotopic
    (I := 𝓡 2) (J := 𝓘(ℝ, RegularLevel.Model (Vector 7))) γ
  obtain ⟨D, hD⟩ := P.exists_native_positive_level_two_sphere_filling A ha hreg
    hhigh hlow δ hδ
  obtain ⟨c, hc⟩ := sphere_nullhomotopy_of_disk δ D hD
  exact ⟨c, hγδ.trans hc⟩

theorem positive_level_two_spheres_homotopic
    (A : AdaptedSurgeryWindows (Vector 7) P.function) {a : ℝ} (ha : 0 < a)
    (hreg : ∀ y, P.function y = a → y ∉ criticalPoints (Vector 7) P.function)
    (hhigh : ∀ p : criticalPoints (Vector 7) P.function, a ≤ P.function p →
      4 ≤ nativeMorseIndex (Vector 7) P.function p)
    (hlow : ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p → P.function p ≤ a →
      nativeMorseIndex (Vector 7) P.function p ≤ 3)
    (γ δ : C(Hemisphere.Sphere 2, {y : S.Space // P.function y = a})) :
    γ.Homotopic δ := by
  let : PathConnectedSpace {y : S.Space // P.function y = a} :=
    P.pathConnectedSpace_positive_level A ha hreg
      (fun p hp => (by decide : 3 ≤ 4).trans (hhigh p hp))
      (fun p hp hpa => (hlow p hp hpa).trans (by decide : 3 ≤ 4)) (γ (SphereCube.point 2))
  obtain ⟨c, hc⟩ := P.positive_level_two_sphere_nullhomotopic A ha hreg hhigh hlow γ
  obtain ⟨d, hd⟩ := P.positive_level_two_sphere_nullhomotopic A ha hreg hhigh hlow δ
  let σ := Joined.somePath (PathConnectedSpace.joined c d)
  let H : (ContinuousMap.const (Hemisphere.Sphere 2) c).Homotopy
      (ContinuousMap.const _ d) := {
    toFun := fun p => σ p.1
    continuous_toFun := σ.continuous.comp continuous_fst
    map_zero_left := fun _ => σ.source
    map_one_left := fun _ => σ.target }
  exact (hc.trans ⟨H⟩).trans hd.symm

theorem exists_smooth_positive_level_two_sphere_homotopy
    (A : AdaptedSurgeryWindows (Vector 7) P.function) {a : ℝ} (ha : 0 < a)
    (hreg : ∀ y, P.function y = a → y ∉ criticalPoints (Vector 7) P.function)
    (hhigh : ∀ p : criticalPoints (Vector 7) P.function, a ≤ P.function p →
      4 ≤ nativeMorseIndex (Vector 7) P.function p)
    (hlow : ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p → P.function p ≤ a →
      nativeMorseIndex (Vector 7) P.function p ≤ 3)
    (γ δ : C(Hemisphere.Sphere 2, {y : S.Space // P.function y = a})) :
    let _ := RegularLevel.chartedSpace P.smooth hreg
    ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ γ →
    ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ δ →
    ∃ H : γ.Homotopy δ,
      ContMDiff ((𝓡∂ 1).prod (𝓡 2)) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ H ∧
      (∀ t : unitInterval, ∀ x, (t : ℝ) ≤ 1 / 4 → H (t, x) = γ x) ∧
      ∀ t : unitInterval, ∀ x, 3 / 4 ≤ (t : ℝ) → H (t, x) = δ x := by
  let _ := RegularLevel.chartedSpace P.smooth hreg
  let _ := RegularLevel.isManifold P.smooth hreg
  change ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ γ →
    ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ δ → _
  intro hγ hδ
  obtain ⟨H⟩ := P.positive_level_two_spheres_homotopic A ha hreg hhigh hlow γ δ
  exact ManifoldSmoothing.exists_smooth_homotopy_with_collars hγ hδ H

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation
