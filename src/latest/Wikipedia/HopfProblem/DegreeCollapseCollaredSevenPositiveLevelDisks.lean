import Wikipedia.HopfProblem.DegreeCollapsePositiveLevelDisks
import Wikipedia.HopfProblem.DegreeCollapsePositiveLevelPaths
import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenExcellentMorse
import Wikipedia.HopfProblem.DegreeCollapseTimeCollarInterior

/-!
# Native positive-level disks in the original seven-dimensional state

The actual collar identifies the strict positive interior up to homotopy
with the original simply connected half. All endpoint dimension bounds
below the chosen positive regular level concern positive critical points
only. The untouched negative Morse data and the original boundary atlas
are unrestricted. The resulting disk is embedded in the original native
regular level, not merely in the ambient state.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization MorseCancellation
open Wikipedia.SmoothSixDPoincare ManifoldMorse

variable {B : Type} [TopologicalSpace B] {S : CollaredSevenState B}
  (P : S.ExcellentMorsePresentation)

theorem pathConnectedSpace_positive_level
    (A : AdaptedSurgeryWindows (Vector 7) P.function) {a : ℝ} (ha : 0 < a)
    (hreg : ∀ y, P.function y = a → y ∉ criticalPoints (Vector 7) P.function)
    (hhigh : ∀ p : criticalPoints (Vector 7) P.function, a ≤ P.function p →
      3 ≤ nativeMorseIndex (Vector 7) P.function p)
    (hlow : ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p → P.function p ≤ a →
      nativeMorseIndex (Vector 7) P.function p ≤ 4)
    (z₀ : {y : S.Space // P.function y = a}) :
    PathConnectedSpace {y : S.Space // P.function y = a} := by
  let : SimplyConnectedSpace S.collar.positiveInterior :=
    S.collar.interiorHalfHomotopyEquiv.simplyConnectedSpace
  apply A.pathConnectedSpace_regular_level_above_cut P.smooth S.collar.positiveInterior
    (fun x => (P.positive_iff x).symm) ha hreg (d := 4) ?_ hlow
    (by simp [GLOrthonormalization.Vector]) z₀
  intro p hp
  have hh := hhigh p hp
  simp only [GLOrthonormalization.Vector, finrank_euclideanSpace_fin] at hh ⊢
  omega

theorem exists_embedded_positive_level_disk
    (A : AdaptedSurgeryWindows (Vector 7) P.function) {a : ℝ} (ha : 0 < a)
    (hreg : ∀ y, P.function y = a → y ∉ criticalPoints (Vector 7) P.function)
    (hhigh : ∀ p : criticalPoints (Vector 7) P.function, a ≤ P.function p →
      3 ≤ nativeMorseIndex (Vector 7) P.function p)
    (hlow : ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p → P.function p ≤ a →
      nativeMorseIndex (Vector 7) P.function p ≤ 4)
    (γ : C(Hemisphere.Sphere 1, S.Space)) (hγ : ContMDiff (𝓡 1) (𝓡 7) ∞ γ)
    (hγinj : Injective γ) (hγderiv : ∀ z, Injective (mfderiv (𝓡 1) (𝓡 7) γ z))
    (hlevel : ∀ z, P.function (γ z) = a) :
    let _ := RegularLevel.chartedSpace P.smooth hreg
    ∃ g : C(Hemisphere.Ambient 2, {y : S.Space // P.function y = a}),
      ContMDiff 𝓘(ℝ, Hemisphere.Ambient 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ g ∧
      (∀ z : Hemisphere.Sphere 1, (g z.val).val = γ z) ∧
      Topology.IsClosedEmbedding (fun z : Hemisphere.Ball 2 => g z.val) ∧
      ∀ z : Hemisphere.Ball 2, Injective (mfderiv 𝓘(ℝ, Hemisphere.Ambient 2)
        𝓘(ℝ, RegularLevel.Model (Vector 7)) g z.val) := by
  let : SimplyConnectedSpace S.collar.positiveInterior :=
    S.collar.interiorHalfHomotopyEquiv.simplyConnectedSpace
  apply exists_embedded_regular_level_disk_above_cut A P.smooth S.collar.positiveInterior
    (fun x => (P.positive_iff x).symm) ha hreg (d := 4) ?_ hlow
    (by simp [GLOrthonormalization.Vector]) (by simp [GLOrthonormalization.Vector])
    γ hγ hγinj hγderiv hlevel
  intro p hp
  have hh := hhigh p hp
  simp only [GLOrthonormalization.Vector, finrank_euclideanSpace_fin] at hh ⊢
  omega

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation
