import Wikipedia.HopfProblem.DegreeCollapsePositiveSphereFillings
import Wikipedia.HopfProblem.DegreeCollapseH2SphereNullhomotopy
import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenTerminalFilling
import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenPositiveLevelDisks

/-!
# Construct two-sphere fillings at the original positive three/four cut

The actual positive interior has zero second homology, inherited through
the original collar and half inclusion. Native Hurewicz gives an actual
nullhomotopy there. Dimension-three endpoint avoidance and the original
flow cylinder give a disk in the literal retained regular level. The
boundary is the entire original sphere map, point for point. The disk
is not asserted to be embedded, and no ambient isotopy is inferred.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState

open NoExoticSixSphere GLOrthonormalization MorseCancellation SingularMayerVietoris
open Wikipedia.SmoothSixDPoincare ManifoldMorse

variable {B : Type} [TopologicalSpace B] [Subsingleton (SingularHomology B 2)]
  {S : CollaredSevenState B}

theorem positiveInterior_second_homology (S : CollaredSevenState B) :
    Subsingleton (SingularHomology S.collar.positiveInterior 2) := by
  let : Subsingleton (SingularHomology S.Half 2) := S.half_second_homology
  exact (S.collar.interiorToHalf_homology_bijective 2).injective.subsingleton

theorem positiveInterior_two_sphere_nullhomotopic (S : CollaredSevenState B)
    (γ : C(Hemisphere.Sphere 2, S.collar.positiveInterior)) :
    γ.HomotopicRel (ContinuousMap.const _ (γ (SphereCube.point 2))) {SphereCube.point 2} := by
  let : SimplyConnectedSpace S.collar.positiveInterior :=
    S.collar.interiorHalfHomotopyEquiv.simplyConnectedSpace
  let : Subsingleton (SingularHomology S.collar.positiveInterior 2) :=
    S.positiveInterior_second_homology
  exact two_sphere_nullhomotopic_of_homology γ

namespace ExcellentMorsePresentation

variable (P : S.ExcellentMorsePresentation)

theorem exists_positive_level_two_sphere_filling
    (A : AdaptedSurgeryWindows (Vector 7) P.function) {a : ℝ} (ha : 0 < a)
    (hreg : ∀ y, P.function y = a → y ∉ criticalPoints (Vector 7) P.function)
    (hhigh : ∀ p : criticalPoints (Vector 7) P.function, a ≤ P.function p →
      4 ≤ nativeMorseIndex (Vector 7) P.function p)
    (hlow : ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p → P.function p ≤ a →
      nativeMorseIndex (Vector 7) P.function p ≤ 3)
    (γ : C(Hemisphere.Sphere 2, S.Space)) (hγ : ContMDiff (𝓡 2) (𝓡 7) ∞ γ)
    (hlevel : ∀ z, P.function (γ z) = a) :
    ∃ D : C(Hemisphere.Ball 3, {y : S.Space // P.function y = a}),
      ∀ z : Hemisphere.Sphere 2,
        (D ⟨z.val, Metric.sphere_subset_closedBall z.property⟩).val = γ z := by
  let γU : C(Hemisphere.Sphere 2, S.collar.positiveInterior) :=
    ⟨fun z => ⟨γ z, (P.positive_iff (γ z)).mp (by rw [hlevel]; exact ha)⟩,
      γ.continuous.subtype_mk _⟩
  have hγU : ContMDiff (𝓡 2) (𝓡 7) ∞ γU :=
    (ContMDiff.subtypeVal_comp_iff S.collar.positiveInterior γU).mp hγ
  have hnull : ∃ c : S.collar.positiveInterior, γU.Homotopic (ContinuousMap.const _ c) :=
    ⟨γU (SphereCube.point 2), (S.positiveInterior_two_sphere_nullhomotopic γU).homotopic⟩
  apply exists_actual_sphere_filling_at_level_above_cut A P.smooth
    S.collar.positiveInterior (fun x => (P.positive_iff x).symm) hreg
    (d := 3) ?_ hlow (by simp) (by simp) γU hγU hnull hlevel
  intro p hp
  have hh := hhigh p hp
  simp only [GLOrthonormalization.Vector, finrank_euclideanSpace_fin] at hh ⊢
  omega

theorem exists_native_positive_level_two_sphere_filling
    (A : AdaptedSurgeryWindows (Vector 7) P.function) {a : ℝ} (ha : 0 < a)
    (hreg : ∀ y, P.function y = a → y ∉ criticalPoints (Vector 7) P.function)
    (hhigh : ∀ p : criticalPoints (Vector 7) P.function, a ≤ P.function p →
      4 ≤ nativeMorseIndex (Vector 7) P.function p)
    (hlow : ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p → P.function p ≤ a →
      nativeMorseIndex (Vector 7) P.function p ≤ 3)
    (γ : C(Hemisphere.Sphere 2, {y : S.Space // P.function y = a})) :
    let _ := RegularLevel.chartedSpace P.smooth hreg
    ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ γ →
    ∃ D : C(Hemisphere.Ball 3, {y : S.Space // P.function y = a}),
      ∀ z : Hemisphere.Sphere 2,
        D ⟨z.val, Metric.sphere_subset_closedBall z.property⟩ = γ z := by
  let _ := RegularLevel.chartedSpace P.smooth hreg
  change ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ γ → _
  intro hγ
  let γM : C(Hemisphere.Sphere 2, S.Space) :=
    ⟨Subtype.val ∘ γ, continuous_subtype_val.comp γ.continuous⟩
  have hγM : ContMDiff (𝓡 2) (𝓡 7) ∞ γM :=
    (RegularLevel.contMDiff_inclusion P.smooth hreg).comp hγ
  obtain ⟨D, hD⟩ := P.exists_positive_level_two_sphere_filling A ha hreg hhigh hlow
    γM hγM (fun z => (γ z).property)
  exact ⟨D, fun z => Subtype.ext (hD z)⟩

end ExcellentMorsePresentation
end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState
