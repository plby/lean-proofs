import Wikipedia.HopfProblem.DegreeCollapseTwoSphereGermComposition
import Wikipedia.HopfProblem.DegreeCollapseBeltMeridianTransversality

/-!
# Native transversality of the retained two-sphere germ

The general pole composition theorem keeps the tangent calculation opaque
to the Morse-chart data. The original disk's immersive and transverse
native derivatives therefore transfer to the retained sphere germ.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.BeltMeridianSphere

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ}

theorem retained_meridian_germ_derivative
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f)
    (L : Hemisphere.Ambient 2 ≃ₗᵢ[ℝ] (S.data p).chart.NegativeCoordinates)
    (v : sphere (0 : (S.data p).chart.PositiveCoordinates) 1)
    (s : unitInterval) (hs : (s : ℝ) ≤ 1 / 2) :
    let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
    ∀ γ : Hemisphere.Sphere 2 → (S.data p).UpperLevel,
      γ =ᶠ[𝓝 pole] (fun x => nativeBeltMeridianDisk S p v s hs (L (Hemisphere.tail x))) →
      (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) γ pole :
        Hemisphere.Ambient 2 →L[ℝ] RegularLevel.Model E) =
      (mfderiv 𝓘(ℝ, (S.data p).chart.NegativeCoordinates) 𝓘(ℝ, RegularLevel.Model E)
        (nativeBeltMeridianDisk S p v s hs) 0).comp
          (L.toContinuousLinearEquiv.toContinuousLinearMap.comp tailDerivative) := by
  let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
  dsimp only
  intro γ hgerm
  exact pole_germ_comp_derivative L (nativeBeltMeridianDisk S p v s hs)
    (nativeBeltMeridianDisk_smooth S hf p v s hs) γ hgerm

theorem retained_meridian_germ_transverse
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f) (n : ℕ)
    [Fact (Module.finrank ℝ (S.data p).chart.PositiveCoordinates = n + 1)]
    (L : Hemisphere.Ambient 2 ≃ₗᵢ[ℝ] (S.data p).chart.NegativeCoordinates)
    (v : sphere (0 : (S.data p).chart.PositiveCoordinates) 1)
    (s : unitInterval) (hs : (s : ℝ) ≤ 1 / 2) (hs0 : 0 < (s : ℝ)) :
    let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
    ∀ γ : Hemisphere.Sphere 2 → (S.data p).UpperLevel,
      γ =ᶠ[𝓝 pole] (fun x => nativeBeltMeridianDisk S p v s hs (L (Hemisphere.tail x))) →
      Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) γ pole) ∧
      Surjective ((mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) γ pole).coprod
        (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) (S.data p).surgery.beltSphere v)) := by
  let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
  dsimp only
  intro γ hgerm
  let N := (S.data p).chart.NegativeCoordinates
  let G := RegularLevel.Model E
  let F : Hemisphere.Ambient 2 →L[ℝ] G := mfderiv (𝓡 2) 𝓘(ℝ, G) γ pole
  let A : N →L[ℝ] G := mfderiv 𝓘(ℝ, N) 𝓘(ℝ, G) (nativeBeltMeridianDisk S p v s hs) 0
  let B : EuclideanSpace ℝ (Fin n) →L[ℝ] G :=
    mfderiv (𝓡 n) 𝓘(ℝ, G) (S.data p).surgery.beltSphere v
  let T : Hemisphere.Ambient 2 →L[ℝ] N :=
    L.toContinuousLinearEquiv.toContinuousLinearMap.comp tailDerivative
  have hF : F = A.comp T := retained_meridian_germ_derivative S hf p L v s hs γ hgerm
  have hA : Injective A := nativeBeltMeridianDisk_immersive S hf p v s hs hs0 0
  have hAB : Surjective (A.coprod B) := nativeBeltMeridianDisk_transverse S hf p n v s hs hs0
  have hTi : Injective T := L.injective.comp tail_mfderiv_bijective.1
  have hTs : Surjective T := L.surjective.comp tail_mfderiv_bijective.2
  change Injective F ∧ Surjective (F.coprod B)
  exact injective_transverse_of_comp F A B T hF hA hAB hTi hTs

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.BeltMeridianSphere
