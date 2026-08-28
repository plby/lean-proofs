import Wikipedia.NoExoticSixSphere.RelativeRegularCylinderReduction
import Wikipedia.NoExoticSixSphere.SardRegularValues
import Wikipedia.NoExoticSixSphere.SmoothCollaredSphereHomotopy

/-!
# Globally regular collared representatives

The proved density of regular values discharges the nearby-value premise
of the endpoint-preserving correction. Relative smooth approximation then
gives a globally regular collared cylinder from any continuous homotopy
between smooth endpoint maps with the specified regular value. The
homotopy class relative to both endpoint slices is preserved.

This constructs the regular cylinder; its induced framing and the framed
bordism comparison are separate steps.
-/

open scoped Manifold ContDiff
open Set

namespace NoExoticSixSphere

variable {B : Type} {H M : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [SecondCountableTopology M]

theorem exists_regularCylinderCorrection {n : ℕ}
    (F : C(ℝ × M, Sphere n)) (hF : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (𝓡 n) ∞ F)
    (f₀ f₁ : C(M, Sphere n)) (h₀ : ContMDiff I (𝓡 n) ∞ f₀) (h₁ : ContMDiff I (𝓡 n) ∞ f₁)
    (hleft : ∀ t ≤ (1 / 4 : ℝ), ∀ x, F (t, x) = f₀ x)
    (hright : ∀ t, (3 / 4 : ℝ) ≤ t → ∀ x, F (t, x) = f₁ x)
    (b : Sphere n)
    (hreg₀ : ∀ x, f₀ x = b → Function.Surjective (mfderiv I (𝓡 n) f₀ x))
    (hreg₁ : ∀ x, f₁ x = b → Function.Surjective (mfderiv I (𝓡 n) f₁ x)) :
    ∃ d : RegularCollaredCylinder (M := M) I (𝓡 n) b 0 1,
      d.leftMap = f₀ ∧ d.rightMap = f₁ ∧
      Nonempty (F.HomotopyRel d.map {p | p.1 ≤ 1 / 8 ∨ 7 / 8 ≤ p.1}) := by
  obtain ⟨ε, hε, hcorrect⟩ :=
    exists_regularCylinderCorrectionRadius F hF f₀ f₁ h₀ h₁ hleft hright b hreg₀ hreg₁
  obtain ⟨c, hreg, hc⟩ := (Sard.dense_regularValues hF).exists_mem_open
    Metric.isOpen_ball (show (Metric.ball b ε).Nonempty from ⟨b, Metric.mem_ball_self hε⟩)
  exact hcorrect c hc hreg

theorem exists_regularCollaredCylinder [T2Space M] {n : ℕ} {f₀ f₁ : C(M, Sphere n)}
    (h₀ : ContMDiff I (𝓡 n) ∞ f₀) (h₁ : ContMDiff I (𝓡 n) ∞ f₁)
    (H : f₀.Homotopy f₁) (b : Sphere n)
    (hreg₀ : ∀ x, f₀ x = b → Function.Surjective (mfderiv I (𝓡 n) f₀ x))
    (hreg₁ : ∀ x, f₁ x = b → Function.Surjective (mfderiv I (𝓡 n) f₁ x)) :
    ∃ d : RegularCollaredCylinder (M := M) I (𝓡 n) b 0 1,
      d.leftMap = f₀ ∧ d.rightMap = f₁ ∧
      H.toContinuousMap.HomotopicRel (d.map.comp CylinderTime.inclusion) CylinderTime.boundary := by
  obtain ⟨F, hF, hleft, hright, hhom⟩ := exists_smoothCollaredSphereHomotopy h₀ h₁ H
  obtain ⟨d, hd₀, hd₁, ⟨K⟩⟩ :=
    exists_regularCylinderCorrection F hF f₀ f₁ h₀ h₁ hleft hright b hreg₀ hreg₁
  refine ⟨d, hd₀, hd₁, hhom.trans ?_⟩
  let K' : (F.comp CylinderTime.inclusion).HomotopyRel
      (d.map.comp CylinderTime.inclusion) CylinderTime.boundary :=
    { toHomotopy := K.toHomotopy.compContinuousMap CylinderTime.inclusion
      prop' := fun t p hp ↦ K.eq_fst t (by
        change (p.1 : ℝ) ≤ 1 / 8 ∨ 7 / 8 ≤ (p.1 : ℝ)
        rcases hp with hp | hp
        · left
          rw [hp]
          norm_num
        · right
          rw [hp]
          norm_num) }
  exact ⟨K'⟩

end NoExoticSixSphere
