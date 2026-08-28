import Wikipedia.NoExoticSixSphere.TimeCollarRadialAnnulus
import Wikipedia.NoExoticSixSphere.VariableAnnulusCollarSmoothing
import Wikipedia.NoExoticSixSphere.IntegralKernelDiskExtension

/-!
# Collared annuli from equality of the actual integral images

Two-connectedness of the nonnegative half turns equality of the integral
sphere classes into an actual homotopy. Prescribed positive collars can
then be glued to a positive interior cylinder. Smooth ambient extensions
of those collars give a smooth annulus retaining narrower collars exactly.
Constructing the native gradient collars and their boundary derivatives
remains a separate geometric step.
-/

noncomputable section

open Set Metric
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse TimeCollar
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology

namespace TimeCollarAnnulus

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B]
  (t : M → ℝ) (C : TimeCollar t B)
  [SimplyConnectedSpace (NonnegativeHalf t)] (w : NonnegativeHalf t)
  [hW₂ : Subsingleton (π_ 2 (NonnegativeHalf t) w)]

include C w hW₂ in
theorem exists_annulus_of_integral_relation
    (f₀ f₁ : C(Sphere 3, {x : M // t x = 0}))
    (hclass : singularHomologyMap (TimeCollarDisk.zeroToHalf t) 3
      (SmoothCube.integralSphereClass f₀) =
      singularHomologyMap (TimeCollarDisk.zeroToHalf t) 3 (SmoothCube.integralSphereClass f₁))
    (ρ₀ ρ₁ : ℝ) (hρ₀ : 1 < ρ₀) (hρ : ρ₀ < ρ₁) (hρ₁ : ρ₁ < 2)
    (g₀ g₁ : Vector 4 → M)
    (hg₀ : ContinuousOn g₀ {x | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ ρ₀})
    (hg₁ : ContinuousOn g₁ {x | ρ₁ ≤ ‖x‖ ∧ ‖x‖ ≤ 2})
    (hb₀ : ∀ s : Sphere 3, g₀ s.val = (f₀ s).val)
    (hb₁ : ∀ s : Sphere 3, g₁ ((2 : ℝ) • s.val) = (f₁ s).val)
    (hp₀ : ∀ x, 1 < ‖x‖ → ‖x‖ ≤ ρ₀ → 0 < t (g₀ x))
    (hp₁ : ∀ x, ρ₁ ≤ ‖x‖ → ‖x‖ < 2 → 0 < t (g₁ x)) :
    ∃ G : C(SphereAnnulus.domain 3, M),
      (∀ x : SphereAnnulus.domain 3, ‖x.val‖ ≤ ρ₀ → G x = g₀ x.val) ∧
      (∀ x : SphereAnnulus.domain 3, ρ₁ ≤ ‖x.val‖ → G x = g₁ x.val) ∧
      ∀ x : SphereAnnulus.domain 3, 1 < ‖x.val‖ → ‖x.val‖ < 2 → 0 < t (G x) := by
  have he : SmoothCube.integralSphereClass ((TimeCollarDisk.zeroToHalf t).comp f₀) =
      SmoothCube.integralSphereClass ((TimeCollarDisk.zeroToHalf t).comp f₁) := by
    rw [SmoothCube.integralSphereClass_comp, SmoothCube.integralSphereClass_comp]
    exact hclass
  obtain ⟨H⟩ := (SmoothCube.integralSphereClass_eq_iff_homotopic w _ _).mp he
  exact exists_annulus_with_prescribed_collars t C (spherePole 3) f₀ f₁ H
    ρ₀ ρ₁ hρ₀ hρ hρ₁ g₀ g₁ hg₀ hg₁ hb₀ hb₁ hp₀ hp₁

end TimeCollarAnnulus

namespace EuclideanEmbedding

variable {n : ℕ} {M B : Type} [TopologicalSpace M] [TopologicalSpace B]
  [ChartedSpace (Vector n) M] [IsManifold (𝓡 n) ∞ M]
  (e : EuclideanEmbedding n M) (t : C(M, ℝ)) (C : TimeCollar t B)
  [SimplyConnectedSpace (NonnegativeHalf t)] (w : NonnegativeHalf t)
  [hW₂ : Subsingleton (π_ 2 (NonnegativeHalf t) w)]

include C w hW₂ in
theorem exists_smooth_annulus_of_integral_relation_and_collars
    (f₀ f₁ : C(Sphere 3, {x : M // t x = 0}))
    (hclass : singularHomologyMap (TimeCollarDisk.zeroToHalf t) 3
      (SmoothCube.integralSphereClass f₀) =
      singularHomologyMap (TimeCollarDisk.zeroToHalf t) 3 (SmoothCube.integralSphereClass f₁))
    (ρ₀ ρ₁ : ℝ) (hρ₀ : 1 < ρ₀) (hρ : ρ₀ < ρ₁) (hρ₁ : ρ₁ < 2)
    (g₀ g₁ : Vector 4 → M)
    (hg₀ : ContinuousOn g₀ {x | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ ρ₀})
    (hg₁ : ContinuousOn g₁ {x | ρ₁ ≤ ‖x‖ ∧ ‖x‖ ≤ 2})
    (hb₀ : ∀ s : Sphere 3, g₀ s.val = (f₀ s).val)
    (hb₁ : ∀ s : Sphere 3, g₁ ((2 : ℝ) • s.val) = (f₁ s).val)
    (hp₀ : ∀ x, 1 < ‖x‖ → ‖x‖ ≤ ρ₀ → 0 < t (g₀ x))
    (hp₁ : ∀ x, ρ₁ ≤ ‖x‖ → ‖x‖ < 2 → 0 < t (g₁ x))
    (H₀ H₁ : C(Vector 4, Vector e.ambientDimension))
    (hH₀ : ContDiff ℝ ∞ H₀) (hH₁ : ContDiff ℝ ∞ H₁)
    (h₀ : ∀ x ∈ SphereAnnulus.domain 3, ‖x‖ ≤ ρ₀ → H₀ x = e.toFun (g₀ x))
    (h₁ : ∀ x ∈ SphereAnnulus.domain 3, ρ₁ ≤ ‖x‖ → H₁ x = e.toFun (g₁ x)) :
    ∃ g : Vector 4 → M,
      (∀ x ∈ SphereAnnulus.domain 3, ContMDiffAt (𝓡 4) (𝓡 n) ∞ g x) ∧
      (∀ x : Vector 4, 1 < ‖x‖ → ‖x‖ < 2 → 0 < t (g x)) ∧
      ∃ σ₀ σ₁ : ℝ, 1 < σ₀ ∧ σ₀ < ρ₀ ∧ ρ₁ < σ₁ ∧ σ₁ < 2 ∧
        (∀ x ∈ SphereAnnulus.domain 3, ‖x‖ ≤ σ₀ → g x = g₀ x) ∧
        ∀ x ∈ SphereAnnulus.domain 3, σ₁ ≤ ‖x‖ → g x = g₁ x := by
  let : Nonempty M := ⟨(f₀ (spherePole 3)).val⟩
  obtain ⟨G, hG₀, hG₁, hGp⟩ := TimeCollarAnnulus.exists_annulus_of_integral_relation
    t C w f₀ f₁ hclass ρ₀ ρ₁ hρ₀ hρ hρ₁ g₀ g₁ hg₀ hg₁ hb₀ hb₁ hp₀ hp₁
  let σ₀ := (1 + ρ₀) / 2
  let σ₁ := (ρ₁ + 2) / 2
  have hσ₀ : 1 < σ₀ := by dsimp only [σ₀]; linarith
  have hσ₀ρ₀ : σ₀ < ρ₀ := by dsimp only [σ₀]; linarith
  have hρ₁σ₁ : ρ₁ < σ₁ := by dsimp only [σ₁]; linarith
  have hσ₁ : σ₁ < 2 := by dsimp only [σ₁]; linarith
  obtain ⟨g, hgs, hgc, hgp⟩ := e.exists_smooth_annulus_with_collars_of_radii
    σ₀ ρ₀ ρ₁ σ₁ hσ₀ hσ₀ρ₀ hρ hρ₁σ₁ hσ₁ G H₀ H₁ hH₀ hH₁
    (fun x hx ↦ (h₀ x.val x.property hx).trans (congrArg e.toFun (hG₀ x hx)).symm)
    (fun x hx ↦ (h₁ x.val x.property hx).trans (congrArg e.toFun (hG₁ x hx)).symm)
    {x | 0 < t x} (isOpen_lt continuous_const t.continuous) hGp
  refine ⟨g, hgs, hgp, σ₀, σ₁, hσ₀, hσ₀ρ₀, hρ₁σ₁, hσ₁, ?_, ?_⟩
  · intro x hx hrx
    exact (hgc ⟨x, hx⟩ (Or.inl hrx)).trans (hG₀ ⟨x, hx⟩ (hrx.trans hσ₀ρ₀.le))
  · intro x hx hrx
    exact (hgc ⟨x, hx⟩ (Or.inr hrx)).trans (hG₁ ⟨x, hx⟩ (hρ₁σ₁.le.trans hrx))

end EuclideanEmbedding
end NoExoticSixSphere
