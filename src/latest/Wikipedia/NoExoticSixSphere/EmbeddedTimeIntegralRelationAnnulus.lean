import Wikipedia.NoExoticSixSphere.EmbeddedTimePositiveAnnulusCollars
import Wikipedia.NoExoticSixSphere.IntegralRelationCollaredAnnulus
import Wikipedia.NoExoticSixSphere.AnnulusDerivativeUniqueness

/-!
# An actual native smooth annulus from equal integral images

Construct both gradient collars, transfer the integral relation to a
homotopy in the two-connected half, glue in positive time, and smooth
relative to both collars. Unique within-derivatives on the closed annulus
retain the actual boundary differentials. No smooth annulus, genericity,
boundary immersion, or radial time signs are supplied as extra hypotheses.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.EmbeddedTime

open GLOrthonormalization SphereAnnulus
open Wikipedia.HopfProblem.DegreeCollapse TimeCollar
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {n : ℕ} {M B : Type} [TopologicalSpace M] [TopologicalSpace B]
  [ChartedSpace (Vector (n + 1)) M] [IsManifold (𝓡 (n + 1)) ∞ M]
  (e : EuclideanEmbedding (n + 1) M) (r : e.TubularRetraction) (t : C(M, ℝ))
  (ht : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ t)
  (hreg : ∀ x, t x = 0 → Surjective (mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) t x))
  (C : TimeCollar t B) [SimplyConnectedSpace (NonnegativeHalf t)] (w : NonnegativeHalf t)
  [hW₂ : Subsingleton (π_ 2 (NonnegativeHalf t) w)]

include r C w hW₂ in
theorem exists_smooth_annulus_of_integral_relation
    (f₀ f₁ : C(Sphere 3, {x : M // t x = 0}))
    (hclass : singularHomologyMap (TimeCollarDisk.zeroToHalf t) 3
      (SmoothCube.integralSphereClass f₀) =
      singularHomologyMap (TimeCollarDisk.zeroToHalf t) 3 (SmoothCube.integralSphereClass f₁)) :
    letI := zeroAtlas t ht hreg;
    ∀ (hf₀ : ContMDiff (𝓡 3) (𝓡 n) ∞ f₀) (hi₀ : Injective f₀)
      (hd₀ : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 n) f₀ s))
      (hf₁ : ContMDiff (𝓡 3) (𝓡 n) ∞ f₁) (hi₁ : Injective f₁)
      (hd₁ : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 n) f₁ s)),
      ∃ g : Vector 4 → M,
        (∀ x ∈ domain 3, ContMDiffAt (𝓡 4) (𝓡 (n + 1)) ∞ g x) ∧
        (∀ s : Sphere 3, g s.val = (f₀ s).val) ∧
        (∀ s : Sphere 3, g ((2 : ℝ) • s.val) = (f₁ s).val) ∧
        (∀ x : Vector 4, 1 < ‖x‖ → ‖x‖ < 2 → 0 < t (g x)) ∧
        (∀ s : Sphere 3, Injective (fderiv ℝ (e.toFun ∘ g) s.val) ∧
          Injective (fderiv ℝ (e.toFun ∘ g) ((2 : ℝ) • s.val))) ∧
        (∀ s : Sphere 3, 0 < fderiv ℝ (t ∘ g) s.val s.val) ∧
        ∀ s : Sphere 3, fderiv ℝ (t ∘ g) ((2 : ℝ) • s.val) ((2 : ℝ) • s.val) < 0 := by
  let := zeroAtlas t ht hreg
  intro hf₀ hi₀ hd₀ hf₁ hi₁ hd₁
  let b := spherePole 3
  obtain ⟨ρ₀, hρ₀, hρ₀small, hc₀, hp₀, H₀, hH₀, hH₀eq⟩ :=
    exists_positive_innerAnnulusCollar e r t ht hreg b f₀ hf₀ hi₀ hd₀
  obtain ⟨ρ₁, hρ₁large, hρ₁, hc₁, hp₁, H₁, hH₁, hH₁eq⟩ :=
    exists_positive_outerAnnulusCollar e r t ht hreg b f₁ hf₁ hi₁ hd₁
  have hρ : ρ₀ < ρ₁ := by linarith
  obtain ⟨g, hgs, hgp, σ₀, σ₁, hσ₀, hσ₀ρ₀, hρ₁σ₁, hσ₁, hgc₀, hgc₁⟩ :=
    e.exists_smooth_annulus_of_integral_relation_and_collars t C w f₀ f₁ hclass
      ρ₀ ρ₁ hρ₀ hρ hρ₁ (innerAnnulusCollar e r t b f₀) (outerAnnulusCollar e r t b f₁)
      (fun x hx ↦ (hc₀ x hx.1 hx.2).continuousAt.continuousWithinAt)
      (fun x hx ↦ (hc₁ x hx.1 hx.2).continuousAt.continuousWithinAt)
      (innerAnnulusCollar_coe e r t b f₀) (outerAnnulusCollar_double e r t b f₁)
      hp₀ hp₁ H₀ H₁ hH₀ hH₁
      (fun x hx hrx ↦ hH₀eq x hx.1 hrx) (fun x hx hrx ↦ hH₁eq x hrx hx.2)
  have hnorm₂ (s : Sphere 3) : ‖(2 : ℝ) • s.val‖ = 2 := by
    rw [norm_smul, ClosedHemisphere.unit_norm]
    norm_num
  have hx₀ (s : Sphere 3) : s.val ∈ domain 3 := by
    change 1 ≤ ‖s.val‖ ∧ ‖s.val‖ ≤ 2
    rw [ClosedHemisphere.unit_norm]
    norm_num
  have hx₁ (s : Sphere 3) : (2 : ℝ) • s.val ∈ domain 3 := by
    change 1 ≤ ‖(2 : ℝ) • s.val‖ ∧ ‖(2 : ℝ) • s.val‖ ≤ 2
    rw [hnorm₂]
    norm_num
  have hσs₀ (s : Sphere 3) : ‖s.val‖ < σ₀ := by
    rw [ClosedHemisphere.unit_norm]
    exact hσ₀
  have hσs₁ (s : Sphere 3) : σ₁ < ‖(2 : ℝ) • s.val‖ := by
    rw [hnorm₂]
    exact hσ₁
  have hcs₀ (s : Sphere 3) :
      ContMDiffAt (𝓡 4) (𝓡 (n + 1)) ∞ (innerAnnulusCollar e r t b f₀) s.val :=
    contMDiffAt_innerAnnulusCollar_coe e r t ht hreg b f₀ s hf₀
  have hcs₁ (s : Sphere 3) :
      ContMDiffAt (𝓡 4) (𝓡 (n + 1)) ∞ (outerAnnulusCollar e r t b f₁)
        ((2 : ℝ) • s.val) :=
    contMDiffAt_outerAnnulusCollar_double e r t ht hreg b f₁ s hf₁
  refine ⟨g, hgs, ?_, ?_, hgp, ?_, ?_, ?_⟩
  · intro s
    exact (hgc₀ s.val (hx₀ s) (hσs₀ s).le).trans (innerAnnulusCollar_coe e r t b f₀ s)
  · intro s
    exact (hgc₁ _ (hx₁ s) (hσs₁ s).le).trans (outerAnnulusCollar_double e r t b f₁ s)
  · intro s
    constructor
    · have heq := fderiv_eq_of_inner_collar (e.toFun ∘ g)
        (e.toFun ∘ innerAnnulusCollar e r t b f₀) σ₀
        (fun x hx hrx ↦ congrArg e.toFun (hgc₀ x hx hrx)) (hx₀ s) (hσs₀ s)
        ((e.smooth.contMDiffAt.comp s.val (hgs s.val (hx₀ s))).contDiffAt.differentiableAt
          (by simp))
        ((e.smooth.contMDiffAt.comp s.val (hcs₀ s)).contDiffAt.differentiableAt (by simp))
      rw [heq]
      exact injective_fderiv_innerAnnulusCollar_coe e r t ht hreg b f₀ s hf₀ hd₀
    · have heq := fderiv_eq_of_outer_collar (e.toFun ∘ g)
        (e.toFun ∘ outerAnnulusCollar e r t b f₁) σ₁
        (fun x hx hrx ↦ congrArg e.toFun (hgc₁ x hx hrx)) (hx₁ s) (hσs₁ s)
        ((e.smooth.contMDiffAt.comp _ (hgs _ (hx₁ s))).contDiffAt.differentiableAt (by simp))
        ((e.smooth.contMDiffAt.comp _ (hcs₁ s)).contDiffAt.differentiableAt (by simp))
      rw [heq]
      exact injective_fderiv_outerAnnulusCollar_double e r t ht hreg b f₁ s hf₁ hd₁
  · intro s
    have heq := fderiv_eq_of_inner_collar (t ∘ g) (t ∘ innerAnnulusCollar e r t b f₀) σ₀
      (fun x hx hrx ↦ congrArg t (hgc₀ x hx hrx)) (hx₀ s) (hσs₀ s)
      ((ht.contMDiffAt.comp s.val (hgs s.val (hx₀ s))).contDiffAt.differentiableAt (by simp))
      ((ht.contMDiffAt.comp s.val (hcs₀ s)).contDiffAt.differentiableAt (by simp))
    rw [heq]
    exact fderiv_time_innerAnnulusCollar_radial_pos e r t ht hreg b f₀ s hf₀
  · intro s
    have heq := fderiv_eq_of_outer_collar (t ∘ g) (t ∘ outerAnnulusCollar e r t b f₁) σ₁
      (fun x hx hrx ↦ congrArg t (hgc₁ x hx hrx)) (hx₁ s) (hσs₁ s)
      ((ht.contMDiffAt.comp _ (hgs _ (hx₁ s))).contDiffAt.differentiableAt (by simp))
      ((ht.contMDiffAt.comp _ (hcs₁ s)).contDiffAt.differentiableAt (by simp))
    rw [heq]
    exact fderiv_time_outerAnnulusCollar_radial_neg e r t ht hreg b f₁ s hf₁

end NoExoticSixSphere.EmbeddedTime
