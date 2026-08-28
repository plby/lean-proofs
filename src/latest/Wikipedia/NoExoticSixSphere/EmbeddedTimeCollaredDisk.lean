import Wikipedia.NoExoticSixSphere.EmbeddedTimeSphereCollarAnnulus
import Wikipedia.NoExoticSixSphere.TimeCollarRadialDisk
import Wikipedia.NoExoticSixSphere.VariableDiskCollarSmoothing
import Wikipedia.NoExoticSixSphere.ClosedDiskCollarDerivative
import Wikipedia.NoExoticSixSphere.IntegralKernelDiskExtension

/-!
# Actual smooth collared disks from integral kernel classes in a framed half

Construct the inward collar from the original embedding and time-gradient,
fill its inner sphere in the positive interior, glue, and smooth relative
to a smaller exact collar. The resulting disk has the original boundary,
positive interior time, strictly negative radial boundary time derivative,
and an injective immersive outer annulus. Interior genericity remains separate.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.EmbeddedTime

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse
open DiskCylinder TimeCollar
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {n p : ℕ} {M B : Type} [TopologicalSpace M] [TopologicalSpace B]
  [ChartedSpace (Vector (n + 1)) M] [IsManifold (𝓡 (n + 1)) ∞ M]
  (e : EuclideanEmbedding (n + 1) M) (r : e.TubularRetraction) (t : C(M, ℝ))
  (ht : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ t)
  (hreg : ∀ x, t x = 0 → Surjective (mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) t x))
  (C : TimeCollar t B)

include C in
theorem exists_smooth_disk_of_half_extension (b : NoExoticSixSphere.Sphere p)
    (f : C(NoExoticSixSphere.Sphere p, {x : M // t x = 0}))
    (F : C(Disk (E := Vector (p + 1)), NonnegativeHalf t))
    (hF : ∀ s, F (boundaryToDisk s) = TimeCollarDisk.zeroToHalf t (f s)) :
    letI := zeroAtlas t ht hreg;
    ContMDiff (𝓡 p) (𝓡 n) ∞ f → Injective f →
      (∀ s, Injective (mfderiv (𝓡 p) (𝓡 n) f s)) →
      ∃ g : Vector (p + 1) → M,
        (∀ x ∈ closedBall 0 1, ContMDiffAt (𝓡 (p + 1)) (𝓡 (n + 1)) ∞ g x) ∧
        (∀ s : NoExoticSixSphere.Sphere p, g s.val = (f s).val) ∧
        (∀ x ∈ ball 0 1, 0 < t (g x)) ∧
        (∀ s : NoExoticSixSphere.Sphere p, fderiv ℝ (t ∘ g) s.val s.val < 0) ∧
        ∃ τ : ℝ, 0 < τ ∧ τ < 1 ∧
          EqOn g (sphereCollar e r t b f) (closedBall 0 1 ∩ {x | τ ≤ ‖x‖}) ∧
          InjOn g (closedBall 0 1 ∩ {x | τ ≤ ‖x‖}) ∧
          ∀ x ∈ closedBall 0 1, τ ≤ ‖x‖ → Injective (fderiv ℝ (e.toFun ∘ g) x) := by
  let := zeroAtlas t ht hreg
  intro hf hi hd
  let : Nonempty M := ⟨(f b).val⟩
  obtain ⟨ρ, hρ, hρ1, hcs, hci, hcd, hcp, H, hH, hHeq⟩ :=
    exists_positive_embedded_sphereCollar_annulus e r t ht hreg b f hf hi hd
  have hcc : ContinuousOn (sphereCollar e r t b f)
      (closedBall (0 : Vector (p + 1)) 1 ∩ {x | ρ ≤ ‖x‖}) :=
    fun x hx ↦ (hcs x hx.1 hx.2).continuousAt.continuousWithinAt
  obtain ⟨G, hGb, hGp, hGc⟩ := TimeCollarDisk.exists_disk_with_prescribed_annulus
    t C b f F hF ρ hρ hρ1 (sphereCollar e r t b f) hcc
    (sphereCollar_coe e r t b f) hcp
  let σ := (ρ + 1) / 2
  have hρσ : ρ < σ := by dsimp only [σ]; linarith
  have hσ1 : σ < 1 := by dsimp only [σ]; linarith
  have hHG (x : Disk (E := Vector (p + 1))) (hx : ρ ≤ ‖x.val‖) :
      H x.val = e.toFun (G x) := (hHeq ⟨x.property, hx⟩).trans (congrArg e.toFun (hGc x hx)).symm
  obtain ⟨g, hgs, hgc, hgp⟩ := e.exists_smooth_disk_with_collar_of_radii ρ σ hρ hρσ hσ1
    G H hH hHG {x | 0 < t x} (isOpen_lt continuous_const t.continuous) hGp
  have hgc' (x : Vector (p + 1)) (hx : x ∈ closedBall 0 1) (hσx : σ ≤ ‖x‖) :
      g x = sphereCollar e r t b f x :=
    (hgc ⟨x, hx⟩ hσx).trans (hGc ⟨x, hx⟩ (hρσ.le.trans hσx))
  have hboundary (s : NoExoticSixSphere.Sphere p) : g s.val = (f s).val :=
    (hgc' s.val (sphere_subset_closedBall s.property)
      (by rw [ClosedHemisphere.unit_norm]; exact hσ1.le)).trans (sphereCollar_coe e r t b f s)
  have hheight (s : NoExoticSixSphere.Sphere p) : fderiv ℝ (t ∘ g) s.val s.val < 0 := by
    have hx := sphere_subset_closedBall s.property
    have hσx : σ < ‖s.val‖ := by rw [ClosedHemisphere.unit_norm]; exact hσ1
    have heq := fderiv_eq_of_closedBall_collar (t ∘ g) (t ∘ sphereCollar e r t b f) σ
      (fun x hx hrx ↦ congrArg t (hgc' x hx hrx)) hx hσx
      ((ht.contMDiffAt.comp s.val (hgs s.val hx)).contDiffAt.differentiableAt (by simp))
      ((ht.contMDiffAt.comp s.val
        (hcs s.val hx (hρσ.le.trans hσx.le))).contDiffAt.differentiableAt (by simp))
    rw [heq]
    exact fderiv_time_sphereCollar_radial_neg e r t ht hreg b f s hf
  let τ := (σ + 1) / 2
  have hστ : σ < τ := by dsimp only [τ]; linarith
  have hτ : 0 < τ := hρ.trans (hρσ.trans hστ)
  have hτ1 : τ < 1 := by dsimp only [τ]; linarith
  refine ⟨g, hgs, hboundary, hgp, hheight, τ, hτ, hτ1,
    fun x hx ↦ hgc' x hx.1 (hστ.le.trans hx.2), ?_, ?_⟩
  · intro x hx y hy heq
    apply hci ⟨hx.1, (hρσ.le.trans hστ.le).trans hx.2⟩
      ⟨hy.1, (hρσ.le.trans hστ.le).trans hy.2⟩
    rw [← hgc' x hx.1 (hστ.le.trans hx.2), ← hgc' y hy.1 (hστ.le.trans hy.2)]
    exact heq
  · intro x hx hτx
    have hσx : σ < ‖x‖ := hστ.trans_le hτx
    have hρx : ρ ≤ ‖x‖ := hρσ.le.trans hσx.le
    have heq := fderiv_eq_of_closedBall_collar (e.toFun ∘ g)
      (e.toFun ∘ sphereCollar e r t b f) σ
      (fun y hy hry ↦ congrArg e.toFun (hgc' y hy hry)) hx hσx
      ((e.smooth.contMDiffAt.comp x (hgs x hx)).contDiffAt.differentiableAt (by simp))
      ((e.smooth.contMDiffAt.comp x (hcs x hx hρx)).contDiffAt.differentiableAt (by simp))
    rw [heq]
    exact hcd x hx hρx

variable [SimplyConnectedSpace (NonnegativeHalf t)] (w : NonnegativeHalf t)
  [hW₂ : Subsingleton (π_ 2 (NonnegativeHalf t) w)]

include C w hW₂ in
theorem exists_smooth_disk_of_integral_kernel
    (f : C(NoExoticSixSphere.Sphere 3, {x : M // t x = 0}))
    (hker : singularHomologyMap (TimeCollarDisk.zeroToHalf t) 3
      (SmoothCube.integralSphereClass f) = 0) : letI := zeroAtlas t ht hreg;
    ContMDiff (𝓡 3) (𝓡 n) ∞ f → Injective f →
      (∀ s, Injective (mfderiv (𝓡 3) (𝓡 n) f s)) →
      ∃ g : Vector 4 → M,
        (∀ x ∈ closedBall 0 1, ContMDiffAt (𝓡 4) (𝓡 (n + 1)) ∞ g x) ∧
        (∀ s : NoExoticSixSphere.Sphere 3, g s.val = (f s).val) ∧
        (∀ x ∈ ball 0 1, 0 < t (g x)) ∧
        (∀ s : NoExoticSixSphere.Sphere 3, fderiv ℝ (t ∘ g) s.val s.val < 0) ∧
        ∃ τ : ℝ, 0 < τ ∧ τ < 1 ∧
          EqOn g (sphereCollar e r t (spherePole 3) f) (closedBall 0 1 ∩ {x | τ ≤ ‖x‖}) ∧
          InjOn g (closedBall 0 1 ∩ {x | τ ≤ ‖x‖}) ∧
          ∀ x ∈ closedBall 0 1, τ ≤ ‖x‖ → Injective (fderiv ℝ (e.toFun ∘ g) x) := by
  let := zeroAtlas t ht hreg
  intro hf hi hd
  obtain ⟨F, hF⟩ := SmoothCube.exists_disk_extension_of_integral_kernel w
    (TimeCollarDisk.zeroToHalf t) f hker
  exact exists_smooth_disk_of_half_extension e r t ht hreg C (spherePole 3) f F hF hf hi hd

end NoExoticSixSphere.EmbeddedTime
