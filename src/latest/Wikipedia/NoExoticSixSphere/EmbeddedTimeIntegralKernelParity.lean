import Wikipedia.NoExoticSixSphere.EmbeddedTimeCollaredDisk
import Wikipedia.NoExoticSixSphere.GenericProperFourDisk
import Wikipedia.NoExoticSixSphere.EmbeddedTimeGenericDiskParity

/-!
# Zero actual induced-boundary parity for integral kernel spheres

The disk is constructed from the actual half extension, not assumed proper
or generic. Relative perturbation retains its exact inward collar, and
positive time separates the interior from the entire zero boundary.
The actual double-point closure consequently has no boundary ends, and
the checked compact curve theorem gives even singular count and zero parity
for the original induced outward frame. Integral, not mod-two, kernel
vanishing supplies the initial continuous disk.
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

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B]
  [ChartedSpace (Vector (6 + 1)) M] [IsManifold (𝓡 (6 + 1)) ∞ M]
  (e : EuclideanEmbedding (6 + 1) M) (r : e.TubularRetraction) (t : C(M, ℝ))
  (ht : ContMDiff (𝓡 (6 + 1)) 𝓘(ℝ, ℝ) ∞ t)
  (hreg : ∀ x, t x = 0 → Surjective (mfderiv (𝓡 (6 + 1)) 𝓘(ℝ, ℝ) t x))
  (C : TimeCollar t B)
  (a : SmoothRangeFrame (𝓡 (6 + 1)) e.normalProjection e.NormalModel) (m : M)

include C in
theorem sphereParity_zero_of_half_disk_extension
    (f : C(NoExoticSixSphere.Sphere 3, {x : M // t x = 0}))
    (F : C(Disk (E := Vector 4), NonnegativeHalf t))
    (hF : ∀ s, F (boundaryToDisk s) = TimeCollarDisk.zeroToHalf t (f s)) :
    letI := zeroAtlas t ht hreg;
    ∀ (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
      (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)),
      (zeroEmbedding e t ht hreg).sphereParity (zeroNormalFrame e r t ht hreg a m)
        f hf hi hd = 0 := by
  let := zeroAtlas t ht hreg
  let : T2Space M := e.closedEmbedding.isEmbedding.t2Space
  intro hf hi hd
  obtain ⟨g₀, hgs₀, hgb₀, hgp₀, hheight₀, ρ, hρ, hρ1, -, hgi₀, hgd₀⟩ :=
    exists_smooth_disk_of_half_extension e r t ht hreg C (spherePole 3) f F hF hf hi hd
  obtain ⟨g, hgs, hgeq, hD, hgp, charts, -, hcov, hgen, hdouble⟩ :=
    GenericFourDisk.exists_relative e g₀ hgs₀ ρ hρ hρ1 {x | 0 < t x}
      (isOpen_lt continuous_const t.continuous) hgp₀
  have hboundary (s : NoExoticSixSphere.Sphere 3) : g s.val = (f s).val := by
    rw [hgeq s.val (sphere_subset_closedBall s.property)
      (by rw [ClosedHemisphere.unit_norm]; exact hρ1.le)]
    exact hgb₀ s
  have hgi : InjOn g (closedBall (0 : Vector 4) 1 ∩ {x | ρ ≤ ‖x‖}) := by
    intro x hx y hy heq
    apply hgi₀ hx hy
    rw [← hgeq x hx.1 hx.2, ← hgeq y hy.1 hy.2]
    exact heq
  have hgd (x : Vector 4) (hx : x ∈ closedBall 0 1) (hρx : ρ ≤ ‖x‖) :
      Injective (fderiv ℝ (e.toFun ∘ g) x) := by
    rw [hD x hx hρx]
    exact hgd₀ x hx hρx
  have hheight (s : NoExoticSixSphere.Sphere 3) : fderiv ℝ (t ∘ g) s.val s.val < 0 := by
    have hx := sphere_subset_closedBall s.property
    have hρx : ρ < ‖s.val‖ := by rw [ClosedHemisphere.unit_norm]; exact hρ1
    have heq := fderiv_eq_of_closedBall_collar (t ∘ g) (t ∘ g₀) ρ
      (fun x hx hrx ↦ congrArg t (hgeq x hx hrx)) hx hρx
      ((ht.contMDiffAt.comp s.val (hgs s.val hx)).contDiffAt.differentiableAt (by simp))
      ((ht.contMDiffAt.comp s.val (hgs₀ s.val hx)).contDiffAt.differentiableAt (by simp))
    rw [heq]
    exact hheight₀ s
  have hfull : CompactRetractionAffineFamily.RegularDoublePointsOn
      g (ball 0 1) (ball 0 1) charts := by
    apply hdouble.of_injOn_compl
    apply hgi.mono
    intro x hx
    exact ⟨ball_subset_closedBall hx.1,
      le_of_not_gt (fun hn ↦ hx.2 (mem_ball_zero_iff.mpr hn))⟩
  have hinside : closure (DiskDoublePoints.points g) ⊆ ball 0 1 ×ˢ ball 0 1 := by
    apply DiskDoublePoints.closure_subset_interior g
      (fun x hx ↦ (hgs x hx).continuousAt.continuousWithinAt) ρ hρ1 hgi
    intro x hx y hy heq
    have hzero : t (g x) = 0 :=
      (congrArg t (heq.trans (hboundary ⟨y, hy⟩))).trans (f ⟨y, hy⟩).property
    exact (ne_of_gt (hgp x hx)) hzero
  exact sphereParity_zero_of_proper_generic_disk e r t ht hreg a m f g hgs hboundary
    ρ hρ1 hgd charts hcov hgen hinside hfull hheight hf hi hd

variable [SimplyConnectedSpace (NonnegativeHalf t)] (w : NonnegativeHalf t)
  [hW₂ : Subsingleton (π_ 2 (NonnegativeHalf t) w)]

include C w hW₂ in
theorem sphereParity_zero_of_integral_kernel
    (f : C(NoExoticSixSphere.Sphere 3, {x : M // t x = 0}))
    (hker : singularHomologyMap (TimeCollarDisk.zeroToHalf t) 3
      (SmoothCube.integralSphereClass f) = 0) : letI := zeroAtlas t ht hreg;
    ∀ (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
      (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)),
      (zeroEmbedding e t ht hreg).sphereParity (zeroNormalFrame e r t ht hreg a m)
        f hf hi hd = 0 := by
  let := zeroAtlas t ht hreg
  intro hf hi hd
  obtain ⟨F, hF⟩ := SmoothCube.exists_disk_extension_of_integral_kernel w
    (TimeCollarDisk.zeroToHalf t) f hker
  exact sphereParity_zero_of_half_disk_extension e r t ht hreg C a m f F hF hf hi hd

end NoExoticSixSphere.EmbeddedTime
