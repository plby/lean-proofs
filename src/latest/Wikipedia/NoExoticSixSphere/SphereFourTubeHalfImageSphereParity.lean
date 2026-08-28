import Wikipedia.NoExoticSixSphere.SphereFourTubeEmbeddedRepresentatives
import Wikipedia.NoExoticSixSphere.SphereFourTubeOldSphereParity
import Wikipedia.NoExoticSixSphere.EmbeddedTimeIntegralRelationParity

/-!
# Zero original sphere parity for the actual double-core half-image relation

Mayer–Vietoris gives an even-longitude tube class with the same new-half
image as the old sphere. Its constructed embedded representative has zero
parity for the original induced frame. Positivity separates it from the
old boundary. The native annulus theorem compares the two parities, and
the exact old-frame comparison transfers zero back to the original atlas.
No vanishing of the half-image obstruction or torsion restriction is used.
-/

noncomputable section

open Function Set ContinuousMap
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SphereFourTube

open GLOrthonormalization EmbeddedTime SmoothCube
open Wikipedia.HopfProblem.SingularMayerVietoris Wikipedia.HopfProblem.SphereHomology
open Wikipedia.HopfProblem.PeriodTorusHigherHomology Wikipedia.HopfProblem.DegreeCollapse
open Wikipedia.HopfProblem.DegreeCollapse.TimeCollar

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B]
  [ChartedSpace (Vector 7) M] [IsManifold (𝓡 7) ∞ M] [T2Space M]
  (Φ : PartialDiffeomorph ((𝓡 3).prod (𝓡 4)) (𝓡 7) (Sphere 3 × Vector 4) M ∞)
  (hΦ : Φ.source = univ) (t τ : C(M, ℝ))
  (hpos : ∀ x ∈ Φ.target, 0 < t x)
  (hout : ∀ x ∉ closedRegion Φ 2, τ x = t x)
  (hhalf : ∀ x, 0 ≤ τ x ↔ 0 ≤ t x ∧ x ∉ openRegion Φ 1)
  (hinner : ∀ p : Sphere 3 × Vector 4, ‖p.2‖ ≤ 3 / 2 → τ (Φ p) = ‖p.2‖ ^ 2 - 1)

theorem oldZeroMap_ne_boundaryMap (p : {x : M // t x = 0}) (q : Sphere 3 × Sphere 3) :
    oldZeroMap Φ hΦ t τ hpos hout p ≠ boundaryMap Φ hΦ τ hinner q := by
  intro hpq
  have h := congrArg (fun z : {x : M // τ x = 0} ↦ t z.val) hpq
  change t p.val = t (Φ (q.1, q.2.val)) at h
  rw [p.property] at h
  exact (ne_of_gt (hpos _ (Φ.map_source (hΦ.symm ▸ mem_univ _)))) h.symm

variable [CompactSpace M] (ht : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ t)
  (hτ : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ τ)
  (hreg : ∀ x, t x = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) t x))
  (hτreg : ∀ x, τ x = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) τ x))
  (e : EuclideanEmbedding 7 M) (r : e.TubularRetraction)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel) (m : M)
  (D : TimeCollar τ B) [SimplyConnectedSpace (NonnegativeHalf τ)] (w : NonnegativeHalf τ)
  [hW₂ : Subsingleton (π_ 2 (NonnegativeHalf τ) w)]

include hhalf hout hinner hτ hτreg D w hW₂ in
theorem sphereParity_zero_of_double_core_image
    (f : C(Sphere 3, {x : M // t x = 0}))
    (hclass : singularHomologyMap (zeroToHalf t) 3
      (singularHomologyMap f 3 (unitSphereTopClass 2)) =
      (2 : ℤ) • singularHomologyMap (coreInHalf Φ hΦ t hpos) 3 (unitSphereTopClass 2)) :
    letI := zeroAtlas (n := 6) t ht hreg;
    ∀ (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
      (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)),
      (zeroEmbedding (n := 6) e t ht hreg).sphereParity
        (zeroNormalFrame (n := 6) e r t ht hreg a m) f hf hi hd = 0 := by
  let := zeroAtlas (n := 6) t ht hreg
  let := zeroAtlas (n := 6) τ hτ hτreg
  intro hf hi hd
  obtain ⟨v, hv, hfst⟩ := old_boundary_class_of_double_core_image
    Φ hΦ t τ hpos hout hhalf hinner (singularHomologyMap f 3 (unitSphereTopClass 2)) hclass
  let p : Sphere 3 × Sphere 3 := (spherePole 3, spherePole 3)
  obtain ⟨g, hg, hgi, hgd, hgclass, hgzero⟩ :=
    exists_native_zero_parity_boundary_representative Φ hΦ τ hinner hτ hτreg e r a m p v hfst
  let F := (oldZeroMap Φ hΦ t τ hpos hout).comp f
  let G := (boundaryMap Φ hΦ τ hinner).comp g
  have hF : ContMDiff (𝓡 3) (𝓡 6) ∞ F :=
    (contMDiff_oldZeroMap Φ hΦ t τ hpos hout ht hτ hreg hτreg).comp hf
  have hFi : Injective F := (oldZeroMap_injective Φ hΦ t τ hpos hout).comp hi
  have hFd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) F s) :=
    oldZeroMap_comp_mfderiv_injective Φ hΦ t τ hpos hout ht hτ hreg hτreg f hf hd
  have hdis : ∀ s u, F s ≠ G u := fun s u ↦
    oldZeroMap_ne_boundaryMap Φ hΦ t τ hpos hout hinner (f s) (g u)
  have hFcomp : (zeroToHalf τ).comp F =
      (oldZeroToNewHalf Φ hΦ t τ hpos hout).comp f := rfl
  have hGcomp : (zeroToHalf τ).comp G = (boundaryInNewHalf Φ hΦ τ hinner).comp g := rfl
  have hFclass : singularHomologyMap (zeroToHalf τ) 3
      (singularHomologyMap F 3 (unitSphereTopClass 2)) =
      singularHomologyMap (oldZeroToNewHalf Φ hΦ t τ hpos hout) 3
        (singularHomologyMap f 3 (unitSphereTopClass 2)) := by
    rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, hFcomp,
      singularHomologyMap_comp, LinearMap.comp_apply]
  have hGclass : singularHomologyMap (zeroToHalf τ) 3
      (singularHomologyMap G 3 (unitSphereTopClass 2)) =
      singularHomologyMap (boundaryInNewHalf Φ hΦ τ hinner) 3
        (singularHomologyMap g 3 (unitSphereTopClass 2)) := by
    rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, hGcomp,
      singularHomologyMap_comp, LinearMap.comp_apply]
  have hmarked : singularHomologyMap (zeroToHalf τ) 3
      (singularHomologyMap F 3 (unitSphereTopClass 2)) =
      singularHomologyMap (zeroToHalf τ) 3
        (singularHomologyMap G 3 (unitSphereTopClass 2)) := by
    rw [hFclass, hGclass, hgclass]
    exact hv
  have hcube : singularHomologyMap (TimeCollarDisk.zeroToHalf τ) 3 (integralSphereClass F) =
      singularHomologyMap (TimeCollarDisk.zeroToHalf τ) 3 (integralSphereClass G) := by
    change singularHomologyMap (zeroToHalf τ) 3 (integralSphereClass F) =
      singularHomologyMap (zeroToHalf τ) 3 (integralSphereClass G)
    rcases CubeSphereGenerator.standard_or_negative with hp | hn
    · simpa only [integralSphereClass, hp] using hmarked
    · simpa only [integralSphereClass, hn, map_neg] using congrArg Neg.neg hmarked
  have H := sphereParity_eq_of_separated_integral_relation e r τ hτ hτreg a m D w
    F G hdis hcube hF hFi hFd hg hgi hgd
  have hold := oldZero_sphereParity_eq Φ hΦ t τ hpos hout ht hτ hreg hτreg e r r a m m
    f hf hi hd hF hFi hFd
  exact hold.symm.trans (H.trans hgzero)

end NoExoticSixSphere.SphereFourTube
