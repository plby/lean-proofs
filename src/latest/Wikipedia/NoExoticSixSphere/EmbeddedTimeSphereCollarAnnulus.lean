import Wikipedia.NoExoticSixSphere.EmbeddedTimeSphereCollar
import Wikipedia.NoExoticSixSphere.CompactCoreImmersion
import Wikipedia.NoExoticSixSphere.RadialBoundarySign
import Wikipedia.NoExoticSixSphere.SmoothLocalExtension

/-!
# A uniformly embedded positive-time collar in the original manifold

Compactness upgrades the actual inward collar's boundary immersion to an
embedded annulus. Every point strictly inside its outer sphere has positive
time. A globally smooth Euclidean map agrees exactly with the embedded
collar on the whole closed annulus, as required for relative disk smoothing.
No disk filling the inner sphere is asserted in this file.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EmbeddedTime

open GLOrthonormalization

variable {n p : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector (n + 1)) M]
  [IsManifold (𝓡 (n + 1)) ∞ M] (e : EuclideanEmbedding (n + 1) M)
  (r : e.TubularRetraction) (t : C(M, ℝ))
  (ht : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ t)
  (hreg : ∀ x, t x = 0 → Surjective (mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) t x))

theorem exists_embedded_sphereCollar_neighborhood (b : Sphere p)
    (f : Sphere p → {x : M // t x = 0}) : letI := zeroAtlas t ht hreg;
    ContMDiff (𝓡 p) (𝓡 n) ∞ f → Injective f →
      (∀ s, Injective (mfderiv (𝓡 p) (𝓡 n) f s)) →
      ∃ U : Set (Vector (p + 1)), IsOpen U ∧ sphere 0 1 ⊆ U ∧
        ContMDiffOn (𝓡 (p + 1)) (𝓡 (n + 1)) ∞ (sphereCollar e r t b f) U ∧
        InjOn (sphereCollar e r t b f) U ∧
        ∀ x ∈ U, Injective (fderiv ℝ (e.toFun ∘ sphereCollar e r t b f) x) := by
  let := zeroAtlas t ht hreg
  intro hf hi hd
  let A := sphereCollarAmbient e r t b f
  let g := sphereCollar e r t b f
  let W : Set (Vector (p + 1)) := A ⁻¹' r.domain
  have hA := contDiff_sphereCollarAmbient e r t ht hreg b f hf
  have hW : IsOpen W := r.domain.isOpen.preimage hA.continuous
  have hSW : sphere (0 : Vector (p + 1)) 1 ⊆ W := by
    intro x hx
    change sphereCollarAmbient e r t b f (⟨x, hx⟩ : Sphere p).val ∈ r.domain
    rw [sphereCollarAmbient_coe]
    exact r.contains ⟨_, rfl⟩
  have hgs (x : Vector (p + 1)) (hx : x ∈ W) :
      ContMDiffAt (𝓡 (p + 1)) (𝓡 (n + 1)) ∞ g x :=
    (r.smooth.contMDiffAt (r.domain.isOpen.mem_nhds hx)).comp x hA.contMDiff.contMDiffAt
  have hegs (x : Vector (p + 1)) (hx : x ∈ sphere 0 1) :
      ContDiffAt ℝ ∞ (e.toFun ∘ g) x :=
    (e.smooth.contMDiffAt.comp x (hgs x (hSW hx))).contDiffAt
  have hgi : InjOn (e.toFun ∘ g) (sphere (0 : Vector (p + 1)) 1) := by
    intro x hx y hy heq
    let sx : Sphere p := ⟨x, hx⟩
    let sy : Sphere p := ⟨y, hy⟩
    have hxy : e.toFun (f sx).val = e.toFun (f sy).val := by
      change e.toFun (sphereCollar e r t b f sx.val) =
        e.toFun (sphereCollar e r t b f sy.val) at heq
      simpa only [sphereCollar_coe] using heq
    exact congrArg Subtype.val (hi (Subtype.ext (e.closedEmbedding.injective hxy)))
  have hgd (x : Vector (p + 1)) (hx : x ∈ sphere 0 1) :
      Injective (fderiv ℝ (e.toFun ∘ g) x) := by
    change Injective (fderiv ℝ (e.toFun ∘ sphereCollar e r t b f) (⟨x, hx⟩ : Sphere p).val)
    rw [fderiv_embedded_sphereCollar_coe e r t ht hreg b f _ hf]
    exact injective_fderiv_sphereCollarAmbient_coe e r t ht hreg b f _ hf hd
  obtain ⟨V, hV, hSV, hVi, hVd⟩ := CompactCoreImmersion.exists_open_injOn_near_compact
    (isCompact_sphere (0 : Vector (p + 1)) 1) hegs hgi hgd
  refine ⟨W ∩ V, hW.inter hV, fun x hx ↦ ⟨hSW hx, hSV hx⟩,
    fun x hx ↦ (hgs x hx.1).contMDiffWithinAt, ?_, fun x hx ↦ hVd x hx.2⟩
  intro x hx y hy heq
  exact hVi hx.2 hy.2 (congrArg e.toFun heq)

theorem exists_positive_embedded_sphereCollar_annulus (b : Sphere p)
    (f : Sphere p → {x : M // t x = 0}) : letI := zeroAtlas t ht hreg;
    ContMDiff (𝓡 p) (𝓡 n) ∞ f → Injective f →
      (∀ s, Injective (mfderiv (𝓡 p) (𝓡 n) f s)) →
      ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
        (∀ x ∈ closedBall (0 : Vector (p + 1)) 1, ρ ≤ ‖x‖ →
          ContMDiffAt (𝓡 (p + 1)) (𝓡 (n + 1)) ∞ (sphereCollar e r t b f) x) ∧
        InjOn (sphereCollar e r t b f) (closedBall 0 1 ∩ {x | ρ ≤ ‖x‖}) ∧
        (∀ x ∈ closedBall (0 : Vector (p + 1)) 1, ρ ≤ ‖x‖ →
          Injective (fderiv ℝ (e.toFun ∘ sphereCollar e r t b f) x)) ∧
        (∀ x ∈ ball (0 : Vector (p + 1)) 1, ρ ≤ ‖x‖ → 0 < t (sphereCollar e r t b f x)) ∧
        ∃ H : C(Vector (p + 1), Vector e.ambientDimension), ContDiff ℝ ∞ H ∧
          EqOn H (e.toFun ∘ sphereCollar e r t b f) (closedBall 0 1 ∩ {x | ρ ≤ ‖x‖}) := by
  let := zeroAtlas t ht hreg
  intro hf hi hd
  obtain ⟨U, hU, hSU, hgs, hgi, hgd⟩ :=
    exists_embedded_sphereCollar_neighborhood e r t ht hreg b f hf hi hd
  have htime : ContDiffOn ℝ ∞ (t ∘ sphereCollar e r t b f) U := by
    intro x hx
    exact (ht.contMDiffAt.comp x (hgs.contMDiffAt (hU.mem_nhds hx))).contDiffAt.contDiffWithinAt
  have hzero (x : Vector (p + 1)) (hx : x ∈ sphere 0 1) :
      (t ∘ sphereCollar e r t b f) x = 0 := by
    change t (sphereCollar e r t b f (⟨x, hx⟩ : Sphere p).val) = 0
    rw [sphereCollar_coe]
    exact (f ⟨x, hx⟩).property
  have hneg (x : Vector (p + 1)) (hx : x ∈ sphere 0 1) :
      fderiv ℝ (t ∘ sphereCollar e r t b f) x x < 0 :=
    fderiv_time_sphereCollar_radial_neg e r t ht hreg b f ⟨x, hx⟩ hf
  obtain ⟨ρ, hρ, hρ1, hsub, _, hpos⟩ :=
    RadialBoundarySign.exists_positive_inner_annulus hU hSU htime hzero hneg
  have hclosed : IsClosed (closedBall (0 : Vector (p + 1)) 1 ∩ {x | ρ ≤ ‖x‖}) :=
    isClosed_closedBall.inter (isClosed_le continuous_const continuous_norm)
  have hegs : ContDiffOn ℝ ∞ (e.toFun ∘ sphereCollar e r t b f) U := by
    intro x hx
    exact (e.smooth.contMDiffAt.comp x
      (hgs.contMDiffAt (hU.mem_nhds hx))).contDiffAt.contDiffWithinAt
  obtain ⟨H, hH, hHeq⟩ := exists_contDiff_eqOn_closed _ hclosed hU hsub hegs
  exact ⟨ρ, hρ, hρ1,
    fun x hx hrx ↦ hgs.contMDiffAt (hU.mem_nhds (hsub ⟨hx, hrx⟩)),
    hgi.mono hsub, fun x hx hrx ↦ hgd x (hsub ⟨hx, hrx⟩), hpos,
    ⟨H, hH.continuous⟩, hH, hHeq⟩

end NoExoticSixSphere.EmbeddedTime
