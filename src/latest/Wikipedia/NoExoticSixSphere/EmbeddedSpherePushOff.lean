import Wikipedia.NoExoticSixSphere.SphereInternalNormalFrame
import Wikipedia.NoExoticSixSphere.EmbeddedInternalSphereTube

/-!
# A disjoint smooth push-off of an embedded three-sphere

The internal normal three-frame is constructed without a parity assumption.
A small nonzero constant vector in its genuine embedded tube gives the
push-off. Scaling that vector supplies a homotopy of the original maps;
injectivity of the full tube proves disjointness of their images.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff unitInterval

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) (r : TubularRetraction e)

include e a r in
theorem exists_disjoint_sphere_pushOff (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) :
    ∃ g : C(Sphere 3, M), ContMDiff (𝓡 3) (𝓡 6) ∞ g ∧
      f.Homotopic g ∧ Disjoint (range f) (range g) := by
  obtain ⟨C, hC, hn, hr⟩ := exists_smooth_internalNormalFrame e f a hf hd
  have hiC (s : Sphere 3) : Injective (C s) := Stiefel.injective ⟨C s, hn s⟩
  obtain ⟨ε, hε, hemb, hlocal⟩ :=
    e.exists_embedded_internalSphereTube f C r hf hi hC hd hiC hr
  let v : Vector 3 := (ε / 2) • (spherePole 2).val
  have hvnorm : ‖v‖ = ε / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (half_pos hε),
      ClosedHemisphere.unit_norm, mul_one]
  have hvne : v ≠ 0 := norm_ne_zero_iff.mp (by rw [hvnorm]; exact (half_pos hε).ne')
  have hv : v ∈ closedBall (0 : Vector 3) ε := by
    rw [mem_closedBall, dist_zero_right, hvnorm]
    exact half_le_self hε.le
  have hz : (0 : Vector 3) ∈ closedBall (0 : Vector 3) ε := by
    simpa only [mem_closedBall, dist_self] using hε.le
  have htv (t : I) : (t : ℝ) • v ∈ closedBall (0 : Vector 3) ε :=
    (convex_closedBall (0 : Vector 3) ε).smul_mem_of_zero_mem hz hv t.property
  let j : C(Sphere 3 × closedBall (0 : Vector 3) ε, M) :=
    ⟨fun p ↦ e.internalSphereTube f C r (p.1, p.2.val), hemb.continuous⟩
  have hg : ContMDiff (𝓡 3) (𝓡 6) ∞
      (fun s ↦ e.internalSphereTube f C r (s, v)) := by
    intro s
    have htube : ContMDiffAt ((𝓡 3).prod (𝓡 3)) (𝓡 6) ∞
        (e.internalSphereTube f C r) (s, v) := (hlocal s v hv).2.contMDiffAt
    have hs : ContMDiffAt (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞
        (fun z : Sphere 3 ↦ (z, v)) s := contMDiffAt_id.prodMk contMDiffAt_const
    exact ContMDiffAt.comp (f := fun z : Sphere 3 ↦ (z, v))
      (g := e.internalSphereTube f C r) s htube hs
  let g : C(Sphere 3, M) := ⟨fun s ↦ e.internalSphereTube f C r (s, v), hg.continuous⟩
  have H : f.Homotopic g := by
    refine ⟨{
      toFun := fun p ↦ j (p.2, ⟨(p.1 : ℝ) • v, htv p.1⟩)
      continuous_toFun := j.continuous.comp (continuous_snd.prodMk
        (((continuous_subtype_val.comp continuous_fst).smul continuous_const).subtype_mk _))
      map_zero_left := ?_
      map_one_left := ?_
    }⟩
    · intro s
      change e.internalSphereTube f C r (s, (0 : ℝ) • v) = f s
      rw [zero_smul, e.internalSphereTube_core]
    · intro s
      change e.internalSphereTube f C r (s, (1 : ℝ) • v) = e.internalSphereTube f C r (s, v)
      rw [one_smul]
  refine ⟨g, hg, H, disjoint_left.mpr ?_⟩
  rintro z ⟨s, hs⟩ ⟨t, ht⟩
  have he : e.internalSphereTube f C r (s, 0) = e.internalSphereTube f C r (t, v) :=
    (e.internalSphereTube_core f C r s).trans (hs.trans ht.symm)
  have hp : (s, (⟨0, hz⟩ : closedBall (0 : Vector 3) ε)) = (t, ⟨v, hv⟩) :=
    hemb.injective he
  exact hvne (congrArg (fun p : Sphere 3 × closedBall (0 : Vector 3) ε ↦ p.2.val) hp).symm

end NoExoticSixSphere.EuclideanEmbedding
