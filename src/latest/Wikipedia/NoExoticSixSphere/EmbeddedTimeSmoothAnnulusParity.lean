import Wikipedia.NoExoticSixSphere.EmbeddedTimeAnnulusParity
import Wikipedia.NoExoticSixSphere.CompactAnnulusBoundaryImmersion
import Wikipedia.NoExoticSixSphere.GenericProperFourAnnulus

/-!
# The actual boundary parity relation from a smooth positive-time annulus

Separated embedded boundary spheres and their immersive germs give jointly
injective collars. Relative perturbation constructs the proper generic
annulus while preserving both original boundary derivatives. Positive time
excludes boundary ends of its double-point closure. No genericity, compact
double-point curve, or even singular count is assumed of the original map.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere

open GLOrthonormalization

namespace SphereAnnulus

theorem boundary_point_cases {p : ℕ} {x : Vector (p + 1)}
    (hx : ‖x‖ = 1 ∨ ‖x‖ = 2) :
    (∃ s : Sphere p, x = s.val) ∨ ∃ s : Sphere p, x = (2 : ℝ) • s.val := by
  rcases hx with hx | hx
  · exact Or.inl ⟨⟨x, mem_sphere_zero_iff_norm.mpr hx⟩, rfl⟩
  · let s : Sphere p := ⟨(1 / 2 : ℝ) • x, by
      rw [mem_sphere_zero_iff_norm, norm_smul, hx]
      norm_num⟩
    refine Or.inr ⟨s, ?_⟩
    change x = (2 : ℝ) • ((1 / 2 : ℝ) • x)
    rw [smul_smul]
    norm_num

theorem injOn_boundary_of_separated_spheres {p : ℕ} {X : Type*}
    (f₀ f₁ : Sphere p → X) (hi₀ : Injective f₀) (hi₁ : Injective f₁)
    (hdis : ∀ s u, f₀ s ≠ f₁ u) (g : Vector (p + 1) → X)
    (hb₀ : ∀ s, g s.val = f₀ s) (hb₁ : ∀ s, g ((2 : ℝ) • s.val) = f₁ s) :
    InjOn g {x | ‖x‖ = 1 ∨ ‖x‖ = 2} := by
  intro x hx y hy heq
  rcases boundary_point_cases hx with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · rcases boundary_point_cases hy with ⟨u, rfl⟩ | ⟨u, rfl⟩
    · rw [hb₀, hb₀] at heq
      exact congrArg Subtype.val (hi₀ heq)
    · exact (hdis s u (by simpa only [hb₀, hb₁] using heq)).elim
  · rcases boundary_point_cases hy with ⟨u, rfl⟩ | ⟨u, rfl⟩
    · exact (hdis u s (by simpa only [hb₀, hb₁] using heq.symm)).elim
    · rw [hb₁, hb₁] at heq
      exact congrArg (fun s : Sphere p ↦ (2 : ℝ) • s.val) (hi₁ heq)

end SphereAnnulus

namespace EmbeddedTime

open Stiefel DiskBoundary SphereAnnulus

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector (6 + 1)) M]
  [IsManifold (𝓡 (6 + 1)) ∞ M] (e : EuclideanEmbedding (6 + 1) M)
  (r : e.TubularRetraction) (t : C(M, ℝ))
  (ht : ContMDiff (𝓡 (6 + 1)) 𝓘(ℝ, ℝ) ∞ t)
  (hreg : ∀ x, t x = 0 → Surjective (mfderiv (𝓡 (6 + 1)) 𝓘(ℝ, ℝ) t x))
  (a : SmoothRangeFrame (𝓡 (6 + 1)) e.normalProjection e.NormalModel) (m : M)

theorem sphereParity_eq_of_smooth_annulus
    (f₀ f₁ : C(Sphere 3, {x : M // t x = 0})) (g₀ : Vector 4 → M)
    (hg₀ : ∀ x ∈ domain 3, ContMDiffAt (𝓡 4) (𝓡 (6 + 1)) ∞ g₀ x)
    (hb₀ : ∀ s : Sphere 3, g₀ s.val = (f₀ s).val)
    (hb₁ : ∀ s : Sphere 3, g₀ ((2 : ℝ) • s.val) = (f₁ s).val)
    (hdis : ∀ s u, f₀ s ≠ f₁ u)
    (himmersive : ∀ s : Sphere 3,
      Injective (fderiv ℝ (e.toFun ∘ g₀) s.val) ∧
      Injective (fderiv ℝ (e.toFun ∘ g₀) ((2 : ℝ) • s.val)))
    (hpos : ∀ x, 1 < ‖x‖ → ‖x‖ < 2 → 0 < t (g₀ x))
    (hheight₀ : ∀ s : Sphere 3, 0 < fderiv ℝ (t ∘ g₀) s.val s.val)
    (hheight₁ : ∀ s : Sphere 3,
      fderiv ℝ (t ∘ g₀) ((2 : ℝ) • s.val) ((2 : ℝ) • s.val) < 0) :
    letI := zeroAtlas t ht hreg;
    ∀ (hf₀ : ContMDiff (𝓡 3) (𝓡 6) ∞ f₀) (hi₀ : Injective f₀)
      (hd₀ : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f₀ s))
      (hf₁ : ContMDiff (𝓡 3) (𝓡 6) ∞ f₁) (hi₁ : Injective f₁)
      (hd₁ : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f₁ s)),
      (zeroEmbedding e t ht hreg).sphereParity (zeroNormalFrame e r t ht hreg a m)
        f₀ hf₀ hi₀ hd₀ =
      (zeroEmbedding e t ht hreg).sphereParity (zeroNormalFrame e r t ht hreg a m)
        f₁ hf₁ hi₁ hd₁ := by
  let := zeroAtlas t ht hreg
  let : T2Space M := e.closedEmbedding.isEmbedding.t2Space
  intro hf₀ hi₀ hd₀ hf₁ hi₁ hd₁
  have hB (x : Vector 4) (hx : ‖x‖ = 1 ∨ ‖x‖ = 2) : x ∈ domain 3 := by
    rcases hx with hx | hx <;> constructor <;> linarith
  have hgi : InjOn g₀ {x | ‖x‖ = 1 ∨ ‖x‖ = 2} :=
    injOn_boundary_of_separated_spheres (fun s ↦ (f₀ s).val) (fun s ↦ (f₁ s).val)
      (Subtype.val_injective.comp hi₀) (Subtype.val_injective.comp hi₁)
      (fun s u he ↦ hdis s u (Subtype.ext he)) g₀ hb₀ hb₁
  have hgd (x : Vector 4) (hx : ‖x‖ = 1 ∨ ‖x‖ = 2) :
      Injective (fderiv ℝ (e.toFun ∘ g₀) x) := by
    rcases boundary_point_cases hx with ⟨s, rfl⟩ | ⟨s, rfl⟩
    · exact (himmersive s).1
    · exact (himmersive s).2
  obtain ⟨r₀, r₁, hr₀, hr₀small, hr₁large, hr₁, hcol, hcolD⟩ :=
    exists_embedded_boundary_annuli (e.toFun ∘ g₀)
      (fun x hx ↦ (e.smooth.contMDiffAt.comp x (hg₀ x (hB x hx))).contDiffAt)
      (fun x hx y hy he ↦ hgi hx hy (e.closedEmbedding.injective he)) hgd
  have hrr : r₀ < r₁ := by linarith
  obtain ⟨g, hg, hgeq, hD, hgp, charts, -, hcov, hgen, hdouble⟩ :=
    GenericFourAnnulus.exists_relative e g₀ hg₀ r₀ r₁ hr₀ hr₁ hrr
      {x | 0 < t x} (isOpen_lt continuous_const t.continuous) hpos
  have hgi' : InjOn g {x | x ∈ domain 3 ∧ (‖x‖ ≤ r₀ ∨ r₁ ≤ ‖x‖)} := by
    intro x hx y hy he
    apply hcol hx hy
    change e.toFun (g₀ x) = e.toFun (g₀ y)
    rw [← hgeq x hx.1 hx.2, ← hgeq y hy.1 hy.2, he]
  have hDb (x : Vector 4) (hx : x ∈ domain 3) (he : ‖x‖ ≤ r₀ ∨ r₁ ≤ ‖x‖) :
      Injective (fderiv ℝ (e.toFun ∘ g) x) := by
    rw [hD x hx he]
    exact hcolD x hx he
  have hbprot (x : Vector 4) (hx : ‖x‖ = 1 ∨ ‖x‖ = 2) : ‖x‖ ≤ r₀ ∨ r₁ ≤ ‖x‖ :=
    hx.elim (fun h ↦ Or.inl (h.trans_le hr₀.le)) (fun h ↦ Or.inr (hr₁.le.trans_eq h.symm))
  have htime (x : Vector 4) (hx : ‖x‖ = 1 ∨ ‖x‖ = 2) (v : Vector 4) :
      fderiv ℝ (t ∘ g) x v = fderiv ℝ (t ∘ g₀) x v := by
    rw [← timeCovector_composedDerivative e r t ht g x (hg x (hB x hx)) v,
      hgeq x (hB x hx) (hbprot x hx), hD x (hB x hx) (hbprot x hx)]
    exact timeCovector_composedDerivative e r t ht g₀ x (hg₀ x (hB x hx)) v
  have hnew₀ (s : Sphere 3) : g s.val = (f₀ s).val :=
    (hgeq s.val (hB _ (Or.inl (ClosedHemisphere.unit_norm s)))
      (hbprot _ (Or.inl (ClosedHemisphere.unit_norm s)))).trans (hb₀ s)
  have hnorm₂ (s : Sphere 3) : ‖(2 : ℝ) • s.val‖ = 2 := by
    rw [norm_smul, ClosedHemisphere.unit_norm]
    norm_num
  have hnew₁ (s : Sphere 3) : g ((2 : ℝ) • s.val) = (f₁ s).val :=
    (hgeq _ (hB _ (Or.inr (hnorm₂ s))) (hbprot _ (Or.inr (hnorm₂ s)))).trans (hb₁ s)
  have hfull : CompactRetractionAffineFamily.RegularDoublePointsOn
      g (openDomain 3) (openDomain 3) charts := by
    apply hdouble.of_injOn_compl
    apply hgi'.mono
    intro x hx
    refine ⟨openDomain_subset_domain 3 hx.1, ?_⟩
    by_contra he
    apply hx.2
    exact ⟨lt_of_not_ge (fun h ↦ he (Or.inl h)), lt_of_not_ge (fun h ↦ he (Or.inr h))⟩
  have hinside : closure (AnnulusDoublePoints.points g) ⊆ openDomain 3 ×ˢ openDomain 3 := by
    apply AnnulusDoublePoints.closure_subset_interior g
      (fun x hx ↦ (hg x hx).continuousAt.continuousWithinAt) r₀ r₁ hr₀ hr₁ hgi'
    intro x hx y hy he
    have hyzero : t (g y) = 0 := by
      rcases boundary_point_cases hy with ⟨s, rfl⟩ | ⟨s, rfl⟩
      · exact (congrArg t (hnew₀ s)).trans (f₀ s).property
      · exact (congrArg t (hnew₁ s)).trans (f₁ s).property
    exact (ne_of_gt (hgp x hx.1 hx.2)) ((congrArg t he).trans hyzero)
  apply sphereParity_eq_of_proper_generic_annulus e r t ht hreg a m f₀ f₁ g hg hnew₀ hnew₁
    r₀ r₁ hr₀ hr₁ hDb charts hcov hgen hinside hfull _ _ hf₀ hi₀ hd₀ hf₁ hi₁ hd₁
  · intro s
    rw [htime s.val (Or.inl (ClosedHemisphere.unit_norm s))]
    exact hheight₀ s
  · intro s
    rw [htime ((2 : ℝ) • s.val) (Or.inr (hnorm₂ s))]
    exact hheight₁ s

end EmbeddedTime
end NoExoticSixSphere
