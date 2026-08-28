import Wikipedia.HopfProblem.DegreeCollapseRelativeTwoSphereFamily
import Wikipedia.NoExoticSixSphere.UniformProductTube

/-!
# Uniform open-set control on a compact part of the actual source sphere

The genuine tubular family is continuous on one parameter ball. Apply the
tube lemma to the compact prescribed source subset, without replacing its
points or requiring a manifold structure on that subset. Every sufficiently
small parameter keeps this whole part of the sphere in the original open set.
-/

noncomputable section

open Set Function TopologicalSpace
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.RelativeTwoSphere

open NoExoticSixSphere GLOrthonormalization EuclideanEmbedding
open TwoSpherePerturbation (Parameters)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  [CompactSpace M] (e : EuclideanEmbedding n M) (r : TubularRetraction e)

theorem exists_open_parameter_radius_on_compact
    (f : C(Sphere 2, M)) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (χ : Sphere 2 → ℝ) (hχ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ) (hbound : ∀ x, ‖χ x‖ ≤ 1)
    (K : Set (Sphere 2)) (hK : IsCompact K)
    (U : Set M) (hU : IsOpen U) (hfU : MapsTo f K U) (t : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p : Parameters e, ‖p‖ < ε → ∀ x ∈ K,
      map e r (fun _ x => f x) χ p t x ∈ U := by
  let f₀ : ℝ → Sphere 2 → M := fun _ x => f x
  have hf₀ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f₀) :=
    hf.comp contMDiff_snd
  obtain ⟨δ, hδ, _, hP⟩ := exists_smooth_parameter_ball e r f₀ χ hf₀ hχ hbound
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let V : Set (K × Parameters e) := {q | ‖q.2‖ < δ}
  let G : K × Parameters e → M := fun q => map e r f₀ χ q.2 t q.1.val
  have hV : IsOpen V := isOpen_lt (continuous_norm.comp continuous_snd) continuous_const
  have hlift : Continuous (fun q : K × Parameters e => (q.2, (t, q.1.val))) :=
    continuous_snd.prodMk (continuous_const.prodMk (continuous_subtype_val.comp continuous_fst))
  have hG : ContinuousOn G V := hP.continuousOn.comp hlift.continuousOn (fun _ hq => hq)
  have hW : IsOpen (V ∩ G ⁻¹' U) := hG.isOpen_inter_preimage hV hU
  have hzero (x : K) : (x, (0 : Parameters e)) ∈ V ∩ G ⁻¹' U := by
    refine ⟨?_, ?_⟩
    · change ‖(0 : Parameters e)‖ < δ
      simpa only [norm_zero] using hδ
    · change map e r f₀ χ 0 t x.val ∈ U
      rw [map_zero_parameter]
      exact hfU x.property
  obtain ⟨ε, hε, hsub⟩ := exists_uniform_closedProductTube hW hzero
  exact ⟨ε, hε, fun p hp x hx => (hsub ⟨x, hx⟩ p hp.le).2⟩

end Wikipedia.HopfProblem.DegreeCollapse.RelativeTwoSphere
