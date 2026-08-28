import Wikipedia.HopfProblem.DegreeCollapseRelativeTwoSphereEmbeddingCharts
import Wikipedia.HopfProblem.DegreeCollapseRelativeTwoSphereOpenControl

/-!
# Actual relative embedded two-sphere representatives with open-set control

One small parameter makes the whole sphere an embedded immersion while
fixing the protected source set. Scaling this same parameter gives an
actual relative homotopy. On the prescribed compact source region, the
entire homotopy stays in the original open subset of the target.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.RelativeTwoSphere

open NoExoticSixSphere GLOrthonormalization EuclideanEmbedding
open TwoSpherePerturbation (Parameters)

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  [IsManifold (𝓡 n) ∞ M] [CompactSpace M] [T2Space M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e)

include e r in
theorem exists_relative_embedding_in_open_on_compact
    (hdim : 5 < n) (f : C(Sphere 2, M)) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (χ : Sphere 2 → ℝ) (hχ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ)
    (hnonneg : ∀ x, 0 ≤ χ x) (hbound : ∀ x, ‖χ x‖ ≤ 1)
    (hinj : InjOn f {x | χ x = 0})
    (hderiv : ∀ x, χ x = 0 → Injective (mfderiv (𝓡 2) (𝓡 n) f x))
    (K : Set (Sphere 2)) (hK : IsCompact K)
    (U : Set M) (hU : IsOpen U) (hfU : MapsTo f K U) :
    ∃ g : C(Sphere 2, M), ContMDiff (𝓡 2) (𝓡 n) ∞ g ∧ IsClosedEmbedding g ∧
      (∀ x, Injective (mfderiv (𝓡 2) (𝓡 n) g x)) ∧
      ∃ H : f.HomotopyRel g {x | χ x = 0}, ∀ t : unitInterval, ∀ x ∈ K, H (t, x) ∈ U := by
  let f₀ : ℝ → Sphere 2 → M := fun _ x => f x
  have hf₀ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f₀) :=
    hf.comp contMDiff_snd
  obtain ⟨δ, hδ, _, hP⟩ := exists_smooth_parameter_ball e r f₀ χ hf₀ hχ hbound
  obtain ⟨ε, hε, hUpar⟩ :=
    exists_open_parameter_radius_on_compact e r f hf χ hχ hbound K hK U hU hfU (1 / 2)
  obtain ⟨S, C, p, _, hS, _, hC, hp, hgen, hmem, hG, _, _⟩ :=
    exists_small_manifold_family_with_embedding_charts e r f₀ χ hf₀ hχ hbound hdim
      (lt_min hδ hε)
  have hpδ : ‖p‖ < δ := hp.trans_le (min_le_left _ _)
  have hpε : ‖p‖ < ε := hp.trans_le (min_le_right _ _)
  have ht : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by constructor <;> norm_num
  let g := slice e r f₀ χ p (1 / 2) hG
  have hg : ContMDiff (𝓡 2) (𝓡 n) ∞ g := hG.comp (contMDiff_const.prodMk contMDiff_id)
  have hgi : Injective g :=
    injective_slice_of_embedding_charts e r f₀ χ hf₀ hχ hS hC p hgen hmem (1 / 2) ht hinj
  have hgd : ∀ x, Injective (mfderiv (𝓡 2) (𝓡 n) g x) :=
    immersive_slice_of_embedding_charts e r f₀ χ hf₀ hχ hnonneg hS hC p hgen hmem hG
      (1 / 2) ht hderiv
  let H : f.HomotopyRel g {x | χ x = 0} :=
    parameterHomotopy e r f₀ χ δ hP p hpδ (1 / 2) f.continuous
  refine ⟨g, hg, g.continuous.isClosedEmbedding hgi, hgd, H, ?_⟩
  intro t x hx
  have hnorm : ‖(t : ℝ) • p‖ ≤ ‖p‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1]
    exact mul_le_of_le_one_left (norm_nonneg p) t.property.2
  change map e r f₀ χ ((t : ℝ) • p) (1 / 2) x ∈ U
  exact hUpar ((t : ℝ) • p) (hnorm.trans_lt hpε) x hx

end Wikipedia.HopfProblem.DegreeCollapse.RelativeTwoSphere
