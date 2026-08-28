import Wikipedia.HopfProblem.DegreeCollapseLowSphereOpenParameters
import Wikipedia.NoExoticSixSphere.FiniteDiffeomorphChartCover
import Wikipedia.SmoothSixDPoincare.GlobalMapSmoothing

/-!

# Original embedded sphere representatives in a prescribed open subset

When the target dimension exceeds twice the sphere dimension, a small actual affine parameter
avoids both double points and nonzero derivative kernel vectors in every
original chart. Scaling that parameter from zero gives an actual homotopy
which remains in the prescribed original open subset. The source sphere
is compact, so the resulting injective smooth map is a closed embedding.
-/

noncomputable section

open Function Set TopologicalSpace Topology
open scoped Manifold ContDiff unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSphereParameters

open NoExoticSixSphere GLOrthonormalization EuclideanEmbedding LowSphereAffine
open NoExoticSixSphere.ManifoldAffineSphereFamily (exists_finite_chart_cover)

variable {d n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  [IsManifold (𝓡 n) ∞ M] [CompactSpace M] [T2Space M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e)

include e r in
theorem exists_embedded_homotopy_in_open_of_smooth (hn : 2 * d < n)
    (f : C(Sphere d, M)) (hf : ContMDiff (𝓡 d) (𝓡 n) ∞ f)
    (U : Set M) (hU : IsOpen U) (hfU : ∀ s, f s ∈ U) :
    ∃ g : C(Sphere d, M), ContMDiff (𝓡 d) (𝓡 n) ∞ g ∧ IsClosedEmbedding g ∧
      (∀ s, Injective (mfderiv (𝓡 d) (𝓡 n) g s)) ∧
      ∃ H : f.Homotopy g, ∀ q, H q ∈ U := by
  let f₀ : ℝ → Sphere d → M := fun _ s ↦ f s
  have hf₀ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 d)) (𝓡 n) ∞ (Function.uncurry f₀) :=
    hf.comp contMDiff_snd
  obtain ⟨S, hS, hScov⟩ := exists_finite_chart_cover d (Sphere d)
  obtain ⟨C, hC, hCcov⟩ := exists_finite_chart_cover n M
  obtain ⟨δ, hδ, hmem, hP⟩ := exists_smooth_parameter_ball e r f₀ hf₀
  obtain ⟨ε, hε, hUpar⟩ := exists_open_parameter_radius e r f hf U hU hfU (1 / 2)
  obtain ⟨p, hp, hpair, hdir⟩ := exists_small_avoiding_parameter e r f₀ hf₀ (1 / 2) hn
    S hS.countable C hC.countable (lt_min hδ hε)
  have hpδ : ‖p‖ < δ := hp.trans_le (min_le_left _ _)
  have hpε : ‖p‖ < ε := hp.trans_le (min_le_right _ _)
  have htime : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by constructor <;> norm_num
  have hPs : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 d)) (𝓡 n) ∞
      (Function.uncurry (LowSphereAffine.map e r f₀ p)) :=
    hP.comp_contMDiff (contMDiff_const.prodMk contMDiff_id) (fun _ ↦ hpδ)
  have hg : ContMDiff (𝓡 d) (𝓡 n) ∞ (LowSphereAffine.map e r f₀ p (1 / 2)) :=
    hPs.comp (contMDiff_const.prodMk contMDiff_id)
  let g : C(Sphere d, M) := ⟨LowSphereAffine.map e r f₀ p (1 / 2), hg.continuous⟩
  have hi : Injective g := injective_slice_of_avoidPairs e r f₀ hf₀ (1 / 2) p htime
    S C hScov hCcov (hmem p hpδ (1 / 2)) hpair
  have hd : ∀ s, Injective (mfderiv (𝓡 d) (𝓡 n) g s) :=
    injective_mfderiv_slice_of_avoidDirections e r f₀ hf₀ (1 / 2) p hPs htime
      S C hScov hCcov (hmem p hpδ (1 / 2)) hdir
  have hnorm (u : unitInterval) : ‖u.val • p‖ ≤ ‖p‖ := by
    rw [norm_smul, Real.norm_of_nonneg u.property.1]
    nlinarith [norm_nonneg p, u.property.2]
  let H : f.Homotopy g :=
    { toFun := fun q ↦ LowSphereAffine.map e r f₀ (q.1.val • p) (1 / 2) q.2
      continuous_toFun := hP.continuousOn.comp_continuous
        (((continuous_subtype_val.comp continuous_fst).smul continuous_const).prodMk
          (continuous_const.prodMk continuous_snd))
        (fun q ↦ (hnorm q.1).trans_lt hpδ)
      map_zero_left := by
        intro s
        change LowSphereAffine.map e r f₀ ((0 : ℝ) • p) (1 / 2) s = f s
        rw [zero_smul, map_zero_parameter]
      map_one_left := by
        intro s
        change LowSphereAffine.map e r f₀ ((1 : ℝ) • p) (1 / 2) s = g s
        rw [one_smul]
        rfl }
  refine ⟨g, hg, g.continuous.isClosedEmbedding hi, hd, H, ?_⟩
  intro q
  exact hUpar (q.1.val • p) ((hnorm q.1).trans_lt hpε) q.2

end Wikipedia.HopfProblem.DegreeCollapse.LowSphereParameters
