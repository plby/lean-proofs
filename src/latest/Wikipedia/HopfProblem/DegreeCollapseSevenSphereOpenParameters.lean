import Wikipedia.HopfProblem.DegreeCollapseSevenSphereJetAvoidance
import Wikipedia.NoExoticSixSphere.UniformProductTube

/-!
# One small parameter avoids singularities and stays in the original open subset

Countable chart intersection combines the two proved almost-everywhere
avoidance conditions. Density chooses one arbitrarily small parameter.
Independently, the actual smooth tubular family and the tube lemma over
the compact original sphere give a parameter ball whose whole fixed-time
slice remains in a prescribed original open subset containing the map.
-/

noncomputable section

open Function Set TopologicalSpace
open MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSphereParameters

open NoExoticSixSphere GLOrthonormalization EuclideanEmbedding ManifoldAffineSphereFamily

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e)

theorem exists_small_avoiding_parameter (f : ℝ → Sphere 3 → M)
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
    (t : ℝ) (hn : 6 < n) (S : Set SourceChart) (hS : S.Countable)
    (C : Set (TargetChart n M)) (hC : C.Countable) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Parameters e, ‖p‖ < ε ∧ AvoidPairsInCharts e r f hf t S C p ∧
      AvoidDirectionsInCharts e r f hf t S C p := by
  let : MeasurableSpace (Parameters e) := borel (Parameters e)
  let : BorelSpace (Parameters e) := ⟨rfl⟩
  have ha := (ae_avoidPairsInCharts e r f hf t addHaar hn S hS C hC).and
    (ae_avoidDirectionsInCharts e r f hf t addHaar hn S hS C hC)
  obtain ⟨p, hp, hsmall⟩ := (Measure.dense_of_ae ha).exists_dist_lt 0 hε
  exact ⟨p, by simpa only [dist_zero_left] using hsmall, hp.1, hp.2⟩

variable [CompactSpace M]

theorem exists_open_parameter_radius (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 n) ∞ f) (U : Set M) (hU : IsOpen U)
    (hfU : ∀ s, f s ∈ U) (t : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p : Parameters e, ‖p‖ < ε → ∀ s : Sphere 3,
      ManifoldAffineSphereFamily.map e r (fun _ s ↦ f s) p t s ∈ U := by
  let f₀ : ℝ → Sphere 3 → M := fun _ s ↦ f s
  have hf₀ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f₀) :=
    hf.comp contMDiff_snd
  obtain ⟨δ, hδ, _, hP⟩ := exists_smooth_parameter_ball e r f₀ hf₀
  let V : Set (Sphere 3 × Parameters e) := {q | ‖q.2‖ < δ}
  let G : Sphere 3 × Parameters e → M :=
    fun q ↦ ManifoldAffineSphereFamily.map e r f₀ q.2 t q.1
  have hV : IsOpen V := isOpen_lt (continuous_norm.comp continuous_snd) continuous_const
  have hlift : ContMDiff ((𝓡 3).prod 𝓘(ℝ, Parameters e))
      (𝓘(ℝ, Parameters e).prod (𝓘(ℝ, ℝ).prod (𝓡 3))) ∞
      (fun q : Sphere 3 × Parameters e ↦ (q.2, (t, q.1))) :=
    contMDiff_snd.prodMk (contMDiff_const.prodMk contMDiff_fst)
  have hG : ContMDiffOn ((𝓡 3).prod 𝓘(ℝ, Parameters e)) (𝓡 n) ∞ G V :=
    hP.comp hlift.contMDiffOn (fun _ hq ↦ hq)
  have hW : IsOpen (V ∩ G ⁻¹' U) := hG.continuousOn.isOpen_inter_preimage hV hU
  have hzero (s : Sphere 3) : (s, (0 : Parameters e)) ∈ V ∩ G ⁻¹' U := by
    refine ⟨?_, ?_⟩
    · change ‖(0 : Parameters e)‖ < δ
      simpa only [norm_zero] using hδ
    · change ManifoldAffineSphereFamily.map e r f₀ 0 t s ∈ U
      rw [map_zero_parameter]
      exact hfU s
  obtain ⟨ε, hε, hsub⟩ := exists_uniform_closedProductTube hW hzero
  exact ⟨ε, hε, fun p hp s ↦ (hsub s p hp.le).2⟩

end Wikipedia.HopfProblem.DegreeCollapse.SevenSphereParameters
