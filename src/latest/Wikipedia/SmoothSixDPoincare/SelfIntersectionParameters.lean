import Wikipedia.SmoothSixDPoincare.ChartMapPerturbation
import Wikipedia.SmoothSixDPoincare.ManifoldImageDimension

/-!
# Chart parameters producing new self-intersections

Two points with different cutoff values can coincide after a chart translation
only at one explicitly determined parameter. The image of these bad parameters
has dimension at most twice the source dimension. Outside that image no new
coincidences are created, and every old coincidence with different cutoff
values is removed.
-/

noncomputable section

open Set
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ChartMapPerturbation

variable {E G F H K X N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K}
  [TopologicalSpace X] [ChartedSpace H X]
  [TopologicalSpace N] [ChartedSpace K N]
  (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ)

def collisionDomain : Set (X × X) :=
  {q | f q.1 ∈ c.source ∧ f q.2 ∈ c.source ∧ β q.1 - β q.2 ≠ 0}

def collisionParameter (q : X × X) : F :=
  (β q.1 - β q.2)⁻¹ • (c (f q.2) - c (f q.1))

variable {f β}

theorem isOpen_collisionDomain (hf : Continuous f) (hβ : Continuous β) :
    IsOpen (collisionDomain c f β) :=
  (c.open_source.preimage (hf.comp continuous_fst)).inter
    ((c.open_source.preimage (hf.comp continuous_snd)).inter
      (isOpen_ne_fun ((hβ.comp continuous_fst).sub (hβ.comp continuous_snd)) continuous_const))

theorem contMDiffOn_collisionParameter (hf : ContMDiff I J ∞ f)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) :
    ContMDiffOn (I.prod I) 𝓘(ℝ, F) ∞ (collisionParameter c f β) (collisionDomain c f β) := by
  intro q hq
  have hcf : ContMDiffAt (I.prod I) 𝓘(ℝ, F) ∞ (fun r : X × X => c (f r.1)) q :=
    (c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hq.1)).comp q
      (hf.comp contMDiff_fst).contMDiffAt
  have hcg : ContMDiffAt (I.prod I) 𝓘(ℝ, F) ∞ (fun r : X × X => c (f r.2)) q :=
    (c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hq.2.1)).comp q
      (hf.comp contMDiff_snd).contMDiffAt
  have hb : ContMDiffAt (I.prod I) 𝓘(ℝ, ℝ) ∞ (fun r : X × X => β r.1 - β r.2) q :=
    (hβ.comp contMDiff_fst).contMDiffAt.sub (hβ.comp contMDiff_snd).contMDiffAt
  exact ((hb.inv₀ hq.2.2).smul (hcg.sub hcf)).contMDiffWithinAt

/-- A good parameter cannot create a new coincidence, and it separates all pairs whose cutoff
values differ. This controls all source pairs, not merely a compact subset. -/
theorem collision_imp_old_and_equal_cutoff (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    {a : F} (hvalid : Valid c f β a)
    (hgood : a ∉ collisionParameter c f β '' collisionDomain c f β)
    {x y : X} (heq : perturb c f β a x = perturb c f β a y) :
    f x = f y ∧ β x = β y := by
  classical
  by_cases hx : f x ∈ c.source
  · have hpy : perturb c f β a y ∈ c.source := heq ▸ perturb_mem_source c f β hvalid hx
    have hy : f y ∈ c.source := by
      by_contra hn
      simp only [perturb, hn, if_false] at hpy
    have hcoord : c (f x) + β x • a = c (f y) + β y • a := by
      have hh := congrArg c heq
      simpa only [chart_perturb c f β hvalid hx, chart_perturb c f β hvalid hy,
        coordinateFamily] using hh
    by_cases hb : β x = β y
    · refine ⟨c.toPartialEquiv.injOn hx hy ?_, hb⟩
      rw [hb] at hcoord
      exact add_right_cancel hcoord
    · have hd : β x - β y ≠ 0 := sub_ne_zero.mpr hb
      have hs : (β x - β y) • a = c (f y) - c (f x) := by
        rw [sub_smul]
        exact sub_eq_sub_iff_add_eq_add.mpr (by simpa only [add_comm] using hcoord)
      exfalso
      apply hgood
      refine ⟨(x, y), ⟨hx, hy, hd⟩, ?_⟩
      change (β x - β y)⁻¹ • (c (f y) - c (f x)) = a
      rw [← hs, inv_smul_smul₀ hd]
  · have hpx : perturb c f β a x = f x := by simp only [perturb, hx, if_false]
    have hy : f y ∉ c.source := by
      intro hy
      have hpy := perturb_mem_source c f β hvalid hy
      rw [← heq, hpx] at hpy
      exact hx hpy
    have hpy : perturb c f β a y = f y := by simp only [perturb, hy, if_false]
    have hβx : β x = 0 := by
      by_contra hn
      exact hx (hsupport (subset_tsupport β hn))
    have hβy : β y = 0 := by
      by_contra hn
      exact hy (hsupport (subset_tsupport β hn))
    exact ⟨hpx.symm.trans (heq.trans hpy), hβx.trans hβy.symm⟩

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [IsManifold I ∞ X] [LindelofSpace (X × X)]

/-- Arbitrarily small valid parameters remove all coincidences with different cutoff values
without creating any new coincidences anywhere. -/
theorem exists_small_collision_removing_parameter (hf : ContMDiff I J ∞ f)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    (hdim : 2 * Module.finrank ℝ E < Module.finrank ℝ F) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : F, ‖a‖ < ε ∧ Valid c f β a ∧ ContMDiff I J ∞ (perturb c f β a) ∧
      ∀ x y, perturb c f β a x = perturb c f β a y → f x = f y ∧ β x = β y := by
  have hd : Module.finrank ℝ (E × E) < Module.finrank ℝ F := by
    simpa only [Module.finrank_prod, two_mul] using hdim
  have hdense := GeneralPosition.dense_compl_manifold_image
    (isOpen_collisionDomain c hf.continuous hβ.continuous)
    (contMDiffOn_collisionParameter c hf hβ) hd
  obtain ⟨δ, hδ, hvalid⟩ := exists_radius_valid c hf hβ hcompact hsupport
  obtain ⟨a, hgood, har⟩ := hdense.exists_dist_lt 0 (lt_min hε hδ)
  have ha : ‖a‖ < min ε δ := by simpa only [dist_zero_left] using har
  have hv := hvalid a (lt_of_lt_of_le ha (min_le_right _ _))
  exact ⟨a, lt_of_lt_of_le ha (min_le_left _ _), hv, contMDiff_perturb c hf hβ hsupport hv,
    fun _ _ heq => collision_imp_old_and_equal_cutoff c hsupport hv hgood heq⟩

end Wikipedia.SmoothSixDPoincare.ChartMapPerturbation
