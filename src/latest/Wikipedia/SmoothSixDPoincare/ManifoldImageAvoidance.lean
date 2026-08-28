import Wikipedia.SmoothSixDPoincare.ChartMapPerturbation
import Wikipedia.SmoothSixDPoincare.SmoothImageAvoidance

/-!
# Localized image avoidance in the original target manifold

The bad parameters are computed only where both maps land in the genuine
target chart. Compact support keeps the perturbed map in that chart, and
the low-dimensional image theorem supplies a small good parameter.
-/

noncomputable section

open Set
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ChartMapPerturbation

variable {E E' G F H H' K X Y N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  {J : ModelWithCorners ℝ G K}
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y]
  [TopologicalSpace N] [ChartedSpace K N]
  [LindelofSpace (X × Y)]

/-- A small smooth perturbation in an actual target chart avoids the obstacle on its active set. -/
theorem exists_small_avoiding_parameter (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞)
    {f : X → N} {g : Y → N} {β : X → ℝ}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    (hdim : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ F)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : F, ‖a‖ < ε ∧ Valid c f β a ∧
      ContMDiff I J ∞ (perturb c f β a) ∧
      ∀ x, β x ≠ 0 → ∀ y, perturb c f β a x ≠ g y := by
  let s : Set (X × Y) := {p | f p.1 ∈ c.source ∧ g p.2 ∈ c.source ∧ β p.1 ≠ 0}
  let bad : X × Y → F := fun p => (β p.1)⁻¹ • (c (g p.2) - c (f p.1))
  have hs : IsOpen s :=
    (c.open_source.preimage (hf.continuous.comp continuous_fst)).inter
      ((c.open_source.preimage (hg.continuous.comp continuous_snd)).inter
        (isOpen_ne_fun (hβ.continuous.comp continuous_fst) continuous_const))
  have hb : ContMDiffOn (I.prod I') 𝓘(ℝ, F) ∞ bad s := by
    intro p hp
    have hcf : ContMDiffAt (I.prod I') 𝓘(ℝ, F) ∞ (fun q : X × Y => c (f q.1)) p :=
      (c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hp.1)).comp p
      (hf.comp contMDiff_fst).contMDiffAt
    have hcg : ContMDiffAt (I.prod I') 𝓘(ℝ, F) ∞ (fun q : X × Y => c (g q.2)) p :=
      (c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hp.2.1)).comp p
      (hg.comp contMDiff_snd).contMDiffAt
    exact (((hβ.comp contMDiff_fst).contMDiffAt.inv₀ hp.2.2).smul
      (hcg.sub hcf)).contMDiffWithinAt
  have hd : Module.finrank ℝ (E × E') < Module.finrank ℝ F := by
    simpa only [Module.finrank_prod] using hdim
  have hdense := GeneralPosition.dense_compl_manifold_image hs hb hd
  obtain ⟨δ, hδ, hvalid⟩ := exists_radius_valid c hf hβ hcompact hsupport
  obtain ⟨a, ha, har⟩ := hdense.exists_dist_lt 0 (lt_min hε hδ)
  have haε : ‖a‖ < ε := (lt_min_iff.mp (show ‖a‖ < min ε δ by
    simpa only [dist_zero_left] using har)).1
  have haδ : ‖a‖ < δ := (lt_min_iff.mp (show ‖a‖ < min ε δ by
    simpa only [dist_zero_left] using har)).2
  have hva : Valid c f β a := hvalid a haδ
  refine ⟨a, haε, hva, contMDiff_perturb c hf hβ hsupport hva, ?_⟩
  intro x hx y hxy
  have hfx : f x ∈ c.source := hsupport (subset_tsupport β hx)
  have hgy : g y ∈ c.source := hxy ▸ perturb_mem_source c f β hva hfx
  have heq : c (f x) + β x • a = c (g y) := by
    rw [← hxy, chart_perturb c f β hva hfx]
    rfl
  apply ha
  refine ⟨(x, y), ⟨hfx, hgy, hx⟩, ?_⟩
  change (β x)⁻¹ • (c (g y) - c (f x)) = a
  rw [← heq, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hx, one_smul]

end Wikipedia.SmoothSixDPoincare.ChartMapPerturbation
