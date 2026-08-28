import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Topology.Algebra.Support

/-!
# Compactly supported perturbations of maps into a manifold

A small vector is added in a genuine target chart, multiplied by a smooth
source cutoff. The compact support lies over that chart. The map is unchanged
elsewhere, and smoothness is proved for the actual piecewise map.
-/

noncomputable section

open Set Filter
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

/-- The translated target-chart coordinate, with parameter and point kept explicit. -/
def coordinateFamily (q : F × X) : F := c (f q.2) + β q.2 • q.1

/-- Parameters for which the whole supported perturbation stays inside the target chart. -/
def Valid (a : F) : Prop := ∀ x ∈ tsupport β, coordinateFamily c f β (a, x) ∈ c.target

/-- The actual perturbed map, equal to the original map off the target chart. -/
def perturb (a : F) (x : X) : N := by
  classical
  exact if f x ∈ c.source then c.symm (coordinateFamily c f β (a, x)) else f x

omit [TopologicalSpace X] in
theorem perturb_eq_of_zero (a : F) {x : X} (hx : β x = 0) :
    perturb c f β a x = f x := by
  classical
  by_cases hs : f x ∈ c.source
  · simp only [perturb, hs, if_pos, coordinateFamily, hx, zero_smul, add_zero]
    exact c.left_inv' hs
  · simp only [perturb, hs, if_false]

omit [TopologicalSpace X] in
theorem perturb_zero (x : X) : perturb c f β 0 x = f x := by
  classical
  by_cases hs : f x ∈ c.source
  · simp only [perturb, hs, if_pos, coordinateFamily, smul_zero, add_zero]
    exact c.left_inv' hs
  · simp only [perturb, hs, if_false]

theorem valid_zero (hsupport : tsupport β ⊆ f ⁻¹' c.source) : Valid c f β (0 : F) := by
  intro x hx
  simpa only [coordinateFamily, smul_zero, add_zero] using c.map_source' (hsupport hx)

theorem coordinate_mem_target {a : F} (ha : Valid c f β a) {x : X}
    (hx : f x ∈ c.source) : coordinateFamily c f β (a, x) ∈ c.target := by
  by_cases hβx : β x = 0
  · simpa only [coordinateFamily, hβx, zero_smul, add_zero] using c.map_source' hx
  · exact ha x (subset_tsupport β hβx)

theorem perturb_mem_source {a : F} (ha : Valid c f β a) {x : X}
    (hx : f x ∈ c.source) : perturb c f β a x ∈ c.source := by
  classical
  simp only [perturb, hx, if_pos]
  exact c.map_target' (coordinate_mem_target c f β ha hx)

theorem chart_perturb {a : F} (ha : Valid c f β a) {x : X}
    (hx : f x ∈ c.source) : c (perturb c f β a x) = coordinateFamily c f β (a, x) := by
  classical
  simp only [perturb, hx, if_pos]
  exact c.right_inv' (coordinate_mem_target c f β ha hx)

variable {f β}

theorem contMDiffAt_coordinateFamily (hf : ContMDiff I J ∞ f)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) (q : F × X) (hq : f q.2 ∈ c.source) :
    ContMDiffAt (𝓘(ℝ, F).prod I) 𝓘(ℝ, F) ∞ (coordinateFamily c f β) q :=
  ((c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hq)).comp q
    (hf.comp contMDiff_snd).contMDiffAt).add
    (((hβ.comp contMDiff_snd).contMDiffAt).smul contMDiffAt_fst)

/-- Compactness gives one parameter neighborhood valid over the entire support. -/
theorem eventually_valid (hf : ContMDiff I J ∞ f)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) : ∀ᶠ a in 𝓝 (0 : F), Valid c f β a := by
  apply hcompact.isCompact.eventually_forall_of_forall_eventually
  intro x hx
  have hh := (contMDiffAt_coordinateFamily c hf hβ (0, x) (hsupport hx)).continuousAt
  apply hh.preimage_mem_nhds
  apply c.open_target.mem_nhds
  simpa only [coordinateFamily, smul_zero, add_zero] using c.map_source' (hsupport hx)

/-- A whole open parameter ball, including every straight-line homotopy to zero, is valid. -/
theorem exists_radius_valid (hf : ContMDiff I J ∞ f)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) :
    ∃ ε > (0 : ℝ), ∀ a : F, ‖a‖ < ε → Valid c f β a := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (eventually_valid c hf hβ hcompact hsupport)
  exact ⟨ε, hε, fun a ha => hball (by simpa only [Metric.mem_ball, dist_zero_right] using ha)⟩

/-- The map family is jointly smooth at every valid parameter and every source point. -/
theorem contMDiffAt_perturb (hf : ContMDiff I J ∞ f)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    (q : F × X) (ha : Valid c f β q.1) :
    ContMDiffAt (𝓘(ℝ, F).prod I) J ∞ (fun r : F × X => perturb c f β r.1 r.2) q := by
  classical
  by_cases hx : f q.2 ∈ c.source
  · have hcoord := contMDiffAt_coordinateFamily c hf hβ q hx
    have htarget := coordinate_mem_target c f β ha hx
    have hh := (c.contMDiffOn_invFun.contMDiffAt (c.open_target.mem_nhds htarget)).comp q hcoord
    apply hh.congr_of_eventuallyEq
    have hs : ∀ᶠ r : F × X in 𝓝 q, f r.2 ∈ c.source :=
      (hf.continuous.comp continuous_snd).continuousAt.preimage_mem_nhds
        (c.open_source.mem_nhds hx)
    filter_upwards [hs] with r hr
    simp only [perturb, hr, if_pos, Function.comp_apply]
    rfl
  · have hn : q.2 ∉ tsupport β := fun h => hx (hsupport h)
    have hz : β =ᶠ[𝓝 q.2] 0 := notMem_tsupport_iff_eventuallyEq.mp hn
    apply (hf.comp contMDiff_snd).contMDiffAt.congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.tendsto.eventually hz] with r hr
    exact perturb_eq_of_zero c f β r.1 hr

/-- Every valid parameter gives a globally smooth map into the original target manifold. -/
theorem contMDiff_perturb (hf : ContMDiff I J ∞ f)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    {a : F} (ha : Valid c f β a) : ContMDiff I J ∞ (perturb c f β a) := by
  intro x
  exact (contMDiffAt_perturb c hf hβ hsupport (a, x) ha).comp x
    (contMDiffAt_const.prodMk contMDiffAt_id)

end Wikipedia.SmoothSixDPoincare.ChartMapPerturbation
