import Wikipedia.SmoothSixDPoincare.ChartMapPerturbation
import Wikipedia.SmoothSixDPoincare.ManifoldImageDimension

/-!
# Explicit chart parameters meeting a smooth obstacle

Where the source cutoff is nonzero, a collision with the obstacle determines
the translation parameter. These parameters are the image of an actual smooth
map on an open subset of the source product.
-/

noncomputable section

open Set
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ChartMapPerturbation

variable {E E' G F H H' K X Y N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  {J : ModelWithCorners ℝ G K}
  [TopologicalSpace X] [ChartedSpace H X]
  [TopologicalSpace Y] [ChartedSpace H' Y]
  [TopologicalSpace N] [ChartedSpace K N]
  (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (g : Y → N) (β : X → ℝ)

def obstacleDomain : Set (X × Y) :=
  {q | f q.1 ∈ c.source ∧ g q.2 ∈ c.source ∧ β q.1 ≠ 0}

def obstacleParameter (q : X × Y) : F := (β q.1)⁻¹ • (c (g q.2) - c (f q.1))

variable {f g β}

theorem isOpen_obstacleDomain (hf : Continuous f) (hg : Continuous g) (hβ : Continuous β) :
    IsOpen (obstacleDomain c f g β) :=
  (c.open_source.preimage (hf.comp continuous_fst)).inter
    ((c.open_source.preimage (hg.comp continuous_snd)).inter
      (isOpen_ne_fun (hβ.comp continuous_fst) continuous_const))

theorem contMDiffOn_obstacleParameter (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) :
    ContMDiffOn (I.prod I') 𝓘(ℝ, F) ∞ (obstacleParameter c f g β) (obstacleDomain c f g β) := by
  intro q hq
  have hcf : ContMDiffAt (I.prod I') 𝓘(ℝ, F) ∞ (fun r : X × Y => c (f r.1)) q :=
    (c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hq.1)).comp q
      (hf.comp contMDiff_fst).contMDiffAt
  have hcg : ContMDiffAt (I.prod I') 𝓘(ℝ, F) ∞ (fun r : X × Y => c (g r.2)) q :=
    (c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hq.2.1)).comp q
      (hg.comp contMDiff_snd).contMDiffAt
  exact (((hβ.comp contMDiff_fst).contMDiffAt.inv₀ hq.2.2).smul
    (hcg.sub hcf)).contMDiffWithinAt

omit [TopologicalSpace Y] in
/-- Avoiding the explicit bad image removes every obstacle collision on the active source. -/
theorem avoids_of_not_obstacle_parameter (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    {a : F} (ha : Valid c f β a)
    (hgood : a ∉ obstacleParameter c f g β '' obstacleDomain c f g β)
    (x : X) (hx : β x ≠ 0) (y : Y) : perturb c f β a x ≠ g y := by
  intro heq
  have hfx : f x ∈ c.source := hsupport (subset_tsupport β hx)
  have hgy : g y ∈ c.source := heq ▸ perturb_mem_source c f β ha hfx
  have hcoord : c (f x) + β x • a = c (g y) := by
    rw [← heq, chart_perturb c f β ha hfx]
    rfl
  apply hgood
  refine ⟨(x, y), ⟨hfx, hgy, hx⟩, ?_⟩
  change (β x)⁻¹ • (c (g y) - c (f x)) = a
  rw [← hcoord, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hx, one_smul]

end Wikipedia.SmoothSixDPoincare.ChartMapPerturbation
