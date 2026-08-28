import Wikipedia.SmoothSixDPoincare.VariableChartPerturbation
import Wikipedia.SmoothSixDPoincare.ChartCoordinateApproximation

/-!
# Smoothing a manifold-valued map on a chart plateau

A smooth approximation to the cutoff coordinates determines a small
point-dependent displacement. On the inner cutoff's unit plateau the
result is exactly the smooth approximation mapped through the inverse chart.
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
  (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β χ : X → ℝ) (g : X → F)

/-- The actual manifold-valued map obtained by replacing coordinates on a unit plateau. -/
def smoothedMap : X → N :=
  variablePerturb c f β (fun x => g x - cutoffCoordinates c f χ x)

omit [TopologicalSpace X] in
theorem coordinateFamily_eq_on_plateau {x : X} (hβx : β x = 1) (hχx : χ x = 1) :
    coordinateFamily c f β (g x - cutoffCoordinates c f χ x, x) = g x := by
  simp only [coordinateFamily, cutoffCoordinates, hβx, hχx, one_smul]
  abel

theorem smoothedMap_eq_on_plateau (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    (hnested : ∀ x ∈ tsupport β, χ x = 1) {x : X} (hβx : β x = 1) :
    smoothedMap c f β χ g x = c.symm (g x) := by
  classical
  have hs : x ∈ tsupport β := subset_tsupport β (by
    change β x ≠ 0
    rw [hβx]
    exact one_ne_zero)
  change perturb c f β (g x - cutoffCoordinates c f χ x) x = _
  have hsource : f x ∈ c.source := hsupport hs
  simp only [perturb, hsource, if_pos]
  rw [coordinateFamily_eq_on_plateau c f β χ g hβx (hnested x hs)]

variable {f β χ g}

/-- The smoothed map is genuinely smooth near every inner unit-plateau point. -/
theorem contMDiffAt_smoothedMap_on_plateau (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    (hnested : ∀ x ∈ tsupport β, χ x = 1) {x : X}
    (hplateau : β =ᶠ[𝓝 x] (fun _ => 1)) (hg : ContMDiffAt I 𝓘(ℝ, F) ∞ g x)
    (hvalid : Valid c f β (g x - cutoffCoordinates c f χ x)) :
    ContMDiffAt I J ∞ (smoothedMap c f β χ g) x := by
  have hβx : β x = 1 := hplateau.eq_of_nhds
  have hs : x ∈ tsupport β := subset_tsupport β (by
    change β x ≠ 0
    rw [hβx]
    exact one_ne_zero)
  have htarget := coordinate_mem_target c f β hvalid (hsupport hs)
  rw [coordinateFamily_eq_on_plateau c f β χ g hβx (hnested x hs)] at htarget
  have hh := (c.contMDiffOn_invFun.contMDiffAt (c.open_target.mem_nhds htarget)).comp x hg
  apply hh.congr_of_eventuallyEq
  filter_upwards [hplateau] with y hy
  exact smoothedMap_eq_on_plateau c f β χ g hsupport hnested hy

/-- The local smoothing step does not destroy smoothness at any previously smooth point. -/
theorem contMDiffAt_smoothedMap_of_old
    (hβsupport : tsupport β ⊆ f ⁻¹' c.source) (hχsupport : tsupport χ ⊆ f ⁻¹' c.source)
    {x : X} (hf : ContMDiffAt I J ∞ f x) (hβ : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ β x)
    (hχ : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ χ x) (hg : ContMDiffAt I 𝓘(ℝ, F) ∞ g x)
    (hvalid : Valid c f β (g x - cutoffCoordinates c f χ x)) :
    ContMDiffAt I J ∞ (smoothedMap c f β χ g) x :=
  contMDiffAt_variablePerturb c hβsupport hf hβ
    (hg.sub (contMDiffAt_cutoffCoordinates c hχsupport hf hχ)) hvalid

end Wikipedia.SmoothSixDPoincare.ChartMapPerturbation
