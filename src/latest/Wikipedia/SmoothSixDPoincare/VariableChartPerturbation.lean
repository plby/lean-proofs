import Wikipedia.SmoothSixDPoincare.ContinuousChartPerturbation
import Wikipedia.SmoothSixDPoincare.ChartMapHomotopy

/-!
# Point-dependent chart perturbations and their relative homotopies

A continuous displacement may vary with the source point. A uniform valid
parameter ball controls the entire displacement and its straight-line
homotopy. Existing pointwise smoothness is preserved when the displacement
is smooth at that point.
-/

noncomputable section

open Set ContinuousMap
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
  (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ) (a : X → F)

/-- The chart perturbation with a source-dependent displacement. -/
def variablePerturb (x : X) : N := perturb c f β (a x) x

variable {f β a}

/-- The actual source-dependent perturbation is continuous. -/
theorem continuous_variablePerturb (hf : Continuous f) (hβ : Continuous β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) (ha : Continuous a)
    (hvalid : ∀ x, Valid c f β (a x)) : Continuous (variablePerturb c f β a) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (continuousAt_perturb c hf hβ hsupport (a x, x) (hvalid x)).comp
    (f := fun y : X => (a y, y)) (ha.prodMk continuous_id).continuousAt

/-- Pointwise smoothness survives a pointwise smooth displacement. -/
theorem contMDiffAt_variablePerturb (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    {x : X} (hf : ContMDiffAt I J ∞ f x) (hβ : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ β x)
    (ha : ContMDiffAt I 𝓘(ℝ, F) ∞ a x) (hvalid : Valid c f β (a x)) :
    ContMDiffAt I J ∞ (variablePerturb c f β a) x :=
  (contMDiffAt_perturb_of_contMDiffAt c hsupport (a x, x) hf hβ hvalid).comp x
    (f := fun y : X => (a y, y))
    (ha.prodMk contMDiffAt_id)

variable (hf : Continuous f) (hβ : Continuous β) (hsupport : tsupport β ⊆ f ⁻¹' c.source)
  (ha : Continuous a) {ε : ℝ} (hvalid : ∀ v : F, ‖v‖ < ε → Valid c f β v)
  (hbound : ∀ x, ‖a x‖ < ε) {C : Set X}
  (hfixed : ∀ x ∈ C, β x = 0 ∨ a x = 0)

/-- A uniformly small displacement gives a genuine relative homotopy of manifold-valued maps. -/
def variableHomotopyRel :
    (⟨f, hf⟩ : C(X, N)).HomotopyRel
      ⟨variablePerturb c f β a,
        continuous_variablePerturb c hf hβ hsupport ha (fun x => hvalid _ (hbound x))⟩ C where
  toFun q := perturb c f β ((q.1 : ℝ) • a q.2) q.2
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    intro q
    have hv := hvalid _ (norm_interval_smul_lt (hbound q.2) q.1)
    have hp : Continuous (fun r : unitInterval × X => ((r.1 : ℝ) • a r.2, r.2)) :=
      ((continuous_subtype_val.comp continuous_fst).smul (ha.comp continuous_snd)).prodMk
        continuous_snd
    exact (continuousAt_perturb c hf hβ hsupport (((q.1 : ℝ) • a q.2), q.2) hv).comp
      (f := fun r : unitInterval × X => ((r.1 : ℝ) • a r.2, r.2)) hp.continuousAt
  map_zero_left x := by
    change perturb c f β ((0 : ℝ) • a x) x = f x
    rw [zero_smul, perturb_zero]
  map_one_left x := by
    change perturb c f β ((1 : ℝ) • a x) x = perturb c f β (a x) x
    rw [one_smul]
  prop' t x hx := by
    rcases hfixed x hx with hb | ha₀
    · exact perturb_eq_of_zero c f β _ hb
    · change perturb c f β ((t : ℝ) • a x) x = f x
      rw [ha₀, smul_zero, perturb_zero]

end Wikipedia.SmoothSixDPoincare.ChartMapPerturbation
