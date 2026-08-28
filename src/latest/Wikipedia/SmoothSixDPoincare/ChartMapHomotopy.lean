import Wikipedia.SmoothSixDPoincare.ChartMapPerturbation
import Mathlib.Topology.Homotopy.Basic

/-!
# Relative homotopies for the genuine chart perturbation

Straight-line parameter paths remain in a sufficiently small valid ball.
Their actual manifold-valued maps form a homotopy fixed on the cutoff's
zero set. Compact families of target-open conditions persist for small parameters.
-/

noncomputable section

open Set Filter ContinuousMap
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
  (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ}
  (hf : ContMDiff I J ∞ f) (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β)
  (hsupport : tsupport β ⊆ f ⁻¹' c.source)

include hf hβ hsupport in
/-- Joint continuity and compactness preserve any already satisfied target-open condition. -/
theorem eventually_maps_compact_into_open {L : Set X} (hL : IsCompact L)
    {U : Set N} (hU : IsOpen U) (hfL : MapsTo f L U) :
    ∀ᶠ a in 𝓝 (0 : F), MapsTo (perturb c f β a) L U := by
  apply hL.eventually_forall_of_forall_eventually
  intro x hx
  have hc := (contMDiffAt_perturb c hf hβ hsupport (0, x) (valid_zero c f β hsupport)).continuousAt
  apply hc.preimage_mem_nhds
  apply hU.mem_nhds
  simpa only [perturb_zero] using hfL hx

variable {ε : ℝ} (hvalid : ∀ a : F, ‖a‖ < ε → Valid c f β a)
  {a : F} (ha : ‖a‖ < ε)

include ha in
theorem norm_interval_smul_lt (t : unitInterval) : ‖(t : ℝ) • a‖ < ε := by
  calc
    ‖(t : ℝ) • a‖ = (t : ℝ) * ‖a‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg t.2.1]
    _ ≤ ‖a‖ := by nlinarith [t.2.2, norm_nonneg a]
    _ < ε := ha

/-- The actual chart perturbation is homotopic to the original map, relative to the zero set. -/
def homotopyRel :
    (⟨f, hf.continuous⟩ : C(X, N)).HomotopyRel
      ⟨perturb c f β a, (contMDiff_perturb c hf hβ hsupport (hvalid a ha)).continuous⟩
      {x | β x = 0} where
  toFun q := perturb c f β ((q.1 : ℝ) • a) q.2
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    intro q
    have hv := hvalid _ (norm_interval_smul_lt ha q.1)
    have hp : Continuous (fun r : unitInterval × X => ((r.1 : ℝ) • a, r.2)) :=
      ((continuous_subtype_val.comp continuous_fst).smul continuous_const).prodMk continuous_snd
    exact ContinuousAt.comp (f := fun r : unitInterval × X => ((r.1 : ℝ) • a, r.2))
      (contMDiffAt_perturb c hf hβ hsupport (((q.1 : ℝ) • a), q.2) hv).continuousAt
      hp.continuousAt
  map_zero_left x := by
    change perturb c f β ((0 : ℝ) • a) x = f x
    rw [zero_smul, perturb_zero]
  map_one_left x := by
    change perturb c f β ((1 : ℝ) • a) x = perturb c f β a x
    rw [one_smul]
  prop' _ x hx := perturb_eq_of_zero c f β _ hx

end Wikipedia.SmoothSixDPoincare.ChartMapPerturbation
