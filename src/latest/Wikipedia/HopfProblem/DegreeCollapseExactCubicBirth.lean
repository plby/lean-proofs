import Wikipedia.HopfProblem.DegreeCollapseExactCubicCancellation

/-!
# A supported birth of exactly two cubic critical points

Reverse the sign in the existing smooth supported cubic family. Compact
stability excludes critical points in the cutoff transition, the positive
cubic is regular outside the support, and the plateau has exactly the two
negative-cubic critical points. Both full cubic endpoint germs are retained.
This is a local birth template, not yet a native handle-trading theorem.
-/

noncomputable section

open Set Function Filter Metric
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open Wikipedia.SmoothSixDPoincare.MorsePerturbation

variable {m : ℕ} (σ : Fin m → ℝ)

theorem exists_exact_cubic_birth (hσ : ∀ i, σ i ≠ 0)
    {φ : Model m → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    {U : Set (Model m)} (hU : IsOpen U) (h0 : (0 : Model m) ∈ U)
    (hφU : EqOn φ (fun _ => 1) U) :
    ∃ a : ℝ, 0 < a ∧ (a, (0 : Fin m → ℝ)) ∈ U ∧ (-a, (0 : Fin m → ℝ)) ∈ U ∧
      ∃ g : Model m → ℝ, ContDiff ℝ ∞ g ∧
        (∀ p, fderiv ℝ g p = 0 ↔ p = (a, 0) ∨ p = (-a, 0)) ∧
        (∀ p ∈ U, g =ᶠ[𝓝 p] cubic σ (-(a ^ 2))) ∧
        ∀ p, p ∉ tsupport φ → g =ᶠ[𝓝 p] cubic σ (a ^ 2) := by
  let K := tsupport φ \ U
  have hK : IsCompact K := hc.diff hU
  have hD := (contDiff_spatialDerivative (contDiff_cancelled_family σ hφ)).continuous
  have hO : IsOpen {t : ℝ | ∀ p ∈ K, fderiv ℝ (cancelled σ φ t) p ≠ 0} :=
    isOpen_forall_mem_compact hK (isClosed_eq hD continuous_const).isOpen_compl
  have hO0 : (0 : ℝ) ∈ {t : ℝ | ∀ p ∈ K, fderiv ℝ (cancelled σ φ t) p ≠ 0} := by
    intro p hp hcrit
    rw [cancelled_zero] at hcrit
    exact hp.2 ((cubic_zero_unique_critical σ hσ p).mp hcrit ▸ h0)
  obtain ⟨δ, hδ, hδball⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hO0)
  obtain ⟨r, hr, hrball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  obtain ⟨a, ha, har⟩ := exists_between (lt_min hr (lt_min zero_lt_one hδ))
  have ha1 : a < 1 := (lt_min_iff.mp (lt_min_iff.mp har).2).1
  have haδ : a < δ := (lt_min_iff.mp (lt_min_iff.mp har).2).2
  have haa : a ^ 2 < δ := by nlinarith
  have htrans : ∀ p ∈ K, fderiv ℝ (cancelled σ φ (-(a ^ 2))) p ≠ 0 :=
    hδball (by simpa [Real.dist_eq, abs_of_nonneg (sq_nonneg a)] using haa)
  have hp : (a, (0 : Fin m → ℝ)) ∈ U := by
    apply hrball
    simpa [mem_ball_zero_iff, abs_of_pos ha] using And.intro (lt_min_iff.mp har).1 hr
  have hq : (-a, (0 : Fin m → ℝ)) ∈ U := by
    apply hrball
    simpa [mem_ball_zero_iff, abs_of_pos ha] using And.intro (lt_min_iff.mp har).1 hr
  refine ⟨a, ha, hp, hq, cancelled σ φ (-(a ^ 2)),
    (contDiff_cancelled_family σ hφ).comp (contDiff_const.prodMk contDiff_id), ?_,
    (fun p hpU => cancelled_germ_plateau σ hU hφU _ hpU), ?_⟩
  · intro p
    by_cases hpU : p ∈ U
    · rw [(cancelled_germ_plateau σ hU hφU (-(a ^ 2)) hpU).fderiv_eq]
      exact negative_parameter_critical_iff σ hσ a p
    · have hreg : fderiv ℝ (cancelled σ φ (-(a ^ 2))) p ≠ 0 := by
        by_cases hpS : p ∈ tsupport φ
        · exact htrans p ⟨hpS, hpU⟩
        · rw [(cancelled_germ_off_support σ φ (-(a ^ 2)) hpS).fderiv_eq, neg_neg]
          exact positive_parameter_no_critical σ hσ (sq_pos_of_pos ha) p
      constructor
      · exact fun h => False.elim (hreg h)
      · rintro (rfl | rfl)
        · exact False.elim (hpU hp)
        · exact False.elim (hpU hq)
  · intro p hpS
    simpa only [neg_neg] using cancelled_germ_off_support σ φ (-(a ^ 2)) hpS

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
