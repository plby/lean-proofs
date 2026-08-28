import Wikipedia.HopfProblem.DegreeCollapseMorseCancellationSupport

/-!
# Supported cancellation starting from the exact cubic normal form

The initial function is the uncut cubic `C_{-a²}`. Only the change to the
function is cut off. Compact control of the transition and the exact two
initial critical points prove that the final function is regular everywhere.
This removes the cutoff from the normal-form placement required on a manifold.
-/

noncomputable section

open Set Filter Metric
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open Wikipedia.SmoothSixDPoincare.MorsePerturbation

variable {m : ℕ} (σ : Fin m → ℝ)

def cancelled (φ : Model m → ℝ) (t : ℝ) (p : Model m) : ℝ :=
  cubic σ (-t) p + 2 * t * φ p * p.1

theorem contDiff_cancelled_family {φ : Model m → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (Function.uncurry (cancelled σ φ)) := by
  exact ((contDiff_cubic_family σ).comp (contDiff_fst.neg.prodMk contDiff_snd)).add
    (((contDiff_const.mul contDiff_fst).mul (hφ.comp contDiff_snd)).mul contDiff_snd.fst)

theorem cancelled_zero (φ : Model m → ℝ) : cancelled σ φ 0 = cubic σ 0 := by
  funext p
  simp [cancelled]

theorem cancelled_germ_plateau {φ : Model m → ℝ} {U : Set (Model m)}
    (hU : IsOpen U) (hφU : EqOn φ (fun _ => 1) U) (t : ℝ) {p : Model m}
    (hp : p ∈ U) : cancelled σ φ t =ᶠ[𝓝 p] cubic σ t := by
  filter_upwards [hU.mem_nhds hp] with q hq
  simp [cancelled, cubic, hφU hq]
  ring

theorem cancelled_eq_off_support (φ : Model m → ℝ) (t : ℝ) {p : Model m}
    (hp : p ∉ tsupport φ) : cancelled σ φ t p = cubic σ (-t) p := by
  simp [cancelled, image_eq_zero_of_notMem_tsupport hp]

theorem cancelled_germ_off_support (φ : Model m → ℝ) (t : ℝ) {p : Model m}
    (hp : p ∉ tsupport φ) : cancelled σ φ t =ᶠ[𝓝 p] cubic σ (-t) := by
  filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hp] with q hq
  exact cancelled_eq_off_support σ φ t hq

/-- Construct a parameter for which the exact cubic pair can be removed
by a change supported in the prescribed cutoff. -/
theorem exists_exact_cubic_cancellation (hσ : ∀ i, σ i ≠ 0)
    {φ : Model m → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    {U : Set (Model m)} (hU : IsOpen U) (h0 : (0 : Model m) ∈ U)
    (hφU : EqOn φ (fun _ => 1) U) :
    ∃ a : ℝ, 0 < a ∧ (a, (0 : Fin m → ℝ)) ∈ U ∧ (-a, (0 : Fin m → ℝ)) ∈ U ∧
      ContDiff ℝ ∞ (cancelled σ φ (a ^ 2)) ∧
      (∀ p, fderiv ℝ (cancelled σ φ (a ^ 2)) p ≠ 0) ∧
      (∀ p, p ∉ tsupport φ → cancelled σ φ (a ^ 2) p = cubic σ (-(a ^ 2)) p) := by
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
  have htrans : ∀ p ∈ K, fderiv ℝ (cancelled σ φ (a ^ 2)) p ≠ 0 :=
    hδball (by simpa [Real.dist_eq, abs_of_nonneg (sq_nonneg a)] using haa)
  have hp : (a, (0 : Fin m → ℝ)) ∈ U := by
    apply hrball
    simpa [mem_ball_zero_iff, abs_of_pos ha] using And.intro (lt_min_iff.mp har).1 hr
  have hq : (-a, (0 : Fin m → ℝ)) ∈ U := by
    apply hrball
    simpa [mem_ball_zero_iff, abs_of_pos ha] using And.intro (lt_min_iff.mp har).1 hr
  refine ⟨a, ha, hp, hq,
    (contDiff_cancelled_family σ hφ).comp (contDiff_const.prodMk contDiff_id), ?_,
    fun p hp => cancelled_eq_off_support σ φ _ hp⟩
  intro p hcrit
  by_cases hpU : p ∈ U
  · rw [(cancelled_germ_plateau σ hU hφU (a ^ 2) hpU).fderiv_eq] at hcrit
    exact positive_parameter_no_critical σ hσ (sq_pos_of_pos ha) p hcrit
  · by_cases hpS : p ∈ tsupport φ
    · exact htrans p ⟨hpS, hpU⟩ hcrit
    · rw [(cancelled_germ_off_support σ φ (a ^ 2) hpS).fderiv_eq] at hcrit
      rcases (negative_parameter_critical_iff σ hσ a p).mp hcrit with h | h
      · exact hpU (h ▸ hp)
      · exact hpU (h ▸ hq)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
