import Wikipedia.HopfProblem.DegreeCollapseMorseCancellationHessian
import Wikipedia.SmoothSixDPoincare.MorseCompactStability
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# A supported cubic cancellation without spurious critical points

The compact transition region excludes the unique critical point of the
zero-parameter cubic. Joint continuity of the actual spatial derivative
therefore controls every sufficiently small parameter on that whole region.
Inside the unit plateau the exact cubic calculation applies; outside the
closed support the entire function germ is unchanged.
-/

noncomputable section

open Set Filter Metric
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open Wikipedia.SmoothSixDPoincare.MorsePerturbation

variable {m : ℕ} (σ : Fin m → ℝ)

def localized (φ : Model m → ℝ) (t : ℝ) (p : Model m) : ℝ :=
  cubic σ 0 p + t * φ p * p.1

theorem contDiff_localized_family {φ : Model m → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (Function.uncurry (localized σ φ)) := by
  exact ((contDiff_cubic σ 0).comp contDiff_snd).add
    ((contDiff_fst.mul (hφ.comp contDiff_snd)).mul contDiff_snd.fst)

theorem localized_zero (φ : Model m → ℝ) : localized σ φ 0 = cubic σ 0 := by
  funext p
  simp [localized]

theorem localized_eq_of_notMem_tsupport (φ : Model m → ℝ) (t : ℝ) {p : Model m}
    (hp : p ∉ tsupport φ) : localized σ φ t p = cubic σ 0 p := by
  simp [localized, image_eq_zero_of_notMem_tsupport hp]

theorem localized_germ_outside (φ : Model m → ℝ) (t : ℝ) {p : Model m}
    (hp : p ∉ tsupport φ) : localized σ φ t =ᶠ[𝓝 p] cubic σ 0 := by
  filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hp] with q hq
  exact localized_eq_of_notMem_tsupport σ φ t hq

theorem localized_germ_plateau {φ : Model m → ℝ} {U : Set (Model m)}
    (hU : IsOpen U) (hφU : EqOn φ (fun _ => 1) U) (t : ℝ) {p : Model m}
    (hp : p ∈ U) : localized σ φ t =ᶠ[𝓝 p] cubic σ t := by
  filter_upwards [hU.mem_nhds hp] with q hq
  simp [localized, cubic, hφU hq]
  ring

/-- Small parameter changes cannot introduce a critical point in the cutoff transition. -/
theorem exists_controlled_parameter (hσ : ∀ i, σ i ≠ 0)
    {φ : Model m → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    {U : Set (Model m)} (hU : IsOpen U) (h0 : (0 : Model m) ∈ U)
    (hφU : EqOn φ (fun _ => 1) U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, |t| < δ → ∀ p,
      fderiv ℝ (localized σ φ t) p = 0 ↔ p ∈ U ∧ fderiv ℝ (cubic σ t) p = 0 := by
  let K := tsupport φ \ U
  have hK : IsCompact K := hc.diff hU
  have hD := (contDiff_spatialDerivative (contDiff_localized_family σ hφ)).continuous
  have hO : IsOpen {t : ℝ | ∀ p ∈ K, fderiv ℝ (localized σ φ t) p ≠ 0} :=
    isOpen_forall_mem_compact hK (isClosed_eq hD continuous_const).isOpen_compl
  have hO0 : (0 : ℝ) ∈ {t : ℝ | ∀ p ∈ K,
      fderiv ℝ (localized σ φ t) p ≠ 0} := by
    intro p hp hcrit
    rw [localized_zero] at hcrit
    have he := (cubic_zero_unique_critical σ hσ p).mp hcrit
    exact hp.2 (he ▸ h0)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hO0)
  refine ⟨δ, hδ, ?_⟩
  intro t ht p
  have htK : ∀ q ∈ K, fderiv ℝ (localized σ φ t) q ≠ 0 :=
    hball (by simpa [Real.dist_eq] using ht)
  by_cases hp : p ∈ U
  · rw [(localized_germ_plateau σ hU hφU t hp).fderiv_eq]
    simp only [hp, true_and]
  · have hnonzero : fderiv ℝ (localized σ φ t) p ≠ 0 := by
      by_cases hs : p ∈ tsupport φ
      · exact htK p ⟨hs, hp⟩
      · rw [(localized_germ_outside σ φ t hs).fderiv_eq]
        intro hcrit
        have he := (cubic_zero_unique_critical σ hσ p).mp hcrit
        exact hp (he ▸ h0)
    simp only [hnonzero, hp, false_and]

/-- A genuine compactly supported change removes precisely the model critical pair. -/
theorem exists_supported_cancellation (hσ : ∀ i, σ i ≠ 0)
    {φ : Model m → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    {U : Set (Model m)} (hU : IsOpen U) (h0 : (0 : Model m) ∈ U)
    (hφU : EqOn φ (fun _ => 1) U) :
    ∃ a : ℝ, 0 < a ∧
      (∀ p, fderiv ℝ (localized σ φ (-(a ^ 2))) p = 0 ↔
        p = (a, 0) ∨ p = (-a, 0)) ∧
      (∀ p, fderiv ℝ (localized σ φ (a ^ 2)) p ≠ 0) ∧
      IsMorse (localized σ φ (-(a ^ 2))) ∧
      (∀ t p, p ∉ tsupport φ → localized σ φ t p = cubic σ 0 p) := by
  obtain ⟨δ, hδ, hcontrol⟩ := exists_controlled_parameter σ hσ hφ hc hU h0 hφU
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  obtain ⟨a, ha, har⟩ := exists_between (lt_min hr (lt_min zero_lt_one hδ))
  have ha1 : a < 1 := (lt_min_iff.mp (lt_min_iff.mp har).2).1
  have haδ : a < δ := (lt_min_iff.mp (lt_min_iff.mp har).2).2
  have haa : a ^ 2 < δ := by nlinarith
  have hplus : |a ^ 2| < δ := by simpa [abs_of_nonneg (sq_nonneg a)] using haa
  have hminus : |-(a ^ 2)| < δ := by simpa only [abs_neg] using hplus
  have hapos : (a, (0 : Fin m → ℝ)) ∈ U := by
    apply hball
    simpa [mem_ball_zero_iff, abs_of_pos ha] using And.intro (lt_min_iff.mp har).1 hr
  have haneg : (-a, (0 : Fin m → ℝ)) ∈ U := by
    apply hball
    simpa [mem_ball_zero_iff, abs_of_pos ha] using And.intro (lt_min_iff.mp har).1 hr
  refine ⟨a, ha, ?_, ?_, ?_, fun t p hp => localized_eq_of_notMem_tsupport σ φ t hp⟩
  · intro p
    rw [hcontrol _ hminus, negative_parameter_critical_iff σ hσ]
    constructor
    · exact And.right
    · intro h
      exact ⟨h.elim (fun hp => hp ▸ hapos) (fun hp => hp ▸ haneg), h⟩
  · intro p hcrit
    exact positive_parameter_no_critical σ hσ (sq_pos_of_pos ha) p
      ((hcontrol _ hplus p).mp hcrit).2
  · intro p hcrit
    obtain ⟨hp, hcp⟩ := (hcontrol _ hminus p).mp hcrit
    have he := localized_germ_plateau σ hU hφU (-(a ^ 2)) hp
    rw [(he.fderiv (𝕜 := ℝ)).fderiv_eq]
    exact cubic_isMorse σ hσ (neg_ne_zero.mpr (ne_of_gt (sq_pos_of_pos ha))) p hcp

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
