import Wikipedia.SmoothSixDPoincare.SmallDerivativeGerm
import Wikipedia.SmoothSixDPoincare.CompactSmoothCutoff

/-!
# Small-Lipschitz supported extensions of zero-derivative germs

A fixed unit-scale cutoff is rescaled to the small ball supplied by the
original derivative. Its inverse-radius Lipschitz growth is canceled by the
radius factor in the bound on the original displacement. The actual germ
and every zero of the displacement are retained.
-/

noncomputable section

open Set Function Filter Topology Metric
open scoped ContDiff NNReal

namespace Wikipedia.SmoothSixDPoincare.SmallPerturbation

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A smooth zero-derivative germ extends with any positive global Lipschitz bound. -/
theorem exists_lipschitz_supported_germ {u : P → E} {U : Set P}
    (hU : IsOpen U) (hzero : (0 : P) ∈ U) (hu : ContDiffOn ℝ ∞ u U)
    (hu₀ : u 0 = 0) (hdu : fderiv ℝ u 0 = 0) {κ : ℝ≥0} (hκ : 0 < κ) :
    ∃ w : P → E, ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧ tsupport w ⊆ U ∧
      LipschitzWith κ w ∧ w =ᶠ[𝓝 (0 : P)] u ∧
      ∀ x, ∃ c ∈ Icc (0 : ℝ) 1, w x = c • u x := by
  obtain ⟨β, hβ, hβcompact, hβsupport, hβone, hβrange⟩ :=
    exists_compact_smooth_cutoff (K := {(0 : P)}) (U := ball (0 : P) 1)
      isCompact_singleton isOpen_ball (by simp)
  obtain ⟨k, hk⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hβcompact hβ (by simp)
  let a : ℝ≥0 := κ / (1 + k)
  have hden : (0 : ℝ≥0) < 1 + k := by positivity
  have ha : 0 < a := div_pos hκ hden
  obtain ⟨ρ, hρ, hρU, hlocal⟩ :=
    exists_closedBall_small_lipschitz_of_fderiv_zero hU hzero hu hdu ha
  let r : ℝ≥0 := ⟨ρ, hρ.le⟩
  have hr : 0 < r := hρ
  let βρ : P → ℝ := fun x => β (ρ⁻¹ • x)
  have hβρ : ContDiff ℝ ∞ βρ :=
    hβ.comp (ρ⁻¹ • ContinuousLinearMap.id ℝ P).contDiff
  have hβρlip : LipschitzWith (k * ‖ρ⁻¹‖₊) βρ := hk.comp (lipschitzWith_smul ρ⁻¹)
  have hβρbound (x : P) : |βρ x| ≤ 1 := by
    change |β (ρ⁻¹ • x)| ≤ 1
    rw [abs_of_nonneg (hβrange _).1]
    exact (hβrange _).2
  have hβρzero (x : P) (hx : x ∉ closedBall (0 : P) ρ) : βρ x = 0 := by
    by_contra hne
    have hm : ρ⁻¹ • x ∈ ball (0 : P) 1 := hβsupport (subset_tsupport β hne)
    have hn : ‖ρ⁻¹ • x‖ < 1 := mem_ball_zero_iff.mp hm
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ), inv_mul_lt_one₀ hρ] at hn
    exact hx (mem_closedBall_zero_iff.mpr hn.le)
  have hbound : ∀ x ∈ closedBall (0 : P) ρ, ‖u x‖ ≤ (a * r : ℝ≥0) := by
    intro x hx
    have h0 : (0 : P) ∈ closedBall (0 : P) ρ := by simpa using hρ.le
    have hn := hlocal.dist_le_mul x hx 0 h0
    rw [hu₀, dist_zero_right, dist_zero_right] at hn
    change ‖u x‖ ≤ (a : ℝ) * ρ
    exact hn.trans (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hx) a.coe_nonneg)
  let w : P → E := fun x => βρ x • u x
  have hwzero (x : P) (hx : x ∉ closedBall (0 : P) ρ) : w x = 0 := by
    change βρ x • u x = 0
    rw [hβρzero x hx, zero_smul]
  have hsmooth : ContDiff ℝ ∞ w := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact hβρ.contDiffAt.smul (hu.contDiffAt (hU.mem_nhds hx))
    · have hnot : x ∉ closedBall (0 : P) ρ := fun h => hx (hρU h)
      have hc : ContDiffAt ℝ ∞ (fun _ : P => (0 : E)) x := contDiffAt_const
      apply hc.congr_of_eventuallyEq
      filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hnot] with y hy
      exact hwzero y hy
  have hcompact : HasCompactSupport w :=
    HasCompactSupport.intro (isCompact_closedBall (0 : P) ρ) hwzero
  have hsupport : tsupport w ⊆ closedBall (0 : P) ρ := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    by_contra hnot
    exact hx (hwzero x hnot)
  have hwlip : LipschitzWith (a + (k * ‖ρ⁻¹‖₊) * (a * r)) w :=
    lipschitzWith_cutoff_smul hlocal hbound hβρlip hβρbound hβρzero
  have hnn : ‖ρ‖₊ = r := Real.nnnorm_of_nonneg hρ.le
  have hcoeff : a + (k * ‖ρ⁻¹‖₊) * (a * r) = κ := by
    rw [nnnorm_inv, hnn]
    calc
      a + (k * r⁻¹) * (a * r) = a + (k * a) * (r⁻¹ * r) := by ring
      _ = a + k * a := by rw [inv_mul_cancel₀ hr.ne', mul_one]
      _ = (1 + k) * a := by ring
      _ = κ := by
        dsimp [a]
        rw [div_eq_mul_inv, ← mul_assoc, mul_comm (1 + k) κ, mul_assoc,
          mul_inv_cancel₀ hden.ne', mul_one]
  rw [hcoeff] at hwlip
  have hβ₀ : ∀ᶠ x in 𝓝 (0 : P), β x = 1 :=
    hβone.filter_mono (nhds_le_nhdsSet (mem_singleton (0 : P)))
  have hscale : Tendsto (fun x : P => ρ⁻¹ • x) (𝓝 0) (𝓝 0) := by
    have hs : Continuous (fun x : P => ρ⁻¹ • x) :=
      (ρ⁻¹ • ContinuousLinearMap.id ℝ P).continuous
    simpa only [smul_zero] using (hs.continuousAt (x := (0 : P))).tendsto
  have hgerm : w =ᶠ[𝓝 (0 : P)] u := by
    have hscaled : ∀ᶠ x in 𝓝 (0 : P), β (ρ⁻¹ • x) = 1 := hscale hβ₀
    filter_upwards [hscaled] with x hx
    change β (ρ⁻¹ • x) • u x = u x
    rw [hx, one_smul]
  refine ⟨w, hsmooth, hcompact, hsupport.trans hρU, hwlip, hgerm, ?_⟩
  intro x
  exact ⟨βρ x, hβrange _, rfl⟩

end Wikipedia.SmoothSixDPoincare.SmallPerturbation
