import ErdosProblems.Erdos1002.FixedAwayPVTransform
import ErdosProblems.Erdos1002.GevreyCutoff

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A uniform smooth cutoff for the fixed-away threshold

For `0 < δ < t`, this file constructs an even cutoff `χ_{t,δ}` which is
zero on `|x| ≤ t - δ` and one on `t ≤ |x|`.  Its compact correction
`κ_{t,δ} = 1 - χ_{t,δ}` takes values in `[0,1]`, is supported in
`[-t,t]`, and has Gevrey derivative bounds independent of the moving
threshold `t`.  These are the uniform cutoff facts required before proving
the analytic decay of the fixed-away principal-value multiplier.
-/

open Filter Set
open scoped Real Topology

namespace Erdos1002

noncomputable section

/-- Even two-sided transition from the inner interval to its complement. -/
def fixedAwaySmoothCutoff (t δ x : ℝ) : ℝ :=
  gevreyTransition (δ⁻¹ * x + (1 - δ⁻¹ * t)) +
    gevreyTransition ((-δ⁻¹) * x + (1 - δ⁻¹ * t))

/-- Compact correction `κ = 1 - χ`. -/
def fixedAwaySmoothCorrection (t δ x : ℝ) : ℝ :=
  1 - fixedAwaySmoothCutoff t δ x

theorem fixedAwaySmoothCutoff_even (t δ : ℝ) :
    Function.Even (fixedAwaySmoothCutoff t δ) := by
  intro x
  unfold fixedAwaySmoothCutoff
  calc
    gevreyTransition (δ⁻¹ * -x + (1 - δ⁻¹ * t)) +
        gevreyTransition ((-δ⁻¹) * -x + (1 - δ⁻¹ * t)) =
      gevreyTransition ((-δ⁻¹) * x + (1 - δ⁻¹ * t)) +
        gevreyTransition (δ⁻¹ * x + (1 - δ⁻¹ * t)) := by
      congr 1 <;> ring_nf
    _ = gevreyTransition (δ⁻¹ * x + (1 - δ⁻¹ * t)) +
        gevreyTransition ((-δ⁻¹) * x + (1 - δ⁻¹ * t)) := add_comm _ _

theorem fixedAwaySmoothCorrection_even (t δ : ℝ) :
    Function.Even (fixedAwaySmoothCorrection t δ) := by
  intro x
  rw [fixedAwaySmoothCorrection, fixedAwaySmoothCorrection,
    fixedAwaySmoothCutoff_even t δ x]

theorem fixedAwaySmoothCutoff_contDiff
    {m : ℕ∞} (t δ : ℝ) :
    ContDiff ℝ m (fixedAwaySmoothCutoff t δ) := by
  unfold fixedAwaySmoothCutoff
  exact (gevreyTransition_affine_contDiff δ⁻¹ (1 - δ⁻¹ * t)).add
    (gevreyTransition_affine_contDiff (-δ⁻¹) (1 - δ⁻¹ * t))

theorem fixedAwaySmoothCorrection_contDiff
    {m : ℕ∞} (t δ : ℝ) :
    ContDiff ℝ m (fixedAwaySmoothCorrection t δ) := by
  unfold fixedAwaySmoothCorrection
  exact contDiff_const.sub (fixedAwaySmoothCutoff_contDiff t δ)

private theorem fixedAway_positive_argument_nonpos
    {t δ x : ℝ} (hδ : 0 < δ) (hx : x ≤ t - δ) :
    δ⁻¹ * x + (1 - δ⁻¹ * t) ≤ 0 := by
  have hinv : 0 ≤ δ⁻¹ := (inv_pos.mpr hδ).le
  have hmul := mul_le_mul_of_nonneg_left hx hinv
  have hcancel : δ⁻¹ * δ = 1 := inv_mul_cancel₀ hδ.ne'
  nlinarith

private theorem fixedAway_negative_argument_nonpos
    {t δ x : ℝ} (hδ : 0 < δ) (hx : -x ≤ t - δ) :
    (-δ⁻¹) * x + (1 - δ⁻¹ * t) ≤ 0 := by
  have h := fixedAway_positive_argument_nonpos hδ hx
  ring_nf at h ⊢
  exact h

theorem fixedAwaySmoothCutoff_eq_zero_of_abs_le_sub
    {t δ x : ℝ} (hδ : 0 < δ) (hx : |x| ≤ t - δ) :
    fixedAwaySmoothCutoff t δ x = 0 := by
  have hxright : x ≤ t - δ := (le_abs_self x).trans hx
  have hxleft : -x ≤ t - δ := (neg_le_abs x).trans hx
  rw [fixedAwaySmoothCutoff,
    gevreyTransition_eq_zero_of_nonpos
      (fixedAway_positive_argument_nonpos hδ hxright),
    gevreyTransition_eq_zero_of_nonpos
      (fixedAway_negative_argument_nonpos hδ hxleft),
    add_zero]

private theorem fixedAway_positive_argument_one_le
    {t δ x : ℝ} (hδ : 0 < δ) (hx : t ≤ x) :
    1 ≤ δ⁻¹ * x + (1 - δ⁻¹ * t) := by
  have hinv : 0 ≤ δ⁻¹ := (inv_pos.mpr hδ).le
  have := mul_le_mul_of_nonneg_left hx hinv
  linarith

private theorem fixedAway_negative_argument_one_le
    {t δ x : ℝ} (hδ : 0 < δ) (hx : x ≤ -t) :
    1 ≤ (-δ⁻¹) * x + (1 - δ⁻¹ * t) := by
  have hxt : t ≤ -x := by linarith
  have h := fixedAway_positive_argument_one_le hδ hxt
  ring_nf at h ⊢
  exact h

private theorem fixedAway_negative_argument_nonpos_of_nonneg
    {t δ x : ℝ} (hδt : δ ≤ t) (hδ : 0 < δ) (hx : 0 ≤ x) :
    (-δ⁻¹) * x + (1 - δ⁻¹ * t) ≤ 0 := by
  have hinv : 0 ≤ δ⁻¹ := (inv_pos.mpr hδ).le
  have hdt := mul_le_mul_of_nonneg_left hδt hinv
  have hcancel : δ⁻¹ * δ = 1 := inv_mul_cancel₀ hδ.ne'
  have hxterm : (-δ⁻¹) * x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr hinv) hx
  nlinarith

private theorem fixedAway_positive_argument_nonpos_of_nonpos
    {t δ x : ℝ} (hδt : δ ≤ t) (hδ : 0 < δ) (hx : x ≤ 0) :
    δ⁻¹ * x + (1 - δ⁻¹ * t) ≤ 0 := by
  have h := fixedAway_negative_argument_nonpos_of_nonneg hδt hδ (neg_nonneg.mpr hx)
  ring_nf at h ⊢
  exact h

theorem fixedAwaySmoothCutoff_eq_one_of_le_abs
    {t δ x : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t) (hx : t ≤ |x|) :
    fixedAwaySmoothCutoff t δ x = 1 := by
  by_cases hx0 : 0 ≤ x
  · have htx : t ≤ x := by simpa [abs_of_nonneg hx0] using! hx
    rw [fixedAwaySmoothCutoff,
      gevreyTransition_eq_one_of_one_le
        (fixedAway_positive_argument_one_le hδ htx),
      gevreyTransition_eq_zero_of_nonpos
        (fixedAway_negative_argument_nonpos_of_nonneg hδt hδ hx0),
      add_zero]
  · have hxnonpos : x ≤ 0 := (lt_of_not_ge hx0).le
    have hxt : x ≤ -t := by
      rw [abs_of_nonpos hxnonpos] at hx
      linarith
    rw [fixedAwaySmoothCutoff,
      gevreyTransition_eq_zero_of_nonpos
        (fixedAway_positive_argument_nonpos_of_nonpos hδt hδ hxnonpos),
      gevreyTransition_eq_one_of_one_le
        (fixedAway_negative_argument_one_le hδ hxt),
      zero_add]

theorem fixedAwaySmoothCutoff_mem_Icc
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t) (x : ℝ) :
    fixedAwaySmoothCutoff t δ x ∈ Icc (0 : ℝ) 1 := by
  by_cases hx : 0 ≤ x
  · rw [fixedAwaySmoothCutoff,
      gevreyTransition_eq_zero_of_nonpos
        (fixedAway_negative_argument_nonpos_of_nonneg hδt hδ hx),
      add_zero]
    exact gevreyTransition_mem_Icc _
  · have hxnonpos : x ≤ 0 := (lt_of_not_ge hx).le
    rw [fixedAwaySmoothCutoff,
      gevreyTransition_eq_zero_of_nonpos
        (fixedAway_positive_argument_nonpos_of_nonpos hδt hδ hxnonpos),
      zero_add]
    exact gevreyTransition_mem_Icc _

theorem fixedAwaySmoothCorrection_mem_Icc
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t) (x : ℝ) :
    fixedAwaySmoothCorrection t δ x ∈ Icc (0 : ℝ) 1 := by
  have h := fixedAwaySmoothCutoff_mem_Icc hδ hδt x
  unfold fixedAwaySmoothCorrection
  constructor <;> linarith [h.1, h.2]

theorem fixedAwaySmoothCorrection_eq_zero_of_le_abs
    {t δ x : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t) (hx : t ≤ |x|) :
    fixedAwaySmoothCorrection t δ x = 0 := by
  rw [fixedAwaySmoothCorrection,
    fixedAwaySmoothCutoff_eq_one_of_le_abs hδ hδt hx, sub_self]

theorem support_fixedAwaySmoothCorrection_subset
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t) :
    Function.support (fixedAwaySmoothCorrection t δ) ⊆ Icc (-t) t := by
  intro x hx
  have hnot : ¬t ≤ |x| := by
    intro hout
    exact hx (fixedAwaySmoothCorrection_eq_zero_of_le_abs hδ hδt hout)
  have habs : |x| < t := lt_of_not_ge hnot
  exact ⟨(abs_lt.mp habs).1.le, (abs_lt.mp habs).2.le⟩

theorem abs_fixedAwaySmoothCorrection_le_one
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t) (x : ℝ) :
    |fixedAwaySmoothCorrection t δ x| ≤ 1 := by
  have h := fixedAwaySmoothCorrection_mem_Icc hδ hδt x
  rw [abs_of_nonneg h.1]
  exact h.2

theorem abs_iteratedDeriv_fixedAwaySmoothCutoff_succ_le
    (n : ℕ) (t δ x : ℝ) :
    |iteratedDeriv (n + 1) (fixedAwaySmoothCutoff t δ) x| ≤
      2 * |δ⁻¹| ^ (n + 1) *
        (gevreyCompactBumpMass⁻¹ *
          (96 ^ n * (n.factorial : ℝ) ^ 2)) := by
  have hpos := gevreyTransition_affine_contDiff
    (m := (n + 1 : ℕ∞)) δ⁻¹ (1 - δ⁻¹ * t)
  have hneg := gevreyTransition_affine_contDiff
    (m := (n + 1 : ℕ∞)) (-δ⁻¹) (1 - δ⁻¹ * t)
  let f : ℝ → ℝ :=
    fun y ↦ gevreyTransition (δ⁻¹ * y + (1 - δ⁻¹ * t))
  let g : ℝ → ℝ :=
    fun y ↦ gevreyTransition ((-δ⁻¹) * y + (1 - δ⁻¹ * t))
  have hposAt : ContDiffAt ℝ (n + 1) f x := by
    exact hpos.contDiffAt
  have hnegAt : ContDiffAt ℝ (n + 1) g x := by
    exact hneg.contDiffAt
  have hadd : iteratedDeriv (n + 1) (fun y ↦ f y + g y) x =
      iteratedDeriv (n + 1) f x + iteratedDeriv (n + 1) g x := by
    simpa only [Pi.add_apply] using! iteratedDeriv_add hposAt hnegAt
  change |iteratedDeriv (n + 1)
      (fun y ↦
        gevreyTransition (δ⁻¹ * y + (1 - δ⁻¹ * t)) +
          gevreyTransition ((-δ⁻¹) * y + (1 - δ⁻¹ * t))) x| ≤ _
  change |iteratedDeriv (n + 1) (fun y ↦ f y + g y) x| ≤ _
  rw [hadd]
  calc
    |iteratedDeriv (n + 1)
          (fun y ↦ gevreyTransition (δ⁻¹ * y + (1 - δ⁻¹ * t))) x +
        iteratedDeriv (n + 1)
          (fun y ↦ gevreyTransition ((-δ⁻¹) * y + (1 - δ⁻¹ * t))) x| ≤
      |iteratedDeriv (n + 1)
          (fun y ↦ gevreyTransition (δ⁻¹ * y + (1 - δ⁻¹ * t))) x| +
        |iteratedDeriv (n + 1)
          (fun y ↦ gevreyTransition ((-δ⁻¹) * y + (1 - δ⁻¹ * t))) x| :=
      abs_add_le _ _
    _ ≤ |δ⁻¹| ^ (n + 1) *
          (gevreyCompactBumpMass⁻¹ *
            (96 ^ n * (n.factorial : ℝ) ^ 2)) +
        |-δ⁻¹| ^ (n + 1) *
          (gevreyCompactBumpMass⁻¹ *
            (96 ^ n * (n.factorial : ℝ) ^ 2)) := by
      gcongr
      · exact abs_iteratedDeriv_gevreyTransition_affine_succ_le
          n δ⁻¹ (1 - δ⁻¹ * t) x
      · exact abs_iteratedDeriv_gevreyTransition_affine_succ_le
          n (-δ⁻¹) (1 - δ⁻¹ * t) x
    _ = 2 * |δ⁻¹| ^ (n + 1) *
        (gevreyCompactBumpMass⁻¹ *
          (96 ^ n * (n.factorial : ℝ) ^ 2)) := by
      rw [abs_neg]
      ring

theorem abs_iteratedDeriv_fixedAwaySmoothCorrection_succ_le
    (n : ℕ) (t δ x : ℝ) :
    |iteratedDeriv (n + 1) (fixedAwaySmoothCorrection t δ) x| ≤
      2 * |δ⁻¹| ^ (n + 1) *
        (gevreyCompactBumpMass⁻¹ *
          (96 ^ n * (n.factorial : ℝ) ^ 2)) := by
  unfold fixedAwaySmoothCorrection
  rw [iteratedDeriv_const_sub (Nat.succ_pos n) (1 : ℝ),
    iteratedDeriv_neg, abs_neg]
  exact abs_iteratedDeriv_fixedAwaySmoothCutoff_succ_le n t δ x

/-- The explicit smooth family has the manuscript's right-hand jump. -/
theorem tendsto_fixedAwayPVTransform_smooth_nhdsGT_zero
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t) :
    Tendsto (fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t)
      (𝓝[>] 0) (nhds (-Complex.I * Real.pi)) := by
  apply tendsto_fixedAwayPVTransform_nhdsGT_zero
  intro v hv
  exact abs_fixedAwaySmoothCorrection_le_one hδ hδt v

/-- The explicit smooth family has the manuscript's left-hand jump. -/
theorem tendsto_fixedAwayPVTransform_smooth_nhdsLT_zero
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t) :
    Tendsto (fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t)
      (𝓝[<] 0) (nhds (Complex.I * Real.pi)) := by
  apply tendsto_fixedAwayPVTransform_nhdsLT_zero
  intro v hv
  exact abs_fixedAwaySmoothCorrection_le_one hδ hδt v

end

end Erdos1002
