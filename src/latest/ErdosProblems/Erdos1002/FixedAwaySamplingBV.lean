import ErdosProblems.Erdos1002.SamplingBV
import ErdosProblems.Erdos1002.FixedAwayHermitianBV

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Integer BV bounds for the fixed-away Hermitian carrier

This file specializes the generic sampling lemmas to the two-carrier
Hermitian product used in the fixed-away argument.  In particular, the
one-sided affine limits below keep track of whether the scale preserves or
reverses the two sides of a carrier.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators ComplexConjugate Real Topology

namespace Erdos1002

noncomputable section

theorem tendsto_sub_div_nhdsGT_zero_of_pos
    {a s : ℝ} (hs : 0 < s) :
    Tendsto (fun x : ℝ ↦ (x - a) / s) (𝓝[>] a) (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · apply Filter.Tendsto.mono_left _ inf_le_left
    have hcont : ContinuousAt (fun x : ℝ ↦ (x - a) / s) a := by
      fun_prop
    have hcont' : Tendsto (fun x : ℝ ↦ (x - a) / s) (nhds a)
        (nhds ((a - a) / s)) := hcont
    simpa using! hcont'
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact div_pos (sub_pos.mpr hx) hs

theorem tendsto_sub_div_nhdsLT_zero_of_pos
    {a s : ℝ} (hs : 0 < s) :
    Tendsto (fun x : ℝ ↦ (x - a) / s) (𝓝[<] a) (𝓝[<] 0) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · apply Filter.Tendsto.mono_left _ inf_le_left
    have hcont : ContinuousAt (fun x : ℝ ↦ (x - a) / s) a := by
      fun_prop
    have hcont' : Tendsto (fun x : ℝ ↦ (x - a) / s) (nhds a)
        (nhds ((a - a) / s)) := hcont
    simpa using! hcont'
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact div_neg_of_neg_of_pos (sub_neg.mpr hx) hs

theorem tendsto_sub_div_nhdsGT_zero_of_neg
    {a s : ℝ} (hs : s < 0) :
    Tendsto (fun x : ℝ ↦ (x - a) / s) (𝓝[>] a) (𝓝[<] 0) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · apply Filter.Tendsto.mono_left _ inf_le_left
    have hcont : ContinuousAt (fun x : ℝ ↦ (x - a) / s) a := by
      fun_prop
    have hcont' : Tendsto (fun x : ℝ ↦ (x - a) / s) (nhds a)
        (nhds ((a - a) / s)) := hcont
    simpa using! hcont'
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact div_neg_of_pos_of_neg (sub_pos.mpr hx) hs

theorem tendsto_sub_div_nhdsLT_zero_of_neg
    {a s : ℝ} (hs : s < 0) :
    Tendsto (fun x : ℝ ↦ (x - a) / s) (𝓝[<] a) (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · apply Filter.Tendsto.mono_left _ inf_le_left
    have hcont : ContinuousAt (fun x : ℝ ↦ (x - a) / s) a := by
      fun_prop
    have hcont' : Tendsto (fun x : ℝ ↦ (x - a) / s) (nhds a)
        (nhds ((a - a) / s)) := hcont
    simpa using! hcont'
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact div_pos_of_neg_of_neg (sub_neg.mpr hx) hs

theorem tendsto_fixedAwayScaledPV_nhdsGT_carrier_of_pos
    {t δ s a : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t) (hs : 0 < s) :
    Tendsto (fixedAwayScaledPV t δ s a) (𝓝[>] a)
      (nhds (-Complex.I * Real.pi)) := by
  exact (tendsto_fixedAwayPVTransform_smooth_nhdsGT_zero hδ hδt).comp
    (tendsto_sub_div_nhdsGT_zero_of_pos hs)

theorem tendsto_fixedAwayScaledPV_nhdsLT_carrier_of_pos
    {t δ s a : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t) (hs : 0 < s) :
    Tendsto (fixedAwayScaledPV t δ s a) (𝓝[<] a)
      (nhds (Complex.I * Real.pi)) := by
  exact (tendsto_fixedAwayPVTransform_smooth_nhdsLT_zero hδ hδt).comp
    (tendsto_sub_div_nhdsLT_zero_of_pos hs)

theorem tendsto_fixedAwayScaledPV_nhdsGT_carrier_of_neg
    {t δ s a : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t) (hs : s < 0) :
    Tendsto (fixedAwayScaledPV t δ s a) (𝓝[>] a)
      (nhds (Complex.I * Real.pi)) := by
  exact (tendsto_fixedAwayPVTransform_smooth_nhdsLT_zero hδ hδt).comp
    (tendsto_sub_div_nhdsGT_zero_of_neg hs)

theorem tendsto_fixedAwayScaledPV_nhdsLT_carrier_of_neg
    {t δ s a : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t) (hs : s < 0) :
    Tendsto (fixedAwayScaledPV t δ s a) (𝓝[<] a)
      (nhds (-Complex.I * Real.pi)) := by
  exact (tendsto_fixedAwayPVTransform_smooth_nhdsGT_zero hδ hδt).comp
    (tendsto_sub_div_nhdsLT_zero_of_neg hs)

@[simp] theorem fixedAwayScaledPV_at_carrier
    (t δ s a : ℝ) : fixedAwayScaledPV t δ s a a = 0 := by
  simp [fixedAwayScaledPV, fixedAwayPVTransform_zero]

theorem continuousAt_fixedAwayScaledPV_of_ne
    {t δ s a x : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    (hs : s ≠ 0) (hxa : x ≠ a) :
    ContinuousAt (fixedAwayScaledPV t δ s a) x :=
  (hasDerivAt_fixedAwayScaledPV hδ hδt hs hxa).continuousAt

theorem tendsto_fixedAwayScaledHermitianProduct_nhdsGT_leftCarrier_of_pos
    {t δ s a s' a' : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    (hs : 0 < s) (hs' : s' ≠ 0) (haa' : a ≠ a') :
    Tendsto (fixedAwayScaledHermitianProduct t δ s a s' a') (𝓝[>] a)
      (nhds ((-Complex.I * Real.pi) *
        conj (fixedAwayScaledPV t δ s' a' a))) := by
  have hleft := tendsto_fixedAwayScaledPV_nhdsGT_carrier_of_pos
    (t := t) (δ := δ) (s := s) (a := a) hδ hδt hs
  have hright := (continuousAt_fixedAwayScaledPV_of_ne
    (t := t) (δ := δ) (s := s') (a := a') (x := a)
    hδ hδt hs' haa').mono_left (show 𝓝[>] a ≤ nhds a from inf_le_left)
  simpa only [fixedAwayScaledHermitianProduct, starRingEnd_apply] using!
    hleft.mul hright.star

theorem tendsto_fixedAwayScaledHermitianProduct_nhdsLT_leftCarrier_of_pos
    {t δ s a s' a' : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    (hs : 0 < s) (hs' : s' ≠ 0) (haa' : a ≠ a') :
    Tendsto (fixedAwayScaledHermitianProduct t δ s a s' a') (𝓝[<] a)
      (nhds ((Complex.I * Real.pi) *
        conj (fixedAwayScaledPV t δ s' a' a))) := by
  have hleft := tendsto_fixedAwayScaledPV_nhdsLT_carrier_of_pos
    (t := t) (δ := δ) (s := s) (a := a) hδ hδt hs
  have hright := (continuousAt_fixedAwayScaledPV_of_ne
    (t := t) (δ := δ) (s := s') (a := a') (x := a)
    hδ hδt hs' haa').mono_left (show 𝓝[<] a ≤ nhds a from inf_le_left)
  simpa only [fixedAwayScaledHermitianProduct, starRingEnd_apply] using!
    hleft.mul hright.star

theorem tendsto_fixedAwayScaledHermitianProduct_nhdsGT_rightCarrier_of_pos
    {t δ s a s' a' : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    (hs : s ≠ 0) (hs' : 0 < s') (haa' : a ≠ a') :
    Tendsto (fixedAwayScaledHermitianProduct t δ s a s' a') (𝓝[>] a')
      (nhds (fixedAwayScaledPV t δ s a a' *
        conj (-Complex.I * Real.pi))) := by
  have hleft := (continuousAt_fixedAwayScaledPV_of_ne
    (t := t) (δ := δ) (s := s) (a := a) (x := a')
    hδ hδt hs haa'.symm).mono_left
      (show 𝓝[>] a' ≤ nhds a' from inf_le_left)
  have hright := tendsto_fixedAwayScaledPV_nhdsGT_carrier_of_pos
    (t := t) (δ := δ) (s := s') (a := a') hδ hδt hs'
  simpa only [fixedAwayScaledHermitianProduct, starRingEnd_apply] using!
    hleft.mul hright.star

theorem tendsto_fixedAwayScaledHermitianProduct_nhdsLT_rightCarrier_of_pos
    {t δ s a s' a' : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    (hs : s ≠ 0) (hs' : 0 < s') (haa' : a ≠ a') :
    Tendsto (fixedAwayScaledHermitianProduct t δ s a s' a') (𝓝[<] a')
      (nhds (fixedAwayScaledPV t δ s a a' *
        conj (Complex.I * Real.pi))) := by
  have hleft := (continuousAt_fixedAwayScaledPV_of_ne
    (t := t) (δ := δ) (s := s) (a := a) (x := a')
    hδ hδt hs haa'.symm).mono_left
      (show 𝓝[<] a' ≤ nhds a' from inf_le_left)
  have hright := tendsto_fixedAwayScaledPV_nhdsLT_carrier_of_pos
    (t := t) (δ := δ) (s := s') (a := a') hδ hδt hs'
  simpa only [fixedAwayScaledHermitianProduct, starRingEnd_apply] using!
    hleft.mul hright.star

theorem tendsto_fixedAwayScaledHermitianProduct_nhdsGT_diagonal_of_pos
    {t δ s s' a : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    (hs : 0 < s) (hs' : 0 < s') :
    Tendsto (fixedAwayScaledHermitianProduct t δ s a s' a) (𝓝[>] a)
      (nhds (Real.pi ^ 2 : ℂ)) := by
  have hleft := tendsto_fixedAwayScaledPV_nhdsGT_carrier_of_pos
    (t := t) (δ := δ) (s := s) (a := a) hδ hδt hs
  have hright := tendsto_fixedAwayScaledPV_nhdsGT_carrier_of_pos
    (t := t) (δ := δ) (s := s') (a := a) hδ hδt hs'
  have hval :
      (-Complex.I * (Real.pi : ℂ)) *
          conj (-Complex.I * (Real.pi : ℂ)) =
        (Real.pi ^ 2 : ℂ) := by
    change (-Complex.I * (Real.pi : ℂ)) *
      conj (-Complex.I * (Real.pi : ℂ)) = (Real.pi : ℂ) ^ 2
    ring_nf
    rw [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [← hval]
  simpa only [fixedAwayScaledHermitianProduct, starRingEnd_apply] using!
    hleft.mul hright.star

theorem tendsto_fixedAwayScaledHermitianProduct_nhdsLT_diagonal_of_pos
    {t δ s s' a : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    (hs : 0 < s) (hs' : 0 < s') :
    Tendsto (fixedAwayScaledHermitianProduct t δ s a s' a) (𝓝[<] a)
      (nhds (Real.pi ^ 2 : ℂ)) := by
  have hleft := tendsto_fixedAwayScaledPV_nhdsLT_carrier_of_pos
    (t := t) (δ := δ) (s := s) (a := a) hδ hδt hs
  have hright := tendsto_fixedAwayScaledPV_nhdsLT_carrier_of_pos
    (t := t) (δ := δ) (s := s') (a := a) hδ hδt hs'
  have hval :
      (Complex.I * (Real.pi : ℂ)) *
          conj (Complex.I * (Real.pi : ℂ)) =
        (Real.pi ^ 2 : ℂ) := by
    change (Complex.I * (Real.pi : ℂ)) *
      conj (Complex.I * (Real.pi : ℂ)) = (Real.pi : ℂ) ^ 2
    ring_nf
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [← hval]
  simpa only [fixedAwayScaledHermitianProduct, starRingEnd_apply] using!
    hleft.mul hright.star

/-! ## FTC between regulated endpoint values -/

theorem norm_sub_oneSidedLimits_le_intervalIntegral_norm_deriv
    {f : ℝ → ℂ} {u v : ℝ} {fu fv : ℂ} (huv : u < v)
    (hderiv : ∀ x ∈ Ioo u v, HasDerivAt f (deriv f x) x)
    (hint : IntervalIntegrable (deriv f) volume u v)
    (hu : Tendsto f (𝓝[>] u) (nhds fu))
    (hv : Tendsto f (𝓝[<] v) (nhds fv)) :
    ‖fu - fv‖ ≤ ∫ x in u..v, ‖deriv f x‖ := by
  have hFTC : ∫ x in u..v, deriv f x = fv - fu :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
      huv hderiv hint hu hv
  calc
    ‖fu - fv‖ = ‖∫ x in u..v, deriv f x‖ := by
      rw [hFTC]
      simpa only [norm_neg] using!
        congrArg norm (show fu - fv = -(fv - fu) by abel)
    _ ≤ ∫ x in u..v, ‖deriv f x‖ :=
      intervalIntegral.norm_integral_le_integral_norm huv.le

theorem tendsto_nhdsGT_of_continuousAt
    {f : ℝ → ℂ} {x : ℝ} (hf : ContinuousAt f x) :
    Tendsto f (𝓝[>] x) (nhds (f x)) :=
  hf.mono_left inf_le_left

theorem tendsto_nhdsLT_of_continuousAt
    {f : ℝ → ℂ} {x : ℝ} (hf : ContinuousAt f x) :
    Tendsto f (𝓝[<] x) (nhds (f x)) :=
  hf.mono_left inf_le_left

def regulatedPointCharge (f : ℝ → ℂ) (c : ℝ) (left right : ℂ) : ℝ :=
  ‖left - f c‖ + ‖f c - right‖

theorem regulatedPointCharge_fixedAwayHermitian_leftCarrier
    {t δ s a s' a' : ℝ} :
    regulatedPointCharge
        (fixedAwayScaledHermitianProduct t δ s a s' a') a
        ((Complex.I * Real.pi) *
          conj (fixedAwayScaledPV t δ s' a' a))
        ((-Complex.I * Real.pi) *
          conj (fixedAwayScaledPV t δ s' a' a)) =
      2 * Real.pi * ‖fixedAwayScaledPV t δ s' a' a‖ := by
  simp [regulatedPointCharge, fixedAwayScaledHermitianProduct,
    Complex.norm_I, Real.norm_eq_abs,
    abs_of_nonneg Real.pi_nonneg]
  ring

theorem regulatedPointCharge_fixedAwayHermitian_rightCarrier
    {t δ s a s' a' : ℝ} :
    regulatedPointCharge
        (fixedAwayScaledHermitianProduct t δ s a s' a') a'
        (fixedAwayScaledPV t δ s a a' *
          conj (Complex.I * Real.pi))
        (fixedAwayScaledPV t δ s a a' *
          conj (-Complex.I * Real.pi)) =
      2 * Real.pi * ‖fixedAwayScaledPV t δ s a a'‖ := by
  simp [regulatedPointCharge, fixedAwayScaledHermitianProduct,
    Complex.norm_I, Real.norm_eq_abs,
    abs_of_nonneg Real.pi_nonneg]
  ring

theorem regulatedPointCharge_fixedAwayHermitian_diagonal
    {t δ s s' a : ℝ} :
    regulatedPointCharge
        (fixedAwayScaledHermitianProduct t δ s a s' a) a
        (Real.pi ^ 2 : ℂ) (Real.pi ^ 2 : ℂ) =
      2 * Real.pi ^ 2 := by
  simp [regulatedPointCharge, fixedAwayScaledHermitianProduct,
    Complex.norm_real]
  ring

/-- FTC on an interval containing at most one regulated jump.  Notice that
the assigned value `f c` is retained: the charge contains both paths through
that value, so the statement also covers a carrier that is an integer
endpoint of the sampled cell. -/
theorem norm_sub_le_integral_add_one_regulatedPointCharge
    {f : ℝ → ℂ} {u v c : ℝ} {left right : ℂ} (huv : u < v)
    (hderiv : ∀ x ∈ Ioo u v, x ≠ c →
      HasDerivAt f (deriv f x) x)
    (hint : Integrable (deriv f))
    (hu : u ≠ c → Tendsto f (𝓝[>] u) (nhds (f u)))
    (hv : v ≠ c → Tendsto f (𝓝[<] v) (nhds (f v)))
    (hcLeft : Tendsto f (𝓝[<] c) (nhds left))
    (hcRight : Tendsto f (𝓝[>] c) (nhds right)) :
    ‖f u - f v‖ ≤
      (∫ x in u..v, ‖deriv f x‖) +
        if c ∈ Icc u v then regulatedPointCharge f c left right else 0 := by
  rcases lt_trichotomy c u with hcu | hcu | huc
  · have huc : u ≠ c := hcu.ne'
    have hvc : v ≠ c := ne_of_gt (hcu.trans huv)
    have hseg := norm_sub_oneSidedLimits_le_intervalIntegral_norm_deriv
      huv (fun x hx ↦ hderiv x hx (ne_of_gt (hcu.trans hx.1)))
      hint.intervalIntegrable (hu huc) (hv hvc)
    simpa [Set.mem_Icc, not_le.mpr hcu] using! hseg
  · subst c
    have hvc : v ≠ u := huv.ne'
    have hseg := norm_sub_oneSidedLimits_le_intervalIntegral_norm_deriv
      huv (fun x hx ↦ hderiv x hx hx.1.ne')
      hint.intervalIntegrable hcRight (hv hvc)
    have hpath : ‖f u - f v‖ ≤ ‖f u - right‖ + ‖right - f v‖ := by
      calc
        ‖f u - f v‖ = ‖(f u - right) + (right - f v)‖ := by ring_nf
        _ ≤ ‖f u - right‖ + ‖right - f v‖ := norm_add_le _ _
    have hleftNonneg : 0 ≤ ‖left - f u‖ := norm_nonneg _
    rw [if_pos (by exact ⟨le_rfl, huv.le⟩)]
    unfold regulatedPointCharge
    exact hpath.trans (by
      have hright := hseg
      nlinarith)
  · rcases lt_trichotomy c v with hcv | hcv | hvc
    · have hucne : u ≠ c := huc.ne
      have hvcne : v ≠ c := hcv.ne'
      have hleftSeg :=
        norm_sub_oneSidedLimits_le_intervalIntegral_norm_deriv
          huc (fun x hx ↦ hderiv x ⟨hx.1, hx.2.trans hcv⟩ hx.2.ne)
          hint.intervalIntegrable (hu hucne) hcLeft
      have hrightSeg :=
        norm_sub_oneSidedLimits_le_intervalIntegral_norm_deriv
          hcv (fun x hx ↦ hderiv x ⟨huc.trans hx.1, hx.2⟩ hx.1.ne')
          hint.intervalIntegrable hcRight (hv hvcne)
      have hadd :
          (∫ x in u..c, ‖deriv f x‖) +
              ∫ x in c..v, ‖deriv f x‖ =
            ∫ x in u..v, ‖deriv f x‖ :=
        intervalIntegral.integral_add_adjacent_intervals
          hint.norm.intervalIntegrable hint.norm.intervalIntegrable
      have hpath :
          ‖f u - f v‖ ≤
            ‖f u - left‖ + ‖left - f c‖ +
              ‖f c - right‖ + ‖right - f v‖ := by
        calc
          ‖f u - f v‖ =
              ‖(f u - left) + (left - f c) +
                (f c - right) + (right - f v)‖ := by ring_nf
          _ ≤ ‖f u - left‖ + ‖left - f c‖ +
                ‖f c - right‖ + ‖right - f v‖ := by
            calc
              _ ≤ ‖(f u - left) + (left - f c) +
                    (f c - right)‖ + ‖right - f v‖ := norm_add_le _ _
              _ ≤ (‖(f u - left) + (left - f c)‖ +
                    ‖f c - right‖) + ‖right - f v‖ := by gcongr; exact norm_add_le _ _
              _ ≤ (‖f u - left‖ + ‖left - f c‖ +
                    ‖f c - right‖) + ‖right - f v‖ := by gcongr; exact norm_add_le _ _
      rw [if_pos ⟨huc.le, hcv.le⟩]
      unfold regulatedPointCharge
      rw [← hadd]
      exact hpath.trans (by nlinarith)
    · subst c
      have hucne : u ≠ v := huv.ne
      have hseg := norm_sub_oneSidedLimits_le_intervalIntegral_norm_deriv
        huv (fun x hx ↦ hderiv x hx hx.2.ne)
        hint.intervalIntegrable (hu hucne) hcLeft
      have hpath : ‖f u - f v‖ ≤ ‖f u - left‖ + ‖left - f v‖ := by
        calc
          ‖f u - f v‖ = ‖(f u - left) + (left - f v)‖ := by ring_nf
          _ ≤ ‖f u - left‖ + ‖left - f v‖ := norm_add_le _ _
      have hrightNonneg : 0 ≤ ‖f v - right‖ := norm_nonneg _
      rw [if_pos (by exact ⟨huv.le, le_rfl⟩)]
      unfold regulatedPointCharge
      exact hpath.trans (by
        have hleft := hseg
        nlinarith)
    · have hucne : u ≠ c := huc.ne
      have hvcne : v ≠ c := hvc.ne
      have hseg := norm_sub_oneSidedLimits_le_intervalIntegral_norm_deriv
        huv (fun x hx ↦ hderiv x hx (ne_of_lt (hx.2.trans hvc)))
        hint.intervalIntegrable (hu hucne) (hv hvcne)
      simpa [Set.mem_Icc, not_le.mpr hvc] using! hseg

/-- Two-jump version of the regulated FTC bound.  The midpoint between the
ordered jump points reduces the proof to two applications of the one-jump
lemma; hence no unproved global `BV` closure principle is hidden here. -/
theorem norm_sub_le_integral_add_two_regulatedPointCharges
    {f : ℝ → ℂ} {u v c d : ℝ}
    {cLeft cRight dLeft dRight : ℂ}
    (huv : u < v) (hcd : c < d)
    (hderiv : ∀ x ∈ Ioo u v, x ≠ c → x ≠ d →
      HasDerivAt f (deriv f x) x)
    (hint : Integrable (deriv f))
    (hcont : ∀ x, x ≠ c → x ≠ d → ContinuousAt f x)
    (hcLeft : Tendsto f (𝓝[<] c) (nhds cLeft))
    (hcRight : Tendsto f (𝓝[>] c) (nhds cRight))
    (hdLeft : Tendsto f (𝓝[<] d) (nhds dLeft))
    (hdRight : Tendsto f (𝓝[>] d) (nhds dRight)) :
    ‖f u - f v‖ ≤
      (∫ x in u..v, ‖deriv f x‖) +
        (if c ∈ Icc u v then
          regulatedPointCharge f c cLeft cRight else 0) +
        (if d ∈ Icc u v then
          regulatedPointCharge f d dLeft dRight else 0) := by
  let m : ℝ := (c + d) / 2
  have hcm : c < m := by
    dsimp only [m]
    linarith
  have hmd : m < d := by
    dsimp only [m]
    linarith
  by_cases hvm : v ≤ m
  · have hdout : d ∉ Icc u v := by
      intro hdmem
      exact (not_lt_of_ge hvm) (hmd.trans_le hdmem.2)
    have hud : u ≠ d := ne_of_lt (huv.trans_le hvm |>.trans hmd)
    have hvd : v ≠ d := ne_of_lt (hvm.trans_lt hmd)
    have hone := norm_sub_le_integral_add_one_regulatedPointCharge
      (f := f) (c := c) (left := cLeft) (right := cRight) huv
      (fun x hx hxc ↦ hderiv x hx hxc
        (ne_of_lt (hx.2.trans_le hvm |>.trans hmd)))
      hint
      (fun huc ↦ tendsto_nhdsGT_of_continuousAt (hcont u huc hud))
      (fun hvc ↦ tendsto_nhdsLT_of_continuousAt (hcont v hvc hvd))
      hcLeft hcRight
    simpa [hdout] using! hone
  · have hmv : m < v := lt_of_not_ge hvm
    by_cases hmu : m ≤ u
    · have hcout : c ∉ Icc u v := by
        intro hcmem
        exact (not_lt_of_ge (hmu.trans hcmem.1)) hcm
      have hcu : u ≠ c := (ne_of_lt (hcm.trans_le hmu)).symm
      have hcv : v ≠ c :=
        (ne_of_lt ((hcm.trans_le hmu).trans huv)).symm
      have hone := norm_sub_le_integral_add_one_regulatedPointCharge
        (f := f) (c := d) (left := dLeft) (right := dRight) huv
        (fun x hx hxd ↦ hderiv x hx
          (ne_of_gt (hcm.trans_le hmu |>.trans hx.1)) hxd)
        hint
        (fun hud ↦ tendsto_nhdsGT_of_continuousAt (hcont u hcu hud))
        (fun hvd ↦ tendsto_nhdsLT_of_continuousAt (hcont v hcv hvd))
        hdLeft hdRight
      simpa [hcout, add_assoc] using! hone
    · have hum : u < m := lt_of_not_ge hmu
      have hmc : m ≠ c := hcm.ne'
      have hmdne : m ≠ d := hmd.ne
      have hud : u ≠ d := ne_of_lt (hum.trans hmd)
      have hcv : v ≠ c := ne_of_gt (hcm.trans hmv)
      have hmcont : ContinuousAt f m := hcont m hmc hmdne
      have hleftBound :=
        norm_sub_le_integral_add_one_regulatedPointCharge
          (f := f) (c := c) (left := cLeft) (right := cRight) hum
          (fun x hx hxc ↦ hderiv x ⟨hx.1, hx.2.trans hmv⟩ hxc
            (ne_of_lt (hx.2.trans hmd)))
          hint
          (fun huc ↦ tendsto_nhdsGT_of_continuousAt (hcont u huc hud))
          (fun _hmc ↦ tendsto_nhdsLT_of_continuousAt hmcont)
          hcLeft hcRight
      have hrightBound :=
        norm_sub_le_integral_add_one_regulatedPointCharge
          (f := f) (c := d) (left := dLeft) (right := dRight) hmv
          (fun x hx hxd ↦ hderiv x ⟨hum.trans hx.1, hx.2⟩
            (ne_of_gt (hcm.trans hx.1)) hxd)
          hint
          (fun _hmd ↦ tendsto_nhdsGT_of_continuousAt hmcont)
          (fun hvd ↦ tendsto_nhdsLT_of_continuousAt (hcont v hcv hvd))
          hdLeft hdRight
      have hcMem : c ∈ Icc u m ↔ c ∈ Icc u v := by
        constructor
        · intro hc
          exact ⟨hc.1, hcm.le.trans (hmv.le)⟩
        · intro hc
          exact ⟨hc.1, hcm.le⟩
      have hdMem : d ∈ Icc m v ↔ d ∈ Icc u v := by
        constructor
        · intro hd
          exact ⟨hum.le.trans hmd.le, hd.2⟩
        · intro hd
          exact ⟨hmd.le, hd.2⟩
      have hadd :
          (∫ x in u..m, ‖deriv f x‖) +
              ∫ x in m..v, ‖deriv f x‖ =
            ∫ x in u..v, ‖deriv f x‖ :=
        intervalIntegral.integral_add_adjacent_intervals
          hint.norm.intervalIntegrable hint.norm.intervalIntegrable
      calc
        ‖f u - f v‖ ≤ ‖f u - f m‖ + ‖f m - f v‖ := by
          calc
            ‖f u - f v‖ = ‖(f u - f m) + (f m - f v)‖ := by ring_nf
            _ ≤ _ := norm_add_le _ _
        _ ≤ ((∫ x in u..m, ‖deriv f x‖) +
                (if c ∈ Icc u m then
                  regulatedPointCharge f c cLeft cRight else 0)) +
              ((∫ x in m..v, ‖deriv f x‖) +
                (if d ∈ Icc m v then
                  regulatedPointCharge f d dLeft dRight else 0)) :=
          add_le_add hleftBound hrightBound
        _ = (∫ x in u..v, ‖deriv f x‖) +
              (if c ∈ Icc u v then
                regulatedPointCharge f c cLeft cRight else 0) +
              (if d ∈ Icc u v then
                regulatedPointCharge f d dLeft dRight else 0) := by
          simp only [hcMem, hdMem]
          rw [← hadd]
          ring

/-! ## Specialization to the Hermitian two-carrier profile -/

def fixedAwayHermitianCellJumpCharge
    (t δ s a s' a' u v : ℝ) : ℝ :=
  if a = a' then
    if a ∈ Icc u v then 2 * Real.pi ^ 2 else 0
  else
    (if a ∈ Icc u v then
      2 * Real.pi * ‖fixedAwayScaledPV t δ s' a' a‖ else 0) +
    (if a' ∈ Icc u v then
      2 * Real.pi * ‖fixedAwayScaledPV t δ s a a'‖ else 0)

theorem norm_sub_fixedAwayScaledHermitianProduct_le_integral_add_cellJumpCharge
    {t δ s a s' a' u v : ℝ}
    (hδ : 0 < δ) (hδt : δ < t) (hs : 0 < s) (hs' : 0 < s')
    (huv : u < v) :
    ‖fixedAwayScaledHermitianProduct t δ s a s' a' u -
        fixedAwayScaledHermitianProduct t δ s a s' a' v‖ ≤
      (∫ x in u..v,
        ‖deriv (fixedAwayScaledHermitianProduct t δ s a s' a') x‖) +
      fixedAwayHermitianCellJumpCharge t δ s a s' a' u v := by
  let f : ℝ → ℂ := fixedAwayScaledHermitianProduct t δ s a s' a'
  have hs0 : s ≠ 0 := hs.ne'
  have hs0' : s' ≠ 0 := hs'.ne'
  have hint : Integrable (deriv f) := by
    simpa only [f] using!
      integrable_deriv_fixedAwayScaledHermitianProduct
        hδ hδt hs0 hs0'
  have hderiv : ∀ x ∈ Ioo u v, x ≠ a → x ≠ a' →
      HasDerivAt f (deriv f x) x := by
    intro x _hx hxa hxa'
    exact (hasDerivAt_fixedAwayScaledHermitianProduct
      hδ hδt.le hs0 hs0' hxa hxa').differentiableAt.hasDerivAt
  have hcont : ∀ x, x ≠ a → x ≠ a' → ContinuousAt f x := by
    intro x hxa hxa'
    exact (hasDerivAt_fixedAwayScaledHermitianProduct
      hδ hδt.le hs0 hs0' hxa hxa').continuousAt
  rcases lt_trichotomy a a' with haa' | haa' | ha'a
  · have hraw := norm_sub_le_integral_add_two_regulatedPointCharges
      (f := f) (c := a) (d := a')
      (cLeft := (Complex.I * Real.pi) *
        conj (fixedAwayScaledPV t δ s' a' a))
      (cRight := (-Complex.I * Real.pi) *
        conj (fixedAwayScaledPV t δ s' a' a))
      (dLeft := fixedAwayScaledPV t δ s a a' *
        conj (Complex.I * Real.pi))
      (dRight := fixedAwayScaledPV t δ s a a' *
        conj (-Complex.I * Real.pi))
      huv haa' hderiv hint hcont
      (tendsto_fixedAwayScaledHermitianProduct_nhdsLT_leftCarrier_of_pos
        hδ hδt.le hs hs0' haa'.ne)
      (tendsto_fixedAwayScaledHermitianProduct_nhdsGT_leftCarrier_of_pos
        hδ hδt.le hs hs0' haa'.ne)
      (tendsto_fixedAwayScaledHermitianProduct_nhdsLT_rightCarrier_of_pos
        hδ hδt.le hs0 hs' haa'.ne)
      (tendsto_fixedAwayScaledHermitianProduct_nhdsGT_rightCarrier_of_pos
        hδ hδt.le hs0 hs' haa'.ne)
    have hclean := hraw
    simp only [f,
      regulatedPointCharge_fixedAwayHermitian_leftCarrier,
      regulatedPointCharge_fixedAwayHermitian_rightCarrier,
      fixedAwayHermitianCellJumpCharge, if_neg haa'.ne] at hclean ⊢
    exact hclean.trans_eq (by ring)
  · subst a'
    have hraw := norm_sub_le_integral_add_one_regulatedPointCharge
      (f := f) (c := a) (left := (Real.pi ^ 2 : ℂ))
      (right := (Real.pi ^ 2 : ℂ)) huv
      (fun x hx hxa ↦ hderiv x hx hxa hxa)
      hint
      (fun hxa ↦ tendsto_nhdsGT_of_continuousAt (hcont u hxa hxa))
      (fun hxa ↦ tendsto_nhdsLT_of_continuousAt (hcont v hxa hxa))
      (by
        simpa only [f] using!
          tendsto_fixedAwayScaledHermitianProduct_nhdsLT_diagonal_of_pos
            hδ hδt.le hs hs')
      (by
        simpa only [f] using!
          tendsto_fixedAwayScaledHermitianProduct_nhdsGT_diagonal_of_pos
            hδ hδt.le hs hs')
    simpa only [f,
      regulatedPointCharge_fixedAwayHermitian_diagonal,
      fixedAwayHermitianCellJumpCharge, if_pos rfl] using! hraw
  · have haane : a ≠ a' := ha'a.ne'
    have hraw := norm_sub_le_integral_add_two_regulatedPointCharges
      (f := f) (c := a') (d := a)
      (cLeft := fixedAwayScaledPV t δ s a a' *
        conj (Complex.I * Real.pi))
      (cRight := fixedAwayScaledPV t δ s a a' *
        conj (-Complex.I * Real.pi))
      (dLeft := (Complex.I * Real.pi) *
        conj (fixedAwayScaledPV t δ s' a' a))
      (dRight := (-Complex.I * Real.pi) *
        conj (fixedAwayScaledPV t δ s' a' a))
      huv ha'a
      (fun x hx hxa' hxa ↦ hderiv x hx hxa hxa')
      hint
      (fun x hxa' hxa ↦ hcont x hxa hxa')
      (tendsto_fixedAwayScaledHermitianProduct_nhdsLT_rightCarrier_of_pos
        hδ hδt.le hs0 hs' haane)
      (tendsto_fixedAwayScaledHermitianProduct_nhdsGT_rightCarrier_of_pos
        hδ hδt.le hs0 hs' haane)
      (tendsto_fixedAwayScaledHermitianProduct_nhdsLT_leftCarrier_of_pos
        hδ hδt.le hs hs0' haane)
      (tendsto_fixedAwayScaledHermitianProduct_nhdsGT_leftCarrier_of_pos
        hδ hδt.le hs hs0' haane)
    have hclean := hraw
    simp only [f,
      regulatedPointCharge_fixedAwayHermitian_leftCarrier,
      regulatedPointCharge_fixedAwayHermitian_rightCarrier,
      fixedAwayHermitianCellJumpCharge, if_neg haane] at hclean ⊢
    exact hclean.trans_eq (by ring)

theorem cellIndicator_le_singleJumpCharge
    {c q : ℝ} (hq : 0 ≤ q) (n : ℤ) :
    (if c ∈ Icc (n : ℝ) ((n : ℝ) + 1) then q else 0) ≤
      singleJumpCharge c q n := by
  by_cases hc : c ∈ Icc (n : ℝ) ((n : ℝ) + 1)
  · rw [if_pos hc]
    have hlo : n ≤ ⌊c⌋ := by
      rw [Int.le_floor]
      exact hc.1
    have hhi : ⌊c⌋ ≤ n + 1 := by
      have hmono := Int.floor_mono hc.2
      simpa using! hmono
    rcases (show ⌊c⌋ = n ∨ ⌊c⌋ = n + 1 by omega) with hfloor | hfloor
    · have hne : n ≠ n - 1 := by omega
      simp [singleJumpCharge, hfloor, hne]
    · have hn : n = ⌊c⌋ - 1 := by omega
      simp [singleJumpCharge, hn]
  · rw [if_neg hc]
    unfold singleJumpCharge
    split_ifs <;> positivity

def fixedAwayHermitianDiscreteJumpCharge
    (t δ s a s' a' : ℝ) (n : ℤ) : ℝ :=
  if a = a' then
    finiteJumpCharge {a} (fun _ ↦ 2 * Real.pi ^ 2) n
  else
    finiteJumpCharge {a, a'}
      (fun x ↦ if x = a then
        2 * Real.pi * ‖fixedAwayScaledPV t δ s' a' a‖
      else 2 * Real.pi * ‖fixedAwayScaledPV t δ s a a'‖) n

theorem summable_fixedAwayHermitianDiscreteJumpCharge
    (t δ s a s' a' : ℝ) :
    Summable (fixedAwayHermitianDiscreteJumpCharge t δ s a s' a') := by
  unfold fixedAwayHermitianDiscreteJumpCharge
  split_ifs
  · exact summable_finiteJumpCharge _ _
  · exact summable_finiteJumpCharge _ _

theorem fixedAwayHermitianCellJumpCharge_le_discreteJumpCharge
    (t δ s a s' a' : ℝ) (n : ℤ) :
    fixedAwayHermitianCellJumpCharge t δ s a s' a'
        (n : ℝ) ((n : ℝ) + 1) ≤
      fixedAwayHermitianDiscreteJumpCharge t δ s a s' a' n := by
  by_cases haa' : a = a'
  · subst a'
    have hq : 0 ≤ 2 * Real.pi ^ 2 := by positivity
    have hsingle := cellIndicator_le_singleJumpCharge (c := a) hq n
    simpa [fixedAwayHermitianCellJumpCharge,
      fixedAwayHermitianDiscreteJumpCharge, finiteJumpCharge] using! hsingle
  · have hqLeft :
        0 ≤ 2 * Real.pi * ‖fixedAwayScaledPV t δ s' a' a‖ := by positivity
    have hqRight :
        0 ≤ 2 * Real.pi * ‖fixedAwayScaledPV t δ s a a'‖ := by positivity
    have ha'a : a' ≠ a := fun h ↦ haa' h.symm
    have hleft := cellIndicator_le_singleJumpCharge (c := a) hqLeft n
    have hright := cellIndicator_le_singleJumpCharge (c := a') hqRight n
    simpa [fixedAwayHermitianCellJumpCharge,
      fixedAwayHermitianDiscreteJumpCharge, finiteJumpCharge, haa', ha'a] using!
      add_le_add hleft hright

theorem tsum_fixedAwayHermitianDiscreteJumpCharge
    (t δ s a s' a' : ℝ) :
    (∑' n : ℤ, fixedAwayHermitianDiscreteJumpCharge
      t δ s a s' a' n) =
      2 * fixedAwayHermitianCarrierJumpCost t δ s a s' a' := by
  by_cases haa' : a = a'
  · subst a'
    have hsum := tsum_finiteJumpCharge {a}
      (fun _ : ℝ ↦ 2 * Real.pi ^ 2)
    simpa [fixedAwayHermitianDiscreteJumpCharge,
      fixedAwayHermitianCarrierJumpCost] using! hsum
  · have hsum := tsum_finiteJumpCharge {a, a'}
      (fun x : ℝ ↦ if x = a then
        2 * Real.pi * ‖fixedAwayScaledPV t δ s' a' a‖
      else 2 * Real.pi * ‖fixedAwayScaledPV t δ s a a'‖)
    have ha'a : a' ≠ a := fun h ↦ haa' h.symm
    simp [fixedAwayHermitianDiscreteJumpCharge, haa', ha'a,
      fixedAwayHermitianCarrierJumpCost] at hsum ⊢
    exact hsum.trans (by ring)

def fixedAwayHermitianIntegerWeight
    (t δ s a s' a' : ℝ) (n : ℤ) : ℂ :=
  fixedAwayScaledHermitianProduct t δ s a s' a' (n : ℝ)

theorem integerSampleVariation_fixedAwayScaledHermitianProduct_le
    {t δ s a s' a' : ℝ}
    (hδ : 0 < δ) (hδt : δ < t) (hs : 0 < s) (hs' : 0 < s')
    (n : ℤ) :
    integerSampleVariation
        (fixedAwayScaledHermitianProduct t δ s a s' a') n ≤
      (∫ x in (n : ℝ)..((n : ℝ) + 1),
        ‖deriv (fixedAwayScaledHermitianProduct t δ s a s' a') x‖) +
      fixedAwayHermitianDiscreteJumpCharge t δ s a s' a' n := by
  have hraw :=
    norm_sub_fixedAwayScaledHermitianProduct_le_integral_add_cellJumpCharge
      (t := t) (δ := δ) (s := s) (a := a) (s' := s') (a' := a')
      hδ hδt hs hs' (show (n : ℝ) < (n : ℝ) + 1 by norm_num)
  unfold integerSampleVariation
  exact hraw.trans (add_le_add_right
    (fixedAwayHermitianCellJumpCharge_le_discreteJumpCharge
      t δ s a s' a' n) _)

theorem summable_variation_fixedAwayHermitianIntegerWeight
    {t δ s a s' a' : ℝ}
    (hδ : 0 < δ) (hδt : δ < t) (hs : 0 < s) (hs' : 0 < s') :
    Summable fun n : ℤ ↦
      ‖fixedAwayHermitianIntegerWeight t δ s a s' a' n -
        fixedAwayHermitianIntegerWeight t δ s a s' a' (n + 1)‖ := by
  let f : ℝ → ℂ := fixedAwayScaledHermitianProduct t δ s a s' a'
  let g : ℤ → ℝ := fun n ↦
    ∫ x in (n : ℝ)..((n : ℝ) + 1), ‖deriv f x‖
  let q : ℤ → ℝ := fixedAwayHermitianDiscreteJumpCharge t δ s a s' a'
  have hderiv : Integrable (deriv f) := by
    simpa only [f] using!
      integrable_deriv_fixedAwayScaledHermitianProduct
        hδ hδt hs.ne' hs'.ne'
  have hgHas := hderiv.norm.hasSum_intervalIntegral (0 : ℝ)
  simp only [zero_add] at hgHas
  have hcell : ∀ n,
      integerSampleVariation f n ≤ g n + q n := by
    intro n
    exact integerSampleVariation_fixedAwayScaledHermitianProduct_le
      hδ hδt hs hs' n
  have hsum := summable_integerSampleVariation_of_jump_charge
    f g q hgHas.summable
      (summable_fixedAwayHermitianDiscreteJumpCharge t δ s a s' a')
      hcell
  simpa only [integerSampleVariation, f,
    fixedAwayHermitianIntegerWeight, Int.cast_add, Int.cast_one] using! hsum

theorem tsum_variation_fixedAwayHermitianIntegerWeight_le
    {t δ s a s' a' : ℝ}
    (hδ : 0 < δ) (hδt : δ < t) (hs : 0 < s) (hs' : 0 < s') :
    (∑' n : ℤ,
      ‖fixedAwayHermitianIntegerWeight t δ s a s' a' n -
        fixedAwayHermitianIntegerWeight t δ s a s' a' (n + 1)‖) ≤
      (∫ x : ℝ,
        ‖deriv (fixedAwayScaledHermitianProduct t δ s a s' a') x‖) +
      2 * fixedAwayHermitianCarrierJumpCost t δ s a s' a' := by
  let f : ℝ → ℂ := fixedAwayScaledHermitianProduct t δ s a s' a'
  let g : ℤ → ℝ := fun n ↦
    ∫ x in (n : ℝ)..((n : ℝ) + 1), ‖deriv f x‖
  let q : ℤ → ℝ := fixedAwayHermitianDiscreteJumpCharge t δ s a s' a'
  have hderiv : Integrable (deriv f) := by
    simpa only [f] using!
      integrable_deriv_fixedAwayScaledHermitianProduct
        hδ hδt hs.ne' hs'.ne'
  have hgHas := hderiv.norm.hasSum_intervalIntegral (0 : ℝ)
  simp only [zero_add] at hgHas
  have hcell : ∀ n,
      integerSampleVariation f n ≤ g n + q n := by
    intro n
    exact integerSampleVariation_fixedAwayScaledHermitianProduct_le
      hδ hδt hs hs' n
  have hraw := tsum_integerSampleVariation_le_of_jump_charge
    f g q hgHas.summable
      (summable_fixedAwayHermitianDiscreteJumpCharge t δ s a s' a')
      hcell
  simp only [integerSampleVariation, f, g, q,
    fixedAwayHermitianIntegerWeight, Int.cast_add, Int.cast_one] at hraw ⊢
  rw [hgHas.tsum_eq,
    tsum_fixedAwayHermitianDiscreteJumpCharge] at hraw
  exact hraw

theorem summable_variation_projected_fixedAwayHermitianIntegerWeight
    {t δ s a s' a' : ℝ} {u v : ℤ}
    (hδ : 0 < δ) (hδt : δ < t) (hs : 0 < s) (hs' : 0 < s')
    (huv : u ≤ v) :
    Summable fun n : ℤ ↦
      ‖integerIntervalComplementMultiplier u v
          (fixedAwayHermitianIntegerWeight t δ s a s' a') n -
        integerIntervalComplementMultiplier u v
          (fixedAwayHermitianIntegerWeight t δ s a s' a') (n + 1)‖ := by
  exact summable_variation_integerIntervalComplementMultiplier huv _
    (summable_variation_fixedAwayHermitianIntegerWeight hδ hδt hs hs')

/-- Final integer `tsum`-BV estimate before inserting the separated rapid
decay envelopes.  The only projection costs are the two displayed endpoint
values; there are no suppressed jumps. -/
theorem tsum_variation_projected_fixedAwayHermitianIntegerWeight_le
    {t δ s a s' a' : ℝ} {u v : ℤ}
    (hδ : 0 < δ) (hδt : δ < t) (hs : 0 < s) (hs' : 0 < s')
    (huv : u ≤ v) :
    (∑' n : ℤ,
      ‖integerIntervalComplementMultiplier u v
          (fixedAwayHermitianIntegerWeight t δ s a s' a') n -
        integerIntervalComplementMultiplier u v
          (fixedAwayHermitianIntegerWeight t δ s a s' a') (n + 1)‖) ≤
      (∫ x : ℝ,
        ‖deriv (fixedAwayScaledHermitianProduct t δ s a s' a') x‖) +
      2 * fixedAwayHermitianCarrierJumpCost t δ s a s' a' +
      ‖fixedAwayHermitianIntegerWeight t δ s a s' a' u‖ +
      ‖fixedAwayHermitianIntegerWeight t δ s a s' a' v‖ := by
  have hproj := tsum_variation_integerIntervalComplementMultiplier_le
    huv (fixedAwayHermitianIntegerWeight t δ s a s' a')
    (summable_variation_fixedAwayHermitianIntegerWeight hδ hδt hs hs')
  have hbase := tsum_variation_fixedAwayHermitianIntegerWeight_le
    (t := t) (δ := δ) (s := s) (a := a) (s' := s') (a' := a')
    hδ hδt hs hs'
  exact hproj.trans (by linarith)

/-! ## A quadratic global envelope (the first rapid-decay case) -/

def fixedAwayPVQuadraticDecayConstant (t δ : ℝ) : ℝ :=
  4 * (fixedAwayPVLocalBound t +
    fixedAwayDerivativeBound t δ 3 /
      (2 * (2 * Real.pi) ^ 3))

theorem fixedAwayPVQuadraticDecayConstant_nonneg (t δ : ℝ) :
    0 ≤ fixedAwayPVQuadraticDecayConstant t δ := by
  unfold fixedAwayPVQuadraticDecayConstant
  have hden : 0 < 2 * (2 * Real.pi) ^ 3 := by positivity
  exact mul_nonneg (by norm_num) (add_nonneg
    (fixedAwayPVLocalBound_nonneg t)
    (div_nonneg (fixedAwayDerivativeBound_nonneg t δ 3) hden.le))

theorem norm_fixedAwayPVTransform_smooth_le_quadraticDecay
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) (y : ℝ) :
    ‖fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t y‖ ≤
      fixedAwayPVQuadraticDecayConstant t δ * (1 + |y|)⁻¹ ^ 2 := by
  let D : ℝ := ‖fixedAwayPVTransform
    (fixedAwaySmoothCorrection t δ) t y‖
  let B : ℝ := fixedAwayPVLocalBound t
  let C : ℝ := fixedAwayDerivativeBound t δ 3 /
    (2 * (2 * Real.pi) ^ 3)
  have hD : 0 ≤ D := norm_nonneg _
  have hB : 0 ≤ B := fixedAwayPVLocalBound_nonneg t
  have hC : 0 ≤ C := by
    dsimp only [C]
    have hdenC : 0 < 2 * (2 * Real.pi) ^ 3 := by positivity
    exact div_nonneg (fixedAwayDerivativeBound_nonneg t δ 3) hdenC.le
  change D ≤ 4 * (B + C) * (1 + |y|)⁻¹ ^ 2
  have hden : 0 < 1 + |y| := by positivity
  rw [inv_pow]
  rw [← div_eq_mul_inv]
  rw [le_div_iff₀ (pow_pos hden 2)]
  by_cases hySmall : |y| ≤ 1
  · have hlocal : D ≤ B := by
      simpa only [D, B] using!
        norm_fixedAwayPVTransform_smooth_le_local hδ hδt.le hySmall
    have hsquare : (1 + |y|) ^ 2 ≤ 4 := by nlinarith [abs_nonneg y]
    nlinarith

  · have hyLarge : 1 < |y| := lt_of_not_ge hySmall
    have hy0 : y ≠ 0 := abs_pos.mp (zero_lt_one.trans hyLarge)
    have htail := norm_fixedAwayPVTransform_smooth_le_rpow_tail_abs
      hδ hδt 3 (by norm_num) hy0
    have htailC : D ≤ C / |y| ^ 2 := by
      dsimp only [D, C]
      calc
        ‖fixedAwayPVTransform
            (fixedAwaySmoothCorrection t δ) t y‖ ≤
            (fixedAwayDerivativeBound t δ 3 /
              (2 * Real.pi) ^ 3) *
              (-|y| ^ (-(3 : ℝ) + 1) / (-(3 : ℝ) + 1)) := htail
        _ = (fixedAwayDerivativeBound t δ 3 /
              (2 * (2 * Real.pi) ^ 3)) / |y| ^ 2 := by
          norm_num
          field_simp [Real.pi_ne_zero, hy0]
    have habsSq : 0 < |y| ^ 2 := by positivity
    have htailMul : D * |y| ^ 2 ≤ C :=
      (le_div_iff₀ habsSq).mp htailC
    have hsquare : (1 + |y|) ^ 2 ≤ 4 * |y| ^ 2 := by
      nlinarith [abs_nonneg y]
    have : D * (1 + |y|) ^ 2 ≤ 4 * C := by
      calc
        D * (1 + |y|) ^ 2 ≤ D * (4 * |y| ^ 2) :=
          mul_le_mul_of_nonneg_left hsquare hD
        _ ≤ 4 * C := by nlinarith
    nlinarith

theorem summable_shiftedScaledQuadraticEnvelope
    {s a : ℝ} (hs : s ≠ 0) :
    Summable fun n : ℤ ↦
      (1 + |((n : ℝ) - a) / s|)⁻¹ ^ 2 := by
  let exceptional : ℤ → ℝ := fun n ↦
    if |(n : ℝ) - a| < 1 then 1 else 0
  have hexceptional : Summable exceptional := by
    apply summable_of_finite_support
    apply (Set.finite_Icc ⌊a⌋ (⌊a⌋ + 1)).subset
    intro n hn
    rw [Function.mem_support] at hn
    have hdlt : |(n : ℝ) - a| < 1 := by
      by_contra h
      simp [exceptional, h] at hn
    rw [abs_lt] at hdlt
    have hlow : ⌊a⌋ ≤ n := by
      rw [Int.floor_le_iff]
      linarith [hdlt.1]
    have hhighAux : n - 1 ≤ ⌊a⌋ := by
      rw [Int.le_floor]
      push_cast
      linarith [hdlt.2]
    exact ⟨hlow, by omega⟩
  have hpRaw : Summable fun n : ℤ ↦
      1 / |(n : ℝ) + (-a)| ^ (2 : ℝ) :=
    (Real.summable_one_div_int_add_rpow (-a) 2).2 (by norm_num)
  have hp : Summable fun n : ℤ ↦
      |(n : ℝ) - a|⁻¹ ^ 2 := by
    simpa only [sub_eq_add_neg, one_div, Real.rpow_two, inv_pow] using! hpRaw
  have hscaled : Summable fun n : ℤ ↦
      |s| ^ 2 * (|(n : ℝ) - a|⁻¹ ^ 2) := hp.mul_left _
  apply (hexceptional.add hscaled).of_nonneg_of_le
  · intro n
    positivity
  · intro n
    let d : ℝ := |(n : ℝ) - a|
    let S : ℝ := |s|
    have hS : 0 < S := abs_pos.mpr hs
    by_cases hdsmall : d < 1
    · have hinv : (1 + |((n : ℝ) - a) / s|)⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀
          (le_add_of_nonneg_right (abs_nonneg _))
      have hinvNonneg : 0 ≤ (1 + |((n : ℝ) - a) / s|)⁻¹ := by
        positivity
      have hsquare : (1 + |((n : ℝ) - a) / s|)⁻¹ ^ 2 ≤ 1 := by
        nlinarith [sq_nonneg ((1 + |((n : ℝ) - a) / s|)⁻¹ - 1)]
      dsimp only [exceptional]
      rw [if_pos hdsmall]
      exact hsquare.trans (le_add_of_nonneg_right (by positivity))
    · have hd : 1 ≤ d := le_of_not_gt hdsmall
      have hdpos : 0 < d := zero_lt_one.trans_le hd
      have hratio : d / S ≤ 1 + d / S := by linarith
      have hratioPos : 0 < d / S := div_pos hdpos hS
      have hinv := (inv_le_inv₀ (by positivity : 0 < 1 + d / S)
        hratioPos).2 hratio
      have hinvLeft : 0 ≤ (1 + d / S)⁻¹ := by positivity
      have hinvRight : 0 ≤ (d / S)⁻¹ := by positivity
      have hsquare : (1 + d / S)⁻¹ ^ 2 ≤ (d / S)⁻¹ ^ 2 := by
        nlinarith [sq_nonneg ((d / S)⁻¹ - (1 + d / S)⁻¹)]
      have hscaleEq : (d / S)⁻¹ ^ 2 = S ^ 2 * d⁻¹ ^ 2 := by
        field_simp [hdpos.ne', hS.ne']
      dsimp only [exceptional]
      rw [if_neg hdsmall]
      dsimp only [d, S] at hsquare hscaleEq ⊢
      rw [abs_div]
      simpa only [zero_add] using! hsquare.trans_eq hscaleEq

theorem summable_norm_fixedAwayHermitianIntegerWeight
    {t δ s a s' a' : ℝ}
    (hδ : 0 < δ) (hδt : δ < t) (hs : 0 < s) (_hs' : 0 < s') :
    Summable fun n : ℤ ↦
      ‖fixedAwayHermitianIntegerWeight t δ s a s' a' n‖ := by
  let C : ℝ := fixedAwayPVQuadraticDecayConstant t δ
  let G : ℝ := fixedAwayPVGlobalDecayConstant t δ
  have hC : 0 ≤ C := fixedAwayPVQuadraticDecayConstant_nonneg t δ
  have hG : 0 ≤ G := fixedAwayPVGlobalDecayConstant_nonneg t δ
  have henv := summable_shiftedScaledQuadraticEnvelope
    (a := a) hs.ne'
  have hmajor : Summable fun n : ℤ ↦
      (C * G) * (1 + |((n : ℝ) - a) / s|)⁻¹ ^ 2 :=
    henv.mul_left (C * G)
  apply hmajor.of_nonneg_of_le
  · intro n
    exact norm_nonneg _
  · intro n
    unfold fixedAwayHermitianIntegerWeight
    unfold fixedAwayScaledHermitianProduct fixedAwayScaledPV
    rw [norm_mul, Complex.norm_conj]
    have hleft := norm_fixedAwayPVTransform_smooth_le_quadraticDecay
      hδ hδt (((n : ℝ) - a) / s)
    have hrightRaw := norm_fixedAwayPVTransform_smooth_le_globalDecay
      hδ hδt (((n : ℝ) - a') / s')
    have hright :
        ‖fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t
            (((n : ℝ) - a') / s')‖ ≤ G := by
      calc
        _ ≤ G * (1 + |((n : ℝ) - a') / s'|)⁻¹ := hrightRaw
        _ ≤ G := by
          apply mul_le_of_le_one_right hG
          exact inv_le_one_of_one_le₀
            (le_add_of_nonneg_right (abs_nonneg _))
    dsimp only [C, G] at hleft hright ⊢
    nlinarith [mul_le_mul hleft hright (norm_nonneg _)
      (mul_nonneg (fixedAwayPVQuadraticDecayConstant_nonneg t δ)
        (by positivity))]

/-- Fully instantiated off-diagonal Abel estimate for the projected
fixed-away Hermitian multiplier.  Subsequent scale-separation estimates only
have to bound the four explicit analytic quantities on the right. -/
theorem norm_tsum_projected_fixedAwayHermitianRamanujanMultiplier_le
    {t δ s a s' a' : ℝ} {u v : ℤ} {p p' : ℕ}
    (hδ : 0 < δ) (hδt : δ < t) (hs : 0 < s) (hs' : 0 < s')
    (huv : u ≤ v) (hp : p ≠ 0) (hp' : p' ≠ 0) (hpp' : p ≠ p') :
    ‖∑' n : ℤ,
        hermitianRamanujanMultiplierTerm
          (integerIntervalComplementMultiplier u v
            (fixedAwayHermitianIntegerWeight t δ s a s' a')) p p' n‖ ≤
      (2 * ((ArithmeticFunction.sigma 1 p : ℝ) *
        (ArithmeticFunction.sigma 1 p' : ℝ))) *
        ((∑' n : ℤ,
          ‖fixedAwayHermitianIntegerWeight t δ s a s' a' n‖) +
          ((∫ x : ℝ,
            ‖deriv (fixedAwayScaledHermitianProduct t δ s a s' a') x‖) +
          2 * fixedAwayHermitianCarrierJumpCost t δ s a s' a' +
          ‖fixedAwayHermitianIntegerWeight t δ s a s' a' u‖ +
          ‖fixedAwayHermitianIntegerWeight t δ s a s' a' v‖)) := by
  have hw := summable_norm_fixedAwayHermitianIntegerWeight
    (t := t) (δ := δ) (s := s) (a := a) (s' := s') (a' := a')
    hδ hδt hs hs'
  have hvar := summable_variation_fixedAwayHermitianIntegerWeight
    (t := t) (δ := δ) (s := s) (a := a) (s' := s') (a' := a')
    hδ hδt hs hs'
  have hraw := norm_tsum_projected_hermitianRamanujanMultiplierTerm_le
    (fixedAwayHermitianIntegerWeight t δ s a s' a')
    huv hp hp' hpp' hw hvar
  have htv := tsum_variation_fixedAwayHermitianIntegerWeight_le
    (t := t) (δ := δ) (s := s) (a := a) (s' := s') (a' := a')
    hδ hδt hs hs'
  exact hraw.trans (by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith)

end

end Erdos1002
