import ErdosProblems.Erdos1038.RecoveryPositiveAssembly
import ErdosProblems.Erdos1038.RecoveryPositiveExterior
import ErdosProblems.Erdos1038.OneCutScaledRootBounds

/-!
# Exact zero-platform limit for positive-buffer recovery

This file identifies the limiting negative set, proves that its volume is
`Lambda(q)`, and passes to the canonical positive buffers by dominated
convergence.
-/

open scoped ENNReal Real
open Filter MeasureTheory Set Topology

namespace Erdos1038

noncomputable section

theorem platformAngularReferenceMeasure_singleton_zero (k a theta : ℝ) :
    platformAngularReferenceMeasure k a {theta} = 0 := by
  unfold platformAngularReferenceMeasure
  apply withDensity_absolutelyContinuous
  simp

theorem platformConstantReferenceMeasure_two_eq_zero
    {k a : ℝ} (ha2 : a < 2) :
    platformConstantReferenceMeasure k a {2} = 0 := by
  have hmeas : Measurable (platformAngularDistance a) := by
    unfold platformAngularDistance
    fun_prop
  rw [platformConstantReferenceMeasure,
    Measure.map_apply hmeas (measurableSet_singleton (2 : ℝ))]
  apply withDensity_absolutelyContinuous
  rw [Measure.restrict_apply
    ((measurableSet_singleton (2 : ℝ)).preimage hmeas)]
  apply measure_mono_null (t := {(Real.pi : ℝ)})
  · intro theta htheta
    rcases htheta with ⟨hthetaTwo, hthetaIoc⟩
    have hcos : Real.cos theta = -1 := by
      change platformAngularDistance a theta = 2 at hthetaTwo
      unfold platformAngularDistance platformCenter platformRadius at hthetaTwo
      have hcoef : 0 < (2 - a) / 2 := by linarith
      nlinarith [Real.neg_one_le_cos theta]
    have hthetaIcc : theta ∈ Icc (0 : ℝ) Real.pi :=
      ⟨hthetaIoc.1.le, hthetaIoc.2⟩
    have hpiIcc : Real.pi ∈ Icc (0 : ℝ) Real.pi :=
      ⟨Real.pi_pos.le, le_rfl⟩
    have heq : theta = Real.pi :=
      Real.bijOn_cos.injOn hthetaIcc hpiIcc (by simpa using! hcos)
    simpa only [mem_singleton_iff] using! heq
  · exact Real.volume_singleton

theorem positiveBufferContinuousRootMeasure_one_eq_zero
    {s alpha : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    positiveBufferContinuousRootMeasure s alpha {1} = 0 := by
  have hroot : Measurable positiveBufferRootCoordinate := by
    unfold positiveBufferRootCoordinate
    fun_prop
  rw [positiveBufferContinuousRootMeasure,
    Measure.map_apply hroot (measurableSet_singleton (1 : ℝ))]
  have hpre : positiveBufferRootCoordinate ⁻¹' ({1} : Set ℝ) = {2} := by
    ext d
    simp only [mem_preimage, mem_singleton_iff, positiveBufferRootCoordinate]
    constructor <;> intro h <;> linarith
  rw [hpre]
  exact platformConstantReferenceMeasure_two_eq_zero (positiveBufferDistanceLeft_lt_two hs hs1)

theorem positiveBufferContinuousRootMeasure_ae_lt_one
    {s alpha : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ∀ᵐ y ∂(positiveBufferContinuousRootMeasure s alpha), y < 1 := by
  have hsupp : ∀ᵐ y ∂(positiveBufferContinuousRootMeasure s alpha),
      y ∈ Icc (positiveBufferDistanceLeft s - 1) 1 :=
    mem_ae_iff.mpr
      (positiveBufferContinuousRootMeasure_compl_support hs hs1)
  have hne : ∀ᵐ y ∂(positiveBufferContinuousRootMeasure s alpha),
      y ≠ 1 := by
    rw [ae_iff]
    simpa only [not_ne_iff] using! positiveBufferContinuousRootMeasure_one_eq_zero hs hs1
  filter_upwards [hsupp, hne] with y hy hyne
  exact lt_of_le_of_ne hy.2 hyne

theorem positiveBufferPotential_zeroPlatform_nonneg_right
    {q x : ℝ} (hq : q ∈ Ioo (0 : ℝ) qCeiling)
    (hqs : q ≤ qSoft) (hx : 1 < x) :
    0 ≤ positiveBufferPotential (s q) (A q) x := by
  have hs := s_mem_Ioo_of_mem_Ioo hq
  have hA := A_mem_Ioo_of_mem_Ioo hq
  have hAs := A_le_s_of_pos_le_qSoft hq.1 hqs
  let mu : Measure ℝ := positiveBufferContinuousRootMeasure (s q) (A q)
  have hae : ∀ᵐ y ∂mu, y < 1 := by
    simpa only [mu] using! positiveBufferContinuousRootMeasure_ae_lt_one hs.1 hs.2
  have hi1 := integrable_positiveBufferContinuousRootMeasure_log_kernel_global
    hs.1 hs.2 hA.1.le hAs (x := (1 : ℝ))
  have hix := integrable_positiveBufferContinuousRootMeasure_log_kernel_global
    hs.1 hs.2 hA.1.le hAs (x := x)
  have hint :
      (∫ y : ℝ, Real.log |(1 : ℝ) - y| ∂mu) ≤
        ∫ y : ℝ, Real.log |x - y| ∂mu := by
    apply integral_mono_ae hi1 hix
    filter_upwards [hae] with y hy
    have hone : 0 < 1 - y := sub_pos.mpr hy
    have hxy : 0 < x - y := sub_pos.mpr (hy.trans hx)
    rw [abs_of_pos hone, abs_of_pos hxy]
    exact (Real.strictMonoOn_log hone hxy (by linarith)).le
  have hatom : Real.log |(1 : ℝ) + 1| ≤ Real.log |x + 1| := by
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 + 1),
      abs_of_pos (by linarith : 0 < x + 1)]
    have htwo : (0 : ℝ) < 2 := by norm_num
    have hxone : 0 < x + 1 := by linarith
    have hlt : (2 : ℝ) < x + 1 := by linarith
    norm_num only
    exact (Real.strictMonoOn_log htwo hxone hlt).le
  have hmulAtom := mul_le_mul_of_nonneg_left hatom hA.1.le
  have hmulCont := mul_le_mul_of_nonneg_left hint
    (sub_nonneg.mpr (hAs.trans_lt hs.2).le)
  have hcomp : positiveBufferPotential (s q) (A q) 1 ≤
      positiveBufferPotential (s q) (A q) x := by
    rw [positiveBufferPotential_eq_atom_add_root hs.1 hs.2 hA.1.le hAs,
      positiveBufferPotential_eq_atom_add_root hs.1 hs.2 hA.1.le hAs]
    exact add_le_add hmulAtom hmulCont
  have hone : positiveBufferPotential (s q) (A q) 1 = 0 := by
    rw [positiveBufferPotential_eq_platformValue hs.1 hs.2 hA.1.le hAs]
    · exact positiveBufferPlatformValue_s_A_eq_zero hq
    · exact ⟨by linarith [positiveBufferDistanceLeft_lt_two hs.1 hs.2], le_rfl⟩
  linarith

def zeroPlatformNegativeLeftEndpoint (q : ℝ) : ℝ :=
  oneCutExteriorDistance q (uMinus q) - 1

def zeroPlatformNegativeRightEndpoint (q : ℝ) : ℝ :=
  oneCutExteriorDistance q (uPlus q) - 1

theorem zeroPlatformNegativeEndpoints_length (q : ℝ) : zeroPlatformNegativeRightEndpoint q - zeroPlatformNegativeLeftEndpoint q = Lambda q := by
  unfold zeroPlatformNegativeRightEndpoint zeroPlatformNegativeLeftEndpoint oneCutExteriorDistance Lambda
  ring

theorem zeroPlatformNegativeEndpoints_order
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    -1 < zeroPlatformNegativeRightEndpoint q ∧ zeroPlatformNegativeRightEndpoint q < positiveBufferDistanceLeft (s q) - 1 ∧
      zeroPlatformNegativeLeftEndpoint q < -1 ∧ zeroPlatformNegativeLeftEndpoint q < zeroPlatformNegativeRightEndpoint q := by
  have hqdom := q_mem_Ioo_of_pos_le_qSoft hq hqs.le
  have hq1 := mem_Ioo_zero_qCeiling_imp_lt_one hqdom
  have hplus := uPlus_spec hq hqs
  have hminus := uMinus_spec hq hqs.le
  have hanti := oneCutExteriorDistance_strictAntiOn_Ici hq
  have hinv1 : 1 < q⁻¹ := one_lt_inv_q hq hq1
  have hDplusPos : 0 < oneCutExteriorDistance q (uPlus q) := by
    have hlt := hanti hplus.1.le hinv1.le hplus.2.1
    rw [oneCutExteriorDistance_inv q] at hlt
    exact hlt
  have hDplusEdge : oneCutExteriorDistance q (uPlus q) <
      positiveBufferDistanceLeft (s q) := by
    have hlt := hanti (show (1 : ℝ) ∈ Ici 1 by simp)
      hplus.1.le hplus.1
    rwa [oneCutExteriorDistance_one hq] at hlt
  have hDminusNeg : oneCutExteriorDistance q (uMinus q) < 0 := by
    have hlt := hanti hinv1.le (hinv1.trans hminus.1).le hminus.1
    rwa [oneCutExteriorDistance_inv q] at hlt
  have hDorder : oneCutExteriorDistance q (uMinus q) <
      oneCutExteriorDistance q (uPlus q) := by
    exact hanti hplus.1.le (hinv1.trans hminus.1).le
      (hplus.2.1.trans hminus.1)
  unfold zeroPlatformNegativeLeftEndpoint zeroPlatformNegativeRightEndpoint
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem positiveBufferPotential_zeroPlatform_nonneg_neg_two
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) qCeiling)
    (hqs : q ≤ qSoft) :
    0 ≤ positiveBufferPotential (s q) (A q) (-2) := by
  have hs := s_mem_Ioo_of_mem_Ioo hq
  have hA := A_mem_Ioo_of_mem_Ioo hq
  have hAs := A_le_s_of_pos_le_qSoft hq.1 hqs
  let mu : Measure ℝ := positiveBufferContinuousRootMeasure (s q) (A q)
  have hsupp : ∀ᵐ y ∂mu,
      y ∈ Icc (positiveBufferDistanceLeft (s q) - 1) 1 := by
    simpa only [mu] using! mem_ae_iff.mpr
      (positiveBufferContinuousRootMeasure_compl_support hs.1 hs.2)
  have hintNonneg : 0 ≤
      ∫ y : ℝ, Real.log |(-2 : ℝ) - y| ∂mu := by
    apply integral_nonneg_of_ae
    filter_upwards [hsupp] with y hy
    have hyneg : 0 < 2 + y := by
      have hdistPos := positiveBufferDistanceLeft_pos hs.1
      linarith [hy.1]
    rw [show (-2 : ℝ) - y = -(2 + y) by ring, abs_neg,
      abs_of_pos hyneg]
    exact Real.log_nonneg (by
      have hdistPos := positiveBufferDistanceLeft_pos hs.1
      linarith [hy.1])
  rw [positiveBufferPotential_eq_atom_add_root hs.1 hs.2 hA.1.le hAs]
  have hatom : Real.log |(-2 : ℝ) + 1| = 0 := by norm_num
  rw [hatom, mul_zero, zero_add]
  exact mul_nonneg (sub_nonneg.mpr (hAs.trans_lt hs.2).le) hintNonneg

theorem zeroPlatformNegativeLeftEndpoint_ge_neg_two
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    -2 ≤ zeroPlatformNegativeLeftEndpoint q := by
  have hqdom := q_mem_Ioo_of_pos_le_qSoft hq hqs.le
  have hs := s_mem_Ioo_of_mem_Ioo hqdom
  obtain ⟨u, hu, huD⟩ :=
    (existsUnique_oneCutExteriorDistance_eq hq
      (d := (-1 : ℝ)) (by linarith [positiveBufferDistanceLeft_pos hs.1])).exists
  have hq1 := mem_Ioo_zero_qCeiling_imp_lt_one hqdom
  have hinv1 : 1 < q⁻¹ := one_lt_inv_q hq hq1
  have huOuter : q⁻¹ < u := by
    by_contra hnot
    have hule : u ≤ q⁻¹ := le_of_not_gt hnot
    rcases hule.eq_or_lt with heq | hlt
    · rw [heq, oneCutExteriorDistance_inv q] at huD
      norm_num at huD
    · have hanti := oneCutExteriorDistance_strictAntiOn_Ici hq
        hu.le hinv1.le hlt
      rw [oneCutExteriorDistance_inv q, huD] at hanti
      norm_num at hanti
  have hformula := positiveBufferPotential_zeroPlatform_oneCut_outer
    hqdom hqs.le huOuter
  rw [huD, show (-1 : ℝ) - 1 = -2 by norm_num] at hformula
  have hU := positiveBufferPotential_zeroPlatform_nonneg_neg_two hqdom hqs.le
  have hFle : exteriorFunction q u ≤ 0 := by linarith
  have hminus := uMinus_spec hq hqs.le
  have hroot : exteriorFunction q (uMinus q) = 0 :=
    exteriorEquation_iff_exteriorFunction_eq_zero.mp hminus.2
  have hrootle : uMinus q ≤ u := by
    by_contra hnot
    have hult : u < uMinus q := lt_of_not_ge hnot
    have hanti := exteriorFunction_strictAntiOn_outer hq hqs.le
      huOuter hminus.1 hult
    rw [hroot] at hanti
    linarith
  have hDle : oneCutExteriorDistance q u ≤
      oneCutExteriorDistance q (uMinus q) := by
    rcases hrootle.eq_or_lt with heq | hlt
    · rw [heq]
    · exact (oneCutExteriorDistance_strictAntiOn_Ici hq
        (show uMinus q ∈ Ici 1 by
          exact (one_lt_inv_q hq hq1 |>.trans hminus.1).le)
        hu.le hlt).le
  unfold zeroPlatformNegativeLeftEndpoint
  linarith

theorem positiveBufferPotential_zeroPlatform_neg_iff_of_lt_edge
    {q x : ℝ} (hq : 0 < q) (hqs : q < qSoft)
    (hxedge : x < positiveBufferDistanceLeft (s q) - 1)
    (hxatom : x ≠ -1) :
    positiveBufferPotential (s q) (A q) x < 0 ↔
      x ∈ Ioo (zeroPlatformNegativeLeftEndpoint q) (zeroPlatformNegativeRightEndpoint q) := by
  have hqdom := q_mem_Ioo_of_pos_le_qSoft hq hqs.le
  have hq1 := mem_Ioo_zero_qCeiling_imp_lt_one hqdom
  have hinv1 : 1 < q⁻¹ := one_lt_inv_q hq hq1
  have hcross := zeroPlatformNegativeEndpoints_order hq hqs
  obtain ⟨u, hu, huD⟩ :=
    (existsUnique_oneCutExteriorDistance_eq hq
      (d := x + 1) (by linarith)).exists
  have hanti := oneCutExteriorDistance_strictAntiOn_Ici hq
  have hplus := uPlus_spec hq hqs
  have hminus := uMinus_spec hq hqs.le
  have hplusRoot : exteriorFunction q (uPlus q) = 0 :=
    exteriorEquation_iff_exteriorFunction_eq_zero.mp hplus.2.2
  have hminusRoot : exteriorFunction q (uMinus q) = 0 :=
    exteriorEquation_iff_exteriorFunction_eq_zero.mp hminus.2
  rcases lt_or_gt_of_ne (Ne.symm hxatom) with hxright | hxleft
  · have huInner : u < q⁻¹ := by
      by_contra hnot
      have hinvle : q⁻¹ ≤ u := le_of_not_gt hnot
      rcases hinvle.eq_or_lt with heq | hlt
      · rw [← heq, oneCutExteriorDistance_inv q] at huD
        linarith
      · have hstrict := hanti hinv1.le hu.le hlt
        rw [oneCutExteriorDistance_inv q, huD] at hstrict
        linarith
    have hformula := positiveBufferPotential_zeroPlatform_oneCut_inner
      hqdom hqs.le hu huInner
    rw [huD, show x + 1 - 1 = x by ring] at hformula
    constructor
    · intro hneg
      have hFpos : 0 < exteriorFunction q u := by linarith
      have hplusu : uPlus q < u := by
        by_contra hnot
        have hule : u ≤ uPlus q := le_of_not_gt hnot
        rcases hule.eq_or_lt with heq | hlt
        · rw [heq, hplusRoot] at hFpos
          linarith
        · have hFneg := exteriorFunction_inner_neg_before_uPlus
            hq hqs hu huInner hlt
          linarith
      have hDlt := hanti hplus.1.le hu.le hplusu
      constructor
      · exact hcross.2.2.1.trans hxright
      · unfold zeroPlatformNegativeRightEndpoint
        linarith
    · intro hxIoo
      have hplusu : uPlus q < u := by
        by_contra hnot
        have hule : u ≤ uPlus q := le_of_not_gt hnot
        rcases hule.eq_or_lt with heq | hlt
        · rw [heq] at huD
          unfold zeroPlatformNegativeRightEndpoint at hxIoo
          linarith [hxIoo.2]
        · have hDlt := hanti hu.le hplus.1.le hlt
          unfold zeroPlatformNegativeRightEndpoint at hxIoo
          linarith [hxIoo.2]
      have hFpos := exteriorFunction_inner_pos_after_uPlus
        hq hqs huInner hplusu
      linarith
  · have huOuter : q⁻¹ < u := by
      by_contra hnot
      have hule : u ≤ q⁻¹ := le_of_not_gt hnot
      rcases hule.eq_or_lt with heq | hlt
      · rw [heq, oneCutExteriorDistance_inv q] at huD
        linarith
      · have hstrict := hanti hu.le hinv1.le hlt
        rw [oneCutExteriorDistance_inv q, huD] at hstrict
        linarith
    have hformula := positiveBufferPotential_zeroPlatform_oneCut_outer
      hqdom hqs.le huOuter
    rw [huD, show x + 1 - 1 = x by ring] at hformula
    constructor
    · intro hneg
      have hFpos : 0 < exteriorFunction q u := by linarith
      have huminu : u < uMinus q := by
        by_contra hnot
        have hmle : uMinus q ≤ u := le_of_not_gt hnot
        rcases hmle.eq_or_lt with heq | hlt
        · rw [← heq, hminusRoot] at hFpos
          linarith
        · have hFneg := exteriorFunction_strictAntiOn_outer hq hqs.le
            hminus.1 huOuter hlt
          rw [hminusRoot] at hFneg
          linarith
      have hDlt := hanti hu.le
        (hinv1.trans hminus.1).le huminu
      constructor
      · unfold zeroPlatformNegativeLeftEndpoint
        linarith
      · exact hxleft.trans hcross.1
    · intro hxIoo
      have huminu : u < uMinus q := by
        by_contra hnot
        have hmle : uMinus q ≤ u := le_of_not_gt hnot
        rcases hmle.eq_or_lt with heq | hlt
        · rw [← heq] at huD
          unfold zeroPlatformNegativeLeftEndpoint at hxIoo
          linarith [hxIoo.1]
        · have hDlt := hanti
            (hinv1.trans hminus.1).le hu.le hlt
          unfold zeroPlatformNegativeLeftEndpoint at hxIoo
          linarith [hxIoo.1]
      have hFpos := exteriorFunction_strictAntiOn_outer hq hqs.le
        huOuter hminus.1 huminu
      rw [hminusRoot] at hFpos
      linarith

theorem positiveBufferPotential_zeroPlatform_neg_iff
    {q x : ℝ} (hq : 0 < q) (hqs : q < qSoft)
    (hxatom : x ≠ -1) :
    positiveBufferPotential (s q) (A q) x < 0 ↔
      x ∈ Ioo (zeroPlatformNegativeLeftEndpoint q) (zeroPlatformNegativeRightEndpoint q) := by
  have hqdom := q_mem_Ioo_of_pos_le_qSoft hq hqs.le
  have hs := s_mem_Ioo_of_mem_Ioo hqdom
  have hA := A_mem_Ioo_of_mem_Ioo hqdom
  have hAs := A_le_s_of_pos_le_qSoft hq hqs.le
  have hcross := zeroPlatformNegativeEndpoints_order hq hqs
  by_cases hxedge : x < positiveBufferDistanceLeft (s q) - 1
  · exact positiveBufferPotential_zeroPlatform_neg_iff_of_lt_edge hq hqs hxedge hxatom
  · have hedgex : positiveBufferDistanceLeft (s q) - 1 ≤ x :=
      le_of_not_gt hxedge
    constructor
    · intro hneg
      by_cases hxone : x ≤ 1
      · have hxmem : x ∈ Icc (positiveBufferDistanceLeft (s q) - 1) 1 :=
          ⟨hedgex, hxone⟩
        have hzero : positiveBufferPotential (s q) (A q) x = 0 := by
          rw [positiveBufferPotential_eq_platformValue
            hs.1 hs.2 hA.1.le hAs hxmem]
          exact positiveBufferPlatformValue_s_A_eq_zero hqdom
        linarith
      · have hnonneg := positiveBufferPotential_zeroPlatform_nonneg_right hqdom hqs.le
          (lt_of_not_ge hxone)
        linarith
    · intro hxIoo
      exfalso
      exact (not_lt_of_ge hedgex) (hxIoo.2.trans hcross.2.1)

theorem volume_positiveBufferPotential_zeroPlatform_negativeSet
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    volume {x : ℝ | x ∈ Icc (-2 : ℝ) 2 ∧
        positiveBufferPotential (s q) (A q) x < 0} =
      ENNReal.ofReal (Lambda q) := by
  have hleft := zeroPlatformNegativeLeftEndpoint_ge_neg_two hq hqs
  have hcross := zeroPlatformNegativeEndpoints_order hq hqs
  have hqdom := q_mem_Ioo_of_pos_le_qSoft hq hqs.le
  have hs := s_mem_Ioo_of_mem_Ioo hqdom
  have hrightTwo : zeroPlatformNegativeRightEndpoint q < 2 := by
    have ha2 := positiveBufferDistanceLeft_lt_two hs.1 hs.2
    linarith [hcross.2.1]
  have hsubset : Ioo (zeroPlatformNegativeLeftEndpoint q) (zeroPlatformNegativeRightEndpoint q) ⊆ Icc (-2 : ℝ) 2 := by
    intro x hx
    exact ⟨hleft.trans hx.1.le, hx.2.trans hrightTwo |>.le⟩
  calc
    volume {x : ℝ | x ∈ Icc (-2 : ℝ) 2 ∧
          positiveBufferPotential (s q) (A q) x < 0} =
        volume (Ioo (zeroPlatformNegativeLeftEndpoint q) (zeroPlatformNegativeRightEndpoint q)) := by
      apply measure_congr
      have hae : ∀ᵐ x : ℝ ∂volume, x ≠ -1 := by
        rw [ae_iff]
        simpa only [not_ne_iff] using!
          (show volume ({-1} : Set ℝ) = 0 from Real.volume_singleton)
      filter_upwards [hae] with x hx
      change (x ∈ Icc (-2 : ℝ) 2 ∧
        positiveBufferPotential (s q) (A q) x < 0) =
          (x ∈ Ioo (zeroPlatformNegativeLeftEndpoint q) (zeroPlatformNegativeRightEndpoint q))
      rw [positiveBufferPotential_zeroPlatform_neg_iff hq hqs hx]
      apply propext
      constructor
      · exact fun h ↦ h.2
      · exact fun h ↦ ⟨hsubset h, h⟩
    _ = ENNReal.ofReal (zeroPlatformNegativeRightEndpoint q - zeroPlatformNegativeLeftEndpoint q) := by
      rw [Real.volume_Ioo]
    _ = ENNReal.ofReal (Lambda q) := by rw [zeroPlatformNegativeEndpoints_length]

theorem tendsto_positiveBufferPotential_alpha
    {q x : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    Tendsto
      (fun n ↦ positiveBufferPotential (s q) (positiveBufferAlpha q n) x)
      atTop (nhds (positiveBufferPotential (s q) (A q) x)) := by
  have hqdom := q_mem_Ioo_of_pos_le_qSoft hq hqs.le
  have hs := s_mem_Ioo_of_mem_Ioo hqdom
  have hA := A_mem_Ioo_of_mem_Ioo hqdom
  have hAs := A_le_s_of_pos_le_qSoft hq hqs.le
  let E : ℝ := (1 / Real.pi) *
    (∫ theta : ℝ in 0..Real.pi,
      Real.log |(x + 1) - platformAngularDistance
        (positiveBufferDistanceLeft (s q)) theta|)
  let B : ℝ := Real.log |x + 1| - (1 / Real.pi) *
    (∫ theta : ℝ in 0..Real.pi,
      (Real.sqrt (2 * positiveBufferDistanceLeft (s q)) /
          platformAngularDistance
            (positiveBufferDistanceLeft (s q)) theta) *
        Real.log |(x + 1) - platformAngularDistance
          (positiveBufferDistanceLeft (s q)) theta|)
  have hn (n : ℕ) :
      positiveBufferPotential (s q) (positiveBufferAlpha q n) x =
        E + positiveBufferAlpha q n * B := by
    have h := positiveBufferPotential_eq_equilibrium_add_atom_sub_balayage
      hs.1 hs.2 (positiveBufferAlpha_nonneg hq hqs n)
      (positiveBufferAlpha_le_s hq hqs n) (d := x + 1)
    simpa only [add_sub_cancel_right, E, B] using! h
  have hlimit : positiveBufferPotential (s q) (A q) x = E + A q * B := by
    have h := positiveBufferPotential_eq_equilibrium_add_atom_sub_balayage
      hs.1 hs.2 hA.1.le hAs (d := x + 1)
    simpa only [add_sub_cancel_right, E, B] using! h
  rw [show (fun n ↦ positiveBufferPotential (s q)
      (positiveBufferAlpha q n) x) =
      fun n ↦ E + positiveBufferAlpha q n * B by
        funext n
        exact hn n,
    hlimit]
  exact tendsto_const_nhds.add
    (tendsto_positiveBufferAlpha.mul tendsto_const_nhds)

theorem finite_positiveBufferPotential_zeroPlatform_off_support_zero
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    {x : ℝ | x ∉ Icc (positiveBufferDistanceLeft (s q) - 1) 1 ∧
      positiveBufferPotential (s q) (A q) x = 0}.Finite := by
  have hqdom := q_mem_Ioo_of_pos_le_qSoft hq hqs.le
  have hs := s_mem_Ioo_of_mem_Ioo hqdom
  have hA := A_mem_Ioo_of_mem_Ioo hqdom
  have hAs := A_le_s_of_pos_le_qSoft hq hqs.le
  let U : ℝ → ℝ := positiveBufferPotential (s q) (A q)
  let ell : ℝ := positiveBufferDistanceLeft (s q) - 1
  let Zleft : Set ℝ := {x | x ∈ Iio (-1 : ℝ) ∧ U x = 0}
  let Zgap : Set ℝ := {x | x ∈ Ioo (-1 : ℝ) ell ∧ U x = 0}
  let Zright : Set ℝ := {x | x ∈ Ioi (1 : ℝ) ∧ U x = 0}
  let Cover : Set ℝ := Zleft ∪ ({-1} ∪ (Zgap ∪ Zright))
  have hZleft : Zleft.Finite := by
    apply finite_zeroSet_of_strictConcaveOn
    simpa only [Zleft, U] using! positiveBufferPotential_strictConcaveOn_left
      hs.1 hs.2 hA.1 hAs
  have hZgap : Zgap.Finite := by
    apply finite_zeroSet_of_strictConcaveOn
    simpa only [Zgap, U, ell] using!
      positiveBufferPotential_strictConcaveOn_gap hs.1 hs.2 hA.1 hAs
  have hZright : Zright.Finite := by
    apply finite_zeroSet_of_strictConcaveOn
    simpa only [Zright, U] using!
      positiveBufferPotential_strictConcaveOn_right hs.1 hs.2 hA.1 hAs
  have hCover : Cover.Finite := by
    exact hZleft.union ((Set.finite_singleton (-1 : ℝ)).union
      (hZgap.union hZright))
  apply hCover.subset
  intro x hx
  have hxzero : U x = 0 := by simpa only [U] using! hx.2
  by_cases hxleft : x < -1
  · exact Or.inl ⟨hxleft, hxzero⟩
  by_cases hxatom : x = -1
  · exact Or.inr (Or.inl hxatom)
  have hxatomRight : -1 < x :=
    lt_of_le_of_ne (le_of_not_gt hxleft) (Ne.symm hxatom)
  by_cases hxedge : x < ell
  · exact Or.inr (Or.inr (Or.inl ⟨⟨hxatomRight, hxedge⟩, hxzero⟩))
  have hxedgeLe : ell ≤ x := le_of_not_gt hxedge
  have hxright : 1 < x := by
    by_contra hnot
    apply hx.1
    simpa only [ell] using! ⟨hxedgeLe, le_of_not_gt hnot⟩
  exact Or.inr (Or.inr (Or.inr ⟨hxright, hxzero⟩))

theorem aestronglyMeasurable_positiveBufferPotential
    {s alpha : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (halpha : 0 ≤ alpha) (halphas : alpha ≤ s) :
    AEStronglyMeasurable (positiveBufferPotential s alpha)
      (volume.restrict (Icc (-2 : ℝ) 2)) := by
  have heq := logarithmicPotentialLp_positiveBuffer_ae
    hs hs1 halpha halphas (a := (-2 : ℝ)) (b := 2) (by norm_num)
  exact (L1.integrable_coeFn _).aestronglyMeasurable.congr heq

theorem tendsto_positiveBuffer_negativeSet_volume
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    Tendsto
      (fun n ↦ volume {x : ℝ | x ∈ Icc (-2 : ℝ) 2 ∧
        positiveBufferPotential (s q) (positiveBufferAlpha q n) x < 0})
      atTop (nhds (ENNReal.ofReal (Lambda q))) := by
  have hqdom := q_mem_Ioo_of_pos_le_qSoft hq hqs.le
  have hs := s_mem_Ioo_of_mem_Ioo hqdom
  have hA := A_mem_Ioo_of_mem_Ioo hqdom
  have hAs := A_le_s_of_pos_le_qSoft hq hqs.le
  let mu : Measure ℝ := volume.restrict (Icc (-2 : ℝ) 2)
  let N : ℝ → Set ℝ := fun alpha ↦
    {x | positiveBufferPotential (s q) alpha x < 0}
  let F : ℕ → ℝ → ℝ≥0∞ := fun n ↦
    (N (positiveBufferAlpha q n)).indicator fun _ ↦ 1
  let f : ℝ → ℝ≥0∞ := (N (A q)).indicator fun _ ↦ 1
  have hmeasN (n : ℕ) : NullMeasurableSet
      (N (positiveBufferAlpha q n)) mu := by
    apply nullMeasurableSet_lt
    · simpa only [mu] using!
        (aestronglyMeasurable_positiveBufferPotential
        hs.1 hs.2 (positiveBufferAlpha_nonneg hq hqs n)
        (positiveBufferAlpha_le_s hq hqs n)).aemeasurable
    · exact stronglyMeasurable_const.measurable.aemeasurable
  have hmeasLimit : NullMeasurableSet (N (A q)) mu := by
    apply nullMeasurableSet_lt
    · simpa only [mu] using!
        (aestronglyMeasurable_positiveBufferPotential
          hs.1 hs.2 hA.1.le hAs).aemeasurable
    · exact stronglyMeasurable_const.measurable.aemeasurable
  have hfiniteZero := finite_positiveBufferPotential_zeroPlatform_off_support_zero hq hqs
  have hzeroVolume : volume {x : ℝ |
      x ∉ Icc (positiveBufferDistanceLeft (s q) - 1) 1 ∧
        positiveBufferPotential (s q) (A q) x = 0} = 0 :=
    hfiniteZero.measure_zero volume
  have haeCasesVolume : ∀ᵐ x : ℝ ∂volume,
      x ∈ Icc (positiveBufferDistanceLeft (s q) - 1) 1 ∨
        positiveBufferPotential (s q) (A q) x ≠ 0 := by
    rw [ae_iff]
    apply measure_mono_null (t := {x : ℝ |
      x ∉ Icc (positiveBufferDistanceLeft (s q) - 1) 1 ∧
        positiveBufferPotential (s q) (A q) x = 0})
    · intro x hx
      simp only [mem_ofPred_eq] at hx ⊢
      push_neg at hx
      exact hx
    · exact hzeroVolume
  have haeCases : ∀ᵐ x : ℝ ∂mu,
      x ∈ Icc (positiveBufferDistanceLeft (s q) - 1) 1 ∨
        positiveBufferPotential (s q) (A q) x ≠ 0 := by
    exact ae_restrict_of_ae haeCasesVolume
  have hlim : ∀ᵐ x : ℝ ∂mu,
      Tendsto (fun n ↦ F n x) atTop (nhds (f x)) := by
    filter_upwards [haeCases] with x hx
    rcases hx with hxsupport | hxne
    · have hzero : positiveBufferPotential (s q) (A q) x = 0 := by
        rw [positiveBufferPotential_eq_platformValue
          hs.1 hs.2 hA.1.le hAs hxsupport]
        exact positiveBufferPlatformValue_s_A_eq_zero hqdom
      have hpos (n : ℕ) : 0 <
          positiveBufferPotential (s q) (positiveBufferAlpha q n) x :=
        positiveBufferPotential_s_pos_of_A_lt hqdom
          (positiveBufferAlpha_nonneg hq hqs n)
          (A_lt_positiveBufferAlpha hq hqs n)
          (positiveBufferAlpha_le_s hq hqs n) hxsupport
      have heq : (fun n ↦ F n x) = fun _n ↦ (0 : ℝ≥0∞) := by
        funext n
        simp only [F, N, Set.indicator_apply, mem_ofPred_eq,
          not_lt_of_ge (hpos n).le, if_false]
      have hfeq : f x = 0 := by
        simp only [f, N, Set.indicator_apply, mem_ofPred_eq, hzero,
          lt_self_iff_false, if_false]
      rw [heq, hfeq]
      exact tendsto_const_nhds
    · have ht := tendsto_positiveBufferPotential_alpha hq hqs (x := x)
      rcases lt_or_gt_of_ne hxne with hxneg | hxpos
      · have hev : ∀ᶠ n in atTop,
            positiveBufferPotential (s q) (positiveBufferAlpha q n) x < 0 :=
          ht.eventually (isOpen_Iio.mem_nhds hxneg)
        refine (tendsto_congr' ?_).2 tendsto_const_nhds
        filter_upwards [hev] with n hn
        simp only [F, f, N, Set.indicator_apply, mem_ofPred_eq, hn,
          hxneg, if_true]
      · have hev : ∀ᶠ n in atTop, 0 <
            positiveBufferPotential (s q) (positiveBufferAlpha q n) x :=
          ht.eventually (isOpen_Ioi.mem_nhds hxpos)
        refine (tendsto_congr' ?_).2 tendsto_const_nhds
        filter_upwards [hev] with n hn
        simp only [F, f, N, Set.indicator_apply, mem_ofPred_eq,
          not_lt_of_ge hn.le, not_lt_of_ge hxpos.le, if_false]
  have hDCT : Tendsto (fun n ↦ ∫⁻ x, F n x ∂mu) atTop
      (nhds (∫⁻ x, f x ∂mu)) := by
    apply tendsto_lintegral_of_dominated_convergence'
      (bound := fun _x : ℝ ↦ (1 : ℝ≥0∞))
    · intro n
      exact (stronglyMeasurable_const.aestronglyMeasurable.indicator₀
        (hmeasN n)).aemeasurable
    · intro n
      filter_upwards with x
      simp only [F, Set.indicator_apply]
      split_ifs <;> simp
    · rw [lintegral_one]
      exact (measure_ne_top mu Set.univ)
    · exact hlim
  have hlin (n : ℕ) : (∫⁻ x, F n x ∂mu) =
      volume {x : ℝ | x ∈ Icc (-2 : ℝ) 2 ∧
        positiveBufferPotential (s q) (positiveBufferAlpha q n) x < 0} := by
    rw [show F n = (N (positiveBufferAlpha q n)).indicator
      (fun _ ↦ (1 : ℝ≥0∞)) by rfl,
      lintegral_indicator_const₀ (hmeasN n) 1, one_mul]
    change (volume.restrict (Icc (-2 : ℝ) 2))
      (N (positiveBufferAlpha q n)) = _
    rw [Measure.restrict_apply₀ (hmeasN n)]
    congr 1
    ext x
    simp only [N, mem_inter_iff, mem_ofPred_eq, mem_Icc]
    tauto
  have hlinLimit : (∫⁻ x, f x ∂mu) =
      volume {x : ℝ | x ∈ Icc (-2 : ℝ) 2 ∧
        positiveBufferPotential (s q) (A q) x < 0} := by
    rw [show f = (N (A q)).indicator (fun _ ↦ (1 : ℝ≥0∞)) by rfl,
      lintegral_indicator_const₀ hmeasLimit 1, one_mul]
    change (volume.restrict (Icc (-2 : ℝ) 2)) (N (A q)) = _
    rw [Measure.restrict_apply₀ hmeasLimit]
    congr 1
    ext x
    simp only [N, mem_inter_iff, mem_ofPred_eq, mem_Icc]
    tauto
  simp_rw [hlin, hlinLimit, volume_positiveBufferPotential_zeroPlatform_negativeSet hq hqs] at hDCT
  exact hDCT

/-! ## Recovery certificates -/

/-- The canonical positive buffers satisfy the full recovery certificate at
every interior one-cut parameter. -/
theorem positiveBufferRecoveryAt_of_pos_lt_qSoft
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    PositiveBufferRecoveryAt q := by
  have hqdom := q_mem_Ioo_of_pos_le_qSoft hq hqs.le
  constructor
  · intro n
    exact volume_positiveBufferPotential_zeroSet_s_of_A_lt hqdom
      (positiveBufferAlpha_nonneg hq hqs n)
      (A_lt_positiveBufferAlpha hq hqs n)
      (positiveBufferAlpha_le_s hq hqs n)
  · exact tendsto_positiveBuffer_negativeSet_volume hq hqs

/-- Once the already-defined minimizer is known to be an interior one-cut
parameter, its positive-buffer recovery certificate is automatic. -/
theorem positiveBufferRecoveryCertificate_of_qStar_mem_Ioo
    (hqStar : qStar ∈ Ioo (0 : ℝ) qSoft) :
    PositiveBufferRecoveryCertificate :=
  ⟨hqStar.1, hqStar.2,
    positiveBufferRecoveryAt_of_pos_lt_qSoft hqStar.1 hqStar.2⟩

/-- The decimal enclosure produced by the exact one-cut certificate is more
than enough to discharge the minimizer-domain side condition. -/
theorem positiveBufferRecoveryCertificate_of_qStar_decimal_bounds
    (hlower : (qStarLowerRat : ℝ) < qStar)
    (hupper : qStar < (qStarUpperRat : ℝ)) :
    PositiveBufferRecoveryCertificate := by
  apply positiveBufferRecoveryCertificate_of_qStar_mem_Ioo
  exact ⟨qStar_candidate_interval_in_domain.1.trans hlower,
    hupper.trans qStar_candidate_interval_in_domain.2⟩

/-- Recovery-facing projection of the existing exact one-cut certificate
reduction.  This lets the final one-cut assembly discharge recovery without
repeating any potential theory. -/
theorem positiveBufferRecoveryCertificate_of_oneCut_global_certificate
    {c : ℝ}
    (hcbox : (qStarLowerRat : ℝ) < c ∧ c < (qStarUpperRat : ℝ))
    (hneg : ∀ q ∈ Ioo (0 : ℝ) c, LambdaDerivativeFormula q < 0)
    (hpos : ∀ q ∈ Ioo c qSoft, 0 < LambdaDerivativeFormula q)
    (hend : Lambda c < Lambda qSoft)
    (hLbox : (lambdaLowerRat : ℝ) < Lambda c ∧
      Lambda c < (lambdaUpperRat : ℝ)) :
    PositiveBufferRecoveryCertificate := by
  obtain ⟨_, _, hqStarLower, hqStarUpper, _, _⟩ :=
    oneCut_global_certificate_reduction hcbox hneg hpos hend hLbox
  have hlower : (qStarLowerRat : ℝ) < qStar := by
    have heq : (25715536866527 / 10 ^ 15 : ℝ) =
        (qStarLowerRat : ℝ) := by
      norm_num [qStarLowerRat]
    rwa [← heq]
  have hupper : qStar < (qStarUpperRat : ℝ) := by
    have heq : (25715536866528 / 10 ^ 15 : ℝ) =
        (qStarUpperRat : ℝ) := by
      norm_num [qStarUpperRat]
    rwa [← heq]
  exact positiveBufferRecoveryCertificate_of_qStar_decimal_bounds
    hlower hupper

end

end Erdos1038
