import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

open Filter MeasureTheory Real Set Topology

namespace Erdos516CommonShift

lemma intervalIntegrable_abs_rpow_neg_half_zero_three :
    IntervalIntegrable (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) volume 0 3 := by
  have hrpow : IntervalIntegrable (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) volume 0 3 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  refine hrpow.congr (fun x hx => ?_)
  rw [abs_of_nonneg]
  rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 3)] at hx
  exact hx.1.le

lemma intervalIntegrable_abs_rpow_neg_half_neg_three_zero :
    IntervalIntegrable (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) volume (-3) 0 := by
  rw [IntervalIntegrable.iff_comp_neg, neg_zero, neg_neg]
  simpa only [abs_neg] using intervalIntegrable_abs_rpow_neg_half_zero_three.symm

lemma intervalIntegrable_abs_rpow_neg_half_neg_three_three :
    IntervalIntegrable (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) volume (-3) 3 :=
  intervalIntegrable_abs_rpow_neg_half_neg_three_zero.trans
    intervalIntegrable_abs_rpow_neg_half_zero_three

lemma integral_abs_rpow_neg_half_neg_three_three :
    (∫ x : ℝ in (-3)..3, |x| ^ (-(1 / 2 : ℝ))) ≤ 8 := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    intervalIntegrable_abs_rpow_neg_half_neg_three_zero
    intervalIntegrable_abs_rpow_neg_half_zero_three]
  have hright : (∫ x : ℝ in 0..3, |x| ^ (-(1 / 2 : ℝ))) =
      ∫ x : ℝ in 0..3, x ^ (-(1 / 2 : ℝ)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    change |x| ^ (-(1 / 2 : ℝ)) = x ^ (-(1 / 2 : ℝ))
    rw [abs_of_nonneg]
    norm_num at hx
    exact hx.1
  have hleft : (∫ x : ℝ in (-3)..0, |x| ^ (-(1 / 2 : ℝ))) =
      ∫ x : ℝ in 0..3, x ^ (-(1 / 2 : ℝ)) := by
    calc
      (∫ x : ℝ in (-3)..0, |x| ^ (-(1 / 2 : ℝ))) =
          ∫ x : ℝ in 0..3, |-x| ^ (-(1 / 2 : ℝ)) := by
        symm
        simpa using (intervalIntegral.integral_comp_neg
          (f := fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) (a := 0) (b := 3))
      _ = ∫ x : ℝ in 0..3, x ^ (-(1 / 2 : ℝ)) := by
        apply intervalIntegral.integral_congr
        intro x hx
        change |-x| ^ (-(1 / 2 : ℝ)) = x ^ (-(1 / 2 : ℝ))
        rw [abs_neg, abs_of_nonneg]
        norm_num at hx
        exact hx.1
  rw [hleft, hright, integral_rpow (by left; norm_num)]
  have hsqrt : (3 : ℝ) ^ (1 / (2 : ℝ)) ≤ 2 := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  norm_num
  nlinarith

lemma integral_abs_sub_rpow_neg_half_le (x : ℝ) (hx : |x| < 5 / 2) :
    (∫ α : ℝ in (-(1 / 2))..(1 / 2), |α - x| ^ (-(1 / 2 : ℝ))) ≤ 8 := by
  let a : ℝ := -(1 / 2) - x
  let b : ℝ := 1 / 2 - x
  have ha : -3 ≤ a := by dsimp [a]; have := (abs_lt.mp hx).2; linarith
  have hb : b ≤ 3 := by dsimp [b]; have := (abs_lt.mp hx).1; linarith
  have hab : a ≤ b := by dsimp [a, b]; norm_num
  have heq : (∫ α : ℝ in (-(1 / 2))..(1 / 2), |α - x| ^ (-(1 / 2 : ℝ))) =
      ∫ y : ℝ in a..b, |y| ^ (-(1 / 2 : ℝ)) := by
    simpa [a, b] using (intervalIntegral.integral_comp_sub_right
      (fun y : ℝ => |y| ^ (-(1 / 2 : ℝ))) x
      (a := -(1 / 2 : ℝ)) (b := (1 / 2 : ℝ)))
  rw [heq]
  exact (intervalIntegral.integral_mono_interval ha hab hb
    (ae_of_all _ fun y => Real.rpow_nonneg (abs_nonneg y) _)
    intervalIntegrable_abs_rpow_neg_half_neg_three_three).trans
      integral_abs_rpow_neg_half_neg_three_three

lemma intervalIntegrable_abs_sub_rpow_neg_half (x : ℝ) (hx : |x| < 5 / 2) :
    IntervalIntegrable (fun α : ℝ => |α - x| ^ (-(1 / 2 : ℝ))) volume
      (-(1 / 2)) (1 / 2) := by
  exact (intervalIntegrable_abs_rpow_neg_half_neg_three_three.comp_sub_right x).mono_set'
    (by
      intro y hy
      rw [Set.uIoc_of_le (by norm_num : (-(1 / 2 : ℝ)) ≤ 1 / 2)] at hy
      rw [Set.uIoc_of_le (by linarith : (-3 : ℝ) + x ≤ 3 + x)]
      have h := abs_lt.mp hx
      constructor <;> linarith [hy.1, hy.2])

lemma exp_neg_log_div_four_half {q : ℝ} (hq : 0 < q) :
    Real.exp (-Real.log (q / 4) / 2) = 2 * q ^ (-(1 / 2 : ℝ)) := by
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  calc
    Real.exp (-Real.log (q / 4) / 2) =
        Real.exp (Real.log 2 + (-(1 / 2 : ℝ)) * Real.log q) := by
      congr 1
      rw [Real.log_div hq.ne' (by norm_num), hlog4]
      ring
    _ = Real.exp (Real.log 2) * Real.exp ((-(1 / 2 : ℝ)) * Real.log q) :=
      Real.exp_add _ _
    _ = 2 * q ^ (-(1 / 2 : ℝ)) := by
      rw [Real.exp_log (by norm_num), Real.rpow_def_of_pos hq]
      ring_nf

lemma weighted_exp_log_integral_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x m : ι → ℝ)
    (hx : ∀ i ∈ s, |x i| < 5 / 2) (hm : ∀ i ∈ s, 0 ≤ m i)
    (hW : 0 < ∑ i ∈ s, m i) :
    let G : ℝ → ℝ := fun α =>
      Real.exp (-(∑ i ∈ s, m i * Real.log (|α - x i| / 4)) /
        (2 * ∑ i ∈ s, m i))
    IntervalIntegrable G volume (-(1 / 2)) (1 / 2) ∧
      (∫ α in (-(1 / 2))..(1 / 2), G α) ≤ 16 := by
  classical
  let W : ℝ := ∑ i ∈ s, m i
  let p : ι → ℝ := fun i => m i / W
  let G : ℝ → ℝ := fun α =>
    Real.exp (-(∑ i ∈ s, m i * Real.log (|α - x i| / 4)) / (2 * W))
  let H : ℝ → ℝ := fun α =>
    ∑ i ∈ s, p i * (2 * |α - x i| ^ (-(1 / 2 : ℝ)))
  have hW' : 0 < W := by simpa [W] using hW
  have hpnonneg : ∀ i ∈ s, 0 ≤ p i := by
    intro i hi
    exact div_nonneg (hm i hi) hW'.le
  have hpsum : ∑ i ∈ s, p i = 1 := by
    dsimp [p]
    rw [← Finset.sum_div, show (∑ i ∈ s, m i) = W by rfl, div_self hW'.ne']
  have hHInt : IntervalIntegrable H volume (-(1 / 2)) (1 / 2) := by
    dsimp [H]
    have h := IntervalIntegrable.sum s (fun i hi =>
      ((intervalIntegrable_abs_sub_rpow_neg_half (x i) (hx i hi)).const_mul 2).const_mul
        (p i))
    refine h.congr (fun α hα => ?_)
    simp only [Finset.sum_apply]
  let roots : Finset ℝ := s.image x
  have hrootNull : volume (roots : Set ℝ) = 0 := roots.finite_toSet.measure_zero volume
  have hJensen : ∀ᵐ α : ℝ ∂volume, G α ≤ H α := by
    have hae : ∀ᵐ α : ℝ ∂volume, α ∉ (roots : Set ℝ) := by
      apply (ae_iff).2
      change volume {α : ℝ | ¬ α ∉ (roots : Set ℝ)} = 0
      rw [show {α : ℝ | ¬ α ∉ (roots : Set ℝ)} = (roots : Set ℝ) by ext; simp]
      exact hrootNull
    filter_upwards [hae] with α hα
    have hne : ∀ i ∈ s, α ≠ x i := by
      intro i hi hEq
      apply hα
      rw [Finset.mem_coe, Finset.mem_image]
      exact ⟨i, hi, hEq.symm⟩
    have hj := convexOn_exp.map_sum_le
      (t := s) (w := p)
      (p := fun i => -Real.log (|α - x i| / 4) / 2)
      hpnonneg hpsum (fun i hi => Set.mem_univ _)
    have hsumexp : (∑ i ∈ s, p i *
        Real.exp (-Real.log (|α - x i| / 4) / 2)) = H α := by
      dsimp [H]
      apply Finset.sum_congr rfl
      intro i hi
      rw [exp_neg_log_div_four_half (abs_pos.mpr (sub_ne_zero.mpr (hne i hi)))]
    simp only [smul_eq_mul] at hj
    rw [hsumexp] at hj
    dsimp [G]
    have harg : (∑ i ∈ s, p i * (-Real.log (|α - x i| / 4) / 2)) =
        -(∑ i ∈ s, m i * Real.log (|α - x i| / 4)) / (2 * W) := by
      calc
        (∑ i ∈ s, p i * (-Real.log (|α - x i| / 4) / 2)) =
            ∑ i ∈ s, (-(m i * Real.log (|α - x i| / 4))) / (2 * W) := by
              apply Finset.sum_congr rfl
              intro i hi
              dsimp [p]
              field_simp
        _ = -(∑ i ∈ s, m i * Real.log (|α - x i| / 4)) / (2 * W) := by
          rw [← Finset.sum_div, Finset.sum_neg_distrib]
    rw [← harg]
    exact hj
  have hGMeas : AEStronglyMeasurable G
      (volume.restrict (Set.uIoc (-(1 / 2 : ℝ)) (1 / 2))) := by
    apply Measurable.aestronglyMeasurable
    dsimp [G]
    fun_prop
  have hGInt : IntervalIntegrable G volume (-(1 / 2)) (1 / 2) := by
    apply hHInt.mono_fun' hGMeas
    filter_upwards [ae_restrict_of_ae hJensen] with α hα
    change |G α| ≤ H α
    rw [abs_of_pos (Real.exp_pos _)]
    exact hα
  have hHint : (∫ α in (-(1 / 2))..(1 / 2), H α) ≤ 16 := by
    dsimp [H]
    rw [intervalIntegral.integral_finset_sum]
    · calc
        (∑ i ∈ s, ∫ α in (-(1 / 2))..(1 / 2),
            p i * (2 * |α - x i| ^ (-(1 / 2 : ℝ)))) =
            ∑ i ∈ s, p i * (2 * (∫ α in (-(1 / 2))..(1 / 2),
              |α - x i| ^ (-(1 / 2 : ℝ)))) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
        _ ≤ ∑ i ∈ s, p i * (2 * 8) := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (integral_abs_sub_rpow_neg_half_le (x i) (hx i hi)) (by norm_num))
            (hpnonneg i hi)
        _ = 16 := by rw [← Finset.sum_mul, hpsum]; norm_num
    · intro i hi
      exact ((intervalIntegrable_abs_sub_rpow_neg_half (x i) (hx i hi)).const_mul 2).const_mul
        (p i)
  refine ⟨hGInt, (intervalIntegral.integral_mono_ae (by norm_num) hGInt hHInt hJensen).trans hHint⟩

lemma measure_bad_weighted_log_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x m : ι → ℝ)
    (hx : ∀ i ∈ s, |x i| < 5 / 2) (hm : ∀ i ∈ s, 0 ≤ m i)
    (hW : 0 < ∑ i ∈ s, m i) (β : ℝ) :
    let μ : Measure ℝ := volume.restrict (Set.Ioc (-(1 / 2 : ℝ)) (1 / 2))
    μ.real {α : ℝ | ∑ i ∈ s, m i * Real.log (|α - x i| / 4) <
        -β * ∑ i ∈ s, m i} ≤ 16 / Real.exp (β / 2) := by
  classical
  let W : ℝ := ∑ i ∈ s, m i
  let G : ℝ → ℝ := fun α =>
    Real.exp (-(∑ i ∈ s, m i * Real.log (|α - x i| / 4)) / (2 * W))
  let μ : Measure ℝ := volume.restrict (Set.Ioc (-(1 / 2 : ℝ)) (1 / 2))
  obtain ⟨hGinterval, hGbound⟩ := weighted_exp_log_integral_le s x m hx hm hW
  have hW' : 0 < W := by simpa [W] using hW
  have hGint : Integrable G μ := by
    dsimp [μ]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1 hGinterval
  have hIntegral : (∫ α, G α ∂μ) ≤ 16 := by
    simpa only [μ, intervalIntegral.integral_of_le (by norm_num : (-(1 / 2 : ℝ)) ≤ 1 / 2)]
      using hGbound
  let bad : Set ℝ := {α : ℝ | ∑ i ∈ s, m i * Real.log (|α - x i| / 4) < -β * W}
  let threshold : ℝ := Real.exp (β / 2)
  have hsubset : bad ⊆ {α : ℝ | threshold ≤ G α} := by
    intro α hα
    dsimp [bad] at hα
    dsimp [threshold, G]
    apply Real.exp_le_exp.mpr
    have hdiv := (div_lt_iff₀ hW').2 hα
    have hquot : β / 2 ≤ (-( (∑ i ∈ s, m i * Real.log (|α - x i| / 4)) / W)) / 2 := by
      linarith
    calc
      β / 2 ≤ (-( (∑ i ∈ s, m i * Real.log (|α - x i| / 4)) / W)) / 2 := hquot
      _ = -(∑ i ∈ s, m i * Real.log (|α - x i| / 4)) / (2 * W) := by
        field_simp
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := G) (ae_of_all _ fun α => (Real.exp_pos _).le) hGint threshold
  have hbadMeasure : threshold * μ.real bad ≤ 16 := by
    calc
      threshold * μ.real bad ≤ threshold * μ.real {α : ℝ | threshold ≤ G α} := by
        exact mul_le_mul_of_nonneg_left
          (measureReal_mono (μ := μ) hsubset) (Real.exp_nonneg _)
      _ ≤ ∫ α, G α ∂μ := hmarkov
      _ ≤ 16 := hIntegral
  have hthreshold : 0 < threshold := Real.exp_pos _
  change μ.real bad ≤ 16 / threshold
  exact (le_div_iff₀ hthreshold).2 (by simpa [mul_comm] using hbadMeasure)

lemma exists_simultaneous_log_shift {κ ι : Type*}
    [DecidableEq κ] [DecidableEq ι] (J : Finset κ) (s : κ → Finset ι)
    (x m : κ → ι → ℝ)
    (hx : ∀ j ∈ J, ∀ i ∈ s j, |x j i| < 5 / 2)
    (hm : ∀ j ∈ J, ∀ i ∈ s j, 0 ≤ m j i)
    (hW : ∀ j ∈ J, 0 < ∑ i ∈ s j, m j i)
    {β : ℝ} (hβ : 16 * (J.card : ℝ) < Real.exp (β / 2)) :
    ∃ α : ℝ, -(1 / 2 : ℝ) < α ∧ α ≤ 1 / 2 ∧
      (∀ j ∈ J, ∀ i ∈ s j, 0 < m j i → α ≠ x j i) ∧
      ∀ j ∈ J, -β * ∑ i ∈ s j, m j i ≤
        ∑ i ∈ s j, m j i * Real.log (|α - x j i| / 4) := by
  classical
  let I : Set ℝ := Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)
  let μ : Measure ℝ := volume.restrict I
  let bad : κ → Set ℝ := fun j =>
    {α : ℝ | ∑ i ∈ s j, m j i * Real.log (|α - x j i| / 4) <
      -β * ∑ i ∈ s j, m j i}
  let badAll : Set ℝ := ⋃ j ∈ J, bad j
  let roots : Finset ℝ := J.biUnion fun j => (s j).image (x j)
  have hbadOne : ∀ j ∈ J, μ.real (bad j) ≤ 16 / Real.exp (β / 2) := by
    intro j hj
    exact measure_bad_weighted_log_le (s j) (x j) (m j) (hx j hj) (hm j hj) (hW j hj) β
  have hbadAll : μ.real badAll ≤ (J.card : ℝ) * (16 / Real.exp (β / 2)) := by
    calc
      μ.real badAll ≤ ∑ j ∈ J, μ.real (bad j) := by
        dsimp [badAll]
        exact measureReal_biUnion_finset_le J bad
      _ ≤ ∑ _j ∈ J, (16 / Real.exp (β / 2)) := by
        apply Finset.sum_le_sum
        intro j hj
        exact hbadOne j hj
      _ = (J.card : ℝ) * (16 / Real.exp (β / 2)) := by simp
  have hcardBound : (J.card : ℝ) * (16 / Real.exp (β / 2)) < 1 := by
    have hexp : 0 < Real.exp (β / 2) := Real.exp_pos _
    calc
      (J.card : ℝ) * (16 / Real.exp (β / 2)) =
          (16 * (J.card : ℝ)) / Real.exp (β / 2) := by ring
      _ < 1 := (div_lt_iff₀ hexp).2 (by simpa using hβ)
  have hroots : μ.real (roots : Set ℝ) = 0 := by
    rw [measureReal_def]
    have hzero : μ (roots : Set ℝ) = 0 := by
      dsimp [μ]
      rw [Measure.restrict_apply roots.measurableSet]
      exact measure_mono_null Set.inter_subset_left (roots.finite_toSet.measure_zero volume)
    rw [hzero]
    simp
  let forbidden : Set ℝ := badAll ∪ (roots : Set ℝ)
  have hforbidden : μ.real forbidden < 1 := by
    calc
      μ.real forbidden ≤ μ.real badAll + μ.real (roots : Set ℝ) := measureReal_union_le _ _
      _ = μ.real badAll := by rw [hroots, add_zero]
      _ ≤ (J.card : ℝ) * (16 / Real.exp (β / 2)) := hbadAll
      _ < 1 := hcardBound
  have hexists : ∃ α : ℝ, α ∈ I ∧ α ∉ forbidden := by
    by_contra h
    push_neg at h
    have hsub : I ⊆ forbidden := fun α hα => h α hα
    have hmeasure := measureReal_mono (μ := μ) hsub
    have hI : μ.real I = 1 := by
      dsimp [μ, I]
      simp
      norm_num
    linarith
  obtain ⟨α, hαI, hαforbidden⟩ := hexists
  refine ⟨α, hαI.1, hαI.2, ?_, ?_⟩
  · intro j hj i hi hmi hEq
    apply hαforbidden
    right
    rw [Finset.mem_coe, Finset.mem_biUnion]
    refine ⟨j, hj, ?_⟩
    rw [Finset.mem_image]
    exact ⟨i, hi, hEq.symm⟩
  · intro j hj
    have hnotbad : α ∉ bad j := by
      intro hbad
      apply hαforbidden
      left
      dsimp [badAll]
      exact Set.mem_iUnion_of_mem j (Set.mem_iUnion_of_mem hj hbad)
    dsimp [bad] at hnotbad
    exact le_of_not_gt hnotbad

end Erdos516CommonShift
