import ErdosProblems.Erdos783.GSFinal
import Mathlib.NumberTheory.Chebyshev

open MeasureTheory Set Finset Filter
open scoped Topology

namespace Erdos783

noncomputable section

def selectedPrimeTheta (P : Finset ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ P, if (p : ℝ) ≤ x then Real.log p else 0

lemma selectedPrimeTheta_nonneg (P : Finset ℕ) (x : ℝ) :
    0 ≤ selectedPrimeTheta P x := by
  unfold selectedPrimeTheta
  positivity

lemma selectedPrimeTheta_le_theta
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (x : ℝ) :
    selectedPrimeTheta P x ≤ Chebyshev.theta x := by
  rw [selectedPrimeTheta, Chebyshev.theta]
  let Q := (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime
  have hsub : P.filter (fun p : ℕ ↦ (p : ℝ) ≤ x) ⊆ Q := by
    intro p hp
    rw [Finset.mem_filter] at hp
    have hp0 : 0 < p := (hP p hp.1).pos
    have hx0 : 0 ≤ x := (Nat.cast_nonneg p).trans hp.2
    have hpfloor : p ≤ ⌊x⌋₊ := Nat.le_floor hp.2
    simp only [Q, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨hp0, hpfloor⟩, hP p hp.1⟩
  calc
    (∑ p ∈ P, if (p : ℝ) ≤ x then Real.log p else 0) =
        ∑ p ∈ P.filter (fun p : ℕ ↦ (p : ℝ) ≤ x), Real.log p := by
          rw [Finset.sum_filter]
    _ ≤ ∑ p ∈ Q, Real.log p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p _hpQ _hpNot
      positivity
    _ = Chebyshev.theta x := rfl

lemma measurable_selectedPrimeTheta_rpow
    {y : ℕ} (hy : y ≠ 0) (P : Finset ℕ) :
    Measurable (fun t : ℝ ↦ selectedPrimeTheta P ((y : ℝ) ^ t)) := by
  unfold selectedPrimeTheta
  apply Finset.measurable_sum
  intro p _hp
  apply Measurable.ite
  · exact measurableSet_le measurable_const
      (Real.continuous_const_rpow (by exact_mod_cast hy)).measurable
  · exact measurable_const
  · exact measurable_const

def primeSieveKernel (y : ℕ) (P : Finset ℕ) (t : ℝ) : ℝ :=
  if t ≤ 1 then 1 else
    1 - selectedPrimeTheta P ((y : ℝ) ^ t) /
      Chebyshev.theta ((y : ℝ) ^ t)

lemma measurable_primeSieveKernel {y : ℕ} (hy : y ≠ 0) (P : Finset ℕ) :
    Measurable (primeSieveKernel y P) := by
  unfold primeSieveKernel
  apply Measurable.ite measurableSet_Iic measurable_const
  have hrpow : Measurable (fun t : ℝ ↦ (y : ℝ) ^ t) :=
    (Real.continuous_const_rpow (by exact_mod_cast hy)).measurable
  exact measurable_const.sub
    ((measurable_selectedPrimeTheta_rpow hy P).div
      (Chebyshev.theta_mono.measurable.comp hrpow))

lemma primeSieveKernel_eq_one_of_le_one
    (y : ℕ) (P : Finset ℕ) {t : ℝ} (ht : t ≤ 1) :
    primeSieveKernel y P t = 1 := by
  simp [primeSieveKernel, ht]

lemma isGSKernel_primeSieveKernel
    {y : ℕ} (hy : 2 ≤ y) {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) :
    IsGSKernel (primeSieveKernel y P) := by
  have hy0 : y ≠ 0 := by omega
  have hmeas : Measurable (primeSieveKernel y P) :=
    measurable_primeSieveKernel hy0 P
  have hb : ∀ t : ℝ, 0 ≤ t → primeSieveKernel y P t ∈ Set.Icc (0 : ℝ) 1 := by
    intro t ht
    by_cases ht1 : t ≤ 1
    · rw [primeSieveKernel_eq_one_of_le_one y P ht1]
      exact ⟨zero_le_one, le_rfl⟩
    · have ht1' : 1 < t := lt_of_not_ge ht1
      have hyrpow : (2 : ℝ) ≤ (y : ℝ) ^ t := by
        have hyR : (2 : ℝ) ≤ y := by exact_mod_cast hy
        have hyy : (y : ℝ) ≤ (y : ℝ) ^ t := by
          simpa using Real.rpow_le_rpow_of_exponent_le
            (by exact_mod_cast (show 1 ≤ y by omega)) ht1'.le
        exact hyR.trans hyy
      have htheta : 0 < Chebyshev.theta ((y : ℝ) ^ t) :=
        Chebyshev.theta_pos hyrpow
      have hsel0 := selectedPrimeTheta_nonneg P ((y : ℝ) ^ t)
      have hselle := selectedPrimeTheta_le_theta hP ((y : ℝ) ^ t)
      rw [primeSieveKernel, if_neg (not_le.mpr ht1')]
      constructor
      · exact sub_nonneg.mpr (div_le_one htheta |>.mpr hselle)
      · have hdiv0 : 0 ≤ selectedPrimeTheta P ((y : ℝ) ^ t) /
            Chebyshev.theta ((y : ℝ) ^ t) := div_nonneg hsel0 htheta.le
        linarith
  refine ⟨?_, fun t ht ↦ (hb t ht).1, fun t ht ↦ (hb t ht).2, ?_⟩
  · intro a b
    rw [intervalIntegrable_iff]
    apply Measure.integrableOn_of_bounded
      ((measure_mono uIoc_subset_uIcc).trans_lt measure_Icc_lt_top).ne
      hmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    rw [Real.norm_eq_abs]
    by_cases ht0 : 0 ≤ t
    · rw [abs_of_nonneg (hb t ht0).1]
      exact (hb t ht0).2
    · by_cases ht1 : t ≤ 1
      · rw [primeSieveKernel_eq_one_of_le_one y P ht1]
        norm_num
      · linarith
  · intro t ht0 ht1
    exact primeSieveKernel_eq_one_of_le_one y P ht1

/-! A finite logarithmic grid kernel.  These kernels are the bridge used to
spread the reciprocal mass in each prime cell into admissible Lebesgue
density without changing its total mass. -/

def gsGridPoint (h : ℝ) (i : ℕ) : ℝ := 1 + i * h

def gsGridDefect (h : ℝ) (K : ℕ) (c : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range K,
    if t ∈ Set.Ioc (gsGridPoint h i) (gsGridPoint h (i + 1)) then c i else 0

def gsGridKernel (h : ℝ) (K : ℕ) (c : ℕ → ℝ) (t : ℝ) : ℝ :=
  1 - gsGridDefect h K c t

lemma gsGridPoint_succ (h : ℝ) (i : ℕ) :
    gsGridPoint h (i + 1) = gsGridPoint h i + h := by
  simp [gsGridPoint]
  ring

lemma gsGridPoint_mono {h : ℝ} (hh : 0 ≤ h) :
    Monotone (gsGridPoint h) := by
  intro i j hij
  unfold gsGridPoint
  have hijR : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  simpa [add_comm] using
    (add_le_add_right (mul_le_mul_of_nonneg_right hijR hh) 1)

lemma gsGridCell_unique {h : ℝ} (hh : 0 < h) {i j : ℕ} {t : ℝ}
    (hi : t ∈ Set.Ioc (gsGridPoint h i) (gsGridPoint h (i + 1)))
    (hj : t ∈ Set.Ioc (gsGridPoint h j) (gsGridPoint h (j + 1))) :
    i = j := by
  by_contra hij
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · have hsucc : i + 1 ≤ j := by omega
    have hp := gsGridPoint_mono hh.le hsucc
    linarith [hi.2, hj.1]
  · have hsucc : j + 1 ≤ i := by omega
    have hp := gsGridPoint_mono hh.le hsucc
    linarith [hj.2, hi.1]

lemma measurable_gsGridDefect (h : ℝ) (K : ℕ) (c : ℕ → ℝ) :
    Measurable (gsGridDefect h K c) := by
  unfold gsGridDefect
  apply Finset.measurable_sum
  intro i _hi
  exact Measurable.ite measurableSet_Ioc measurable_const measurable_const

lemma gsGridDefect_nonneg {h : ℝ} {K : ℕ} {c : ℕ → ℝ}
    (hc0 : ∀ i < K, 0 ≤ c i) (t : ℝ) :
    0 ≤ gsGridDefect h K c t := by
  unfold gsGridDefect
  apply Finset.sum_nonneg
  intro i hi
  split_ifs
  · exact hc0 i (Finset.mem_range.mp hi)
  · exact le_rfl

lemma gsGridDefect_le_one {h : ℝ} (hh : 0 < h) {K : ℕ} {c : ℕ → ℝ}
    (hc1 : ∀ i < K, c i ≤ 1) (t : ℝ) :
    gsGridDefect h K c t ≤ 1 := by
  unfold gsGridDefect
  by_cases hex : ∃ i ∈ Finset.range K,
      t ∈ Set.Ioc (gsGridPoint h i) (gsGridPoint h (i + 1))
  · obtain ⟨i, hiK, hit⟩ := hex
    rw [Finset.sum_eq_single i]
    · simp [hit]
      exact hc1 i (Finset.mem_range.mp hiK)
    · intro j hjK hji
      have hjnot : t ∉ Set.Ioc (gsGridPoint h j) (gsGridPoint h (j + 1)) := by
        intro hjt
        exact hji (gsGridCell_unique hh hjt hit)
      simp [hjnot]
    · exact fun hiNot ↦ (hiNot hiK).elim
  · push_neg at hex
    rw [Finset.sum_eq_zero]
    · norm_num
    · intro i hi
      simp [hex i hi]

lemma gsGridDefect_eq_zero_of_le_one {h : ℝ} (hh : 0 ≤ h) (K : ℕ)
    (c : ℕ → ℝ) {t : ℝ} (ht : t ≤ 1) :
    gsGridDefect h K c t = 0 := by
  unfold gsGridDefect
  apply Finset.sum_eq_zero
  intro i hi
  have hp : 1 ≤ gsGridPoint h i := by
    unfold gsGridPoint
    have : 0 ≤ (i : ℝ) * h := mul_nonneg (by positivity) hh
    linarith
  have hnot : t ∉ Set.Ioc (gsGridPoint h i) (gsGridPoint h (i + 1)) := by
    intro hmem
    linarith [hmem.1]
  simp [hnot]

lemma isGSKernel_gsGridKernel {h : ℝ} (hh : 0 < h) {K : ℕ} {c : ℕ → ℝ}
    (hc0 : ∀ i < K, 0 ≤ c i) (hc1 : ∀ i < K, c i ≤ 1) :
    IsGSKernel (gsGridKernel h K c) := by
  have hmeas : Measurable (gsGridKernel h K c) :=
    measurable_const.sub (measurable_gsGridDefect h K c)
  have hb (t : ℝ) : gsGridDefect h K c t ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨gsGridDefect_nonneg hc0 t, gsGridDefect_le_one hh hc1 t⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b
    rw [intervalIntegrable_iff]
    apply Measure.integrableOn_of_bounded (M := 1)
      ((measure_mono uIoc_subset_uIcc).trans_lt measure_Icc_lt_top).ne
      hmeas.aestronglyMeasurable
    filter_upwards with t
    unfold gsGridKernel
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hb t).2)]
    linarith [(hb t).1]
  · intro t _ht
    exact sub_nonneg.mpr (hb t).2
  · intro t _ht
    unfold gsGridKernel
    linarith [(hb t).1]
  · intro t _ht0 ht1
    rw [gsGridKernel, gsGridDefect_eq_zero_of_le_one hh.le K c ht1, sub_zero]

def packetExponentCell (P : Finset ℕ) (y : ℕ) (a b : ℝ) : Finset ℕ :=
  P ∩ primeExponentCell y a b

def packetExponentCellMass (P : Finset ℕ) (y : ℕ) (a b : ℝ) : ℝ :=
  ∑ p ∈ packetExponentCell P y a b, (p : ℝ)⁻¹

lemma packetExponentCellMass_nonneg (P : Finset ℕ) (y : ℕ) (a b : ℝ) :
    0 ≤ packetExponentCellMass P y a b := by
  unfold packetExponentCellMass
  positivity

lemma packetExponentCellMass_le_primeExponentCellMass
    (P : Finset ℕ) (y : ℕ) (a b : ℝ) :
    packetExponentCellMass P y a b ≤ primeExponentCellMass y a b := by
  unfold packetExponentCellMass packetExponentCell primeExponentCellMass
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
    (fun p _hp _hpP ↦ by positivity)

def packetGridCoefficient (lambda : ℝ) (P : Finset ℕ) (y : ℕ)
    (h : ℝ) (i : ℕ) : ℝ :=
  lambda * packetExponentCellMass P y (gsGridPoint h i) (gsGridPoint h (i + 1)) /
    Real.log (gsGridPoint h (i + 1) / gsGridPoint h i)

lemma gsGridPoint_pos {h : ℝ} (hh : 0 ≤ h) (i : ℕ) :
    0 < gsGridPoint h i := by
  unfold gsGridPoint
  positivity

lemma gsGridPoint_lt_succ {h : ℝ} (hh : 0 < h) (i : ℕ) :
    gsGridPoint h i < gsGridPoint h (i + 1) := by
  rw [gsGridPoint_succ]
  linarith

lemma gsGridCellLog_pos {h : ℝ} (hh : 0 < h) (i : ℕ) :
    0 < Real.log (gsGridPoint h (i + 1) / gsGridPoint h i) := by
  rw [Real.log_pos_iff (div_nonneg
    (gsGridPoint_pos hh.le (i + 1)).le (gsGridPoint_pos hh.le i).le)]
  apply (lt_div_iff₀ (gsGridPoint_pos hh.le i)).mpr
  simpa only [one_mul] using gsGridPoint_lt_succ hh i

lemma packetGridCoefficient_nonneg
    {lambda h : ℝ} (hlambda : 0 ≤ lambda) (hh : 0 < h)
    (P : Finset ℕ) (y i : ℕ) :
    0 ≤ packetGridCoefficient lambda P y h i := by
  unfold packetGridCoefficient
  exact div_nonneg (mul_nonneg hlambda (packetExponentCellMass_nonneg _ _ _ _))
    (gsGridCellLog_pos hh i).le

lemma packetGridCoefficient_le_one
    {lambda h error : ℝ} (hlambda : 0 ≤ lambda) (hh : 0 < h)
    {P : Finset ℕ} {y i : ℕ}
    (hmass : primeExponentCellMass y (gsGridPoint h i)
        (gsGridPoint h (i + 1)) ≤
      Real.log (gsGridPoint h (i + 1) / gsGridPoint h i) + error)
    (hscale : lambda *
        (Real.log (gsGridPoint h (i + 1) / gsGridPoint h i) + error) ≤
      Real.log (gsGridPoint h (i + 1) / gsGridPoint h i)) :
    packetGridCoefficient lambda P y h i ≤ 1 := by
  have hpacket := packetExponentCellMass_le_primeExponentCellMass P y
    (gsGridPoint h i) (gsGridPoint h (i + 1))
  have hmul : lambda * packetExponentCellMass P y
        (gsGridPoint h i) (gsGridPoint h (i + 1)) ≤
      Real.log (gsGridPoint h (i + 1) / gsGridPoint h i) := by
    calc
      _ ≤ lambda * primeExponentCellMass y (gsGridPoint h i)
          (gsGridPoint h (i + 1)) :=
        mul_le_mul_of_nonneg_left hpacket hlambda
      _ ≤ lambda *
          (Real.log (gsGridPoint h (i + 1) / gsGridPoint h i) + error) :=
        mul_le_mul_of_nonneg_left hmass hlambda
      _ ≤ _ := hscale
  unfold packetGridCoefficient
  exact (div_le_one (gsGridCellLog_pos hh i)).mpr hmul

lemma gsGridDefect_eq_coeff_of_mem {h : ℝ} (hh : 0 < h) {K : ℕ}
    (c : ℕ → ℝ) {i : ℕ} (hiK : i < K) {t : ℝ}
    (ht : t ∈ Set.Ioc (gsGridPoint h i) (gsGridPoint h (i + 1))) :
    gsGridDefect h K c t = c i := by
  unfold gsGridDefect
  rw [Finset.sum_eq_single i]
  · simp [ht]
  · intro j hjK hji
    have hjnot : t ∉ Set.Ioc (gsGridPoint h j) (gsGridPoint h (j + 1)) := by
      intro hjt
      exact hji (gsGridCell_unique hh hjt ht)
    simp [hjnot]
  · simp [hiK]

lemma gsGridDefect_cell_integral {h : ℝ} (hh : 0 < h) {K : ℕ}
    (c : ℕ → ℝ) {i : ℕ} (hiK : i < K) :
    (∫ t : ℝ in gsGridPoint h i..gsGridPoint h (i + 1),
        gsGridDefect h K c t / t) =
      c i * Real.log (gsGridPoint h (i + 1) / gsGridPoint h i) := by
  have hab : gsGridPoint h i ≤ gsGridPoint h (i + 1) :=
    (gsGridPoint_lt_succ hh i).le
  calc
    (∫ t : ℝ in gsGridPoint h i..gsGridPoint h (i + 1),
        gsGridDefect h K c t / t) =
        ∫ t : ℝ in gsGridPoint h i..gsGridPoint h (i + 1), c i / t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with t ht
      rw [uIoc_of_le hab] at ht
      rw [gsGridDefect_eq_coeff_of_mem hh c hiK ht]
    _ = c i * ∫ t : ℝ in gsGridPoint h i..gsGridPoint h (i + 1), t⁻¹ := by
      rw [show (fun t : ℝ ↦ c i / t) = fun t ↦ c i * t⁻¹ by
        funext t; rw [div_eq_mul_inv], intervalIntegral.integral_const_mul]
    _ = c i * Real.log (gsGridPoint h (i + 1) / gsGridPoint h i) := by
      rw [integral_inv_of_pos (gsGridPoint_pos hh.le i)
        (gsGridPoint_pos hh.le (i + 1))]

lemma gsLogScale_gsGridKernel {h : ℝ} (hh : 0 < h) {K : ℕ} {c : ℕ → ℝ}
    (hc0 : ∀ i < K, 0 ≤ c i) (hc1 : ∀ i < K, c i ≤ 1) :
    gsLogScale (gsGridKernel h K c) (gsGridPoint h K) =
      ∑ i ∈ Finset.range K,
        c i * Real.log (gsGridPoint h (i + 1) / gsGridPoint h i) := by
  let chi := gsGridKernel h K c
  have hchi : IsGSKernel chi := isGSKernel_gsGridKernel hh hc0 hc1
  have hpoint0 : gsGridPoint h 0 = 1 := by simp [gsGridPoint]
  have hsplit :
      (∑ i ∈ Finset.range K,
        ∫ t : ℝ in gsGridPoint h i..gsGridPoint h (i + 1),
          gsDefectWeight chi t) =
        ∫ t : ℝ in gsGridPoint h 0..gsGridPoint h K,
          gsDefectWeight chi t := by
    apply intervalIntegral.sum_integral_adjacent_intervals
    intro i hi
    exact intervalIntegrable_gsDefectKernel hchi
      (gsGridPoint_pos hh.le i) (gsGridPoint_mono hh.le (Nat.le_succ i))
  rw [hpoint0] at hsplit
  change (∫ t : ℝ in 1..gsGridPoint h K, gsDefectWeight chi t) = _
  rw [← hsplit]
  apply Finset.sum_congr rfl
  intro i hi
  have hiK := Finset.mem_range.mp hi
  change (∫ t : ℝ in gsGridPoint h i..gsGridPoint h (i + 1),
      (1 - gsGridKernel h K c t) / t) = _
  rw [show (fun t : ℝ ↦ (1 - gsGridKernel h K c t) / t) =
      fun t ↦ gsGridDefect h K c t / t by
    funext t; simp [gsGridKernel]]
  exact gsGridDefect_cell_integral hh c hiK

lemma gsLogScale_packetGridKernel
    {lambda h : ℝ} (hh : 0 < h) {K y : ℕ} {P : Finset ℕ}
    (hc0 : ∀ i < K, 0 ≤ packetGridCoefficient lambda P y h i)
    (hc1 : ∀ i < K, packetGridCoefficient lambda P y h i ≤ 1) :
    gsLogScale
        (gsGridKernel h K (packetGridCoefficient lambda P y h))
        (gsGridPoint h K) =
      lambda * ∑ i ∈ Finset.range K,
        packetExponentCellMass P y (gsGridPoint h i) (gsGridPoint h (i + 1)) := by
  rw [gsLogScale_gsGridKernel hh hc0 hc1]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  unfold packetGridCoefficient
  have hlogne := (gsGridCellLog_pos hh i).ne'
  field_simp

end

end Erdos783
