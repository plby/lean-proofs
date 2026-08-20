import ErdosProblems.Erdos783.PrimeCombinatorics

open MeasureTheory Set Finset Filter
open scoped BigOperators Topology

namespace Erdos783

noncomputable section

def gsGridCellDefectWeight (h : ℝ) (c : ℕ → ℝ) (i : ℕ) (t : ℝ) : ℝ :=
  if t ∈ Set.Ioc (gsGridPoint h i) (gsGridPoint h (i + 1)) then c i / t else 0

def gsGridCellMass (h : ℝ) (c : ℕ → ℝ) (i : ℕ) : ℝ :=
  c i * Real.log (gsGridPoint h (i + 1) / gsGridPoint h i)

lemma gsGridCellDefectWeight_eq_indicator
    {h : ℝ} (hh : 0 < h) {K : ℕ} (c : ℕ → ℝ) {i : ℕ} (hi : i < K) :
    gsGridCellDefectWeight h c i =
      (Set.Ioc (gsGridPoint h i) (gsGridPoint h (i + 1))).indicator
        (gsDefectWeight (gsGridKernel h K c)) := by
  funext t
  by_cases ht : t ∈ Set.Ioc (gsGridPoint h i) (gsGridPoint h (i + 1))
  · rw [Set.indicator_of_mem ht]
    unfold gsGridCellDefectWeight gsDefectWeight gsGridKernel
    rw [if_pos ht, gsGridDefect_eq_coeff_of_mem hh c hi ht]
    ring
  · rw [Set.indicator_of_notMem ht]
    simp [gsGridCellDefectWeight, ht]

lemma gsDefectWeight_gsGridKernel_eq_sum
    {h : ℝ} {K : ℕ} (c : ℕ → ℝ) (t : ℝ) :
    gsDefectWeight (gsGridKernel h K c) t =
      ∑ i ∈ Finset.range K, gsGridCellDefectWeight h c i t := by
  unfold gsDefectWeight gsGridKernel gsGridDefect gsGridCellDefectWeight
  simp only [sub_sub_cancel]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases ht : t ∈ Set.Ioc (gsGridPoint h i) (gsGridPoint h (i + 1)) <;>
    simp [ht]

lemma intervalIntegrable_gsGridCellDefectWeight
    {h : ℝ} (hh : 0 < h) (c : ℕ → ℝ) (i : ℕ) (a b : ℝ) :
    IntervalIntegrable (gsGridCellDefectWeight h c i) volume a b := by
  rw [intervalIntegrable_iff]
  apply Measure.integrableOn_of_bounded (M := |c i|)
    ((measure_mono uIoc_subset_uIcc).trans_lt measure_Icc_lt_top).ne
    ((measurable_const.div measurable_id).ite measurableSet_Ioc measurable_const).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  rw [Real.norm_eq_abs]
  simp only [Pi.div_apply, id_eq]
  split_ifs with hcell
  · rw [abs_div, abs_of_pos (gsGridPoint_pos hh.le i |>.trans hcell.1)]
    apply (div_le_iff₀ (gsGridPoint_pos hh.le i |>.trans hcell.1)).2
    have ht1 : 1 ≤ t := by
      have hli : 1 ≤ gsGridPoint h i := by
        unfold gsGridPoint
        have : 0 ≤ (i : ℝ) * h := mul_nonneg (by positivity) hh.le
        linarith
      exact hli.trans hcell.1.le
    nlinarith [abs_nonneg (c i)]
  · simp

lemma gsGridCellDefectWeight_nonneg
    {h : ℝ} {c : ℕ → ℝ} {i : ℕ} (hci : 0 ≤ c i) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ gsGridCellDefectWeight h c i t := by
  unfold gsGridCellDefectWeight
  split_ifs
  · positivity
  · exact le_rfl

lemma integral_gsGridCellDefectWeight_cell
    {h : ℝ} (hh : 0 < h) {K : ℕ} {c : ℕ → ℝ}
    {i : ℕ} (hi : i < K) :
    (∫ t : ℝ in gsGridPoint h i..gsGridPoint h (i + 1),
        gsGridCellDefectWeight h c i t) = gsGridCellMass h c i := by
  rw [gsGridCellMass]
  rw [show (∫ t : ℝ in gsGridPoint h i..gsGridPoint h (i + 1),
      gsGridCellDefectWeight h c i t) =
      ∫ t : ℝ in gsGridPoint h i..gsGridPoint h (i + 1),
        gsGridDefect h K c t / t by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    rw [uIoc_of_le (gsGridPoint_lt_succ hh i).le] at ht
    rw [gsGridDefect_eq_coeff_of_mem hh c hi ht]
    simp [gsGridCellDefectWeight, ht]]
  exact gsGridDefect_cell_integral hh c hi

lemma integral_gsGridCellDefectWeight_full
    {h : ℝ} (hh : 0 < h) {K : ℕ} {c : ℕ → ℝ}
    (hc0 : ∀ i < K, 0 ≤ c i) (hc1 : ∀ i < K, c i ≤ 1)
    {i : ℕ} (hi : i < K) :
    (∫ t : ℝ in 1..gsGridPoint h K, gsGridCellDefectWeight h c i t) =
      gsGridCellMass h c i := by
  let f := gsGridCellDefectWeight h c i
  have h1i : (1 : ℝ) ≤ gsGridPoint h i := by
    unfold gsGridPoint
    have : 0 ≤ (i : ℝ) * h := mul_nonneg (by positivity) hh.le
    linarith
  have hii : gsGridPoint h i ≤ gsGridPoint h (i + 1) :=
    (gsGridPoint_lt_succ hh i).le
  have hiK : gsGridPoint h (i + 1) ≤ gsGridPoint h K :=
    gsGridPoint_mono hh.le (by omega)
  have hleftInt : IntervalIntegrable f volume 1 (gsGridPoint h i) :=
    intervalIntegrable_gsGridCellDefectWeight hh c i _ _
  have hcellInt : IntervalIntegrable f volume (gsGridPoint h i)
      (gsGridPoint h (i + 1)) :=
    intervalIntegrable_gsGridCellDefectWeight hh c i _ _
  have hrightInt : IntervalIntegrable f volume (gsGridPoint h (i + 1))
      (gsGridPoint h K) :=
    intervalIntegrable_gsGridCellDefectWeight hh c i _ _
  have hleft : (∫ t : ℝ in 1..gsGridPoint h i, f t) = 0 := by
    rw [show (∫ t : ℝ in 1..gsGridPoint h i, f t) =
        ∫ _t : ℝ in 1..gsGridPoint h i, (0 : ℝ) by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with t ht
      rw [uIoc_of_le h1i] at ht
      unfold f gsGridCellDefectWeight
      rw [if_neg]
      intro hcell
      exact (not_lt_of_ge ht.2) hcell.1]
    simp
  have hright : (∫ t : ℝ in gsGridPoint h (i + 1)..gsGridPoint h K, f t) = 0 := by
    rw [show (∫ t : ℝ in gsGridPoint h (i + 1)..gsGridPoint h K, f t) =
        ∫ _t : ℝ in gsGridPoint h (i + 1)..gsGridPoint h K, (0 : ℝ) by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with t ht
      rw [uIoc_of_le hiK] at ht
      unfold f gsGridCellDefectWeight
      rw [if_neg]
      intro hcell
      exact (not_lt_of_ge hcell.2) ht.1]
    simp
  have hadd1 := intervalIntegral.integral_add_adjacent_intervals hleftInt hcellInt
  have hadd2 := intervalIntegral.integral_add_adjacent_intervals
    (hleftInt.trans hcellInt) hrightInt
  rw [hleft, zero_add, integral_gsGridCellDefectWeight_cell hh hi] at hadd1
  rw [← hadd1, hright, add_zero] at hadd2
  exact hadd2.symm

def gsGridLowerMoment (h : ℝ) (K : ℕ) (c : ℕ → ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  atomMoment (Finset.range K) (gsGridCellMass h c) (gsGridPoint h) n u

def gsGridUpperMoment (h : ℝ) (K : ℕ) (c : ℕ → ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  atomMoment (Finset.range K) (gsGridCellMass h c)
    (fun i ↦ gsGridPoint h (i + 1)) n u

lemma gsGridCellMass_nonneg
    {h : ℝ} (hh : 0 < h) {c : ℕ → ℝ} {i : ℕ} (hci : 0 ≤ c i) :
    0 ≤ gsGridCellMass h c i := by
  unfold gsGridCellMass
  exact mul_nonneg hci (gsGridCellLog_pos hh i).le

lemma intervalIntegrable_gsGridCellDefect_mul_moment
    {h : ℝ} (hh : 0 < h) {K : ℕ} {c : ℕ → ℝ}
    (hc0 : ∀ i < K, 0 ≤ c i) (hc1 : ∀ i < K, c i ≤ 1)
    {i n : ℕ} (hi : i < K) {u : ℝ} (hu : 1 ≤ u) :
    IntervalIntegrable
      (fun t ↦ gsGridCellDefectWeight h c i t *
        gsMoment (gsGridKernel h K c) n (u - t)) volume 1 u := by
  let chi := gsGridKernel h K c
  have hchi : IsGSKernel chi := isGSKernel_gsGridKernel hh hc0 hc1
  have htotal := intervalIntegrable_gsDefect_mul_moment hchi n hu
  rw [intervalIntegrable_iff] at htotal ⊢
  have hind := htotal.indicator
    (measurableSet_Ioc : MeasurableSet
      (Set.Ioc (gsGridPoint h i) (gsGridPoint h (i + 1))))
  convert hind using 1
  funext t
  by_cases ht : t ∈ Set.Ioc (gsGridPoint h i) (gsGridPoint h (i + 1))
  · rw [Set.indicator_of_mem ht]
    have hpoint := congrFun (gsGridCellDefectWeight_eq_indicator hh c hi) t
    have hpoint' : gsGridCellDefectWeight h c i t = gsDefectWeight chi t := by
      simpa [chi, ht] using hpoint
    rw [hpoint']
  · rw [Set.indicator_of_notMem ht]
    simp [gsGridCellDefectWeight, ht]

lemma gsMoment_gsGridKernel_succ_eq_sum
    {h : ℝ} (hh : 0 < h) {K : ℕ} {c : ℕ → ℝ}
    (hc0 : ∀ i < K, 0 ≤ c i) (hc1 : ∀ i < K, c i ≤ 1)
    (n : ℕ) {u : ℝ} (hu : 1 ≤ u) :
    gsMoment (gsGridKernel h K c) (n + 1) u =
      ∑ i ∈ Finset.range K,
        ∫ t : ℝ in 1..u, gsGridCellDefectWeight h c i t *
          gsMoment (gsGridKernel h K c) n (u - t) := by
  rw [gsMoment, if_pos hu]
  simp_rw [gsDefectWeight_gsGridKernel_eq_sum c]
  rw [show (fun t : ℝ ↦
      (∑ i ∈ Finset.range K, gsGridCellDefectWeight h c i t) *
        gsMoment (gsGridKernel h K c) n (u - t)) =
      fun t ↦ ∑ i ∈ Finset.range K,
        gsGridCellDefectWeight h c i t *
          gsMoment (gsGridKernel h K c) n (u - t) by
    funext t
    rw [Finset.sum_mul]]
  rw [intervalIntegral.integral_finset_sum]
  intro i hi
  exact intervalIntegrable_gsGridCellDefect_mul_moment hh hc0 hc1
    (Finset.mem_range.mp hi) hu

lemma integral_gsGridCellDefectWeight_nonneg
    {h : ℝ} (hh : 0 < h) {c : ℕ → ℝ} {i : ℕ} (hci : 0 ≤ c i)
    {u : ℝ} (hu : 1 ≤ u) :
    0 ≤ ∫ t : ℝ in 1..u, gsGridCellDefectWeight h c i t := by
  apply intervalIntegral.integral_nonneg hu
  intro t ht
  exact gsGridCellDefectWeight_nonneg hci (zero_le_one.trans ht.1)

lemma integral_gsGridCellDefectWeight_le_mass
    {h : ℝ} (hh : 0 < h) {K : ℕ} {c : ℕ → ℝ}
    (hc0 : ∀ i < K, 0 ≤ c i) (hc1 : ∀ i < K, c i ≤ 1)
    {i : ℕ} (hi : i < K) {u : ℝ} (hu : 1 ≤ u)
    (huK : u ≤ gsGridPoint h K) :
    (∫ t : ℝ in 1..u, gsGridCellDefectWeight h c i t) ≤
      gsGridCellMass h c i := by
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc (1 : ℝ) (gsGridPoint h K))]
      gsGridCellDefectWeight h c i := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact gsGridCellDefectWeight_nonneg (hc0 i hi) (zero_le_one.trans ht.1.le)
  have hfullInt := intervalIntegrable_gsGridCellDefectWeight hh c i
    1 (gsGridPoint h K)
  have hle := intervalIntegral.integral_mono_interval le_rfl hu huK hnonneg hfullInt
  rw [integral_gsGridCellDefectWeight_full hh hc0 hc1 hi] at hle
  exact hle

lemma integral_gsGridCellDefectWeight_eq_zero_of_endpoint_lt
    {h : ℝ} {c : ℕ → ℝ} {i : ℕ} {u : ℝ}
    (hu : 1 ≤ u) (hui : u < gsGridPoint h i) :
    (∫ t : ℝ in 1..u, gsGridCellDefectWeight h c i t) = 0 := by
  rw [show (∫ t : ℝ in 1..u, gsGridCellDefectWeight h c i t) =
      ∫ _t : ℝ in 1..u, (0 : ℝ) by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    rw [uIoc_of_le hu] at ht
    unfold gsGridCellDefectWeight
    rw [if_neg]
    intro hcell
    exact (not_lt_of_ge (ht.2.trans hui.le)) hcell.1]
  simp

lemma gsGridCellMoment_le_lowerTerm
    {h : ℝ} (hh : 0 < h) {K : ℕ} {c : ℕ → ℝ}
    (hc0 : ∀ i < K, 0 ≤ c i) (hc1 : ∀ i < K, c i ≤ 1)
    {n : ℕ}
    (hIH : ∀ v : ℝ, 0 ≤ v → v ≤ gsGridPoint h K →
      gsMoment (gsGridKernel h K c) n v ≤ gsGridLowerMoment h K c n v)
    {i : ℕ} (hi : i < K) {u : ℝ} (hu : 1 ≤ u)
    (huK : u ≤ gsGridPoint h K) :
    (∫ t : ℝ in 1..u, gsGridCellDefectWeight h c i t *
        gsMoment (gsGridKernel h K c) n (u - t)) ≤
      if gsGridPoint h i ≤ u then
        gsGridCellMass h c i *
          gsGridLowerMoment h K c n (u - gsGridPoint h i)
      else 0 := by
  have hw : ∀ j ∈ Finset.range K, 0 ≤ gsGridCellMass h c j := by
    intro j hj
    exact gsGridCellMass_nonneg hh (hc0 j (Finset.mem_range.mp hj))
  have hx : ∀ j ∈ Finset.range K, 0 ≤ gsGridPoint h j := by
    intro j hj
    exact (gsGridPoint_pos hh.le j).le
  by_cases hliu : gsGridPoint h i ≤ u
  · rw [if_pos hliu]
    let M : ℝ := gsGridLowerMoment h K c n (u - gsGridPoint h i)
    have hM0 : 0 ≤ M := by
      dsimp only [M, gsGridLowerMoment]
      exact atomMoment_nonneg hw n _
    have hactual := intervalIntegrable_gsGridCellDefect_mul_moment
      hh hc0 hc1 hi hu (n := n)
    have hmodel : IntervalIntegrable
        (fun t ↦ gsGridCellDefectWeight h c i t * M) volume 1 u :=
      (intervalIntegrable_gsGridCellDefectWeight hh c i 1 u).mul_const M
    have hpoint : ∀ t ∈ Set.Icc (1 : ℝ) u,
        gsGridCellDefectWeight h c i t *
            gsMoment (gsGridKernel h K c) n (u - t) ≤
          gsGridCellDefectWeight h c i t * M := by
      intro t ht
      by_cases hcell : t ∈ Set.Ioc (gsGridPoint h i) (gsGridPoint h (i + 1))
      · have hcell0 : 0 ≤ gsGridCellDefectWeight h c i t :=
          gsGridCellDefectWeight_nonneg (h := h) (c := c) (i := i)
            (hc0 i hi) (zero_le_one.trans ht.1)
        apply mul_le_mul_of_nonneg_left _ hcell0
        have hv0 : 0 ≤ u - t := sub_nonneg.mpr ht.2
        have hvK : u - t ≤ gsGridPoint h K := by
          exact (sub_le_self _ (zero_le_one.trans ht.1)).trans huK
        have hfirst := hIH (u - t) hv0 hvK
        have hmono : gsGridLowerMoment h K c n (u - t) ≤ M := by
          dsimp only [gsGridLowerMoment, M]
          apply atomMoment_mono_endpoint hw hx n
          linarith [hcell.1]
        exact hfirst.trans hmono
      · simp [gsGridCellDefectWeight, hcell]
    have hint := intervalIntegral.integral_mono_on hu hactual hmodel hpoint
    rw [intervalIntegral.integral_mul_const] at hint
    have hmass := integral_gsGridCellDefectWeight_le_mass hh hc0 hc1 hi hu huK
    calc
      _ ≤ (∫ t : ℝ in 1..u, gsGridCellDefectWeight h c i t) * M := hint
      _ ≤ gsGridCellMass h c i * M :=
        mul_le_mul_of_nonneg_right hmass hM0
      _ = _ := rfl
  · rw [if_neg hliu]
    have hult : u < gsGridPoint h i := lt_of_not_ge hliu
    rw [show (∫ t : ℝ in 1..u, gsGridCellDefectWeight h c i t *
          gsMoment (gsGridKernel h K c) n (u - t)) =
        ∫ _t : ℝ in 1..u, (0 : ℝ) by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with t ht
      rw [uIoc_of_le hu] at ht
      have hnot : t ∉ Set.Ioc (gsGridPoint h i) (gsGridPoint h (i + 1)) := by
        intro hcell
        exact (not_lt_of_ge (ht.2.trans hult.le)) hcell.1
      simp [gsGridCellDefectWeight, hnot]]
    simp

theorem gsMoment_gsGridKernel_le_lowerMoment
    {h : ℝ} (hh : 0 < h) {K : ℕ} {c : ℕ → ℝ}
    (hc0 : ∀ i < K, 0 ≤ c i) (hc1 : ∀ i < K, c i ≤ 1)
    (n : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (huK : u ≤ gsGridPoint h K) :
    gsMoment (gsGridKernel h K c) n u ≤ gsGridLowerMoment h K c n u := by
  have hw : ∀ j ∈ Finset.range K, 0 ≤ gsGridCellMass h c j := by
    intro j hj
    exact gsGridCellMass_nonneg hh (hc0 j (Finset.mem_range.mp hj))
  induction n generalizing u with
  | zero => simp [gsGridLowerMoment]
  | succ n ih =>
      by_cases hu : 1 ≤ u
      · rw [gsMoment_gsGridKernel_succ_eq_sum hh hc0 hc1 n hu]
        unfold gsGridLowerMoment
        rw [atomMoment]
        apply Finset.sum_le_sum
        intro i hi
        exact gsGridCellMoment_le_lowerTerm hh hc0 hc1
          (fun v hv0 hvK ↦ ih hv0 hvK) (Finset.mem_range.mp hi) hu huK
      · rw [gsMoment, if_neg hu]
        exact atomMoment_nonneg hw (n + 1) u

lemma gsGridUpperTerm_le_cellMoment
    {h : ℝ} (hh : 0 < h) {K : ℕ} {c : ℕ → ℝ}
    (hc0 : ∀ i < K, 0 ≤ c i) (hc1 : ∀ i < K, c i ≤ 1)
    {n : ℕ}
    (hIH : ∀ v : ℝ, 0 ≤ v → v ≤ gsGridPoint h K →
      gsGridUpperMoment h K c n v ≤ gsMoment (gsGridKernel h K c) n v)
    {i : ℕ} (hi : i < K) {u : ℝ} (hu : 1 ≤ u)
    (huK : u ≤ gsGridPoint h K) :
    (if gsGridPoint h (i + 1) ≤ u then
        gsGridCellMass h c i *
          gsGridUpperMoment h K c n (u - gsGridPoint h (i + 1))
      else 0) ≤
      ∫ t : ℝ in 1..u, gsGridCellDefectWeight h c i t *
        gsMoment (gsGridKernel h K c) n (u - t) := by
  let chi := gsGridKernel h K c
  have hchi : IsGSKernel chi := isGSKernel_gsGridKernel hh hc0 hc1
  have hw : ∀ j ∈ Finset.range K, 0 ≤ gsGridCellMass h c j := by
    intro j hj
    exact gsGridCellMass_nonneg hh (hc0 j (Finset.mem_range.mp hj))
  have hx : ∀ j ∈ Finset.range K, 0 ≤ gsGridPoint h (j + 1) := by
    intro j hj
    exact (gsGridPoint_pos hh.le (j + 1)).le
  have hactual := intervalIntegrable_gsGridCellDefect_mul_moment
    hh hc0 hc1 hi hu (n := n)
  have hactualNonneg : 0 ≤ ∫ t : ℝ in 1..u,
      gsGridCellDefectWeight h c i t *
        gsMoment chi n (u - t) := by
    apply intervalIntegral.integral_nonneg hu
    intro t ht
    exact mul_nonneg
      (gsGridCellDefectWeight_nonneg (h := h) (c := c) (i := i)
        (hc0 i hi) (zero_le_one.trans ht.1))
      (gsMoment_nonneg hchi n (sub_nonneg.mpr ht.2))
  by_cases hriu : gsGridPoint h (i + 1) ≤ u
  · rw [if_pos hriu]
    let M : ℝ := gsGridUpperMoment h K c n (u - gsGridPoint h (i + 1))
    have hM0 : 0 ≤ M := by
      dsimp only [M, gsGridUpperMoment]
      exact atomMoment_nonneg hw n _
    have hmodel : IntervalIntegrable
        (fun t ↦ gsGridCellDefectWeight h c i t * M) volume
          (gsGridPoint h i) (gsGridPoint h (i + 1)) :=
      (intervalIntegrable_gsGridCellDefectWeight hh c i _ _).mul_const M
    have hcellActual : IntervalIntegrable
        (fun t ↦ gsGridCellDefectWeight h c i t *
          gsMoment chi n (u - t)) volume
          (gsGridPoint h i) (gsGridPoint h (i + 1)) := by
      apply hactual.mono_set
      rw [uIcc_of_le (gsGridPoint_lt_succ hh i).le, uIcc_of_le hu]
      exact Set.Icc_subset_Icc
        (by
          unfold gsGridPoint
          have : 0 ≤ (i : ℝ) * h := mul_nonneg (by positivity) hh.le
          linarith)
        hriu
    have hpoint : ∀ t ∈ Set.Icc (gsGridPoint h i) (gsGridPoint h (i + 1)),
        gsGridCellDefectWeight h c i t * M ≤
          gsGridCellDefectWeight h c i t * gsMoment chi n (u - t) := by
      intro t ht
      have hcell0 : 0 ≤ gsGridCellDefectWeight h c i t :=
        gsGridCellDefectWeight_nonneg (h := h) (c := c) (i := i)
          (hc0 i hi) (gsGridPoint_pos hh.le i |>.le.trans ht.1)
      apply mul_le_mul_of_nonneg_left _ hcell0
      have hv0 : 0 ≤ u - t := sub_nonneg.mpr (ht.2.trans hriu)
      have hvK : u - t ≤ gsGridPoint h K := by
        exact (sub_le_self _ (gsGridPoint_pos hh.le i |>.le.trans ht.1)).trans huK
      have hmono : M ≤ gsGridUpperMoment h K c n (u - t) := by
        dsimp only [M, gsGridUpperMoment]
        apply atomMoment_mono_endpoint hw hx n
        linarith [ht.2]
      exact hmono.trans (hIH (u - t) hv0 hvK)
    have hcellLe := intervalIntegral.integral_mono_on
      (gsGridPoint_lt_succ hh i).le hmodel hcellActual hpoint
    rw [intervalIntegral.integral_mul_const,
      integral_gsGridCellDefectWeight_cell hh hi] at hcellLe
    have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc (1 : ℝ) u)]
        (fun t ↦ gsGridCellDefectWeight h c i t *
          gsMoment chi n (u - t)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact mul_nonneg
        (gsGridCellDefectWeight_nonneg (h := h) (c := c) (i := i)
          (hc0 i hi) (zero_le_one.trans ht.1.le))
        (gsMoment_nonneg hchi n (sub_nonneg.mpr ht.2))
    have hextend := intervalIntegral.integral_mono_interval
      (show (1 : ℝ) ≤ gsGridPoint h i by
        unfold gsGridPoint
        have : 0 ≤ (i : ℝ) * h := mul_nonneg (by positivity) hh.le
        linarith)
      (gsGridPoint_lt_succ hh i).le hriu hnonneg hactual
    exact hcellLe.trans hextend
  · rw [if_neg hriu]
    exact hactualNonneg

theorem gsGridUpperMoment_le_gsMoment_gsGridKernel
    {h : ℝ} (hh : 0 < h) {K : ℕ} {c : ℕ → ℝ}
    (hc0 : ∀ i < K, 0 ≤ c i) (hc1 : ∀ i < K, c i ≤ 1)
    (n : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (huK : u ≤ gsGridPoint h K) :
    gsGridUpperMoment h K c n u ≤ gsMoment (gsGridKernel h K c) n u := by
  induction n generalizing u with
  | zero => simp [gsGridUpperMoment]
  | succ n ih =>
      by_cases hu : 1 ≤ u
      · unfold gsGridUpperMoment
        rw [atomMoment]
        rw [gsMoment_gsGridKernel_succ_eq_sum hh hc0 hc1 n hu]
        apply Finset.sum_le_sum
        intro i hi
        exact gsGridUpperTerm_le_cellMoment hh hc0 hc1
          (fun v hv0 hvK ↦ ih hv0 hvK) (Finset.mem_range.mp hi) hu huK
      · rw [gsMoment, if_neg hu]
        have hzero : gsGridUpperMoment h K c (n + 1) u = 0 := by
          unfold gsGridUpperMoment
          rw [atomMoment]
          apply Finset.sum_eq_zero
          intro i hi
          rw [if_neg]
          have hright : 1 < gsGridPoint h (i + 1) := by
            rw [gsGridPoint_succ]
            have hpos : 0 < h := hh
            have hnonneg : 0 ≤ (i : ℝ) * h := mul_nonneg (by positivity) hh.le
            unfold gsGridPoint
            nlinarith
          exact fun hle ↦ hu (hright.le.trans hle)
        rw [hzero]

def packetGridAtoms (P : Finset ℕ) (y : ℕ) (h : ℝ) (K : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range K ×ˢ P).filter fun q ↦
    q.2 ∈ packetExponentCell P y (gsGridPoint h q.1) (gsGridPoint h (q.1 + 1))

@[simp] lemma mem_packetGridAtoms {P : Finset ℕ} {y : ℕ} {h : ℝ} {K i p : ℕ} :
    (i, p) ∈ packetGridAtoms P y h K ↔
      i < K ∧ p ∈ packetExponentCell P y
        (gsGridPoint h i) (gsGridPoint h (i + 1)) := by
  simp only [packetGridAtoms, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range, packetExponentCell, Finset.mem_inter]
  constructor
  · rintro ⟨⟨hi, hpP⟩, hpP', hpCell⟩
    exact ⟨hi, hpP', hpCell⟩
  · rintro ⟨hi, hpP, hpCell⟩
    exact ⟨⟨hi, hpP⟩, hpP, hpCell⟩

noncomputable def packetGridIndex
    (P : Finset ℕ) (y : ℕ) (h : ℝ) (K p : ℕ) : ℕ :=
  if hp : ∃ i < K, p ∈ packetExponentCell P y
      (gsGridPoint h i) (gsGridPoint h (i + 1)) then
    Nat.find hp
  else 0

lemma packetGridIndex_spec
    {P : Finset ℕ} {y : ℕ} {h : ℝ} {K p : ℕ}
    (hp : ∃ i < K, p ∈ packetExponentCell P y
      (gsGridPoint h i) (gsGridPoint h (i + 1))) :
    packetGridIndex P y h K p < K ∧
      p ∈ packetExponentCell P y
        (gsGridPoint h (packetGridIndex P y h K p))
        (gsGridPoint h (packetGridIndex P y h K p + 1)) := by
  unfold packetGridIndex
  rw [dif_pos hp]
  exact Nat.find_spec hp

lemma packetGridIndex_eq_of_mem
    {P : Finset ℕ} {y : ℕ} {h : ℝ} {K p i : ℕ}
    (hunique : ∀ {i j p : ℕ}, i < K → j < K →
      p ∈ packetExponentCell P y (gsGridPoint h i) (gsGridPoint h (i + 1)) →
      p ∈ packetExponentCell P y (gsGridPoint h j) (gsGridPoint h (j + 1)) → i = j)
    (hi : i < K)
    (hp : p ∈ packetExponentCell P y
      (gsGridPoint h i) (gsGridPoint h (i + 1))) :
    packetGridIndex P y h K p = i := by
  have hex : ∃ j < K, p ∈ packetExponentCell P y
      (gsGridPoint h j) (gsGridPoint h (j + 1)) := ⟨i, hi, hp⟩
  have hs := packetGridIndex_spec hex
  exact hunique hs.1 hi hs.2 hp

lemma packetGridProjection_bij
    {P : Finset ℕ} {y : ℕ} {h : ℝ} {K : ℕ}
    (hcover : ∀ p ∈ P, ∃ i < K, p ∈ packetExponentCell P y
      (gsGridPoint h i) (gsGridPoint h (i + 1)))
    (hunique : ∀ {i j p : ℕ}, i < K → j < K →
      p ∈ packetExponentCell P y (gsGridPoint h i) (gsGridPoint h (i + 1)) →
      p ∈ packetExponentCell P y (gsGridPoint h j) (gsGridPoint h (j + 1)) → i = j) :
    (∀ q ∈ packetGridAtoms P y h K, q.2 ∈ P) ∧
    (∀ q₁ ∈ packetGridAtoms P y h K, ∀ q₂ ∈ packetGridAtoms P y h K,
      q₁.2 = q₂.2 → q₁ = q₂) ∧
    (∀ p ∈ P, ∃ q ∈ packetGridAtoms P y h K, q.2 = p) := by
  constructor
  · rintro ⟨i, p⟩ hq
    have hm := mem_packetGridAtoms.mp hq
    exact (Finset.mem_inter.mp hm.2).1
  constructor
  · rintro ⟨i, p⟩ hq₁ ⟨j, q⟩ hq₂ hpq
    simp only [Prod.snd] at hpq
    subst q
    have hm₁ := mem_packetGridAtoms.mp hq₁
    have hm₂ := mem_packetGridAtoms.mp hq₂
    have hij := hunique hm₁.1 hm₂.1 hm₁.2 hm₂.2
    subst j
    rfl
  · intro p hp
    obtain ⟨i, hi, hpi⟩ := hcover p hp
    exact ⟨(i, p), mem_packetGridAtoms.mpr ⟨hi, hpi⟩, rfl⟩

lemma packetExponentCell_grid_unique
    {P : Finset ℕ} {y : ℕ} (hy : 1 ≤ y) {h : ℝ} (hh : 0 < h)
    {i j p : ℕ}
    (hpi : p ∈ packetExponentCell P y
      (gsGridPoint h i) (gsGridPoint h (i + 1)))
    (hpj : p ∈ packetExponentCell P y
      (gsGridPoint h j) (gsGridPoint h (j + 1))) :
    i = j := by
  have hiCell := (Finset.mem_filter.mp (Finset.mem_inter.mp hpi).2).1
  have hjCell := (Finset.mem_filter.mp (Finset.mem_inter.mp hpj).2).1
  by_contra hij
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · have hstep : i + 1 ≤ j := by omega
    have hfloor := floor_rpow_mono hy (gsGridPoint_mono hh.le hstep)
    have hiBounds := Finset.mem_Ioc.mp hiCell
    have hjBounds := Finset.mem_Ioc.mp hjCell
    omega
  · have hstep : j + 1 ≤ i := by omega
    have hfloor := floor_rpow_mono hy (gsGridPoint_mono hh.le hstep)
    have hiBounds := Finset.mem_Ioc.mp hiCell
    have hjBounds := Finset.mem_Ioc.mp hjCell
    omega

lemma exists_mem_primeExponentCell_grid
    {y : ℕ} (hy : 1 ≤ y) {h : ℝ} (hh : 0 ≤ h)
    {K p : ℕ}
    (hlow : ⌊(y : ℝ) ^ gsGridPoint h 0⌋₊ < p)
    (hhigh : p ≤ ⌊(y : ℝ) ^ gsGridPoint h K⌋₊)
    (hp : p.Prime) :
    ∃ i < K, p ∈ primeExponentCell y
      (gsGridPoint h i) (gsGridPoint h (i + 1)) := by
  induction K with
  | zero =>
      exfalso
      omega
  | succ K ih =>
      by_cases hmid : p ≤ ⌊(y : ℝ) ^ gsGridPoint h K⌋₊
      · obtain ⟨i, hi, hpi⟩ := ih hmid
        exact ⟨i, hi.trans (Nat.lt_succ_self K), hpi⟩
      · refine ⟨K, Nat.lt_succ_self K, ?_⟩
        unfold primeExponentCell
        rw [Finset.mem_filter, Finset.mem_Ioc]
        exact ⟨⟨Nat.lt_of_not_ge hmid, hhigh⟩, hp⟩

lemma packetGrid_cover_of_bounds
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {y : ℕ} (hy : 1 ≤ y) {h : ℝ} (hh : 0 ≤ h) {K : ℕ}
    (hlow : ∀ p ∈ P, ⌊(y : ℝ) ^ gsGridPoint h 0⌋₊ < p)
    (hhigh : ∀ p ∈ P, p ≤ ⌊(y : ℝ) ^ gsGridPoint h K⌋₊) :
    ∀ p ∈ P, ∃ i < K, p ∈ packetExponentCell P y
      (gsGridPoint h i) (gsGridPoint h (i + 1)) := by
  intro p hp
  obtain ⟨i, hi, hcell⟩ :=
    exists_mem_primeExponentCell_grid hy hh (hlow p hp) (hhigh p hp) (hP p hp)
  exact ⟨i, hi, Finset.mem_inter.mpr ⟨hp, hcell⟩⟩

def primeLogLocation (y p : ℕ) : ℝ :=
  Real.log p / Real.log y

lemma primeLogLocation_mem_packetExponentCell
    {P : Finset ℕ} {y : ℕ} (hy : 2 ≤ y) {h : ℝ} {i p : ℕ}
    (hp : p ∈ packetExponentCell P y
      (gsGridPoint h i) (gsGridPoint h (i + 1))) :
    gsGridPoint h i < primeLogLocation y p ∧
      primeLogLocation y p ≤ gsGridPoint h (i + 1) := by
  have hcellData := Finset.mem_filter.mp (Finset.mem_inter.mp hp).2
  have hb := Finset.mem_Ioc.mp hcellData.1
  have hpPrime := hcellData.2
  have hyR : 0 < (y : ℝ) := by positivity
  have hylog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hpR : (p : ℝ) ∈ Set.Ioi 0 := by
    change 0 < (p : ℝ)
    exact_mod_cast hpPrime.pos
  constructor
  · have hpowlt : (y : ℝ) ^ gsGridPoint h i < (p : ℝ) :=
      Nat.lt_of_floor_lt hb.1
    have hpowpos : (y : ℝ) ^ gsGridPoint h i ∈ Set.Ioi 0 := by
      change 0 < (y : ℝ) ^ gsGridPoint h i
      exact Real.rpow_pos_of_pos hyR _
    have hloglt :=
      (Real.strictMonoOn_log.lt_iff_lt hpowpos hpR).2 hpowlt
    rw [Real.log_rpow hyR] at hloglt
    unfold primeLogLocation
    exact (lt_div_iff₀ hylog).2 hloglt
  · have hfloorle :
        ((⌊(y : ℝ) ^ gsGridPoint h (i + 1)⌋₊ : ℕ) : ℝ) ≤
          (y : ℝ) ^ gsGridPoint h (i + 1) :=
      Nat.floor_le (Real.rpow_nonneg (by positivity) _)
    have hpRle : (p : ℝ) ≤ (y : ℝ) ^ gsGridPoint h (i + 1) := by
      exact (by exact_mod_cast hb.2 : (p : ℝ) ≤
        (⌊(y : ℝ) ^ gsGridPoint h (i + 1)⌋₊ : ℕ)).trans hfloorle
    have hpowpos : (y : ℝ) ^ gsGridPoint h (i + 1) ∈ Set.Ioi 0 := by
      change 0 < (y : ℝ) ^ gsGridPoint h (i + 1)
      exact Real.rpow_pos_of_pos hyR _
    have hlogle :=
      (Real.strictMonoOn_log.le_iff_le hpR hpowpos).2 hpRle
    rw [Real.log_rpow hyR] at hlogle
    unfold primeLogLocation
    exact (div_le_iff₀ hylog).2 hlogle

lemma mem_primeExponentCell_of_primeLogLocation
    {y : ℕ} (hy : 2 ≤ y) {a b : ℝ} {p : ℕ} (hp : p.Prime)
    (ha : a < primeLogLocation y p) (hb : primeLogLocation y p ≤ b) :
    p ∈ primeExponentCell y a b := by
  have hyR : 0 < (y : ℝ) := by positivity
  have hylog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hpR : (p : ℝ) ∈ Set.Ioi 0 := by
    change 0 < (p : ℝ)
    exact_mod_cast hp.pos
  have hpowApos : (y : ℝ) ^ a ∈ Set.Ioi 0 := by
    change 0 < (y : ℝ) ^ a
    exact Real.rpow_pos_of_pos hyR _
  have hpowBpos : (y : ℝ) ^ b ∈ Set.Ioi 0 := by
    change 0 < (y : ℝ) ^ b
    exact Real.rpow_pos_of_pos hyR _
  have hlogA : Real.log ((y : ℝ) ^ a) < Real.log p := by
    rw [Real.log_rpow hyR]
    exact (lt_div_iff₀ hylog).1 ha
  have hlogB : Real.log p ≤ Real.log ((y : ℝ) ^ b) := by
    rw [Real.log_rpow hyR]
    exact (div_le_iff₀ hylog).1 hb
  have hpowA : (y : ℝ) ^ a < (p : ℝ) :=
    (Real.strictMonoOn_log.lt_iff_lt hpowApos hpR).1 hlogA
  have hpowB : (p : ℝ) ≤ (y : ℝ) ^ b :=
    (Real.strictMonoOn_log.le_iff_le hpR hpowBpos).1 hlogB
  unfold primeExponentCell
  rw [Finset.mem_filter, Finset.mem_Ioc]
  refine ⟨⟨?_, Nat.le_floor hpowB⟩, hp⟩
  exact (Nat.floor_lt (Real.rpow_nonneg (by positivity) _)).2 hpowA

lemma atomIntervalMass_primeLogLocation_le
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {y : ℕ} (hy : 2 ≤ y) {h : ℝ} (hh : 0 < h) {K : ℕ}
    (hcover : ∀ p ∈ P, ∃ i < K, p ∈ packetExponentCell P y
      (gsGridPoint h i) (gsGridPoint h (i + 1)))
    {lambda delta error : ℝ} (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (hdelta : 0 ≤ delta) (herror : 0 ≤ error)
    (hclose : ∀ a b : ℝ, 1 ≤ a → a ≤ b →
      |primeExponentCellMass y a b - (Real.log b - Real.log a)| < error)
    (v : ℝ) :
    atomIntervalMass P (fun p : ℕ ↦ lambda * (p : ℝ)⁻¹)
        (primeLogLocation y) v delta ≤ delta + error := by
  let a : ℝ := max 1 v
  let b : ℝ := a + delta
  have ha1 : 1 ≤ a := by simp [a]
  have ha0 : 0 < a := zero_lt_one.trans_le ha1
  have hab : a ≤ b := by dsimp only [b]; linarith
  let Q := P.filter fun p ↦ v < primeLogLocation y p ∧
    primeLogLocation y p ≤ v + delta
  have hQsub : Q ⊆ packetExponentCell P y a b := by
    intro p hpQ
    rw [Finset.mem_filter] at hpQ
    obtain ⟨i, hiK, hpi⟩ := hcover p hpQ.1
    have hcellLoc := primeLogLocation_mem_packetExponentCell hy hpi
    have haloc : a < primeLogLocation y p := by
      dsimp only [a]
      rw [max_lt_iff]
      constructor
      · exact (show (1 : ℝ) ≤ gsGridPoint h i by
          unfold gsGridPoint
          have : 0 ≤ (i : ℝ) * h := mul_nonneg (by positivity) hh.le
          linarith).trans_lt hcellLoc.1
      · exact hpQ.2.1
    have hlocb : primeLogLocation y p ≤ b := by
      dsimp only [b, a]
      by_cases hv : 1 ≤ v
      · rw [max_eq_right hv]
        exact hpQ.2.2
      · rw [max_eq_left (le_of_not_ge hv)]
        linarith [hpQ.2.2]
    exact Finset.mem_inter.mpr
      ⟨hpQ.1, mem_primeExponentCell_of_primeLogLocation hy (hP p hpQ.1) haloc hlocb⟩
  have hpacket :
      (∑ p ∈ Q, lambda * (p : ℝ)⁻¹) ≤
        lambda * packetExponentCellMass P y a b := by
    unfold packetExponentCellMass
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg hQsub
      (fun p hp _ ↦ mul_nonneg hlambda0 (by positivity))
  have hprime := packetExponentCellMass_le_primeExponentCellMass P y a b
  have hclose' := hclose a b ha1 hab
  have hmass : primeExponentCellMass y a b ≤
      Real.log b - Real.log a + error := by
    linarith [le_abs_self (primeExponentCellMass y a b -
      (Real.log b - Real.log a))]
  have hlog : Real.log b - Real.log a ≤ delta := by
    have hb0 : 0 < b := ha0.trans_le hab
    calc
      Real.log b - Real.log a = Real.log (b / a) := by
        rw [Real.log_div hb0.ne' ha0.ne']
      _ ≤ b / a - 1 := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
      _ = delta / a := by
        dsimp only [b]
        field_simp
        ring
      _ ≤ delta := by
        apply (div_le_iff₀ ha0).2
        nlinarith
  unfold atomIntervalMass
  rw [← Finset.sum_filter]
  change (∑ p ∈ Q, lambda * (p : ℝ)⁻¹) ≤ delta + error
  calc
    _ ≤ lambda * packetExponentCellMass P y a b := hpacket
    _ ≤ lambda * primeExponentCellMass y a b :=
      mul_le_mul_of_nonneg_left hprime hlambda0
    _ ≤ primeExponentCellMass y a b := by
      apply mul_le_of_le_one_left
      · unfold primeExponentCellMass
        positivity
      · exact hlambda1
    _ ≤ Real.log b - Real.log a + error := hmass
    _ ≤ delta + error := by linarith

lemma sum_packetGridAtoms
    {M : Type*} [AddCommMonoid M]
    (P : Finset ℕ) (y : ℕ) (h : ℝ) (K : ℕ) (F : ℕ × ℕ → M) :
    ∑ q ∈ packetGridAtoms P y h K, F q =
      ∑ i ∈ Finset.range K,
        ∑ p ∈ packetExponentCell P y (gsGridPoint h i) (gsGridPoint h (i + 1)),
          F (i, p) := by
  unfold packetGridAtoms
  rw [Finset.sum_filter]
  let G : ℕ × ℕ → M := fun q ↦
    if q.2 ∈ packetExponentCell P y
      (gsGridPoint h q.1) (gsGridPoint h (q.1 + 1)) then F q else 0
  change (∑ q ∈ Finset.range K ×ˢ P, G q) = _
  rw [Finset.sum_product (Finset.range K) P G]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [G, Prod.snd, Prod.fst]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext p
    simp [packetExponentCell]
  · intro p hp
    rfl

lemma sum_packetExponentCellMass_eq_reciprocalMass
    {P : Finset ℕ} {y : ℕ} {h : ℝ} {K : ℕ}
    (hcover : ∀ p ∈ P, ∃ i < K, p ∈ packetExponentCell P y
      (gsGridPoint h i) (gsGridPoint h (i + 1)))
    (hunique : ∀ {i j p : ℕ}, i < K → j < K →
      p ∈ packetExponentCell P y (gsGridPoint h i) (gsGridPoint h (i + 1)) →
      p ∈ packetExponentCell P y (gsGridPoint h j) (gsGridPoint h (j + 1)) → i = j) :
    ∑ i ∈ Finset.range K,
        packetExponentCellMass P y (gsGridPoint h i) (gsGridPoint h (i + 1)) =
      reciprocalMass P := by
  have hproj := packetGridProjection_bij hcover hunique
  have htag :
      ∑ q ∈ packetGridAtoms P y h K, (q.2 : ℝ)⁻¹ =
        ∑ p ∈ P, (p : ℝ)⁻¹ := by
    apply Finset.sum_bij (fun q _hq ↦ q.2)
    · exact hproj.1
    · exact hproj.2.1
    · intro p hp
      obtain ⟨q, hq, hqp⟩ := hproj.2.2 p hp
      exact ⟨q, hq, hqp⟩
    · intro q hq
      rfl
  rw [sum_packetGridAtoms] at htag
  simpa [packetExponentCellMass, reciprocalMass] using htag

lemma gsScale_packetGridKernel_eq_exp_reciprocalMass
    {lambda h : ℝ} (hh : 0 < h) {K y : ℕ} {P : Finset ℕ}
    (hcover : ∀ p ∈ P, ∃ i < K, p ∈ packetExponentCell P y
      (gsGridPoint h i) (gsGridPoint h (i + 1)))
    (hunique : ∀ {i j p : ℕ}, i < K → j < K →
      p ∈ packetExponentCell P y (gsGridPoint h i) (gsGridPoint h (i + 1)) →
      p ∈ packetExponentCell P y (gsGridPoint h j) (gsGridPoint h (j + 1)) → i = j)
    (hc0 : ∀ i < K, 0 ≤ packetGridCoefficient lambda P y h i)
    (hc1 : ∀ i < K, packetGridCoefficient lambda P y h i ≤ 1) :
    gsScale
        (gsGridKernel h K (packetGridCoefficient lambda P y h))
        (gsGridPoint h K) =
      Real.exp (lambda * reciprocalMass P) := by
  unfold gsScale
  rw [gsLogScale_packetGridKernel hh hc0 hc1]
  rw [sum_packetExponentCellMass_eq_reciprocalMass hcover hunique]

lemma gsGridCellMass_packetGridCoefficient
    {lambda h : ℝ} (hh : 0 < h) (P : Finset ℕ) (y i : ℕ) :
    gsGridCellMass h (packetGridCoefficient lambda P y h) i =
      lambda * packetExponentCellMass P y
        (gsGridPoint h i) (gsGridPoint h (i + 1)) := by
  unfold gsGridCellMass packetGridCoefficient
  have hlogne := (gsGridCellLog_pos hh i).ne'
  field_simp

def packetGridAtomWeight (lambda : ℝ) (q : ℕ × ℕ) : ℝ :=
  lambda * (q.2 : ℝ)⁻¹

def packetGridAtomLowerLocation (h : ℝ) (q : ℕ × ℕ) : ℝ :=
  gsGridPoint h q.1

def packetGridAtomUpperLocation (h : ℝ) (q : ℕ × ℕ) : ℝ :=
  gsGridPoint h (q.1 + 1)

def packetGridPrimeLowerLocation
    (P : Finset ℕ) (y : ℕ) (h : ℝ) (K p : ℕ) : ℝ :=
  gsGridPoint h (packetGridIndex P y h K p)

def packetGridPrimeUpperLocation
    (P : Finset ℕ) (y : ℕ) (h : ℝ) (K p : ℕ) : ℝ :=
  gsGridPoint h (packetGridIndex P y h K p + 1)

lemma packetGridPrimeLocation_bounds
    {P : Finset ℕ} {y : ℕ} (hy : 2 ≤ y) {h : ℝ} {K p : ℕ}
    (hp : ∃ i < K, p ∈ packetExponentCell P y
      (gsGridPoint h i) (gsGridPoint h (i + 1))) :
    packetGridPrimeLowerLocation P y h K p < primeLogLocation y p ∧
      primeLogLocation y p ≤ packetGridPrimeUpperLocation P y h K p := by
  have hs := packetGridIndex_spec hp
  simpa [packetGridPrimeLowerLocation, packetGridPrimeUpperLocation] using
    primeLogLocation_mem_packetExponentCell hy hs.2

lemma atomMoment_packetGridAtoms_eq_prime_lower
    {lambda h : ℝ} {P : Finset ℕ} {y K : ℕ}
    (hcover : ∀ p ∈ P, ∃ i < K, p ∈ packetExponentCell P y
      (gsGridPoint h i) (gsGridPoint h (i + 1)))
    (hunique : ∀ {i j p : ℕ}, i < K → j < K →
      p ∈ packetExponentCell P y (gsGridPoint h i) (gsGridPoint h (i + 1)) →
      p ∈ packetExponentCell P y (gsGridPoint h j) (gsGridPoint h (j + 1)) → i = j)
    (n : ℕ) (u : ℝ) :
    atomMoment (packetGridAtoms P y h K) (packetGridAtomWeight lambda)
        (packetGridAtomLowerLocation h) n u =
      atomMoment P (fun p : ℕ ↦ lambda * (p : ℝ)⁻¹)
        (packetGridPrimeLowerLocation P y h K) n u := by
  have hproj := packetGridProjection_bij hcover hunique
  apply atomMoment_bij Prod.snd hproj.1 hproj.2.1 hproj.2.2
  · rintro ⟨i, p⟩ hq
    rfl
  · rintro ⟨i, p⟩ hq
    have hm := mem_packetGridAtoms.mp hq
    have hidx := packetGridIndex_eq_of_mem hunique hm.1 hm.2
    simp [packetGridAtomLowerLocation, packetGridPrimeLowerLocation, hidx]

lemma atomMoment_packetGridAtoms_eq_prime_upper
    {lambda h : ℝ} {P : Finset ℕ} {y K : ℕ}
    (hcover : ∀ p ∈ P, ∃ i < K, p ∈ packetExponentCell P y
      (gsGridPoint h i) (gsGridPoint h (i + 1)))
    (hunique : ∀ {i j p : ℕ}, i < K → j < K →
      p ∈ packetExponentCell P y (gsGridPoint h i) (gsGridPoint h (i + 1)) →
      p ∈ packetExponentCell P y (gsGridPoint h j) (gsGridPoint h (j + 1)) → i = j)
    (n : ℕ) (u : ℝ) :
    atomMoment (packetGridAtoms P y h K) (packetGridAtomWeight lambda)
        (packetGridAtomUpperLocation h) n u =
      atomMoment P (fun p : ℕ ↦ lambda * (p : ℝ)⁻¹)
        (packetGridPrimeUpperLocation P y h K) n u := by
  have hproj := packetGridProjection_bij hcover hunique
  apply atomMoment_bij Prod.snd hproj.1 hproj.2.1 hproj.2.2
  · rintro ⟨i, p⟩ hq
    rfl
  · rintro ⟨i, p⟩ hq
    have hm := mem_packetGridAtoms.mp hq
    have hidx := packetGridIndex_eq_of_mem hunique hm.1 hm.2
    simp [packetGridAtomUpperLocation, packetGridPrimeUpperLocation, hidx]

lemma atomMoment_packetGridAtoms_lower
    {lambda h : ℝ} (hh : 0 < h) (P : Finset ℕ) (y K n : ℕ) (u : ℝ) :
    atomMoment (packetGridAtoms P y h K) (packetGridAtomWeight lambda)
        (packetGridAtomLowerLocation h) n u =
      gsGridLowerMoment h K (packetGridCoefficient lambda P y h) n u := by
  induction n generalizing u with
  | zero => simp [gsGridLowerMoment]
  | succ n ih =>
      rw [atomMoment]
      unfold gsGridLowerMoment
      rw [atomMoment]
      rw [sum_packetGridAtoms]
      apply Finset.sum_congr rfl
      intro i hi
      rw [gsGridCellMass_packetGridCoefficient hh]
      simp only [packetGridAtomLowerLocation, packetGridAtomWeight,
        Prod.fst, Prod.snd, ih]
      by_cases hiu : gsGridPoint h i ≤ u
      · rw [if_pos hiu]
        simp_rw [if_pos hiu]
        unfold packetExponentCellMass
        rw [Finset.mul_sum]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p hp
        change _ = lambda * (p : ℝ)⁻¹ *
          gsGridLowerMoment h K (packetGridCoefficient lambda P y h) n
            (u - gsGridPoint h i)
        rfl
      · rw [if_neg hiu]
        simp [hiu]

lemma atomMoment_packetGridAtoms_upper
    {lambda h : ℝ} (hh : 0 < h) (P : Finset ℕ) (y K n : ℕ) (u : ℝ) :
    atomMoment (packetGridAtoms P y h K) (packetGridAtomWeight lambda)
        (packetGridAtomUpperLocation h) n u =
      gsGridUpperMoment h K (packetGridCoefficient lambda P y h) n u := by
  induction n generalizing u with
  | zero => simp [gsGridUpperMoment]
  | succ n ih =>
      rw [atomMoment]
      unfold gsGridUpperMoment
      rw [atomMoment]
      rw [sum_packetGridAtoms]
      apply Finset.sum_congr rfl
      intro i hi
      rw [gsGridCellMass_packetGridCoefficient hh]
      simp only [packetGridAtomUpperLocation, packetGridAtomWeight,
        Prod.fst, Prod.snd, ih]
      by_cases hiu : gsGridPoint h (i + 1) ≤ u
      · rw [if_pos hiu]
        simp_rw [if_pos hiu]
        unfold packetExponentCellMass
        rw [Finset.mul_sum]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p hp
        change _ = lambda * (p : ℝ)⁻¹ *
          gsGridUpperMoment h K (packetGridCoefficient lambda P y h) n
            (u - gsGridPoint h (i + 1))
        rfl
      · rw [if_neg hiu]
        simp [hiu]

theorem abs_gsMoment_packetGrid_sub_primeAtomMoment_le
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {y : ℕ} (hy : 2 ≤ y) {lambda h error M : ℝ}
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) (hh : 0 < h)
    (herror : 0 ≤ error) {K : ℕ}
    (hcover : ∀ p ∈ P, ∃ i < K, p ∈ packetExponentCell P y
      (gsGridPoint h i) (gsGridPoint h (i + 1)))
    (hc0 : ∀ i < K, 0 ≤ packetGridCoefficient lambda P y h i)
    (hc1 : ∀ i < K, packetGridCoefficient lambda P y h i ≤ 1)
    (hclose : ∀ a b : ℝ, 1 ≤ a → a ≤ b →
      |primeExponentCellMass y a b - (Real.log b - Real.log a)| < error)
    (hM1 : 1 ≤ M)
    (hmass : atomMass P (fun p : ℕ ↦ lambda * (p : ℝ)⁻¹) ≤ M)
    (n : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (huK : u ≤ gsGridPoint h K) :
    |gsMoment
        (gsGridKernel h K (packetGridCoefficient lambda P y h)) n u -
      atomMoment P (fun p : ℕ ↦ lambda * (p : ℝ)⁻¹)
        (primeLogLocation y) n u| ≤
      (n : ℝ) * (((n + 1 : ℕ) : ℝ) * h + error) * M ^ (n - 1) := by
  let w : ℕ → ℝ := fun p ↦ lambda * (p : ℝ)⁻¹
  let x : ℕ → ℝ := primeLogLocation y
  let lo : ℕ → ℝ := packetGridPrimeLowerLocation P y h K
  let up : ℕ → ℝ := packetGridPrimeUpperLocation P y h K
  let c : ℕ → ℝ := packetGridCoefficient lambda P y h
  let chi : ℝ → ℝ := gsGridKernel h K c
  have hunique : ∀ {i j p : ℕ}, i < K → j < K →
      p ∈ packetExponentCell P y (gsGridPoint h i) (gsGridPoint h (i + 1)) →
      p ∈ packetExponentCell P y (gsGridPoint h j) (gsGridPoint h (j + 1)) → i = j := by
    intro i j p hi hj hpi hpj
    exact packetExponentCell_grid_unique (show 1 ≤ y by omega) hh hpi hpj
  have hw : ∀ p ∈ P, 0 ≤ w p := by
    intro p hp
    dsimp only [w]
    positivity
  have hbounds : ∀ p ∈ P, lo p < x p ∧ x p ≤ up p := by
    intro p hp
    dsimp only [lo, x, up]
    exact packetGridPrimeLocation_bounds hy (hcover p hp)
  have hlo0 : ∀ p ∈ P, 0 ≤ lo p := by
    intro p hp
    dsimp only [lo, packetGridPrimeLowerLocation]
    exact (gsGridPoint_pos hh.le _).le
  have hx0 : ∀ p ∈ P, 0 ≤ x p := by
    intro p hp
    exact (hlo0 p hp).trans (hbounds p hp).1.le
  have hup0 : ∀ p ∈ P, 0 ≤ up p := by
    intro p hp
    exact (hx0 p hp).trans (hbounds p hp).2
  have huplo : ∀ p ∈ P, up p = lo p + h := by
    intro p hp
    dsimp only [up, lo, packetGridPrimeUpperLocation,
      packetGridPrimeLowerLocation]
    exact gsGridPoint_succ h _
  have hlowerEq :
      gsGridLowerMoment h K c n u = atomMoment P w lo n u := by
    rw [← atomMoment_packetGridAtoms_lower hh P y K n u]
    exact atomMoment_packetGridAtoms_eq_prime_lower hcover hunique n u
  have hupperEq :
      gsGridUpperMoment h K c n u = atomMoment P w up n u := by
    rw [← atomMoment_packetGridAtoms_upper hh P y K n u]
    exact atomMoment_packetGridAtoms_eq_prime_upper hcover hunique n u
  have hchiLower : gsMoment chi n u ≤ atomMoment P w lo n u := by
    rw [← hlowerEq]
    exact gsMoment_gsGridKernel_le_lowerMoment hh hc0 hc1 n hu0 huK
  have hupperChi : atomMoment P w up n u ≤ gsMoment chi n u := by
    rw [← hupperEq]
    exact gsGridUpperMoment_le_gsMoment_gsGridKernel hh hc0 hc1 n hu0 huK
  have htrueLower : atomMoment P w x n u ≤ atomMoment P w lo n u :=
    atomMoment_mono_location hw hlo0 (fun p hp ↦ (hbounds p hp).1.le) n u
  have hupperTrue : atomMoment P w up n u ≤ atomMoment P w x n u :=
    atomMoment_mono_location hw hx0 (fun p hp ↦ (hbounds p hp).2) n u
  have hsandwich :
      |gsMoment chi n u - atomMoment P w x n u| ≤
        atomMoment P w lo n u - atomMoment P w up n u := by
    rw [abs_le]
    constructor <;> linarith
  have hshift : atomMoment P w lo n u ≤
      atomMoment P w up n (u + n * h) := by
    apply atomMoment_location_shift_le hw hlo0 hup0 hh.le
    intro p hp
    rw [huplo p hp]
  have hinterval : ∀ v : ℝ,
      atomIntervalMass P w up v ((n : ℝ) * h) ≤
        ((n + 1 : ℕ) : ℝ) * h + error := by
    intro v
    have hmove := atomIntervalMass_location_shift_le hw
      (fun p hp ↦ (hbounds p hp).2)
      (fun p hp ↦ by rw [huplo p hp]; linarith [hbounds p hp |>.1])
      (shift := h) (delta := (n : ℝ) * h) v
    have hprime := atomIntervalMass_primeLogLocation_le hP hy hh hcover
      hlambda0 hlambda1
      (show 0 ≤ (n : ℝ) * h + h by positivity) herror hclose (v - h)
    dsimp only [w, x, up] at hmove ⊢
    calc
      _ ≤ atomIntervalMass P (fun p : ℕ ↦ lambda * (p : ℝ)⁻¹)
          (primeLogLocation y) (v - h) ((n : ℝ) * h + h) := hmove
      _ ≤ (n : ℝ) * h + h + error := hprime
      _ = ((n + 1 : ℕ) : ℝ) * h + error := by push_cast; ring
  have hincrement := atomMoment_endpoint_increment_le hw
    (show 0 ≤ (n : ℝ) * h by positivity)
    (show 0 ≤ ((n + 1 : ℕ) : ℝ) * h + error by positivity)
    hinterval hmass hM1 n u
  dsimp only [chi, c] at hchiLower hupperChi hsandwich ⊢
  calc
    _ ≤ atomMoment P w lo n u - atomMoment P w up n u := hsandwich
    _ ≤ atomMoment P w up n (u + (n : ℝ) * h) - atomMoment P w up n u := by
      linarith
    _ ≤ (n : ℝ) * (((n + 1 : ℕ) : ℝ) * h + error) * M ^ (n - 1) :=
      hincrement

lemma distinctAtomMoment_scaled_primeLog_eq_cutoff
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {y N j : ℕ} (hy : 2 ≤ y) (hN : 0 < N) (lambda : ℝ) :
    distinctAtomMoment (fun p : ℕ ↦ lambda * (p : ℝ)⁻¹)
        (primeLogLocation y) P j (Real.log N / Real.log y) =
      lambda ^ j * (j.factorial : ℝ) * cutoffElementaryReciprocalMass N P j := by
  have hx : ∀ p ∈ P, 0 ≤ primeLogLocation y p := by
    intro p hp
    unfold primeLogLocation
    exact div_nonneg
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ p from (hP p hp).one_le)))
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ y by omega)))
  rw [distinctAtomMoment_const_mul_weight]
  rw [distinctAtomMoment_eq_factorial_mul_subset hx]
  unfold primeLogLocation
  rw [atomSubsetMoment_primeLogDiv_eq_cutoff hP hy hN]
  ring

lemma primeAtomMoment_sub_scaled_cutoff_le
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {y N j : ℕ} (hy : 2 ≤ y) (hN : 0 < N)
    {lambda M : ℝ} (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (hhigh : ∀ p ∈ P, y < p)
    (hM1 : 1 ≤ M)
    (hmass : atomMass P (fun p : ℕ ↦ lambda * (p : ℝ)⁻¹) ≤ M) :
    atomMoment P (fun p : ℕ ↦ lambda * (p : ℝ)⁻¹)
        (primeLogLocation y) j (Real.log N / Real.log y) -
      lambda ^ j * (j.factorial : ℝ) * cutoffElementaryReciprocalMass N P j ≤
        (j : ℝ) ^ 2 * (y : ℝ)⁻¹ * M ^ j := by
  have hw0 : ∀ p ∈ P, 0 ≤ lambda * (p : ℝ)⁻¹ := by
    intro p hp
    positivity
  have hwdelta : ∀ p ∈ P, lambda * (p : ℝ)⁻¹ ≤ (y : ℝ)⁻¹ := by
    intro p hp
    have hy0 : 0 < (y : ℝ) := by positivity
    have hp0 : 0 < (p : ℝ) := by exact_mod_cast (hP p hp).pos
    have hinv : (p : ℝ)⁻¹ ≤ (y : ℝ)⁻¹ := by
      exact (inv_le_inv₀ hp0 hy0).2 (by exact_mod_cast (hhigh p hp).le)
    exact (mul_le_of_le_one_left (inv_nonneg.mpr hp0.le) hlambda1).trans hinv
  have hcollision := atomMoment_sub_distinct_le (x := primeLogLocation y) hw0
    (show 0 ≤ (y : ℝ)⁻¹ by positivity) hwdelta hM1 hmass j
      (Real.log N / Real.log y)
  rw [distinctAtomMoment_scaled_primeLog_eq_cutoff hP hy hN lambda] at hcollision
  exact hcollision

def packetMomentTransferError
    (y n : ℕ) (h error M : ℝ) : ℝ :=
  (n : ℝ) * (((n + 1 : ℕ) : ℝ) * h + error) * M ^ (n - 1) +
    (n : ℝ) ^ 2 * (y : ℝ)⁻¹ * M ^ n

lemma abs_gsMoment_packetGrid_sub_scaled_cutoff_le
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {y N : ℕ} (hy : 2 ≤ y) (hN : 0 < N)
    {lambda h error M : ℝ}
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) (hh : 0 < h)
    (herror : 0 ≤ error) {K : ℕ}
    (hcover : ∀ p ∈ P, ∃ i < K, p ∈ packetExponentCell P y
      (gsGridPoint h i) (gsGridPoint h (i + 1)))
    (hc0 : ∀ i < K, 0 ≤ packetGridCoefficient lambda P y h i)
    (hc1 : ∀ i < K, packetGridCoefficient lambda P y h i ≤ 1)
    (hclose : ∀ a b : ℝ, 1 ≤ a → a ≤ b →
      |primeExponentCellMass y a b - (Real.log b - Real.log a)| < error)
    (hhigh : ∀ p ∈ P, y < p)
    (hM1 : 1 ≤ M)
    (hmass : atomMass P (fun p : ℕ ↦ lambda * (p : ℝ)⁻¹) ≤ M)
    (n : ℕ)
    (hu0 : 0 ≤ Real.log N / Real.log y)
    (huK : Real.log N / Real.log y ≤ gsGridPoint h K) :
    |gsMoment
          (gsGridKernel h K (packetGridCoefficient lambda P y h)) n
          (Real.log N / Real.log y) -
        lambda ^ n * (n.factorial : ℝ) *
          cutoffElementaryReciprocalMass N P n| ≤
      packetMomentTransferError y n h error M := by
  let w : ℕ → ℝ := fun p ↦ lambda * (p : ℝ)⁻¹
  let x : ℕ → ℝ := primeLogLocation y
  have hw : ∀ p ∈ P, 0 ≤ w p := by
    intro p hp
    dsimp only [w]
    positivity
  have hgrid := abs_gsMoment_packetGrid_sub_primeAtomMoment_le hP hy
    hlambda0 hlambda1 hh herror hcover hc0 hc1 hclose hM1 hmass n hu0 huK
  have hcollision := primeAtomMoment_sub_scaled_cutoff_le hP hy hN
    hlambda0 hlambda1 hhigh hM1 hmass (j := n)
  have hdistinct := distinctAtomMoment_le_atomMoment (x := x) hw n
    (Real.log N / Real.log y)
  have hdistinctEq := distinctAtomMoment_scaled_primeLog_eq_cutoff
    hP hy hN lambda (j := n)
  have hcollisionNonneg :
      0 ≤ atomMoment P w x n (Real.log N / Real.log y) -
        lambda ^ n * (n.factorial : ℝ) *
          cutoffElementaryReciprocalMass N P n := by
    dsimp only [w, x]
    rw [← hdistinctEq]
    exact sub_nonneg.mpr hdistinct
  have hcollisionAbs :
      |atomMoment P w x n (Real.log N / Real.log y) -
          lambda ^ n * (n.factorial : ℝ) *
            cutoffElementaryReciprocalMass N P n| ≤
        (n : ℝ) ^ 2 * (y : ℝ)⁻¹ * M ^ n := by
    rw [abs_of_nonneg hcollisionNonneg]
    exact hcollision
  dsimp only [w, x] at hcollisionAbs
  calc
    _ ≤
        |gsMoment
            (gsGridKernel h K (packetGridCoefficient lambda P y h)) n
              (Real.log N / Real.log y) -
          atomMoment P (fun p : ℕ ↦ lambda * (p : ℝ)⁻¹)
            (primeLogLocation y) n (Real.log N / Real.log y)| +
        |atomMoment P (fun p : ℕ ↦ lambda * (p : ℝ)⁻¹)
            (primeLogLocation y) n (Real.log N / Real.log y) -
          lambda ^ n * (n.factorial : ℝ) *
            cutoffElementaryReciprocalMass N P n| := abs_sub_le _ _ _
    _ ≤
        (n : ℝ) * (((n + 1 : ℕ) : ℝ) * h + error) * M ^ (n - 1) +
          (n : ℝ) ^ 2 * (y : ℝ)⁻¹ * M ^ n :=
      add_le_add hgrid hcollisionAbs
    _ = packetMomentTransferError y n h error M := rfl

theorem abs_gsAlternatingMomentSum_packetGrid_sub_scaledTruncated_le
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {y N : ℕ} (hy : 2 ≤ y) (hN : 0 < N)
    {lambda h error M : ℝ}
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) (hh : 0 < h)
    (herror : 0 ≤ error) {K : ℕ}
    (hcover : ∀ p ∈ P, ∃ i < K, p ∈ packetExponentCell P y
      (gsGridPoint h i) (gsGridPoint h (i + 1)))
    (hc0 : ∀ i < K, 0 ≤ packetGridCoefficient lambda P y h i)
    (hc1 : ∀ i < K, packetGridCoefficient lambda P y h i ≤ 1)
    (hclose : ∀ a b : ℝ, 1 ≤ a → a ≤ b →
      |primeExponentCellMass y a b - (Real.log b - Real.log a)| < error)
    (hhigh : ∀ p ∈ P, y < p)
    (hM1 : 1 ≤ M)
    (hmass : atomMass P (fun p : ℕ ↦ lambda * (p : ℝ)⁻¹) ≤ M)
    (r : ℕ)
    (hu0 : 0 ≤ Real.log N / Real.log y)
    (huK : Real.log N / Real.log y ≤ gsGridPoint h K) :
    |gsAlternatingMomentSum
          (gsGridKernel h K (packetGridCoefficient lambda P y h)) r
          (Real.log N / Real.log y) -
        ∑ j ∈ Finset.range (r + 1),
          (-1 : ℝ) ^ j * lambda ^ j *
            cutoffElementaryReciprocalMass N P j| ≤
      ∑ j ∈ Finset.range (r + 1),
        packetMomentTransferError y j h error M / j.factorial := by
  unfold gsAlternatingMomentSum
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ j ∈ Finset.range (r + 1),
        ((-1 : ℝ) ^ j *
              gsMoment
                (gsGridKernel h K (packetGridCoefficient lambda P y h)) j
                  (Real.log N / Real.log y) /
              j.factorial -
          (-1 : ℝ) ^ j * lambda ^ j *
            cutoffElementaryReciprocalMass N P j)| ≤
        ∑ j ∈ Finset.range (r + 1),
          |(-1 : ℝ) ^ j *
                gsMoment
                  (gsGridKernel h K (packetGridCoefficient lambda P y h)) j
                    (Real.log N / Real.log y) /
                j.factorial -
            (-1 : ℝ) ^ j * lambda ^ j *
              cutoffElementaryReciprocalMass N P j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (r + 1),
        packetMomentTransferError y j h error M / j.factorial := by
      apply Finset.sum_le_sum
      intro j hj
      have hjfact : (0 : ℝ) < j.factorial := by positivity
      have hmom := abs_gsMoment_packetGrid_sub_scaled_cutoff_le hP hy hN
        hlambda0 hlambda1 hh herror hcover hc0 hc1 hclose hhigh hM1 hmass
        j hu0 huK
      rw [show
          (-1 : ℝ) ^ j *
                gsMoment
                  (gsGridKernel h K (packetGridCoefficient lambda P y h)) j
                    (Real.log N / Real.log y) /
                j.factorial -
              (-1 : ℝ) ^ j * lambda ^ j *
                cutoffElementaryReciprocalMass N P j =
            ((-1 : ℝ) ^ j /
              (j.factorial : ℝ)) *
              (gsMoment
                  (gsGridKernel h K (packetGridCoefficient lambda P y h)) j
                    (Real.log N / Real.log y) -
                lambda ^ j * (j.factorial : ℝ) *
                  cutoffElementaryReciprocalMass N P j) by
            field_simp
            <;> ring]
      rw [abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow,
        one_div, abs_of_pos hjfact]
      simpa [div_eq_mul_inv, mul_comm] using
        (mul_le_mul_of_nonneg_left hmom (inv_nonneg.mpr hjfact.le))

lemma abs_scaledTruncated_sub_truncatedSieveApprox_le
    (N : ℕ) (P : Finset ℕ) (lambda : ℝ) (r : ℕ) :
    |∑ j ∈ Finset.range (r + 1),
          (-1 : ℝ) ^ j * lambda ^ j *
            cutoffElementaryReciprocalMass N P j -
        truncatedSieveApprox N P r| ≤
      ∑ j ∈ Finset.range (r + 1),
        |lambda ^ j - 1| * cutoffElementaryReciprocalMass N P j := by
  unfold truncatedSieveApprox
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ j ∈ Finset.range (r + 1),
        ((-1 : ℝ) ^ j * lambda ^ j *
            cutoffElementaryReciprocalMass N P j -
          (-1 : ℝ) ^ j * cutoffElementaryReciprocalMass N P j)| ≤
        ∑ j ∈ Finset.range (r + 1),
          |(-1 : ℝ) ^ j * lambda ^ j *
              cutoffElementaryReciprocalMass N P j -
            (-1 : ℝ) ^ j * cutoffElementaryReciprocalMass N P j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ Finset.range (r + 1),
        |lambda ^ j - 1| * cutoffElementaryReciprocalMass N P j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [show
          (-1 : ℝ) ^ j * lambda ^ j *
                cutoffElementaryReciprocalMass N P j -
              (-1 : ℝ) ^ j * cutoffElementaryReciprocalMass N P j =
            (-1 : ℝ) ^ j * (lambda ^ j - 1) *
              cutoffElementaryReciprocalMass N P j by ring]
      rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg (cutoffElementaryReciprocalMass_nonneg N P j)]

theorem packetGrid_lower_bound
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {y N : ℕ} (hy : 2 ≤ y) (hN : 0 < N)
    {lambda h error M : ℝ}
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) (hh : 0 < h)
    (herror : 0 ≤ error) {K : ℕ}
    (hcover : ∀ p ∈ P, ∃ i < K, p ∈ packetExponentCell P y
      (gsGridPoint h i) (gsGridPoint h (i + 1)))
    (hc0 : ∀ i < K, 0 ≤ packetGridCoefficient lambda P y h i)
    (hc1 : ∀ i < K, packetGridCoefficient lambda P y h i ≤ 1)
    (hclose : ∀ a b : ℝ, 1 ≤ a → a ≤ b →
      |primeExponentCellMass y a b - (Real.log b - Real.log a)| < error)
    (hhigh : ∀ p ∈ P, y < p)
    (hM1 : 1 ≤ M)
    (hmass : atomMass P (fun p : ℕ ↦ lambda * (p : ℝ)⁻¹) ≤ M)
    (r : ℕ)
    (hu0 : 0 ≤ Real.log N / Real.log y)
    (huK : Real.log N / Real.log y = gsGridPoint h K)
    (huR : Real.log N / Real.log y ≤ (r : ℝ)) :
    dickmanRho (Real.exp (lambda * reciprocalMass P)) ≤
      truncatedSieveApprox N P r +
        (∑ j ∈ Finset.range (r + 1),
          packetMomentTransferError y j h error M / j.factorial) +
        (∑ j ∈ Finset.range (r + 1),
          |lambda ^ j - 1| * cutoffElementaryReciprocalMass N P j) := by
  let c : ℕ → ℝ := packetGridCoefficient lambda P y h
  let chi : ℝ → ℝ := gsGridKernel h K c
  have hchi : IsGSKernel chi := by
    dsimp only [chi, c]
    exact isGSKernel_gsGridKernel hh hc0 hc1
  have hunique : ∀ {i j p : ℕ}, i < K → j < K →
      p ∈ packetExponentCell P y (gsGridPoint h i) (gsGridPoint h (i + 1)) →
      p ∈ packetExponentCell P y (gsGridPoint h j) (gsGridPoint h (j + 1)) → i = j := by
    intro i j p hi hj hpi hpj
    exact packetExponentCell_grid_unique (show 1 ≤ y by omega) hh hpi hpj
  have hscale :
      gsScale chi (Real.log N / Real.log y) =
        Real.exp (lambda * reciprocalMass P) := by
    rw [huK]
    dsimp only [chi, c]
    exact gsScale_packetGridKernel_eq_exp_reciprocalMass hh hcover hunique hc0 hc1
  have hcontinuous := gs_continuous_extremal_canonical hchi
    (Real.log N / Real.log y) hu0
  rw [hscale, gsCanonicalSolution_eq_fixed hu0 huR] at hcontinuous
  have hmoment :=
    abs_gsAlternatingMomentSum_packetGrid_sub_scaledTruncated_le hP hy hN
      hlambda0 hlambda1 hh herror hcover hc0 hc1 hclose hhigh hM1 hmass
      r hu0 huK.le
  have hscaled := abs_scaledTruncated_sub_truncatedSieveApprox_le N P lambda r
  dsimp only [chi, c] at hcontinuous
  calc
    dickmanRho (Real.exp (lambda * reciprocalMass P)) ≤
        gsAlternatingMomentSum
          (gsGridKernel h K (packetGridCoefficient lambda P y h)) r
            (Real.log N / Real.log y) := hcontinuous
    _ ≤
        (∑ j ∈ Finset.range (r + 1),
          (-1 : ℝ) ^ j * lambda ^ j *
            cutoffElementaryReciprocalMass N P j) +
          (∑ j ∈ Finset.range (r + 1),
            packetMomentTransferError y j h error M / j.factorial) := by
      linarith [le_abs_self
        (gsAlternatingMomentSum
            (gsGridKernel h K (packetGridCoefficient lambda P y h)) r
              (Real.log N / Real.log y) -
          ∑ j ∈ Finset.range (r + 1),
            (-1 : ℝ) ^ j * lambda ^ j *
              cutoffElementaryReciprocalMass N P j)]
    _ ≤ truncatedSieveApprox N P r +
          (∑ j ∈ Finset.range (r + 1),
            packetMomentTransferError y j h error M / j.factorial) +
          (∑ j ∈ Finset.range (r + 1),
            |lambda ^ j - 1| * cutoffElementaryReciprocalMass N P j) := by
      linarith [le_abs_self
        ((∑ j ∈ Finset.range (r + 1),
            (-1 : ℝ) ^ j * lambda ^ j *
              cutoffElementaryReciprocalMass N P j) -
          truncatedSieveApprox N P r)]

lemma one_sub_pow_le_nat_mul_one_sub
    {lambda : ℝ} (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (n : ℕ) :
    1 - lambda ^ n ≤ (n : ℝ) * (1 - lambda) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hpow0 : 0 ≤ lambda ^ n := pow_nonneg hlambda0 n
      have hpow1 : lambda ^ n ≤ 1 := pow_le_one₀ hlambda0 hlambda1
      have hone : 0 ≤ 1 - lambda := sub_nonneg.mpr hlambda1
      rw [pow_succ]
      calc
        1 - lambda ^ n * lambda =
            (1 - lambda ^ n) + lambda ^ n * (1 - lambda) := by ring
        _ ≤ (n : ℝ) * (1 - lambda) + 1 * (1 - lambda) := by
          exact add_le_add ih (mul_le_mul_of_nonneg_right hpow1 hone)
        _ = ((n + 1 : ℕ) : ℝ) * (1 - lambda) := by
          push_cast
          ring

lemma abs_pow_sub_one_le_nat_mul_one_sub
    {lambda : ℝ} (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (n : ℕ) :
    |lambda ^ n - 1| ≤ (n : ℝ) * (1 - lambda) := by
  rw [abs_of_nonpos (sub_nonpos.mpr (pow_le_one₀ hlambda0 hlambda1))]
  simpa only [neg_sub] using one_sub_pow_le_nat_mul_one_sub hlambda0 hlambda1 n

lemma scaledTruncatedError_le_uniform
    {C lambda M : ℝ} (hC : 0 ≤ C)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (hM1 : 1 ≤ M) (hCM : C ≤ M)
    {N : ℕ} {P : Finset ℕ} (hmass : reciprocalMass P ≤ C)
    (r : ℕ) :
    (∑ j ∈ Finset.range (r + 1),
        |lambda ^ j - 1| * cutoffElementaryReciprocalMass N P j) ≤
      ((r + 1 : ℕ) : ℝ) *
        ((r : ℝ) * (1 - lambda) * M ^ r) := by
  calc
    _ ≤ ∑ _j ∈ Finset.range (r + 1),
        (r : ℝ) * (1 - lambda) * M ^ r := by
      apply Finset.sum_le_sum
      intro j hj
      have hjr : j ≤ r := by
        have : j < r + 1 := Finset.mem_range.mp hj
        omega
      have hjR : (j : ℝ) ≤ r := by exact_mod_cast hjr
      have hpow : C ^ j ≤ M ^ r := by
        exact (pow_le_pow_left₀ hC hCM j).trans
          (pow_le_pow_right₀ hM1 hjr)
      have hcut := cutoffElementaryReciprocalMass_le_budget hC hmass
        (N := N) (j := j)
      have hfact : (1 : ℝ) ≤ j.factorial := by
        exact_mod_cast Nat.factorial_pos j
      have hcutM : cutoffElementaryReciprocalMass N P j ≤ M ^ r := by
        calc
          _ ≤ C ^ j / j.factorial := hcut
          _ ≤ C ^ j := div_le_self (pow_nonneg hC j) hfact
          _ ≤ M ^ r := hpow
      have habs := abs_pow_sub_one_le_nat_mul_one_sub
        hlambda0 hlambda1 j
      have hone : 0 ≤ 1 - lambda := sub_nonneg.mpr hlambda1
      have hcut0 := cutoffElementaryReciprocalMass_nonneg N P j
      calc
        |lambda ^ j - 1| * cutoffElementaryReciprocalMass N P j ≤
            ((j : ℝ) * (1 - lambda)) *
              cutoffElementaryReciprocalMass N P j :=
          mul_le_mul_of_nonneg_right habs hcut0
        _ ≤ ((r : ℝ) * (1 - lambda)) * M ^ r := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_right hjR hone) hcutM
            hcut0 (mul_nonneg (Nat.cast_nonneg r) hone)
        _ = (r : ℝ) * (1 - lambda) * M ^ r := rfl
    _ = ((r + 1 : ℕ) : ℝ) *
        ((r : ℝ) * (1 - lambda) * M ^ r) := by simp

lemma packetMomentTransferError_nonneg
    (y n : ℕ) {h error M : ℝ}
    (hh : 0 ≤ h) (herror : 0 ≤ error) (hM : 0 ≤ M) :
    0 ≤ packetMomentTransferError y n h error M := by
  unfold packetMomentTransferError
  positivity

lemma packetMomentTransferError_le_uniform
    {y n r : ℕ} {h error M : ℝ}
    (hnr : n ≤ r) (hh : 0 ≤ h) (herror : 0 ≤ error) (hM1 : 1 ≤ M) :
    packetMomentTransferError y n h error M ≤
      (r : ℝ) * (((r + 1 : ℕ) : ℝ) * h + error) * M ^ r +
        (r : ℝ) ^ 2 * (y : ℝ)⁻¹ * M ^ r := by
  have hnR : (n : ℝ) ≤ r := by exact_mod_cast hnr
  have hnsuccR : ((n + 1 : ℕ) : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ hnr
  have hpowSub : M ^ (n - 1) ≤ M ^ r := by
    exact pow_le_pow_right₀ hM1 ((Nat.sub_le n 1).trans hnr)
  have hpow : M ^ n ≤ M ^ r := pow_le_pow_right₀ hM1 hnr
  unfold packetMomentTransferError
  apply add_le_add
  · gcongr
  · gcongr

lemma packetMomentTransferErrorSum_le_uniform
    {y r : ℕ} {h error M : ℝ}
    (hh : 0 ≤ h) (herror : 0 ≤ error) (hM1 : 1 ≤ M) :
    (∑ j ∈ Finset.range (r + 1),
        packetMomentTransferError y j h error M / j.factorial) ≤
      ((r + 1 : ℕ) : ℝ) *
        ((r : ℝ) * (((r + 1 : ℕ) : ℝ) * h + error) * M ^ r +
          (r : ℝ) ^ 2 * (y : ℝ)⁻¹ * M ^ r) := by
  let B : ℝ :=
    (r : ℝ) * (((r + 1 : ℕ) : ℝ) * h + error) * M ^ r +
      (r : ℝ) ^ 2 * (y : ℝ)⁻¹ * M ^ r
  calc
    _ ≤ ∑ _j ∈ Finset.range (r + 1), B := by
      apply Finset.sum_le_sum
      intro j hj
      have hjr : j ≤ r := by
        have : j < r + 1 := Finset.mem_range.mp hj
        omega
      have hfact : (1 : ℝ) ≤ j.factorial := by
        exact_mod_cast Nat.factorial_pos j
      have herr0 := packetMomentTransferError_nonneg y j hh herror
        (zero_le_one.trans hM1)
      calc
        packetMomentTransferError y j h error M / j.factorial ≤
            packetMomentTransferError y j h error M :=
          div_le_self herr0 hfact
        _ ≤ B := packetMomentTransferError_le_uniform hjr hh herror hM1
    _ = ((r + 1 : ℕ) : ℝ) * B := by simp
    _ = _ := rfl

end

end Erdos783
