import ErdosProblems.Erdos1038.ResidualDeficit

/-!
# Separation and contact for a finite residual configuration

This module formalizes the finite empirical part of the separation--contact
criterion in equations (4.11)--(4.12) of the manuscript.  The first residual
location is selected intrinsically as the minimum of the finite support.  The
critical point is characterized by a strictly increasing rational balance,
and the logarithmic potential is identified exactly with the inverse-map
level ratio.
-/

set_option warningAsError false

open scoped BigOperators Real
open Finset Set

namespace Erdos1038

noncomputable section

/-- The leftmost location of a finite residual configuration. -/
def residualMinLocation {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) : ℝ := by
  classical
  exact (Finset.univ.image C.location).min'
    ((residual_index_univ_nonempty C).image C.location)

lemma residualMinLocation_mem_locations {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) :
    residualMinLocation C ∈ Finset.univ.image C.location := by
  classical
  exact Finset.min'_mem _ _

lemma exists_location_eq_residualMinLocation {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) :
    ∃ i, C.location i = residualMinLocation C := by
  classical
  simpa only [Finset.mem_image, Finset.mem_univ, true_and] using!
    residualMinLocation_mem_locations C

/-- A canonical index at the leftmost residual location. -/
def residualMinIndex {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) : ι :=
  Classical.choose (exists_location_eq_residualMinLocation C)

@[simp]
lemma location_residualMinIndex {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) :
    C.location (residualMinIndex C) = residualMinLocation C :=
  Classical.choose_spec (exists_location_eq_residualMinLocation C)

lemma residualMinLocation_le_location {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) (i : ι) :
    residualMinLocation C ≤ C.location i := by
  classical
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

lemma residualMinLocation_mem_Icc {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) :
    residualMinLocation C ∈ Icc (1 : ℝ) 2 := by
  rw [← location_residualMinIndex C]
  exact C.location_mem _

lemma residualMinLocation_pos {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) : 0 < residualMinLocation C :=
  zero_lt_one.trans_le (residualMinLocation_mem_Icc C).1

/-- The positive critical-point equation, written without divisions by the
variable itself.  Its unique solution is characterized by
`residualCriticalBalance C y = k`. -/
def residualCriticalBalance {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) (y : ℝ) : ℝ :=
  ∑ i, C.weight i * y / (C.location i - y)

/-- The level corresponding to potential zero in the inverse coordinate. -/
def residualScale {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) (k : ℝ) : ℝ :=
  Real.exp (-(1 / k) * ∑ i, C.weight i * Real.log (C.location i))

/-- The finite empirical inverse map from equation (4.11). -/
def residualPsi {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) (k y : ℝ) : ℝ :=
  y * Real.exp ((1 / k) *
    ∑ i, C.weight i * Real.log (1 - y / C.location i))

lemma residualScale_pos {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) (k : ℝ) :
    0 < residualScale C k := by
  exact Real.exp_pos _

lemma residualPsi_pos {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) {k y : ℝ} (hy : 0 < y) :
    0 < residualPsi C k y := by
  exact mul_pos hy (Real.exp_pos _)

lemma residualPsi_zero {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) (k : ℝ) :
    residualPsi C k 0 = 0 := by
  simp [residualPsi]

lemma residualCriticalBalance_zero {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) :
    residualCriticalBalance C 0 = 0 := by
  simp [residualCriticalBalance]

lemma residual_location_sub_pos {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) {y : ℝ}
    (hy : y < residualMinLocation C) (i : ι) :
    0 < C.location i - y := by
  linarith [residualMinLocation_le_location C i]

theorem residualCriticalBalance_strictMonoOn {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) :
    StrictMonoOn (residualCriticalBalance C)
      (Iio (residualMinLocation C)) := by
  intro x hx y hy hxy
  rw [residualCriticalBalance, residualCriticalBalance]
  apply Finset.sum_lt_sum_of_nonempty (residual_index_univ_nonempty C)
  intro i hi
  have hdx : 0 < C.location i - x := residual_location_sub_pos C hx i
  have hdy : 0 < C.location i - y := residual_location_sub_pos C hy i
  rw [div_lt_div_iff₀ hdx hdy]
  calc
    C.weight i * x * (C.location i - y) <
        C.weight i * x * (C.location i - y) +
          C.weight i * C.location i * (y - x) := by
      exact lt_add_of_pos_right _
        (mul_pos (mul_pos (C.weight_pos i)
            (zero_lt_one.trans_le (C.location_mem i).1))
          (sub_pos.mpr hxy))
    _ = C.weight i * y * (C.location i - x) := by ring

lemma continuousOn_residualCriticalBalance_Iio {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) :
    ContinuousOn (residualCriticalBalance C)
      (Iio (residualMinLocation C)) := by
  intro y hy
  apply ContinuousAt.continuousWithinAt
  unfold residualCriticalBalance
  apply tendsto_finsetSum
  intro i hi
  exact (continuousAt_const.mul continuousAt_id).div
    (continuousAt_const.sub continuousAt_id)
    (residual_location_sub_pos C hy i).ne'

theorem existsUnique_residualCriticalBalance_eq {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) {k : ℝ} (hk : 0 < k) :
    ∃! y, y ∈ Ioo (0 : ℝ) (residualMinLocation C) ∧
      residualCriticalBalance C y = k := by
  let i₀ := residualMinIndex C
  let w := C.weight i₀
  let d := residualMinLocation C
  let upper := d * k / (k + w)
  have hw : 0 < w := C.weight_pos i₀
  have hd : 0 < d := residualMinLocation_pos C
  have hden : 0 < k + w := add_pos hk hw
  have hupper0 : 0 < upper := by
    dsimp [upper]
    positivity
  have hupperd : upper < d := by
    dsimp [upper]
    rw [div_lt_iff₀ hden]
    nlinarith
  have hterm : C.weight i₀ * upper / (C.location i₀ - upper) = k := by
    dsimp only [i₀]
    rw [location_residualMinIndex]
    change w * upper / (d - upper) = k
    dsimp [upper]
    field_simp [hden.ne', hd.ne', hw.ne']
    ring
  have hbalanceUpper : k ≤ residualCriticalBalance C upper := by
    rw [← hterm, residualCriticalBalance]
    apply Finset.single_le_sum
      (f := fun i ↦ C.weight i * upper / (C.location i - upper))
      (s := Finset.univ)
    · intro i hi
      exact div_nonneg (mul_nonneg (C.weight_pos i).le hupper0.le)
        (residual_location_sub_pos C hupperd i).le
    · exact Finset.mem_univ i₀
  have hcont : ContinuousOn (residualCriticalBalance C) (Icc 0 upper) :=
    (continuousOn_residualCriticalBalance_Iio C).mono fun y hy ↦
      lt_of_le_of_lt hy.2 hupperd
  have hkIcc : k ∈ Icc (residualCriticalBalance C 0)
      (residualCriticalBalance C upper) := by
    rw [residualCriticalBalance_zero]
    exact ⟨hk.le, hbalanceUpper⟩
  obtain ⟨y, hyIcc, hyEq⟩ :=
    intermediate_value_Icc hupper0.le hcont hkIcc
  have hy0 : 0 < y := by
    apply lt_of_le_of_ne hyIcc.1
    intro hyzero
    subst y
    have hzero : (0 : ℝ) = k := by
      simpa [residualCriticalBalance_zero] using! hyEq
    exact hk.ne' hzero.symm
  have hyMin : y < residualMinLocation C := hyIcc.2.trans_lt hupperd
  refine ⟨y, ⟨⟨hy0, hyMin⟩, hyEq⟩, ?_⟩
  intro z hz
  by_contra hyz
  rcases lt_or_gt_of_ne hyz with hzy | hyz
  · have := residualCriticalBalance_strictMonoOn C hz.1.2 hyMin hzy
    linarith [hyEq, hz.2]
  · have := residualCriticalBalance_strictMonoOn C hyMin hz.1.2 hyz
    linarith [hyEq, hz.2]

/-- The intrinsic positive critical point of the empirical inverse map. -/
def residualCriticalPoint {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) (k : ℝ) (hk : 0 < k) : ℝ :=
  Classical.choose (existsUnique_residualCriticalBalance_eq C hk).exists

lemma residualCriticalPoint_mem_Ioo {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) (k : ℝ) (hk : 0 < k) :
    residualCriticalPoint C k hk ∈
      Ioo (0 : ℝ) (residualMinLocation C) :=
  (Classical.choose_spec (existsUnique_residualCriticalBalance_eq C hk).exists).1

lemma residualCriticalBalance_criticalPoint {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) (k : ℝ) (hk : 0 < k) :
    residualCriticalBalance C (residualCriticalPoint C k hk) = k :=
  (Classical.choose_spec (existsUnique_residualCriticalBalance_eq C hk).exists).2

lemma residual_one_sub_div_pos {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) {y : ℝ}
    (hy : y < residualMinLocation C) (i : ι) :
    0 < 1 - y / C.location i := by
  have hloc : 0 < C.location i :=
    zero_lt_one.trans_le (C.location_mem i).1
  rw [sub_pos, div_lt_one hloc]
  exact hy.trans_le (residualMinLocation_le_location C i)

lemma residual_abs_sub_location {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) {y : ℝ}
    (hy : y < residualMinLocation C) (i : ι) :
    |y - C.location i| = C.location i - y := by
  rw [abs_of_neg (sub_neg.mpr <|
    hy.trans_le (residualMinLocation_le_location C i))]
  ring

lemma residual_log_factor_add_log_location {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) {y : ℝ}
    (hy : y < residualMinLocation C) (i : ι) :
    Real.log (1 - y / C.location i) + Real.log (C.location i) =
      Real.log |y - C.location i| := by
  have hloc : 0 < C.location i :=
    zero_lt_one.trans_le (C.location_mem i).1
  have hfactor := residual_one_sub_div_pos C hy i
  rw [residual_abs_sub_location C hy i, ← Real.log_mul hfactor.ne' hloc.ne']
  congr 1
  field_simp [hloc.ne']

lemma log_abs_residualPsi {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) {k y : ℝ} (hy0 : y ≠ 0) :
    Real.log |residualPsi C k y| =
      Real.log |y| + (1 / k) *
        ∑ i, C.weight i * Real.log (1 - y / C.location i) := by
  rw [residualPsi, abs_mul,
    Real.log_mul (abs_ne_zero.mpr hy0) (abs_ne_zero.mpr (Real.exp_ne_zero _)),
    abs_of_pos (Real.exp_pos _), Real.log_exp]

lemma log_residualScale {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) (k : ℝ) :
    Real.log (residualScale C k) =
      -(1 / k) * ∑ i, C.weight i * Real.log (C.location i) := by
  exact Real.log_exp _

lemma residual_weighted_log_distance_eq {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) {y : ℝ}
    (hy : y < residualMinLocation C) :
    ∑ i, C.weight i * Real.log |y - C.location i| =
      (∑ i, C.weight i * Real.log (1 - y / C.location i)) +
        ∑ i, C.weight i * Real.log (C.location i) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← mul_add, residual_log_factor_add_log_location C hy i]

/-- Exact equation (4.11): below the first residual atom, the potential is
the logarithm of the inverse-map level ratio. -/
theorem residualPotential_eq_k_mul_log_abs_psi_div_scale
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι)
    {k y : ℝ} (hk : k ≠ 0) (hy0 : y ≠ 0)
    (hy : y < residualMinLocation C) :
    residualPotential C k y =
      k * Real.log (|residualPsi C k y| / residualScale C k) := by
  have hpsi : |residualPsi C k y| ≠ 0 := by
    rw [abs_ne_zero, residualPsi]
    exact mul_ne_zero hy0 (Real.exp_ne_zero _)
  have hscale : residualScale C k ≠ 0 := (residualScale_pos C k).ne'
  rw [Real.log_div hpsi hscale, log_abs_residualPsi C hy0,
    log_residualScale, residualPotential,
    residual_weighted_log_distance_eq C hy]
  field_simp [hk]
  ring

theorem residualPotential_eq_zero_iff_abs_psi_eq_scale
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι)
    {k y : ℝ} (hk : k ≠ 0) (hy0 : y ≠ 0)
    (hy : y < residualMinLocation C) :
    residualPotential C k y = 0 ↔
      |residualPsi C k y| = residualScale C k := by
  rw [residualPotential_eq_k_mul_log_abs_psi_div_scale C hk hy0 hy,
    mul_eq_zero]
  simp only [hk, false_or]
  rw [Real.log_eq_zero]
  have hpsi : 0 < |residualPsi C k y| := abs_pos.mpr <| by
    rw [residualPsi]
    exact mul_ne_zero hy0 (Real.exp_ne_zero _)
  have hscale := residualScale_pos C k
  constructor
  · rintro (hratio0 | hratio1 | hratioNeg)
    · exact False.elim ((div_pos hpsi hscale).ne' hratio0)
    · exact (div_eq_one_iff_eq hscale.ne').mp hratio1
    · have hpositive := div_pos hpsi hscale
      rw [hratioNeg] at hpositive
      norm_num at hpositive
  · intro heq
    exact Or.inr <| Or.inl <| (div_eq_one_iff_eq hscale.ne').mpr heq

theorem residualPotential_eq_zero_iff_psi_eq_scale_of_pos
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι)
    {k y : ℝ} (hk : k ≠ 0) (hy0 : 0 < y)
    (hy : y < residualMinLocation C) :
    residualPotential C k y = 0 ↔
      residualPsi C k y = residualScale C k := by
  rw [residualPotential_eq_zero_iff_abs_psi_eq_scale C hk hy0.ne' hy,
    abs_of_pos (residualPsi_pos C hy0)]

lemma residualCriticalBalance_eq_mul_sum {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) (y : ℝ) :
    residualCriticalBalance C y =
      y * ∑ i, C.weight i / (C.location i - y) := by
  rw [residualCriticalBalance, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma hasDerivAt_residual_log_factor {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) {y : ℝ}
    (hy : y < residualMinLocation C) (i : ι) :
    HasDerivAt
      (fun z ↦ C.weight i * Real.log (1 - z / C.location i))
      (-C.weight i / (C.location i - y)) y := by
  have hloc : C.location i ≠ 0 :=
    (zero_lt_one.trans_le (C.location_mem i).1).ne'
  have harg := residual_one_sub_div_pos C hy i
  have hinner : HasDerivAt (fun z : ℝ ↦ 1 - z / C.location i)
      (-(1 / C.location i)) y :=
    ((hasDerivAt_id y).div_const (C.location i)).const_sub 1
  convert! (hinner.log harg.ne').const_mul (C.weight i) using 1
  field_simp [hloc]

lemma hasDerivAt_residual_psi_exponent {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) {k y : ℝ}
    (hy : y < residualMinLocation C) :
    HasDerivAt
      (fun z ↦ (1 / k) *
        ∑ i, C.weight i * Real.log (1 - z / C.location i))
      (-(1 / k) * ∑ i, C.weight i / (C.location i - y)) y := by
  have hsum : HasDerivAt
      (fun z ↦ ∑ i, C.weight i * Real.log (1 - z / C.location i))
      (∑ i, -C.weight i / (C.location i - y)) y := by
    have hs := HasDerivAt.sum (u := Finset.univ)
      (fun i _ ↦ hasDerivAt_residual_log_factor C hy i)
    convert! hs using 1
    funext z
    simp
  convert! hsum.const_mul (1 / k) using 1
  have hsumneg :
      (∑ i, -C.weight i / (C.location i - y)) =
        -(∑ i, C.weight i / (C.location i - y)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsumneg]
  ring

/-- Derivative form of the critical-point equation. -/
theorem hasDerivAt_residualPsi {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) {k y : ℝ} (hk : k ≠ 0)
    (hy : y < residualMinLocation C) :
    HasDerivAt (residualPsi C k)
      (Real.exp ((1 / k) *
          ∑ i, C.weight i * Real.log (1 - y / C.location i)) *
        (1 - residualCriticalBalance C y / k)) y := by
  have hexponent := hasDerivAt_residual_psi_exponent C (k := k) hy
  have hproduct := (hasDerivAt_id y).mul hexponent.exp
  simp only [id_eq] at hproduct
  rw [residualCriticalBalance_eq_mul_sum]
  convert! hproduct using 1
  field_simp [hk]
  ring

lemma continuousOn_residualPsi_Iio {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) {k : ℝ} (hk : k ≠ 0) :
    ContinuousOn (residualPsi C k) (Iio (residualMinLocation C)) := by
  intro y hy
  exact (hasDerivAt_residualPsi C hk hy).continuousAt.continuousWithinAt

theorem residualPsi_strictMonoOn_left {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) (k : ℝ) (hk : 0 < k) :
    StrictMonoOn (residualPsi C k)
      (Icc 0 (residualCriticalPoint C k hk)) := by
  let yc := residualCriticalPoint C k hk
  have hyc := residualCriticalPoint_mem_Ioo C k hk
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · exact (continuousOn_residualPsi_Iio C hk.ne').mono fun y hy ↦
      hy.2.trans_lt hyc.2
  · rw [interior_Icc]
    intro y hy
    rw [(hasDerivAt_residualPsi C hk.ne' (hy.2.trans hyc.2)).deriv]
    have hbalance : residualCriticalBalance C y < k := by
      rw [← residualCriticalBalance_criticalPoint C k hk]
      exact residualCriticalBalance_strictMonoOn C
        (hy.2.trans hyc.2) hyc.2 hy.2
    have hexp : 0 < Real.exp ((1 / k) *
        ∑ i, C.weight i * Real.log (1 - y / C.location i)) :=
      Real.exp_pos _
    have hfactor : 0 < 1 - residualCriticalBalance C y / k := by
      rw [sub_pos, div_lt_one hk]
      exact hbalance
    exact mul_pos hexp hfactor

theorem residualPsi_strictAntiOn_right {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) (k : ℝ) (hk : 0 < k) :
    StrictAntiOn (residualPsi C k)
      (Ico (residualCriticalPoint C k hk) (residualMinLocation C)) := by
  let yc := residualCriticalPoint C k hk
  have hyc := residualCriticalPoint_mem_Ioo C k hk
  apply strictAntiOn_of_deriv_neg (convex_Ico _ _)
  · exact (continuousOn_residualPsi_Iio C hk.ne').mono fun y hy ↦ hy.2
  · rw [interior_Ico]
    intro y hy
    rw [(hasDerivAt_residualPsi C hk.ne' hy.2).deriv]
    have hbalance : k < residualCriticalBalance C y := by
      rw [← residualCriticalBalance_criticalPoint C k hk]
      exact residualCriticalBalance_strictMonoOn C hyc.2 hy.2 hy.1
    have hexp : 0 < Real.exp ((1 / k) *
        ∑ i, C.weight i * Real.log (1 - y / C.location i)) :=
      Real.exp_pos _
    have hfactor : 1 - residualCriticalBalance C y / k < 0 := by
      rw [sub_neg, one_lt_div hk]
      exact hbalance
    exact mul_neg_of_pos_of_neg hexp hfactor

theorem residualPsi_lt_critical_of_ne {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) (k : ℝ) (hk : 0 < k)
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) (residualMinLocation C))
    (hne : y ≠ residualCriticalPoint C k hk) :
    residualPsi C k y <
      residualPsi C k (residualCriticalPoint C k hk) := by
  have hyc := residualCriticalPoint_mem_Ioo C k hk
  rcases lt_or_gt_of_ne hne with hy_lt | hy_gt
  · exact residualPsi_strictMonoOn_left C k hk
      ⟨hy.1.le, hy_lt.le⟩ ⟨hyc.1.le, le_rfl⟩ hy_lt
  · exact residualPsi_strictAntiOn_right C k hk
      ⟨le_rfl, hyc.2⟩ ⟨hy_gt.le, hy.2⟩ hy_gt

theorem residualPotential_nonneg_iff_scale_le_psi_of_pos
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι)
    {k y : ℝ} (hk : 0 < k) (hy0 : 0 < y)
    (hy : y < residualMinLocation C) :
    0 ≤ residualPotential C k y ↔
      residualScale C k ≤ residualPsi C k y := by
  have hpsi := residualPsi_pos C (k := k) hy0
  have hscale := residualScale_pos C k
  rw [residualPotential_eq_k_mul_log_abs_psi_div_scale
      C hk.ne' hy0.ne' hy,
    abs_of_pos hpsi, mul_nonneg_iff_of_pos_left hk,
    Real.log_nonneg_iff (div_pos hpsi hscale), one_le_div hscale]

theorem residualPotential_pos_iff_scale_lt_psi_of_pos
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι)
    {k y : ℝ} (hk : 0 < k) (hy0 : 0 < y)
    (hy : y < residualMinLocation C) :
    0 < residualPotential C k y ↔
      residualScale C k < residualPsi C k y := by
  have hpsi := residualPsi_pos C (k := k) hy0
  have hscale := residualScale_pos C k
  rw [residualPotential_eq_k_mul_log_abs_psi_div_scale
      C hk.ne' hy0.ne' hy,
    abs_of_pos hpsi, mul_pos_iff]
  simp only [hk, true_and, not_lt_of_ge hk.le, false_and, or_false]
  rw [Real.log_pos_iff (div_pos hpsi hscale).le, one_lt_div hscale]

theorem residualPotential_neg_iff_psi_lt_scale_of_pos
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι)
    {k y : ℝ} (hk : 0 < k) (hy0 : 0 < y)
    (hy : y < residualMinLocation C) :
    residualPotential C k y < 0 ↔
      residualPsi C k y < residualScale C k := by
  have hpsi := residualPsi_pos C (k := k) hy0
  have hscale := residualScale_pos C k
  rw [residualPotential_eq_k_mul_log_abs_psi_div_scale
      C hk.ne' hy0.ne' hy,
    abs_of_pos hpsi, mul_neg_iff]
  simp only [hk, true_and, not_lt_of_ge hk.le, false_and, or_false]
  rw [Real.log_neg_iff (div_pos hpsi hscale), div_lt_one hscale]

/-- A separated atomized configuration can only lie below the critical
inverse-map height.  This is the inequality part of the finite
separation--contact criterion. -/
theorem residualScale_le_psi_critical_of_separation
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι)
    {k b : ℝ} (hk : 0 < k) (hsep : IsResidualSeparationPoint C k b) :
    residualScale C k ≤
      residualPsi C k (residualCriticalPoint C k hk) := by
  have hbmin : b < residualMinLocation C := by
    rw [← location_residualMinIndex C]
    exact hsep.2.1 (residualMinIndex C)
  have hbscale : residualScale C k ≤ residualPsi C k b :=
    (residualPotential_nonneg_iff_scale_le_psi_of_pos
      C hk hsep.1 hbmin).mp hsep.2.2
  have hbmax : residualPsi C k b ≤
      residualPsi C k (residualCriticalPoint C k hk) := by
    by_cases hb : b = residualCriticalPoint C k hk
    · exact le_of_eq <| congrArg (residualPsi C k) hb
    · exact (residualPsi_lt_critical_of_ne C k hk ⟨hsep.1, hbmin⟩ hb).le
  exact hbscale.trans hbmax

/-- Equality in the critical-height comparison is exactly potential-zero
contact at the unique critical point. -/
theorem residualScale_eq_psi_critical_iff_contact
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι)
    (k : ℝ) (hk : 0 < k) :
    residualScale C k =
        residualPsi C k (residualCriticalPoint C k hk) ↔
      residualPotential C k (residualCriticalPoint C k hk) = 0 := by
  have hyc := residualCriticalPoint_mem_Ioo C k hk
  rw [residualPotential_eq_zero_iff_psi_eq_scale_of_pos
    C hk.ne' hyc.1 hyc.2]
  exact eq_comm

/-- At contact the critical point is the unique nonnegative-potential point
between zero and the first residual atom. -/
theorem residualPotential_neg_off_critical_of_contact
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι)
    (k : ℝ) (hk : 0 < k)
    (hcontact : residualScale C k =
      residualPsi C k (residualCriticalPoint C k hk))
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) (residualMinLocation C))
    (hne : y ≠ residualCriticalPoint C k hk) :
    residualPotential C k y < 0 := by
  apply (residualPotential_neg_iff_psi_lt_scale_of_pos
    C hk hy.1 hy.2).mpr
  rw [hcontact]
  exact residualPsi_lt_critical_of_ne C k hk hy hne

/-- Strict separation is equivalent to the existence of a positive-potential
barrier between the endpoint component and the first residual atom. -/
theorem residualScale_lt_psi_critical_iff_exists_potential_pos
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι)
    (k : ℝ) (hk : 0 < k) :
    residualScale C k <
        residualPsi C k (residualCriticalPoint C k hk) ↔
      ∃ y ∈ Ioo (0 : ℝ) (residualMinLocation C),
        0 < residualPotential C k y := by
  constructor
  · intro hstrict
    let yc := residualCriticalPoint C k hk
    have hyc := residualCriticalPoint_mem_Ioo C k hk
    refine ⟨yc, hyc, ?_⟩
    exact (residualPotential_pos_iff_scale_lt_psi_of_pos
      C hk hyc.1 hyc.2).mpr hstrict
  · rintro ⟨y, hy, hpotential⟩
    have hyScale : residualScale C k < residualPsi C k y :=
      (residualPotential_pos_iff_scale_lt_psi_of_pos
        C hk hy.1 hy.2).mp hpotential
    by_cases heq : y = residualCriticalPoint C k hk
    · simpa [heq] using! hyScale
    · exact hyScale.trans
        (residualPsi_lt_critical_of_ne C k hk hy heq)

/-- Every configuration carrying a residual separation point is in exactly
one of the strict-separation and contact regimes. -/
theorem residual_strictSeparation_or_contact
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι)
    {k b : ℝ} (hk : 0 < k) (hsep : IsResidualSeparationPoint C k b) :
    residualScale C k <
        residualPsi C k (residualCriticalPoint C k hk) ∨
      residualScale C k =
        residualPsi C k (residualCriticalPoint C k hk) :=
  (lt_or_eq_of_le <| residualScale_le_psi_critical_of_separation
    C hk hsep)

end

end Erdos1038
