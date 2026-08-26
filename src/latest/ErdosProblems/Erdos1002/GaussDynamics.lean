import ErdosProblems.Erdos1002.GaussMeasure
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The Gauss map

This file formalizes the elementary dynamics of the regular continued-fraction
Gauss map.  The map is made total on `ℝ` by Lean's convention `0⁻¹ = 0`; all
continued-fraction statements explicitly assume that the argument belongs to
`(0,1]`.
-/

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace Erdos1002

noncomputable section

/-- The (total) regular continued-fraction Gauss map. -/
def gaussMap (x : ℝ) : ℝ := Int.fract x⁻¹

/-- The integer-valued first regular continued-fraction digit. -/
def gaussFirstDigit (x : ℝ) : ℤ := ⌊x⁻¹⌋

/-- The inverse branch indexed by the positive digit `q`. -/
def gaussInverseBranch (q : ℕ) (y : ℝ) : ℝ :=
  1 / ((q : ℝ) + y)

theorem measurable_gaussMap : Measurable gaussMap := by
  exact measurable_inv.fract

theorem continuousOn_gaussInverseBranch (q : ℕ) (hq : 0 < q) :
    ContinuousOn (gaussInverseBranch q) (Icc (0 : ℝ) 1) := by
  unfold gaussInverseBranch
  apply ContinuousOn.div continuousOn_const (continuous_const.add continuous_id).continuousOn
  intro y hy
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  change (q : ℝ) + y ≠ 0
  exact ne_of_gt (add_pos_of_pos_of_nonneg hqR hy.1)

theorem measurable_gaussInverseBranch (q : ℕ) :
    Measurable (gaussInverseBranch q) :=
  measurable_const.div (measurable_const.add measurable_id)

/-- On `(0,1]`, the equation saying that the first digit is `q` is exactly the
half-open first-digit cylinder from `GaussMeasure`. -/
theorem gaussFirstDigit_eq_iff_mem_firstDigitCylinder
    {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) (q : ℕ) (hq : 0 < q) :
    gaussFirstDigit x = (q : ℤ) ↔ x ∈ firstDigitCylinder q := by
  have hx0 : 0 < x := hx.1
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1R : (0 : ℝ) < (q + 1 : ℕ) := by positivity
  rw [gaussFirstDigit, Int.floor_eq_iff]
  constructor
  · rintro ⟨hl, hu⟩
    rw [firstDigitCylinder]
    constructor
    · apply (one_div_lt hq1R hx0).2
      simpa only [one_div, Nat.cast_add, Nat.cast_one] using! hu
    · apply (le_one_div hx0 hqR).2
      simpa only [one_div] using! hl
  · rintro ⟨hl, hu⟩
    constructor
    · have h := (le_one_div hx0 hqR).1 hu
      simpa only [one_div] using! h
    · have h := (one_div_lt hq1R hx0).1 hl
      simpa only [one_div, Nat.cast_add, Nat.cast_one] using! h

theorem firstDigitCylinder_subset_unit (q : ℕ) (hq : 0 < q) :
    firstDigitCylinder q ⊆ Ioc (0 : ℝ) 1 := by
  intro x hx
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq_one : (1 : ℝ) ≤ q := by exact_mod_cast hq
  constructor
  · exact lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / ((q + 1 : ℕ) : ℝ)) hx.1.le
  · exact hx.2.trans ((div_le_one hqR).2 hq_one)

theorem gaussInverseBranch_mem_firstDigitCylinder
    {y : ℝ} (hy : y ∈ Ico (0 : ℝ) 1) (q : ℕ) (hq : 0 < q) :
    gaussInverseBranch q y ∈ firstDigitCylinder q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hden : 0 < (q : ℝ) + y := add_pos_of_pos_of_nonneg hqR hy.1
  rw [gaussInverseBranch, firstDigitCylinder]
  constructor
  · apply one_div_lt_one_div_of_lt hden
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith [hy.2]
  · exact one_div_le_one_div_of_le hqR (le_add_of_nonneg_right hy.1)

theorem gaussMap_gaussInverseBranch
    {y : ℝ} (hy : y ∈ Ico (0 : ℝ) 1) (q : ℕ) (hq : 0 < q) :
    gaussMap (gaussInverseBranch q y) = y := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hden : (q : ℝ) + y ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg hqR hy.1)
  rw [gaussMap, gaussInverseBranch]
  simp only [one_div, inv_inv]
  rw [Int.fract_natCast_add]
  exact Int.fract_eq_self.mpr hy

theorem gaussInverseBranch_gaussMap
    {x : ℝ} {q : ℕ} (hq : 0 < q) (hx : x ∈ firstDigitCylinder q) :
    gaussInverseBranch q (gaussMap x) = x := by
  have hxunit := firstDigitCylinder_subset_unit q hq hx
  have hdigit :=
    (gaussFirstDigit_eq_iff_mem_firstDigitCylinder hxunit q hq).2 hx
  have hxne : x ≠ 0 := ne_of_gt hxunit.1
  change ⌊x⁻¹⌋ = (q : ℤ) at hdigit
  unfold gaussInverseBranch gaussMap
  rw [Int.fract, hdigit]
  norm_num only [Int.cast_natCast]
  field_simp
  ring

/-- Exact inverse-branch decomposition on one first-digit cylinder. -/
theorem gaussMap_preimage_inter_firstDigitCylinder
    (s : Set ℝ) (q : ℕ) (hq : 0 < q) :
    gaussMap ⁻¹' s ∩ firstDigitCylinder q =
      gaussInverseBranch q '' (s ∩ Ico (0 : ℝ) 1) := by
  ext x
  constructor
  · rintro ⟨hxs, hxcyl⟩
    refine ⟨gaussMap x, ⟨hxs, Int.fract_nonneg _, Int.fract_lt_one _⟩, ?_⟩
    exact gaussInverseBranch_gaussMap hq hxcyl
  · rintro ⟨y, ⟨hys, hyunit⟩, rfl⟩
    exact ⟨by simpa [gaussMap_gaussInverseBranch hyunit q hq] using! hys,
      gaussInverseBranch_mem_firstDigitCylinder hyunit q hq⟩

theorem strictAntiOn_gaussInverseBranch (q : ℕ) (hq : 0 < q) :
    StrictAntiOn (gaussInverseBranch q) (Icc (0 : ℝ) 1) := by
  intro a ha b hb hab
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  unfold gaussInverseBranch
  apply one_div_lt_one_div_of_lt
  · exact add_pos_of_pos_of_nonneg hqR ha.1
  · linarith

/-- A positive inverse branch sends an `Ioc` interval strictly inside
`[0,1)` to the reversed `Ico` interval.  Both endpoint conventions are
recorded explicitly. -/
theorem gaussInverseBranch_image_Ioc
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1)
    (q : ℕ) (hq : 0 < q) :
    gaussInverseBranch q '' Ioc a b =
      Ico (gaussInverseBranch q b) (gaussInverseBranch q a) := by
  have hanti := strictAntiOn_gaussInverseBranch q hq
  have hab_unit : Icc a b ⊆ Icc (0 : ℝ) 1 := by
    intro y hy
    exact ⟨ha.trans hy.1, hy.2.trans hb.le⟩
  apply le_antisymm
  · exact (hanti.mono hab_unit).image_Ioc_subset
  · intro x hx
    have ha_unit : a ∈ Icc (0 : ℝ) 1 := ⟨ha, hab.trans hb.le⟩
    have hb_unit : b ∈ Ico (0 : ℝ) 1 := ⟨ha.trans hab, hb⟩
    have hb_cyl := gaussInverseBranch_mem_firstDigitCylinder hb_unit q hq
    have hba : gaussInverseBranch q a ≤ gaussInverseBranch q 0 :=
      hanti.antitoneOn (by simp) ha_unit ha
    have hba' : gaussInverseBranch q a ≤ 1 / (q : ℝ) := by
      simpa [gaussInverseBranch] using! hba
    have hxcyl : x ∈ firstDigitCylinder q := by
      rw [firstDigitCylinder] at hb_cyl ⊢
      constructor
      · exact hb_cyl.1.trans_le hx.1
      · exact hx.2.le.trans hba'
    let y := gaussMap x
    have hy_unit : y ∈ Ico (0 : ℝ) 1 :=
      ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    have hy_unit_cc : y ∈ Icc (0 : ℝ) 1 := ⟨hy_unit.1, hy_unit.2.le⟩
    have hb_unit_cc : b ∈ Icc (0 : ℝ) 1 := ⟨hb_unit.1, hb_unit.2.le⟩
    have hbranch : gaussInverseBranch q y = x :=
      gaussInverseBranch_gaussMap hq hxcyl
    refine ⟨y, ?_, hbranch⟩
    constructor
    · by_contra hay
      have hya : y ≤ a := le_of_not_gt hay
      have hle : gaussInverseBranch q a ≤ gaussInverseBranch q y :=
        hanti.antitoneOn hy_unit_cc ha_unit hya
      rw [hbranch] at hle
      exact (not_le_of_gt hx.2) hle
    · by_contra hyb
      have hby : b < y := lt_of_not_ge hyb
      have hlt : gaussInverseBranch q y < gaussInverseBranch q b :=
        hanti hb_unit_cc hy_unit_cc hby
      rw [hbranch] at hlt
      exact (not_lt_of_ge hx.1) hlt

theorem gaussInverseBranch_image_Icc_zero
    {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) (q : ℕ) (hq : 0 < q) :
    gaussInverseBranch q '' Icc (0 : ℝ) b =
      Icc (gaussInverseBranch q b) (gaussInverseBranch q 0) := by
  have hle : gaussInverseBranch q b ≤ gaussInverseBranch q 0 := by
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    simpa [gaussInverseBranch] using!
      (one_div_le_one_div_of_le hqR (le_add_of_nonneg_right hb0))
  rw [← Ioc_insert_left hb0, Set.image_insert_eq,
    gaussInverseBranch_image_Ioc (a := 0) (b := b) (by positivity) hb0 hb1 q hq,
    Ico_insert_right hle]

theorem pairwise_disjoint_firstDigitCylinder :
    Pairwise fun m n : ℕ =>
      Disjoint (firstDigitCylinder (m + 1)) (firstDigitCylinder (n + 1)) := by
  intro m n hmn
  apply Set.disjoint_left.2
  intro x hxm hxn
  have hxm_unit := firstDigitCylinder_subset_unit (m + 1) (by omega) hxm
  have hdm :=
    (gaussFirstDigit_eq_iff_mem_firstDigitCylinder hxm_unit (m + 1) (by omega)).2 hxm
  have hdn :=
    (gaussFirstDigit_eq_iff_mem_firstDigitCylinder hxm_unit (n + 1) (by omega)).2 hxn
  apply hmn
  exact Nat.add_right_cancel (by exact_mod_cast hdm.symm.trans hdn)

/-- The positive first-digit cylinders are a disjoint countable partition of
the Gauss state space `(0,1]`. -/
theorem iUnion_firstDigitCylinder :
    (⋃ n : ℕ, firstDigitCylinder (n + 1)) = Ioc (0 : ℝ) 1 := by
  ext x
  constructor
  · rintro hx
    rcases Set.mem_iUnion.1 hx with ⟨n, hn⟩
    exact firstDigitCylinder_subset_unit (n + 1) (by omega) hn
  · intro hx
    have hxinv : (1 : ℝ) ≤ x⁻¹ := by
      rw [le_inv_comm₀ (by positivity) hx.1]
      simpa only [inv_one] using! hx.2
    have hz1 : (1 : ℤ) ≤ ⌊x⁻¹⌋ := by
      apply Int.le_floor.mpr
      simpa only [Int.cast_one] using! hxinv
    have hz0 : (0 : ℤ) ≤ ⌊x⁻¹⌋ := zero_le_one.trans hz1
    let k : ℕ := ⌊x⁻¹⌋.toNat
    have hk1 : 1 ≤ k := by
      rw [← Int.ofNat_le]
      simpa only [k, Int.toNat_of_nonneg hz0] using! hz1
    have hkcast : (k : ℤ) = ⌊x⁻¹⌋ := Int.toNat_of_nonneg hz0
    apply Set.mem_iUnion.2
    refine ⟨k - 1, ?_⟩
    have hksucc : k - 1 + 1 = k := Nat.sub_add_cancel hk1
    rw [hksucc]
    apply (gaussFirstDigit_eq_iff_mem_firstDigitCylinder hx k (by omega)).1
    exact hkcast.symm

/-- Countable inverse-branch decomposition of the Gauss preimage, with no
endpoint or support convention suppressed. -/
theorem gaussMap_preimage_inter_unit (s : Set ℝ) :
    gaussMap ⁻¹' s ∩ Ioc (0 : ℝ) 1 =
      ⋃ n : ℕ, gaussInverseBranch (n + 1) '' (s ∩ Ico (0 : ℝ) 1) := by
  rw [← iUnion_firstDigitCylinder, inter_iUnion]
  congr 1
  funext n
  exact gaussMap_preimage_inter_firstDigitCylinder s (n + 1) (by omega)

theorem gaussMap_preimage_Iic_inter_unit
    {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    gaussMap ⁻¹' Iic b ∩ Ioc (0 : ℝ) 1 =
      ⋃ n : ℕ, Icc (gaussInverseBranch (n + 1) b)
        (gaussInverseBranch (n + 1) 0) := by
  rw [gaussMap_preimage_inter_unit]
  have hinter : Iic b ∩ Ico (0 : ℝ) 1 = Icc 0 b := by
    ext y
    simp only [mem_inter_iff, mem_Iic, mem_Ico, mem_Icc]
    constructor
    · rintro ⟨hyb, hy0, -⟩
      exact ⟨hy0, hyb⟩
    · rintro ⟨hy0, hyb⟩
      exact ⟨hyb, hy0, hyb.trans_lt hb1⟩
  rw [hinter]
  congr 1
  funext n
  exact gaussInverseBranch_image_Icc_zero hb0 hb1 (n + 1) (by omega)

/-- The finite logarithmic identity behind invariance of Gauss measure.  It is
stated separately so that the cancellation used in the countable branch sum
is kernel-visible. -/
theorem gaussLog_telescope (b : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n,
      ((Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1)) -
       (Real.log ((k : ℝ) + b + 2) - Real.log ((k : ℝ) + b + 1)))) =
      (Real.log ((n : ℝ) + 1) - Real.log 1) -
       (Real.log ((n : ℝ) + b + 1) - Real.log (b + 1)) := by
  rw [Finset.sum_sub_distrib]
  have h₁ := Finset.sum_range_sub (fun k : ℕ => Real.log ((k : ℝ) + 1)) n
  have h₂ := Finset.sum_range_sub (fun k : ℕ => Real.log ((k : ℝ) + b + 1)) n
  have h₁' : (∑ k ∈ Finset.range n,
      (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1))) =
      Real.log ((n : ℝ) + 1) - Real.log 1 := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_assoc, add_comm, add_left_comm,
      one_add_one_eq_two, zero_add] using! h₁
  have h₂' : (∑ k ∈ Finset.range n,
      (Real.log ((k : ℝ) + b + 2) - Real.log ((k : ℝ) + b + 1))) =
      Real.log ((n : ℝ) + b + 1) - Real.log (b + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_assoc, add_comm, add_left_comm,
      one_add_one_eq_two, zero_add] using! h₂
  rw [h₁', h₂']

theorem gaussMeasure_singleton (x : ℝ) : gaussMeasure {x} = 0 := by
  rw [gaussMeasure, gaussStieltjes.measure_singleton]
  have hleft : Function.leftLim gaussCDF x = gaussCDF x :=
    continuous_gaussCDF.continuousAt.continuousWithinAt.leftLim_eq
  change ENNReal.ofReal (gaussCDF x - Function.leftLim gaussCDF x) = 0
  rw [hleft, sub_self, ENNReal.ofReal_zero]

theorem gaussMeasure_real_Icc {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    gaussMeasure.real (Icc a b) =
      (Real.log (1 + b) - Real.log (1 + a)) / Real.log 2 := by
  rw [← Ioc_insert_left hab, insert_eq, measureReal_union
    (disjoint_singleton_left.2 fun h => (lt_irrefl a h.1)) measurableSet_Ioc]
  rw [measureReal_def, gaussMeasure_singleton, ENNReal.toReal_zero, zero_add]
  exact gaussMeasure_real_Ioc ha hab hb

/-- Exact contribution of one inverse branch to the preimage of `[0,b]`. -/
theorem gaussMeasure_real_inverseBranch_Icc
    {b : ℝ} (hb0 : 0 ≤ b) (q : ℕ) (hq : 0 < q) :
    gaussMeasure.real
        (Icc (gaussInverseBranch q b) (gaussInverseBranch q 0)) =
      ((Real.log ((q : ℝ) + 1) - Real.log (q : ℝ)) -
        (Real.log ((q : ℝ) + b + 1) - Real.log ((q : ℝ) + b))) /
        Real.log 2 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqb : 0 < (q : ℝ) + b := add_pos_of_pos_of_nonneg hqR hb0
  have habr : gaussInverseBranch q b ≤ gaussInverseBranch q 0 := by
    simpa [gaussInverseBranch] using!
      (one_div_le_one_div_of_le hqR (le_add_of_nonneg_right hb0))
  rw [gaussMeasure_real_Icc (by simp [gaussInverseBranch, hqb.le]) habr (by
    simp only [gaussInverseBranch, add_zero]
    exact (div_le_one hqR).2 (by exact_mod_cast hq))]
  have h₁ : 1 + gaussInverseBranch q 0 = ((q : ℝ) + 1) / (q : ℝ) := by
    simp only [gaussInverseBranch, add_zero]
    field_simp
  have h₂ : 1 + gaussInverseBranch q b =
      ((q : ℝ) + b + 1) / ((q : ℝ) + b) := by
    unfold gaussInverseBranch
    field_simp
  rw [h₁, h₂, Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity)]

private theorem inverseBranch_Icc_subset_firstDigitCylinder
    {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) (q : ℕ) (hq : 0 < q) :
    Icc (gaussInverseBranch q b) (gaussInverseBranch q 0) ⊆
      firstDigitCylinder q := by
  intro x hx
  have hbmem : b ∈ Ico (0 : ℝ) 1 := ⟨hb0, hb1⟩
  have h0mem : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := by simp
  have hbcyl := gaussInverseBranch_mem_firstDigitCylinder hbmem q hq
  have h0cyl := gaussInverseBranch_mem_firstDigitCylinder h0mem q hq
  rw [firstDigitCylinder] at hbcyl h0cyl ⊢
  exact ⟨hbcyl.1.trans_le hx.1, hx.2.trans h0cyl.2⟩

private theorem pairwise_disjoint_inverseBranch_Icc
    {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    Pairwise fun m n : ℕ => Disjoint
      (Icc (gaussInverseBranch (m + 1) b) (gaussInverseBranch (m + 1) 0))
      (Icc (gaussInverseBranch (n + 1) b) (gaussInverseBranch (n + 1) 0)) := by
  intro m n hmn
  exact (pairwise_disjoint_firstDigitCylinder hmn).mono
    (inverseBranch_Icc_subset_firstDigitCylinder hb0 hb1 (m + 1) (by omega))
    (inverseBranch_Icc_subset_firstDigitCylinder hb0 hb1 (n + 1) (by omega))

theorem gaussMeasure_real_preimage_Iic_inter_unit
    {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    gaussMeasure.real (gaussMap ⁻¹' Iic b ∩ Ioc (0 : ℝ) 1) =
      ∑' n : ℕ, gaussMeasure.real
        (Icc (gaussInverseBranch (n + 1) b) (gaussInverseBranch (n + 1) 0)) := by
  rw [gaussMap_preimage_Iic_inter_unit hb0 hb1, measureReal_def,
    measure_iUnion (pairwise_disjoint_inverseBranch_Icc hb0 hb1)
      (fun _ => measurableSet_Icc), ENNReal.tsum_toReal_eq (fun _ => by finiteness)]
  rfl

theorem gaussMeasure_real_preimage_Iic_inter_unit_eq
    {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    gaussMeasure.real (gaussMap ⁻¹' Iic b ∩ Ioc (0 : ℝ) 1) =
      Real.log (1 + b) / Real.log 2 := by
  rw [gaussMeasure_real_preimage_Iic_inter_unit hb0 hb1]
  have hsum : HasSum (fun n : ℕ => gaussMeasure.real
      (Icc (gaussInverseBranch (n + 1) b) (gaussInverseBranch (n + 1) 0)))
      (Real.log (1 + b) / Real.log 2) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg (fun _ => measureReal_nonneg)]
    have hpartial (n : ℕ) :
        (∑ k ∈ Finset.range n, gaussMeasure.real
          (Icc (gaussInverseBranch (k + 1) b) (gaussInverseBranch (k + 1) 0))) =
        ((Real.log ((n : ℝ) + 1) - Real.log 1) -
          (Real.log ((n : ℝ) + b + 1) - Real.log (b + 1))) / Real.log 2 := by
      calc
        _ = ∑ k ∈ Finset.range n,
            (((Real.log (((k + 1 : ℕ) : ℝ) + 1) - Real.log ((k + 1 : ℕ) : ℝ)) -
              (Real.log (((k + 1 : ℕ) : ℝ) + b + 1) -
                Real.log (((k + 1 : ℕ) : ℝ) + b))) / Real.log 2) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact gaussMeasure_real_inverseBranch_Icc hb0 (k + 1) (by omega)
        _ = _ := by
          rw [← Finset.sum_div]
          congr 1
          simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm,
            one_add_one_eq_two] using! gaussLog_telescope b n
    simp_rw [hpartial]
    have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have hlog := (Real.tendsto_log_comp_add_sub_log b).comp hn
    have hmain : Tendsto (fun n : ℕ =>
        ((Real.log ((n : ℝ) + 1) - Real.log 1) -
          (Real.log ((n : ℝ) + b + 1) - Real.log (b + 1))))
        atTop (𝓝 (Real.log (1 + b))) := by
      convert! hlog.neg.add_const (Real.log (b + 1)) using 1
      · funext n
        simp only [Function.comp_apply, Real.log_one, sub_zero]
        ring_nf
      · simp [add_comm]
    exact hmain.div_const (Real.log 2)
  exact hsum.tsum_eq

theorem gaussMeasure_unit : gaussMeasure (Ioc (0 : ℝ) 1) = 1 := by
  have hreal := gaussMeasure_real_Ioc (a := 0) (b := 1)
    (by positivity) (by norm_num) (by norm_num)
  rw [measureReal_def] at hreal
  norm_num at hreal
  exact (ENNReal.toReal_eq_one_iff _).mp hreal

theorem gaussMeasure_unit_ae : ∀ᵐ x ∂gaussMeasure, x ∈ Ioc (0 : ℝ) 1 :=
  (mem_ae_iff_prob_eq_one measurableSet_Ioc).2 gaussMeasure_unit

theorem gaussCDF_nonneg (x : ℝ) : 0 ≤ gaussCDF x := by
  unfold gaussCDF
  exact div_nonneg (Real.log_nonneg (by linarith [unitClamp_nonneg x]))
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

theorem gaussMeasure_real_Iic_eq_gaussCDF (x : ℝ) :
    gaussMeasure.real (Iic x) = gaussCDF x := by
  rw [measureReal_def, gaussMeasure,
    gaussStieltjes.measure_Iic tendsto_gaussCDF_atBot]
  change (ENNReal.ofReal (gaussCDF x - 0)).toReal = gaussCDF x
  rw [sub_zero, ENNReal.toReal_ofReal (gaussCDF_nonneg x)]

theorem gaussMeasure_real_preimage_Iic_eq_gaussCDF (b : ℝ) :
    gaussMeasure.real (gaussMap ⁻¹' Iic b) = gaussCDF b := by
  rcases lt_trichotomy b 0 with hbneg | hbzero | hbpos
  · have hempty : gaussMap ⁻¹' Iic b = ∅ := by
      ext x
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false, gaussMap]
      exact not_le_of_gt (hbneg.trans_le (Int.fract_nonneg x⁻¹))
    rw [hempty, measureReal_empty, gaussCDF_eq_zero_of_le hbneg.le]
  · subst b
    have hrestrict := gaussMeasure_real_preimage_Iic_inter_unit_eq
      (b := 0) (by positivity) (by norm_num)
    have hinter : gaussMeasure (gaussMap ⁻¹' Iic 0 ∩ Ioc (0 : ℝ) 1) =
        gaussMeasure (gaussMap ⁻¹' Iic 0) := by
      simpa [inter_comm] using!
        (Measure.measure_inter_eq_of_ae (s := gaussMap ⁻¹' Iic 0) gaussMeasure_unit_ae)
    rw [measureReal_def, hinter] at hrestrict
    rw [measureReal_def, gaussCDF,
      unitClamp_eq_of_mem_Icc (by norm_num : (0 : ℝ) ∈ Icc 0 1)]
    simpa using! hrestrict
  · by_cases hb1 : b < 1
    · have hrestrict := gaussMeasure_real_preimage_Iic_inter_unit_eq hbpos.le hb1
      have hinter : gaussMeasure (gaussMap ⁻¹' Iic b ∩ Ioc (0 : ℝ) 1) =
          gaussMeasure (gaussMap ⁻¹' Iic b) := by
        simpa [inter_comm] using!
          (Measure.measure_inter_eq_of_ae (s := gaussMap ⁻¹' Iic b) gaussMeasure_unit_ae)
      rw [measureReal_def, hinter] at hrestrict
      rw [measureReal_def, gaussCDF,
        unitClamp_eq_of_mem_Icc ⟨hbpos.le, hb1.le⟩]
      exact hrestrict
    · have hb1' : 1 ≤ b := le_of_not_gt hb1
      have huniv : gaussMap ⁻¹' Iic b = Set.univ := by
        ext x
        simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
        exact (Int.fract_lt_one x⁻¹).le.trans hb1'
      rw [huniv, gaussCDF_eq_one_of_le hb1']
      exact probReal_univ

/-- The Gauss probability measure is invariant under the total Gauss map. -/
theorem map_gaussMap_gaussMeasure :
    Measure.map gaussMap gaussMeasure = gaussMeasure := by
  apply Measure.ext_of_Iic
  intro b
  rw [Measure.map_apply measurable_gaussMap measurableSet_Iic]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  change gaussMeasure.real (gaussMap ⁻¹' Iic b) = gaussMeasure.real (Iic b)
  rw [gaussMeasure_real_preimage_Iic_eq_gaussCDF,
    gaussMeasure_real_Iic_eq_gaussCDF]

end

end Erdos1002
