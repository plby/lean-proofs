import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Complex.Basic

/-!
# Finite Riemann errors with rounded real endpoints

Complete unit cells cost the derivative bound times their number. The
remaining terminal summand and two fractional cells cost three supremum
bounds. All evaluations stay inside the stated differentiability interval.
-/

open MeasureTheory
open scoped BigOperators

namespace Erdos67b

noncomputable section

theorem mrNorm_cell_sum_sub_integral_le {F F' : ℝ → ℂ} {a C : ℝ} (hC : 0 ≤ C)
    (hderiv : ∀ x ∈ Set.Icc a (a + 1), HasDerivAt F (F' x) x)
    (hbound : ∀ x ∈ Set.Icc a (a + 1), ‖F' x‖ ≤ C) :
    ‖F a - ∫ x in a..a + 1, F x‖ ≤ C := by
  have hInt : IntervalIntegrable F volume a (a + 1) :=
    (HasDerivAt.continuousOn hderiv).intervalIntegrable_of_Icc (by linarith)
  calc
    _ = ‖∫ x in a..a + 1, (F a - F x)‖ := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const hInt]
      simp
    _ ≤ C * |(a + 1) - a| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      have hxI : x ∈ Set.Icc a (a + 1) := by
        simpa only [Set.uIcc_of_le (by linarith : a ≤ a + 1)] using Set.uIoc_subset_uIcc hx
      have hh := norm_image_sub_le_of_norm_deriv_le_segment'
        (fun y hy ↦ (hderiv y hy).hasDerivWithinAt)
        (fun y hy ↦ hbound y (Set.Ico_subset_Icc_self hy)) x hxI
      rw [norm_sub_rev]
      exact hh.trans (by nlinarith [hxI.2])
    _ = C := by norm_num

theorem mrNorm_sum_Ico_sub_integral_le {F F' : ℝ → ℂ} {A Z : ℕ} (hAZ : A ≤ Z)
    {C : ℝ} (hC : 0 ≤ C)
    (hderiv : ∀ x ∈ Set.Icc (A : ℝ) Z, HasDerivAt F (F' x) x)
    (hbound : ∀ x ∈ Set.Icc (A : ℝ) Z, ‖F' x‖ ≤ C) :
    ‖(∑ n ∈ Finset.Ico A Z, F n) - ∫ x in (A : ℝ)..(Z : ℝ), F x‖ ≤
      ((Z - A : ℕ) : ℝ) * C := by
  have hsub (n : ℕ) (hn : n ∈ Finset.Ico A Z) :
      Set.Icc (n : ℝ) ((n : ℝ) + 1) ⊆ Set.Icc (A : ℝ) Z := by
    have hnRange := Finset.mem_Ico.mp hn
    have hlo : (A : ℝ) ≤ n := by exact_mod_cast hnRange.1
    have hhi : (n : ℝ) + 1 ≤ Z := by exact_mod_cast (show n + 1 ≤ Z by omega)
    intro x hx
    exact ⟨hlo.trans hx.1, hx.2.trans hhi⟩
  have hInt : ∀ n ∈ Set.Ico A Z,
      IntervalIntegrable F volume (n : ℝ) ((n + 1 : ℕ) : ℝ) := by
    intro n hn
    have hc : ContinuousOn F (Set.Icc (n : ℝ) ((n : ℝ) + 1)) :=
      HasDerivAt.continuousOn (fun x hx ↦ hderiv x (hsub n (Finset.mem_Ico.mpr hn) hx))
    simpa only [Nat.cast_add, Nat.cast_one] using hc.intervalIntegrable_of_Icc (by linarith)
  have hsum : (∑ n ∈ Finset.Ico A Z, ∫ x in (n : ℝ)..(n : ℝ) + 1, F x) =
      ∫ x in (A : ℝ)..(Z : ℝ), F x := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      intervalIntegral.sum_integral_adjacent_intervals_Ico
        (f := F) (μ := volume) (a := fun n : ℕ ↦ (n : ℝ)) hAZ hInt
  calc
    _ = ‖∑ n ∈ Finset.Ico A Z, (F n - ∫ x in (n : ℝ)..(n : ℝ) + 1, F x)‖ := by
      rw [Finset.sum_sub_distrib, hsum]
    _ ≤ ∑ n ∈ Finset.Ico A Z, ‖F n - ∫ x in (n : ℝ)..(n : ℝ) + 1, F x‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Ico A Z, C := by
      apply Finset.sum_le_sum
      intro n hn
      exact mrNorm_cell_sum_sub_integral_le hC
        (fun x hx ↦ hderiv x (hsub n hn hx)) (fun x hx ↦ hbound x (hsub n hn hx))
    _ = _ := by simp

theorem mrNorm_sum_rounded_sub_integral_le {F F' : ℝ → ℂ} {a b B C : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hAZ : ⌈a⌉₊ ≤ ⌊b⌋₊) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hderiv : ∀ x ∈ Set.Icc a b, HasDerivAt F (F' x) x)
    (hbound : ∀ x ∈ Set.Icc a b, ‖F x‖ ≤ B)
    (hderivBound : ∀ x ∈ Set.Icc a b, ‖F' x‖ ≤ C) :
    ‖(∑ n ∈ Finset.Icc ⌈a⌉₊ ⌊b⌋₊, F n) - ∫ x in a..b, F x‖ ≤ C * (b - a) + 3 * B := by
  let A := ⌈a⌉₊
  let Z := ⌊b⌋₊
  have hAZR : (A : ℝ) ≤ Z := by exact_mod_cast hAZ
  have haA : a ≤ A := Nat.le_ceil a
  have hZb : (Z : ℝ) ≤ b := Nat.floor_le (ha.trans hab)
  have hAa : (A : ℝ) < a + 1 := Nat.ceil_lt_add_one ha
  have hbZ : b < (Z : ℝ) + 1 := Nat.lt_floor_add_one b
  have hcont : ContinuousOn F (Set.Icc a b) := HasDerivAt.continuousOn hderiv
  have hInt {x y : ℝ} (hax : a ≤ x) (hxy : x ≤ y) (hyb : y ≤ b) :
      IntervalIntegrable F volume x y :=
    (hcont.mono (Set.Icc_subset_Icc hax hyb)).intervalIntegrable_of_Icc hxy
  have hleftInt := hInt le_rfl haA (hAZR.trans hZb)
  have hmidInt := hInt haA hAZR hZb
  have hrightInt := hInt (haA.trans hAZR) hZb le_rfl
  have hmain : (∫ x in a..b, F x) =
      (∫ x in a..(A : ℝ), F x) + (∫ x in (A : ℝ)..(Z : ℝ), F x) +
        (∫ x in (Z : ℝ)..b, F x) := by
    rw [intervalIntegral.integral_add_adjacent_intervals hleftInt hmidInt,
      intervalIntegral.integral_add_adjacent_intervals (hleftInt.trans hmidInt) hrightInt]
  have hcell := mrNorm_sum_Ico_sub_integral_le hAZ hC
    (fun x hx ↦ hderiv x ⟨haA.trans hx.1, hx.2.trans hZb⟩)
    (fun x hx ↦ hderivBound x ⟨haA.trans hx.1, hx.2.trans hZb⟩)
  have hcell' : ‖(∑ n ∈ Finset.Ico A Z, F n) -
      ∫ x in (A : ℝ)..(Z : ℝ), F x‖ ≤ C * (b - a) := by
    apply hcell.trans
    rw [Nat.cast_sub hAZ]
    nlinarith
  have hleft : ‖∫ x in a..(A : ℝ), F x‖ ≤ B := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (C := B) (f := F)
      (a := a) (b := (A : ℝ)) (by
        intro x hx
        have hxI : x ∈ Set.Icc a (A : ℝ) := by
          simpa only [Set.uIcc_of_le haA] using Set.uIoc_subset_uIcc hx
        exact hbound x ⟨hxI.1, hxI.2.trans (hAZR.trans hZb)⟩)
    rw [abs_of_nonneg (sub_nonneg.mpr haA)] at hh
    exact hh.trans (by nlinarith)
  have hright : ‖∫ x in (Z : ℝ)..b, F x‖ ≤ B := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (C := B) (f := F)
      (a := (Z : ℝ)) (b := b) (by
        intro x hx
        have hxI : x ∈ Set.Icc (Z : ℝ) b := by
          simpa only [Set.uIcc_of_le hZb] using Set.uIoc_subset_uIcc hx
        exact hbound x ⟨(haA.trans hAZR).trans hxI.1, hxI.2⟩)
    rw [abs_of_nonneg (sub_nonneg.mpr hZb)] at hh
    exact hh.trans (by nlinarith)
  have hterminal : ‖F Z‖ ≤ B := hbound Z ⟨haA.trans hAZR, hZb⟩
  have hsum : (∑ n ∈ Finset.Icc A Z, F n) = (∑ n ∈ Finset.Ico A Z, F n) + F Z := by
    have hset : Finset.Icc A Z = Finset.Ico A (Z + 1) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hset, Finset.sum_Ico_succ_top hAZ]
  have heq : (∑ n ∈ Finset.Icc A Z, F n) - (∫ x in a..b, F x) =
      (((∑ n ∈ Finset.Ico A Z, F n) - (∫ x in (A : ℝ)..(Z : ℝ), F x)) + F Z) -
        (∫ x in a..(A : ℝ), F x) - (∫ x in (Z : ℝ)..b, F x) := by
    rw [hsum, hmain]
    ring
  change ‖(∑ n ∈ Finset.Icc A Z, F n) - (∫ x in a..b, F x)‖ ≤ _
  rw [heq]
  calc
    _ ≤ ‖((∑ n ∈ Finset.Ico A Z, F n) - (∫ x in (A : ℝ)..(Z : ℝ), F x)) + F Z -
        (∫ x in a..(A : ℝ), F x)‖ + ‖∫ x in (Z : ℝ)..b, F x‖ := norm_sub_le _ _
    _ ≤ (‖((∑ n ∈ Finset.Ico A Z, F n) - (∫ x in (A : ℝ)..(Z : ℝ), F x)) + F Z‖ +
        ‖∫ x in a..(A : ℝ), F x‖) + ‖∫ x in (Z : ℝ)..b, F x‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ ((‖(∑ n ∈ Finset.Ico A Z, F n) - (∫ x in (A : ℝ)..(Z : ℝ), F x)‖ + ‖F Z‖) +
        ‖∫ x in a..(A : ℝ), F x‖) + ‖∫ x in (Z : ℝ)..b, F x‖ :=
      add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
    _ ≤ ((C * (b - a) + B) + B) + B :=
      add_le_add (add_le_add (add_le_add hcell' hterminal) hleft) hright
    _ = _ := by ring

end

end Erdos67b
