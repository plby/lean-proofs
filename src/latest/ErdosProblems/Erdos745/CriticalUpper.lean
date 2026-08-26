import ErdosProblems.Erdos745.ComponentUpper
import ErdosProblems.Erdos745.CriticalLower

/-! # Critical upper tightness and the two-sided critical order theorem -/

open Filter
open scoped Topology

namespace Erdos745

theorem criticalScale_pos {n : ℕ} (hn : 0 < n) : 0 < criticalScale n := by
  unfold criticalScale
  positivity

theorem criticalScale_mul_sqrt (n : ℕ) :
    criticalScale n * Real.sqrt (criticalScale n) = n := by
  have hs := criticalScale_nonneg n
  have hb := Real.sqrt_nonneg (criticalScale n)
  have heq : (criticalScale n * Real.sqrt (criticalScale n)) ^ 2 = (n : ℝ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hs]
    convert criticalScale_cube n using 1 <;> ring
  nlinarith [Nat.cast_nonneg (α := ℝ) n, mul_nonneg hs hb]

theorem critical_tail_scale_bound {n k h : ℕ} (hn : 0 < n) {C : ℝ} (hC : 1 ≤ C)
    (hk : C * criticalScale n ≤ (k : ℝ))
    (hh : (h : ℝ) ≤ Real.sqrt (criticalScale n))
    (hh1 : Real.sqrt (criticalScale n) ≤ (h : ℝ) + 1) :
    (n : ℝ) / k * ((1 / pathHeightDecay) / ((h : ℝ) + 1) + (h : ℝ) / k) ≤
      (1 / pathHeightDecay + 1) / C := by
  let s := criticalScale n
  let b := Real.sqrt s
  let D := 1 / pathHeightDecay
  have hs : 0 < s := criticalScale_pos hn
  have hb : 0 < b := Real.sqrt_pos.mpr hs
  have hD : 0 < D := one_div_pos.mpr pathHeightDecay_pos
  have hC0 : 0 < C := by linarith
  have hCs : 0 < C * s := mul_pos hC0 hs
  have hsk : s ≤ (k : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hC hs.le
    change C * s ≤ (k : ℝ) at hk
    nlinarith
  have hk0 : (0 : ℝ) < k := hs.trans_le hsk
  have hb2 : b ^ 2 = s := Real.sq_sqrt hs.le
  have hnb : (n : ℝ) = s * b := (criticalScale_mul_sqrt n).symm
  have hfirst : D / ((h : ℝ) + 1) ≤ D / b :=
    div_le_div_of_nonneg_left hD.le hb hh1
  have hsecond : (h : ℝ) / k ≤ 1 / b := by
    apply (div_le_div_of_nonneg_right hh hk0.le).trans
    apply (div_le_div_iff₀ hk0 hb).mpr
    nlinarith
  have hleft : (n : ℝ) / k ≤ (n : ℝ) / (C * s) :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg _) hCs hk
  change (n : ℝ) / k * (D / ((h : ℝ) + 1) + (h : ℝ) / k) ≤ (D + 1) / C
  calc
    _ ≤ (n : ℝ) / (C * s) * (D / b + 1 / b) :=
      mul_le_mul hleft (add_le_add hfirst hsecond)
        (by positivity) (by positivity)
    _ = (D + 1) / C := by
      rw [hnb]
      field_simp

theorem critical_upper_tightness : CriticalUpperTightness := by
  intro ε hε
  let C := max 1 ((1 / pathHeightDecay + 1) / ε)
  have hC : 1 ≤ C := le_max_left _ _
  have hC0 : 0 < C := by linarith
  have herror : (1 / pathHeightDecay + 1) / C ≤ ε := by
    rw [div_le_iff₀ hC0]
    have h := le_max_right 1 ((1 / pathHeightDecay + 1) / ε)
    change (1 / pathHeightDecay + 1) / ε ≤ C at h
    have := (div_le_iff₀ hε).mp h
    linarith
  refine ⟨C, hC0, ?_⟩
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn0 : 0 < n := by omega
  let k : ℕ := ⌈C * criticalScale n⌉₊
  let h : ℕ := ⌊Real.sqrt (criticalScale n)⌋₊
  have hk : C * criticalScale n ≤ (k : ℝ) := Nat.le_ceil _
  have hk0 : 0 < k := by
    have hprod := mul_pos hC0 (criticalScale_pos hn0)
    have : (0 : ℝ) < k := hprod.trans_le hk
    exact_mod_cast this
  have hh : (h : ℝ) ≤ Real.sqrt (criticalScale n) := Nat.floor_le (Real.sqrt_nonneg _)
  have hh1 : Real.sqrt (criticalScale n) ≤ (h : ℝ) + 1 := (Nat.lt_floor_add_one _).le
  have htail := (critical_secondLargest_tail hn hk0 h).trans
    ((critical_tail_scale_bound hn0 hC hk hh hh1).trans herror)
  have hbad : probability 1 n (fun G ↦ ¬ secondOrder n G ≤ C * criticalScale n) ≤ ε := by
    apply (probability_mono (fun G hG ↦ ?_)).trans htail
    apply Nat.ceil_le.mpr
    change C * criticalScale n ≤ (secondLargestComponentOrder G : ℝ)
    exact (lt_of_not_ge hG).le
  rw [probability_not, probability_one] at hbad
  linarith

/-- At exactly `p = 1/n`, the second-largest component has order `n^(2/3)`
in probability, with positive constants chosen for each error tolerance. -/
theorem critical_secondLargest_scaling : CriticalSecondLargestScaling :=
  criticalSecondLargestScaling_of_tightness critical_lower_tightness critical_upper_tightness

end Erdos745
