/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.MediumRangeInfrastructure
import ErdosProblems.Erdos387.RoughHarmonicEstimate

/-! # Reciprocal mass in a fixed smooth-part class -/

namespace Erdos822

open scoped BigOperators Classical

theorem exists_roughReciprocalMass_le_const_log_ratio :
    ∃ A : ℝ, 0 < A ∧ ∀ z T : ℕ, 2 ≤ z → z ≤ T →
      Erdos387.roughReciprocalMass z T ≤ A * (Real.log T / Real.log z) := by
  obtain ⟨K, hK, hbound⟩ := Erdos387.RoughHarmonic.exists_uniform_roughReciprocalMass_le_log_ratio
  let B := |K + BoundedGaps.Maynard.primeLogDivisorMass 1 + Real.log 2|
  let E := |2 * (Real.exp 16 + 4 * BoundedGaps.Maynard.reciprocalTotientCorrectionQuarterConstant)|
  let D := 10 * (B / Real.log 2 + 1) + E
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hB : 0 ≤ B := abs_nonneg _
  have hE : 0 ≤ E := abs_nonneg _
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨1 + D, by positivity, ?_⟩
  intro z T hz hzT
  have hzR : (2 : ℝ) ≤ z := by exact_mod_cast hz
  have hlogz : 0 < Real.log (z : ℝ) := Real.log_pos (by linarith)
  have h2z : Real.log (2 : ℝ) ≤ Real.log (z : ℝ) := Real.log_le_log (by norm_num) hzR
  have hprev : Real.log (z - 1 : ℕ) ≤ Real.log (z : ℝ) :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < z - 1))
      (by exact_mod_cast Nat.sub_le z 1)
  have hKbound : K + Real.log (z - 1 : ℕ) +
      BoundedGaps.Maynard.primeLogDivisorMass 1 + Real.log 2 ≤ B + Real.log (z : ℝ) := by
    have h := le_abs_self (K + BoundedGaps.Maynard.primeLogDivisorMass 1 + Real.log 2)
    dsimp [B]
    linarith only [h, hprev]
  have hquot : (K + Real.log (z - 1 : ℕ) +
      BoundedGaps.Maynard.primeLogDivisorMass 1 + Real.log 2) / Real.log (z : ℝ) ≤
      B / Real.log 2 + 1 := by
    calc
      _ ≤ (B + Real.log (z : ℝ)) / Real.log (z : ℝ) := div_le_div_of_nonneg_right hKbound hlogz.le
      _ = B / Real.log (z : ℝ) + 1 := by rw [add_div, div_self hlogz.ne']
      _ ≤ _ := add_le_add (div_le_div_of_nonneg_left hB hlog2 h2z) le_rfl
  have hratio : 1 ≤ Real.log (T : ℝ) / Real.log (z : ℝ) :=
    (le_div_iff₀ hlogz).mpr (by
      simpa using Real.log_le_log (by exact_mod_cast (by omega : 0 < z)) (by exact_mod_cast hzT))
  have htotal := hbound z T hz
  have hEbound := le_abs_self (2 * (Real.exp 16 +
    4 * BoundedGaps.Maynard.reciprocalTotientCorrectionQuarterConstant))
  calc
    _ ≤ Real.log (T : ℝ) / Real.log (z : ℝ) + D := by
      dsimp [D, E]
      linarith only [htotal, hquot, hEbound]
    _ ≤ Real.log (T : ℝ) / Real.log (z : ℝ) + D * (Real.log (T : ℝ) / Real.log (z : ℝ)) :=
      add_le_add le_rfl (le_mul_of_one_le_right hD hratio)
    _ = _ := by ring

theorem sum_inv_smoothClass_le_roughMass {B : Finset ℕ} {N d y : ℕ}
    (hBpos : ∀ n ∈ B, 0 < n) (hBle : ∀ n ∈ B, n ≤ N)
    (hclass : ∀ n ∈ B, smoothPart n y = d) :
    (∑ n ∈ B, (1 : ℝ) / n) ≤ (1 : ℝ) / d * Erdos387.roughReciprocalMass (y + 1) N := by
  have hfactor (n : ℕ) (hn : n ∈ B) : d * roughPart n y = n := by
    rw [← hclass n hn]
    exact smoothPart_mul_roughPart (hBpos n hn).ne'
  have hinj : Set.InjOn (fun n ↦ roughPart n y) B := by
    intro a ha b hb heq
    change roughPart a y = roughPart b y at heq
    rw [← hfactor a ha, ← hfactor b hb, heq]
  have himage : B.image (fun n ↦ roughPart n y) ⊆ Erdos387.roughPositiveUpTo (y + 1) N := by
    intro t ht
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ht
    apply Erdos387.mem_roughPositiveUpTo_iff.mpr
    refine ⟨Nat.pos_of_ne_zero (roughPart_ne_zero n y),
      (Nat.le_of_dvd (hBpos n hn) (roughPart_dvd n y)).trans (hBle n hn), ?_⟩
    intro p hp hpy hpdvd
    have hgt := prime_dvd_roughPart_gt hp hpdvd
    omega
  calc
    _ = (1 : ℝ) / d * ∑ n ∈ B, (1 : ℝ) / roughPart n y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      conv_lhs => rw [← hfactor n hn]
      push_cast
      ring
    _ = (1 : ℝ) / d * ∑ t ∈ B.image (fun n ↦ roughPart n y), (1 : ℝ) / t := by
      rw [Finset.sum_image hinj]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg himage (fun t ht hnot ↦ by positivity)) (by positivity)

#print axioms exists_roughReciprocalMass_le_const_log_ratio
#print axioms sum_inv_smoothClass_le_roughMass

theorem exists_sum_inv_smoothClass_le_log_ratio :
    ∃ A : ℝ, 0 < A ∧ ∀ (B : Finset ℕ) (N d y : ℕ), 1 ≤ y → y + 1 ≤ N →
      (∀ n ∈ B, 0 < n) → (∀ n ∈ B, n ≤ N) → (∀ n ∈ B, smoothPart n y = d) →
      (∑ n ∈ B, (1 : ℝ) / n) ≤ A * Real.log (N : ℝ) / ((d : ℝ) * Real.log (y + 1 : ℕ)) := by
  obtain ⟨A, hA, hmass⟩ := exists_roughReciprocalMass_le_const_log_ratio
  refine ⟨A, hA, ?_⟩
  intro B N d y hy hyN hBpos hBle hclass
  calc
    _ ≤ (1 : ℝ) / d * Erdos387.roughReciprocalMass (y + 1) N :=
      sum_inv_smoothClass_le_roughMass hBpos hBle hclass
    _ ≤ (1 : ℝ) / d * (A * (Real.log (N : ℝ) / Real.log (y + 1 : ℕ))) :=
      mul_le_mul_of_nonneg_left (hmass (y + 1) N (by omega) hyN) (by positivity)
    _ = _ := by ring

#print axioms exists_sum_inv_smoothClass_le_log_ratio

end Erdos822
