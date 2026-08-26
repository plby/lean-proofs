import ErdosProblems.Erdos69.PatternShifts
import ErdosProblems.Erdos69.CompositeTails

/-! # Grouping the retained terms by their actual shift -/

open scoped BigOperators

namespace Erdos69.Elementary

abbrev PatternTerm (m H : ℕ) := PatternLabel m × Fin H

def termShift (m P H : ℕ) (t : PatternTerm m H) : ℕ :=
  patternShift m P t.1 (6 * m + 1 + t.2.val)

noncomputable def termCoefficient (m H : ℕ) (q : ℝ) (t : PatternTerm m H) : ℝ :=
  q * (patternSign m t.1 : ℝ) / 2 ^ (6 * m + 1 + t.2.val)

def retainedShifts (m P H : ℕ) : Finset ℕ := Finset.univ.image (termShift m P H)

noncomputable def shiftCoefficient (m P H : ℕ) (q : ℝ) (r : ℕ) : ℝ :=
  ∑ t : PatternTerm m H, if termShift m P H t = r then termCoefficient m H q t else 0

theorem termShift_mem (m P H : ℕ) (t : PatternTerm m H) :
    termShift m P H t ∈ retainedShifts m P H :=
  Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩

theorem sum_shiftCoefficient (m P H : ℕ) (q : ℝ) :
    (∑ r ∈ retainedShifts m P H, shiftCoefficient m P H q r) =
      ∑ t : PatternTerm m H, termCoefficient m H q t := by
  unfold shiftCoefficient
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  simp [termShift_mem]

theorem sum_termCoefficient {m : ℕ} (hm : 0 < m) (H : ℕ) (q : ℝ) :
    (∑ t : PatternTerm m H, termCoefficient m H q t) = 0 := by
  unfold termCoefficient
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k hk
  simp only [Prod.fst, Prod.snd]
  rw [← Finset.sum_div, ← Finset.mul_sum]
  have hs : (∑ i : PatternLabel m, (patternSign m i : ℝ)) = 0 := by
    exact_mod_cast sum_patternSign hm
  rw [hs, mul_zero, zero_div]

theorem sum_shiftCoefficient_zero {m : ℕ} (hm : 0 < m) (P H : ℕ) (q : ℝ) :
    (∑ r ∈ retainedShifts m P H, shiftCoefficient m P H q r) = 0 := by
  rw [sum_shiftCoefficient, sum_termCoefficient hm]

theorem abs_shiftCoefficient_mass_le (m P H : ℕ) (q : ℝ) :
    (∑ r ∈ retainedShifts m P H, |shiftCoefficient m P H q r|) ≤
      ∑ t : PatternTerm m H, |termCoefficient m H q t| := by
  calc
    _ ≤ ∑ r ∈ retainedShifts m P H,
        ∑ t : PatternTerm m H, |if termShift m P H t = r then termCoefficient m H q t else 0| :=
      Finset.sum_le_sum (fun r _ ↦ Finset.abs_sum_le_sum_abs _ _)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t ht
      simp [apply_ite abs, termShift_mem]

theorem finite_binary_tail_le (K H : ℕ) :
    (∑ k : Fin H, (1 : ℝ) / 2 ^ (K + 1 + k.val)) ≤ (1 : ℝ) / 2 ^ K := by
  have heq (k : ℕ) : (1 : ℝ) / 2 ^ (K + 1 + k) =
      (1 / 2 ^ K) * (1 / 2 ^ (k + 1)) := by
    rw [show K + 1 + k = K + (k + 1) by omega, pow_add]
    ring
  rw [Fin.sum_univ_eq_sum_range (fun k ↦ (1 : ℝ) / 2 ^ (K + 1 + k)) H]
  simp_rw [heq]
  rw [← Finset.mul_sum]
  have hb : (∑ k ∈ Finset.range H, (1 : ℝ) / 2 ^ (k + 1)) ≤ 1 := by
    calc
      _ ≤ ∑' k : ℕ, (1 : ℝ) / 2 ^ (k + 1) :=
        summable_binary_weights.sum_le_tsum (Finset.range H) (fun _ _ ↦ by positivity)
      _ = 1 := tsum_binary_weights
  simpa using mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ 1 / 2 ^ K)

theorem termCoefficient_mass_le (m H : ℕ) (q : ℝ) :
    (∑ t : PatternTerm m H, |termCoefficient m H q t|) ≤
      |q| * (36 : ℝ) ^ m / 2 ^ (6 * m) := by
  have heq : (∑ t : PatternTerm m H, |termCoefficient m H q t|) =
      |q| * (36 : ℝ) ^ m * ∑ k : Fin H, (1 : ℝ) / 2 ^ (6 * m + 1 + k.val) := by
    simp [termCoefficient, Fintype.sum_prod_type, abs_div, abs_mul,
      patternSign_abs_real, ← Finset.mul_sum, card_patternLabel, div_eq_mul_inv,
      mul_assoc, mul_left_comm]
  rw [heq]
  have h := mul_le_mul_of_nonneg_left (finite_binary_tail_le (6 * m) H)
    (by positivity : 0 ≤ |q| * (36 : ℝ) ^ m)
  simpa only [mul_one_div] using h

theorem shiftCoefficient_mass_le (m P H : ℕ) (q : ℝ) :
    (∑ r ∈ retainedShifts m P H, |shiftCoefficient m P H q r|) ≤
      |q| * (9 / 16 : ℝ) ^ m := by
  have h := (abs_shiftCoefficient_mass_le m P H q).trans (termCoefficient_mass_le m H q)
  rwa [mul_div_assoc, pattern_mass_ratio] at h

theorem retainedShifts_card_le (m P H : ℕ) :
    (retainedShifts m P H).card ≤ 36 ^ m * H := by
  have h := Finset.card_image_le (f := termShift m P H) (s := Finset.univ)
  simpa only [retainedShifts, Finset.card_univ, Fintype.card_prod, card_patternLabel,
    Fintype.card_fin] using h

theorem termShift_eq_minimal_iff (m P H : ℕ) (t : PatternTerm m H) :
    termShift m P H t = (primorial P + 1) * (6 * m + 1) ↔
      t.1 = patternZero m ∧ t.2.val = 0 := by
  rw [termShift, patternShift_eq_minimal_iff (by omega)]
  simp

theorem minimal_mem_retainedShifts (m P H : ℕ) (hH : 0 < H) :
    (primorial P + 1) * (6 * m + 1) ∈ retainedShifts m P H := by
  apply Finset.mem_image.mpr
  refine ⟨(patternZero m, ⟨0, hH⟩), Finset.mem_univ _, ?_⟩
  exact (termShift_eq_minimal_iff m P H _).mpr ⟨rfl, rfl⟩

theorem shiftCoefficient_minimal (m P H : ℕ) (hH : 0 < H) (q : ℝ) :
    shiftCoefficient m P H q ((primorial P + 1) * (6 * m + 1)) =
      q / 2 ^ (6 * m + 1) := by
  classical
  unfold shiftCoefficient
  simp_rw [termShift_eq_minimal_iff]
  rw [Fintype.sum_prod_type]
  let z : Fin H := ⟨0, hH⟩
  have hz (k : Fin H) : k.val = 0 ↔ k = z := by
    exact ⟨fun h ↦ Fin.ext h, fun h ↦ congrArg Fin.val h⟩
  simp only [hz]
  simp [termCoefficient, z, ite_and]

theorem sum_grouped_shift_test (m P H : ℕ) (q : ℝ) (f : ℕ → ℝ) :
    (∑ r ∈ retainedShifts m P H, shiftCoefficient m P H q r * f r) =
      ∑ t : PatternTerm m H, termCoefficient m H q t * f (termShift m P H t) := by
  unfold shiftCoefficient
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [ite_mul, zero_mul]
  simp [termShift_mem]

end Erdos69.Elementary
