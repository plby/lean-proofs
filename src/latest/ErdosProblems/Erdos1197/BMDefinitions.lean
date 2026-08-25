import ErdosProblems.Erdos1197.PNTBridge
import ErdosProblems.Erdos1197.TorusSeparation

namespace Erdos1197

open Chebyshev
open MeasureTheory Set
open scoped Asymptotics BigOperators Chebyshev ENNReal

noncomputable section

/-- `I_∞ = [16/25, 2/3]`, the interval on which the covering property fails. -/
def I_inf : Set ℝ := Icc (16/25 : ℝ) (2/3)

abbrev PrimeIdx (k : ℕ) := Fin (2 ^ k)

abbrev IntIdx (ν : ℕ) := Fin (2 ^ (ν - 2) + 1)

abbrev BMIdx (k ν : ℕ) := PrimeIdx k ⊕ IntIdx ν

/-- The BM integer block is the full interval of consecutive integers
`[7 * 2^(ν-3), 9 * 2^(ν-3)]`. -/
def bmIntVal (ν : ℕ) (j : IntIdx ν) : ℕ :=
  7 * 2 ^ (ν - 3) + j.1

/-- Positive part of an integer coefficient, viewed as a natural-number exponent. -/
abbrev zpos (z : ℤ) : ℕ := Int.toNat z

/-- Negative part of an integer coefficient, viewed as a natural-number exponent. -/
abbrev zneg (z : ℤ) : ℕ := Int.toNat (-z)

lemma zpos_sub_zneg (z : ℤ) : (zpos z : ℤ) - zneg z = z := by
  simp [zpos, zneg]

lemma cast_zpos_sub_zneg (z : ℤ) : (zpos z : ℝ) - zneg z = z := by
  exact_mod_cast zpos_sub_zneg z

lemma zpos_eq_zero_of_nonpos {z : ℤ} (hz : z ≤ 0) : zpos z = 0 := by
  simp [zpos, Int.toNat_of_nonpos hz]

lemma zneg_eq_zero_of_nonneg {z : ℤ} (hz : 0 ≤ z) : zneg z = 0 := by
  simp [zneg, Int.toNat_of_nonpos (neg_nonpos.mpr hz)]

lemma zpos_pos_of_pos {z : ℤ} (hz : 0 < z) : 0 < zpos z := by
  have hz' : (0 : ℤ) < z.toNat := by
    rw [Int.toNat_of_nonneg hz.le]
    exact hz
  exact_mod_cast hz'

lemma zneg_pos_of_neg {z : ℤ} (hz : z < 0) : 0 < zneg z := by
  have hneg : 0 < -z := by simpa using neg_pos.mpr hz
  have hneg' : (0 : ℤ) < (-z).toNat := by
    rw [Int.toNat_of_nonneg hneg.le]
    exact hneg
  simpa [zneg] using hneg'

lemma logb_nat_finset_prod_pow
    {α : Type*} (s : Finset α) (f : α → ℕ) (e : α → ℕ)
    (hf : ∀ a ∈ s, f a ≠ 0) :
    Real.logb 2 ((∏ a ∈ s, f a ^ e a : ℕ) : ℝ) =
      ∑ a ∈ s, (e a : ℝ) * Real.logb 2 (f a : ℝ) := by
  have hpow_ne :
      ∀ a ∈ s, (((f a) ^ e a : ℕ) : ℝ) ≠ 0 := by
    intro a ha
    exact_mod_cast pow_ne_zero _ (hf a ha)
  rw [Nat.cast_prod, Real.logb_prod]
  · simp_rw [Nat.cast_pow, Real.logb_pow]
  · simpa using hpow_ne

lemma logb_nat_fintype_prod_pow
    {α : Type*} [Fintype α] (f : α → ℕ) (e : α → ℕ)
    (hf : ∀ a, f a ≠ 0) :
    Real.logb 2 ((∏ a, f a ^ e a : ℕ) : ℝ) =
      ∑ a, (e a : ℝ) * Real.logb 2 (f a : ℝ) := by
  simpa using logb_nat_finset_prod_pow Finset.univ f e (fun a _ => hf a)

lemma logb_nat_fintype_prod_zparts
    {α : Type*} [Fintype α] (f : α → ℕ) (r : α → ℤ)
    (hf : ∀ a, f a ≠ 0) :
    Real.logb 2 ((∏ a, f a ^ zpos (r a) : ℕ) : ℝ) -
        Real.logb 2 ((∏ a, f a ^ zneg (r a) : ℕ) : ℝ) =
      ∑ a, (r a : ℝ) * Real.logb 2 (f a : ℝ) := by
  rw [logb_nat_fintype_prod_pow f (fun a => zpos (r a)) hf,
    logb_nat_fintype_prod_pow f (fun a => zneg (r a)) hf]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro a ha
  have hz : (zpos (r a) : ℝ) - zneg (r a) = r a := cast_zpos_sub_zneg (r a)
  calc
    (zpos (r a) : ℝ) * Real.logb 2 (f a : ℝ) -
        (zneg (r a) : ℝ) * Real.logb 2 (f a : ℝ)
      = ((zpos (r a) : ℝ) - zneg (r a)) * Real.logb 2 (f a : ℝ) := by ring
    _ = (r a : ℝ) * Real.logb 2 (f a : ℝ) := by rw [hz]

lemma logb_nat_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Real.logb 2 ((a * b : ℕ) : ℝ) = Real.logb 2 (a : ℝ) + Real.logb 2 (b : ℝ) := by
  rw [Nat.cast_mul, Real.logb_mul]
  · exact_mod_cast ha
  · exact_mod_cast hb

lemma bm_lower_endpoint (ν : ℕ) (hν : 3 ≤ ν) :
    ((7 : ℝ) / 8) * 2 ^ ν = 7 * 2 ^ (ν - 3) := by
  have hsplit : ν = (ν - 3) + 3 := by omega
  rw [hsplit, pow_add]
  norm_num
  ring

lemma bm_upper_endpoint (ν : ℕ) (hν : 3 ≤ ν) :
    ((9 : ℝ) / 8) * 2 ^ ν = 9 * 2 ^ (ν - 3) := by
  have hsplit : ν = (ν - 3) + 3 := by omega
  rw [hsplit, pow_add]
  norm_num
  ring

lemma bmIntVal_mem_Icc (ν : ℕ) (hν : 3 ≤ ν) (j : IntIdx ν) :
    (bmIntVal ν j : ℝ) ∈
      Icc (((7 : ℝ) / 8) * 2 ^ ν) (((9 : ℝ) / 8) * 2 ^ ν) := by
  constructor
  · rw [bm_lower_endpoint ν hν]
    exact_mod_cast Nat.le_add_right _ _
  · rw [bm_upper_endpoint ν hν]
    have hj : j.1 ≤ 2 ^ (ν - 2) := Nat.lt_succ_iff.mp j.2
    have hpow : (2 : ℝ) ^ (ν - 2) = (2 : ℝ) ^ (ν - 3) * 2 := by
      have hsplit : ν - 2 = (ν - 3) + 1 := by omega
      rw [hsplit, pow_add]
      norm_num
    calc
      (bmIntVal ν j : ℝ) = 7 * 2 ^ (ν - 3) + j.1 := by
        simp [bmIntVal, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
      _ ≤ 7 * 2 ^ (ν - 3) + 2 ^ (ν - 2) := by
        gcongr
        exact_mod_cast hj
      _ = 9 * 2 ^ (ν - 3) := by
        rw [hpow]
        ring

/-- Every integer in the open BM integer window occurs in the enumerated integer block. -/
lemma exists_bmIntVal_eq_of_mem_Ioo (ν : ℕ) (hν : 3 ≤ ν) {n : ℕ}
    (hn : (n : ℝ) ∈ Ioo (((7 : ℝ) / 8) * 2 ^ ν) (((9 : ℝ) / 8) * 2 ^ ν)) :
    ∃ j : IntIdx ν, bmIntVal ν j = n := by
  rw [bm_lower_endpoint ν hν, bm_upper_endpoint ν hν] at hn
  have hlow : 7 * 2 ^ (ν - 3) < n := by exact_mod_cast hn.1
  have hhigh : n < 9 * 2 ^ (ν - 3) := by exact_mod_cast hn.2
  refine ⟨⟨n - 7 * 2 ^ (ν - 3), ?_⟩, ?_⟩
  · have hpow : 2 ^ (ν - 2) = 2 ^ (ν - 3) * 2 := by
      have hsplit : ν - 2 = (ν - 3) + 1 := by omega
      rw [hsplit, pow_add]
      norm_num
    omega
  · simp [bmIntVal, Nat.add_sub_of_le (Nat.le_of_lt hlow)]

end

end Erdos1197
