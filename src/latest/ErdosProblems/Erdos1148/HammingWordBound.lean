import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # An exponential bound for families of words with few mismatches -/

namespace Erdos1148.DukeArithmetic

def wordMismatchCount {α : Type*} [DecidableEq α] {n : ℕ} (v w : Fin n → α) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => w i ≠ v i)).card

lemma pow_wordMismatchCount {α : Type*} [DecidableEq α] {n : ℕ} (v w : Fin n → α) (t : ℝ) :
    t ^ wordMismatchCount v w = ∏ i : Fin n, if w i ≠ v i then t else 1 := by
  rw [← Finset.prod_filter]
  simp only [wordMismatchCount, Finset.prod_const]

theorem sum_pow_wordMismatchCount_le {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (v : Fin n → α) {t : ℝ} (ht : 0 ≤ t) :
    (∑ w : Fin n → α, t ^ wordMismatchCount v w) ≤ (1 + (Fintype.card α : ℝ) * t) ^ n := by
  have hterm (i : Fin n) : (∑ a : α, if a ≠ v i then t else 1) ≤ 1 + (Fintype.card α : ℝ) * t := by
    calc
      _ ≤ ∑ a : α, (t + if a = v i then 1 else 0) := by
        apply Finset.sum_le_sum
        intro a _
        by_cases ha : a = v i <;> simp [ha, ht]
      _ = _ := by simp [Finset.sum_add_distrib, add_comm]
  simp_rw [pow_wordMismatchCount]
  rw [← Fintype.prod_sum (fun (i : Fin n) (a : α) => if a ≠ v i then t else 1)]
  calc
    (∏ i : Fin n, ∑ a : α, if a ≠ v i then t else 1) ≤
        ∏ _i : Fin n, (1 + (Fintype.card α : ℝ) * t) := by
      apply Finset.prod_le_prod
      · intro i _
        exact Finset.sum_nonneg (fun a _ => by split_ifs <;> positivity)
      · exact fun i _ => hterm i
    _ = _ := by simp

theorem mismatch_family_card_bound {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (v : Fin n → α) (F : Finset (Fin n → α)) {τ t : ℝ}
    (ht : 0 < t) (htone : t ≤ 1)
    (hF : ∀ w ∈ F, (wordMismatchCount v w : ℝ) ≤ τ * n) :
    (F.card : ℝ) ≤ Real.exp ((n : ℝ) * ((Fintype.card α : ℝ) * t - τ * Real.log t)) := by
  have hlog : Real.log t ≤ 0 := Real.log_nonpos ht.le htone
  have hweight (w : Fin n → α) (hw : w ∈ F) :
      Real.exp (τ * n * Real.log t) ≤ t ^ wordMismatchCount v w := by
    have h := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right (hF w hw) hlog)
    simpa only [Real.exp_nat_mul, Real.exp_log ht] using h
  have hsum : (F.card : ℝ) * Real.exp (τ * n * Real.log t) ≤
      Real.exp ((n : ℝ) * ((Fintype.card α : ℝ) * t)) := by
    calc
      _ = ∑ _w ∈ F, Real.exp (τ * n * Real.log t) := by simp
      _ ≤ ∑ w ∈ F, t ^ wordMismatchCount v w := Finset.sum_le_sum (fun w hw => hweight w hw)
      _ ≤ ∑ w : Fin n → α, t ^ wordMismatchCount v w :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
          (fun _ _ _ => pow_nonneg ht.le _)
      _ ≤ (1 + (Fintype.card α : ℝ) * t) ^ n := sum_pow_wordMismatchCount_le v ht.le
      _ ≤ Real.exp ((Fintype.card α : ℝ) * t) ^ n := by
        apply pow_le_pow_left₀ (by positivity)
        simpa only [add_comm] using Real.add_one_le_exp ((Fintype.card α : ℝ) * t)
      _ = _ := (Real.exp_nat_mul _ _).symm
  apply ((le_div_iff₀ (Real.exp_pos _)).mpr hsum).trans_eq
  rw [← Real.exp_sub]
  congr 1
  ring

theorem exists_small_mismatch_family_bound (α : Type*) [Fintype α] [DecidableEq α]
    {ε : ℝ} (hε : 0 < ε) : ∃ τ : ℝ, 0 < τ ∧ ∀ (n : ℕ) (v : Fin n → α)
      (F : Finset (Fin n → α)),
      (∀ w ∈ F, (wordMismatchCount v w : ℝ) ≤ τ * n) →
      (F.card : ℝ) ≤ Real.exp (ε * n) := by
  let q : ℝ := Fintype.card α
  have hq : 0 ≤ q := Nat.cast_nonneg _
  let t := min (1 / 2 : ℝ) (ε / (4 * (q + 1)))
  have ht : 0 < t := lt_min (by norm_num) (by positivity)
  have htone : t ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have htbound : t * (4 * (q + 1)) ≤ ε :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  let τ := ε / (4 * (1 + |Real.log t|))
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  have hτeq : τ * (4 * (1 + |Real.log t|)) = ε := by
    dsimp only [τ]
    field_simp
  have hrate : q * t - τ * Real.log t ≤ ε := by
    have habs := neg_le_abs (Real.log t)
    have hlogbound := mul_le_mul_of_nonneg_left habs hτ.le
    nlinarith only [htbound, hτeq, hlogbound, ht, hτ, hε]
  refine ⟨τ, hτ, ?_⟩
  intro n v F hF
  exact (mismatch_family_card_bound v F ht htone hF).trans (Real.exp_le_exp.mpr (by
    have h := mul_le_mul_of_nonneg_left hrate (Nat.cast_nonneg n)
    simpa only [mul_comm (n : ℝ) ε] using h))

end Erdos1148.DukeArithmetic
