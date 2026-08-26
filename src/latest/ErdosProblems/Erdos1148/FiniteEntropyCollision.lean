import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Shannon entropy is bounded below by the logarithm of collision mass -/

namespace Erdos1148.DukeArithmetic

noncomputable def finiteEntropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (p i)

lemma finite_collision_pos_of_sum_pos {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hsum : 0 < ∑ i, p i) : 0 < ∑ i, p i ^ 2 := by
  classical
  have hex : ∃ i, p i ≠ 0 := by
    by_contra h
    push Not at h
    simp only [h, Finset.sum_const_zero] at hsum
    norm_num at hsum
  obtain ⟨i, hi⟩ := hex
  exact (sq_pos_of_ne_zero hi).trans_le
    (Finset.single_le_sum (fun j _ => sq_nonneg (p j)) (Finset.mem_univ i))

lemma finite_collision_pos {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hsum : ∑ i, p i = 1) : 0 < ∑ i, p i ^ 2 :=
  finite_collision_pos_of_sum_pos (by rw [hsum]; norm_num)

theorem neg_log_collision_le_finiteEntropy {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    -Real.log (∑ i, p i ^ 2) ≤ finiteEntropy p := by
  let B : ℝ := ∑ i, p i ^ 2
  have hB : 0 < B := finite_collision_pos hsum
  have hpoint (i : ι) :
      p i * Real.log (p i) - p i * Real.log B ≤ p i ^ 2 / B - p i := by
    rcases eq_or_lt_of_le (hp i) with hi | hi
    · simp [← hi]
    · have hlog := Real.log_le_sub_one_of_pos (div_pos hi hB)
      rw [Real.log_div hi.ne' hB.ne'] at hlog
      calc
        _ = p i * (Real.log (p i) - Real.log B) := by ring
        _ ≤ p i * (p i / B - 1) := mul_le_mul_of_nonneg_left hlog (hp i)
        _ = _ := by ring
  have htotal := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  have hBsum : (∑ i, p i ^ 2) = B := rfl
  simp only [Finset.sum_sub_distrib, div_eq_mul_inv, ← Finset.sum_mul, hsum, hBsum,
    one_mul, mul_inv_cancel₀ hB.ne', sub_self] at htotal
  have hentropy : finiteEntropy p = -(∑ i, p i * Real.log (p i)) := by
    simp only [finiteEntropy, Real.negMulLog, neg_mul, Finset.sum_neg_distrib]
  rw [hentropy]
  linarith

end Erdos1148.DukeArithmetic
