import ErdosProblems.Erdos1148.FiniteEntropyBounds

/-! # Entropy bounds from subprobability comparison weights -/

namespace Erdos1148.DukeArithmetic

theorem finiteEntropy_le_crossEntropy_of_sum_le {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (hpsum : ∑ i, p i = 1) (hqsum : ∑ i, q i ≤ 1) :
    finiteEntropy p ≤ -(∑ i, p i * Real.log (q i)) := by
  have hpoint (i : ι) : p i * Real.log (q i) - p i * Real.log (p i) ≤ q i - p i := by
    rcases eq_or_lt_of_le (hp i) with hi | hi
    · simpa only [← hi, zero_mul, sub_zero] using (hq i).le
    · have hlog := Real.log_le_sub_one_of_pos (div_pos (hq i) hi)
      rw [Real.log_div (hq i).ne' hi.ne'] at hlog
      calc
        _ = p i * (Real.log (q i) - Real.log (p i)) := by ring
        _ ≤ p i * (q i / p i - 1) := mul_le_mul_of_nonneg_left hlog (hp i)
        _ = q i - p i := by field_simp
  have htotal := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  simp only [Finset.sum_sub_distrib, hpsum] at htotal
  rw [finiteEntropy_eq_neg_sum_mul_log]
  linarith only [htotal, hqsum]

theorem finiteEntropy_le_classification_bound {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (c : ι → κ) (B : κ → ℝ) (hB : ∀ j, 0 < B j) (hκ : 0 < Fintype.card κ)
    (hcard : ∀ j, ((Finset.univ.filter (fun i : ι => c i = j)).card : ℝ) ≤ B j)
    {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1) :
    finiteEntropy p ≤ Real.log (Fintype.card κ) + ∑ i, p i * Real.log (B (c i)) := by
  classical
  have hm : (0 : ℝ) < Fintype.card κ := by exact_mod_cast hκ
  let q : ι → ℝ := fun i => 1 / ((Fintype.card κ : ℝ) * B (c i))
  have hq (i : ι) : 0 < q i := one_div_pos.mpr (mul_pos hm (hB (c i)))
  have hterm (j : κ) : (∑ i : ι, if c i = j then q i else 0) ≤ 1 / (Fintype.card κ : ℝ) := by
    rw [← Finset.sum_filter]
    have heq : (∑ i ∈ Finset.univ.filter (fun i : ι => c i = j), q i) =
        ((Finset.univ.filter (fun i : ι => c i = j)).card : ℝ) /
          ((Fintype.card κ : ℝ) * B j) := by
      calc
        _ = ∑ _i ∈ Finset.univ.filter (fun i : ι => c i = j), 1 / ((Fintype.card κ : ℝ) * B j) :=
          Finset.sum_congr rfl (fun i hi => by simp only [q, (Finset.mem_filter.mp hi).2])
        _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
    rw [heq]
    calc
      _ ≤ B j / ((Fintype.card κ : ℝ) * B j) :=
        div_le_div_of_nonneg_right (hcard j) (mul_pos hm (hB j)).le
      _ = _ := by field_simp [hm.ne', (hB j).ne']
  have hqsum : ∑ i, q i ≤ 1 := by
    calc
      ∑ i, q i = ∑ j : κ, ∑ i : ι, if c i = j then q i else 0 := by
        rw [Finset.sum_comm]
        simp
      _ ≤ ∑ _j : κ, 1 / (Fintype.card κ : ℝ) := Finset.sum_le_sum (fun j _ => hterm j)
      _ = 1 := by simp [hm.ne']
  have h := finiteEntropy_le_crossEntropy_of_sum_le hp hq hpsum hqsum
  have hlog (i : ι) : Real.log (q i) = -Real.log (Fintype.card κ) - Real.log (B (c i)) := by
    dsimp only [q]
    rw [one_div, Real.log_inv, Real.log_mul hm.ne' (hB (c i)).ne']
    ring
  have heq : -(∑ i, p i * Real.log (q i)) =
      Real.log (Fintype.card κ) + ∑ i, p i * Real.log (B (c i)) := by
    simp only [hlog, mul_sub, mul_neg, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
      ← Finset.sum_mul, hpsum, one_mul]
    ring
  exact h.trans_eq heq

end Erdos1148.DukeArithmetic
