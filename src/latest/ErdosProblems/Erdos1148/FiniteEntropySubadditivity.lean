import ErdosProblems.Erdos1148.FiniteEntropyCollision
import Mathlib.Data.Fintype.BigOperators

/-! # Subadditivity of finite Shannon entropy -/

namespace Erdos1148.DukeArithmetic

lemma finiteEntropy_eq_neg_sum_mul_log {ι : Type*} [Fintype ι] (p : ι → ℝ) :
    finiteEntropy p = -(∑ i, p i * Real.log (p i)) := by
  simp only [finiteEntropy, Real.negMulLog, neg_mul, Finset.sum_neg_distrib]

theorem finiteEntropy_le_crossEntropy {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (hsupp : ∀ i, 0 < p i → 0 < q i)
    (hpsum : ∑ i, p i = 1) (hqsum : ∑ i, q i = 1) :
    finiteEntropy p ≤ -(∑ i, p i * Real.log (q i)) := by
  have hpoint (i : ι) :
      p i * Real.log (q i) - p i * Real.log (p i) ≤ q i - p i := by
    rcases eq_or_lt_of_le (hp i) with hi | hi
    · simpa only [← hi, zero_mul, sub_zero] using hq i
    · have hqi := hsupp i hi
      have hlog := Real.log_le_sub_one_of_pos (div_pos hqi hi)
      rw [Real.log_div hqi.ne' hi.ne'] at hlog
      calc
        _ = p i * (Real.log (q i) - Real.log (p i)) := by ring
        _ ≤ p i * (q i / p i - 1) := mul_le_mul_of_nonneg_left hlog (hp i)
        _ = q i - p i := by field_simp
  have htotal := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  simp only [Finset.sum_sub_distrib, hpsum, hqsum, sub_self] at htotal
  rw [finiteEntropy_eq_neg_sum_mul_log]
  linarith

theorem finiteEntropy_joint_le_add_marginals {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι × κ → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    finiteEntropy p ≤ finiteEntropy (fun i => ∑ j, p (i, j)) +
      finiteEntropy (fun j => ∑ i, p (i, j)) := by
  classical
  let a : ι → ℝ := fun i => ∑ j, p (i, j)
  let b : κ → ℝ := fun j => ∑ i, p (i, j)
  have ha (i : ι) : 0 ≤ a i := Finset.sum_nonneg (fun j _ => hp (i, j))
  have hb (j : κ) : 0 ≤ b j := Finset.sum_nonneg (fun i _ => hp (i, j))
  have hpa (i : ι) (j : κ) : p (i, j) ≤ a i :=
    Finset.single_le_sum (fun k _ => hp (i, k)) (Finset.mem_univ j)
  have hpb (i : ι) (j : κ) : p (i, j) ≤ b j :=
    Finset.single_le_sum (fun k _ => hp (k, j)) (Finset.mem_univ i)
  have hasum : ∑ i, a i = 1 := by simpa only [a, Fintype.sum_prod_type] using hsum
  have hbsum : ∑ j, b j = 1 := by
    dsimp only [b]
    rw [Finset.sum_comm]
    exact hasum
  have hqsum : ∑ x : ι × κ, a x.1 * b x.2 = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, hbsum, mul_one, hasum]
  have h := finiteEntropy_le_crossEntropy hp (fun x => mul_nonneg (ha x.1) (hb x.2))
    (fun x hx => mul_pos (hx.trans_le (hpa x.1 x.2)) (hx.trans_le (hpb x.1 x.2))) hsum hqsum
  have hterm (i : ι) (j : κ) : p (i, j) * Real.log (a i * b j) =
      p (i, j) * Real.log (a i) + p (i, j) * Real.log (b j) := by
    by_cases hz : p (i, j) = 0
    · simp only [hz, zero_mul, add_zero]
    · have hpos : 0 < p (i, j) := lt_of_le_of_ne (hp (i, j)) (Ne.symm hz)
      rw [Real.log_mul (hpos.trans_le (hpa i j)).ne' (hpos.trans_le (hpb i j)).ne', mul_add]
  have hleft : (∑ i, ∑ j, p (i, j) * Real.log (a i)) = ∑ i, a i * Real.log (a i) := by
    simp only [← Finset.sum_mul, a]
  have hright : (∑ i, ∑ j, p (i, j) * Real.log (b j)) = ∑ j, b j * Real.log (b j) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, b]
  have hcross : -(∑ x : ι × κ, p x * Real.log (a x.1 * b x.2)) =
      finiteEntropy a + finiteEntropy b := by
    rw [Fintype.sum_prod_type]
    simp only [hterm, Finset.sum_add_distrib]
    rw [hleft, hright, neg_add, ← finiteEntropy_eq_neg_sum_mul_log,
      ← finiteEntropy_eq_neg_sum_mul_log]
  exact h.trans_eq hcross

end Erdos1148.DukeArithmetic
