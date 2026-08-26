import ErdosProblems.Erdos1148.FormAction

/-!
# Elementary bounds for reduced indefinite forms

Balancing the middle coefficient by an integral shear, after minimizing
the absolute leading coefficient in its orbit, gives a finite box of
representatives. These are the numerical estimates for that reduction.
-/

namespace Erdos1148.DukeArithmetic

lemma exists_balanced_shear_of_pos {a : ℤ} (ha : 0 < a) (b : ℤ) :
    ∃ k : ℤ, |b + 2 * a * k| ≤ a := by
  refine ⟨-((b + a) / (2 * a)), ?_⟩
  have hmod0 := Int.emod_nonneg (b + a) (by omega : 2 * a ≠ 0)
  have hmodlt := Int.emod_lt_of_pos (b + a) (by omega : 0 < 2 * a)
  have hdiv := Int.emod_add_mul_ediv (b + a) (2 * a)
  apply abs_le.mpr
  constructor <;> nlinarith

lemma exists_balanced_shear {a : ℤ} (ha : a ≠ 0) (b : ℤ) :
    ∃ k : ℤ, |b + 2 * a * k| ≤ |a| := by
  rcases ha.lt_or_gt with hneg | hpos
  · obtain ⟨k, hk⟩ := exists_balanced_shear_of_pos (neg_pos.mpr hneg) b
    refine ⟨-k, ?_⟩
    rw [abs_of_neg hneg]
    convert hk using 1 <;> congr 1 <;> ring
  · simpa only [abs_of_pos hpos] using exists_balanced_shear_of_pos hpos b

lemma coeff_bounds_of_reduced {d a b c : ℤ} (hd : 0 < d)
    (hdisc : b ^ 2 - 4 * a * c = d) (ha : a ≠ 0)
    (hb : |b| ≤ |a|) (hmin : |a| ≤ |c|) :
    |a| ≤ d ∧ |b| ≤ d ∧ |c| ≤ d := by
  have hA : 1 ≤ |a| := by have := abs_pos.mpr ha; omega
  have hb2 : b ^ 2 ≤ a ^ 2 := by nlinarith [sq_abs b, sq_abs a, abs_nonneg b]
  have hminmul : |a| ^ 2 ≤ |a| * |c| := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_left hmin (abs_nonneg a)
  have hmain : 4 * |a| * |c| ≤ b ^ 2 + d := by
    calc
      4 * |a| * |c| = |4 * a * c| := by simp [abs_mul]
      _ = |b ^ 2 - d| := by congr 1; linarith
      _ ≤ |b ^ 2| + |d| := by
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (b ^ 2) (-d)
      _ = b ^ 2 + d := by rw [abs_of_nonneg (sq_nonneg b), abs_of_pos hd]
  have ha2 : a ^ 2 ≤ d := by nlinarith [sq_abs a]
  have habound : |a| ≤ d := by nlinarith [sq_abs a]
  have hcbound : |c| ≤ d := by
    have hmul := mul_le_mul_of_nonneg_right hA (abs_nonneg c)
    nlinarith
  exact ⟨habound, hb.trans habound, hcbound⟩

end Erdos1148.DukeArithmetic
