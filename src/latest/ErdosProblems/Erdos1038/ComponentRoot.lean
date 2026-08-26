import ErdosProblems.Erdos1038.SublevelBoundary

namespace Erdos1038

open Set MeasureTheory

/-- A bounded interval component of the strict unit sublevel set contains a root.

The proof is elementary. If all roots lie outside `(a, b)`, then at the midpoint
each root factor is strictly larger (after multiplying the two endpoint distances)
than its endpoint geometric mean. Multiplying over every root contradicts the
strict sublevel inequality at the midpoint. -/
lemma interval_sublevel_contains_root {f : Polynomial ℝ} (hf : IsAdmissible f)
    {a b : ℝ} (hab : a < b) (ha : |f.eval a| = 1) (hb : |f.eval b| = 1)
    (hsub : Ioo a b ⊆ sublevelSet f) :
    ∃ r ∈ f.roots, r ∈ Ioo a b := by
  by_contra hnone
  push_neg at hnone
  let l : List ℝ := f.roots.toList
  have hlength : l.length = f.natDegree := by
    simp [l, hf.card_roots_eq_natDegree]
  have hnpos : 0 < l.length := by
    rw [hlength]
    exact hf.monic.natDegree_pos.mpr hf.ne_one
  let m : ℝ := (a + b) / 2
  have hm : m ∈ Ioo a b := by
    constructor <;> dsimp [m] <;> linarith
  have hroot (i : Fin l.length) : l[i.1] ∈ f.roots := by
    rw [← Multiset.mem_toList]
    change l[i.1] ∈ l
    exact List.getElem_mem i.isLt
  have hout (i : Fin l.length) : l[i.1] ≤ a ∨ b ≤ l[i.1] := by
    rcases le_or_gt l[i.1] a with h | h
    · exact Or.inl h
    · right
      exact le_of_not_gt fun hrb => hnone l[i.1] (hroot i) ⟨h, hrb⟩
  have hleftpos (i : Fin l.length) : 0 < |a - l[i.1]| * |b - l[i.1]| := by
    have hane : a - l[i.1] ≠ 0 := by
      intro hz
      have heq : a = l[i.1] := sub_eq_zero.mp hz
      have hzroot : f.eval l[i.1] = 0 := (Polynomial.mem_roots'.mp (hroot i)).2
      rw [← heq] at hzroot
      rw [hzroot] at ha
      norm_num at ha
    have hbne : b - l[i.1] ≠ 0 := by
      intro hz
      have heq : b = l[i.1] := sub_eq_zero.mp hz
      have hzroot : f.eval l[i.1] = 0 := (Polynomial.mem_roots'.mp (hroot i)).2
      rw [← heq] at hzroot
      rw [hzroot] at hb
      norm_num at hb
    exact mul_pos (abs_pos.mpr hane) (abs_pos.mpr hbne)
  have hpoint (i : Fin l.length) :
      |a - l[i.1]| * |b - l[i.1]| < |m - l[i.1]| ^ 2 := by
    have hformula :
        |a - l[i.1]| * |b - l[i.1]| = (a - l[i.1]) * (b - l[i.1]) := by
      rcases hout i with h | h
      · rw [abs_of_nonneg (sub_nonneg.mpr h),
          abs_of_nonneg (sub_nonneg.mpr (h.trans hab.le))]
      · rw [abs_of_nonpos (sub_nonpos.mpr (hab.le.trans h)),
          abs_of_nonpos (sub_nonpos.mpr h)]
        ring
    rw [hformula, sq_abs]
    dsimp [m]
    nlinarith [sq_pos_of_pos (sub_pos.mpr hab)]
  have hprod :
      ∏ i : Fin l.length, (|a - l[i.1]| * |b - l[i.1]|) <
        ∏ i : Fin l.length, |m - l[i.1]| ^ 2 := by
    apply Finset.prod_lt_prod_of_nonempty
      (fun i _ => hleftpos i) (fun i _ => hpoint i)
    exact Finset.univ_nonempty_iff.mpr ⟨0, hnpos⟩
  have hprod_eval (x : ℝ) :
      (∏ i : Fin l.length, |x - l[i.1]|) = |f.eval x| := by
    rw [hf.abs_eval_eq_prod_abs_roots]
    have hprodlist :
        (∏ i : Fin l.length, |x - l[i.1]|) =
          (l.map fun r => |x - r|).prod := by
      simpa using! Fin.prod_univ_fun_getElem l (fun r : ℝ => |x - r|)
    rw [hprodlist]
    simp [l]
  rw [Finset.prod_mul_distrib, Finset.prod_pow] at hprod
  simp_rw [hprod_eval] at hprod
  rw [ha, hb, one_mul] at hprod
  have hmabs : |f.eval m| < 1 := hsub hm
  nlinarith [sq_nonneg (|f.eval m|), abs_nonneg (f.eval m)]

end Erdos1038
