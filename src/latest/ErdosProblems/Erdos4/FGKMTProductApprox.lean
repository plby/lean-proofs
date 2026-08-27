import ErdosProblems.Erdos4.FGKMTRound

/-! Elementary product-to-exponential estimates for a covering round. -/

open scoped BigOperators

namespace Erdos4.FGKMT

theorem abs_prod_sub_prod_le {I : Type*} (s : Finset I) (f g : I → ℝ)
    (hf0 : ∀ i ∈ s, 0 ≤ f i) (hf1 : ∀ i ∈ s, f i ≤ 1)
    (hg0 : ∀ i ∈ s, 0 ≤ g i) (hg1 : ∀ i ∈ s, g i ≤ 1) :
    |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤ ∑ i ∈ s, |f i - g i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    have hmem : ∀ i ∈ s, i ∈ insert j s := fun i hi => Finset.mem_insert_of_mem hi
    have hprev := ih (fun i hi => hf0 i (hmem i hi)) (fun i hi => hf1 i (hmem i hi))
      (fun i hi => hg0 i (hmem i hi)) (fun i hi => hg1 i (hmem i hi))
    have hfj0 := hf0 j (Finset.mem_insert_self _ _)
    have hfj1 := hf1 j (Finset.mem_insert_self _ _)
    have hgprod0 : 0 ≤ ∏ i ∈ s, g i := Finset.prod_nonneg (fun i hi => hg0 i (hmem i hi))
    have hgprod1 : (∏ i ∈ s, g i) ≤ 1 :=
      Finset.prod_le_one (fun i hi => hg0 i (hmem i hi)) (fun i hi => hg1 i (hmem i hi))
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
    calc
      _ = |f j * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) + (f j - g j) * ∏ i ∈ s, g i| := by ring_nf
      _ ≤ |f j * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)| + |(f j - g j) * ∏ i ∈ s, g i| := abs_add_le _ _
      _ = f j * |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| + |f j - g j| * ∏ i ∈ s, g i := by
        rw [abs_mul, abs_mul, abs_of_nonneg hfj0, abs_of_nonneg hgprod0]
      _ ≤ |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| + |f j - g j| :=
        add_le_add (mul_le_of_le_one_left (abs_nonneg _) hfj1)
          (mul_le_of_le_one_right (abs_nonneg _) hgprod1)
      _ ≤ _ := by linarith

theorem one_sub_exp_error {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    |(1 - a) - Real.exp (-a)| ≤ a ^ 2 := by
  have hh := Real.abs_exp_sub_one_sub_id_le (x := -a) (by simpa [abs_of_nonneg ha0] using ha1)
  have heq : (1 - a) - Real.exp (-a) = -(Real.exp (-a) - 1 - (-a)) := by ring
  rw [heq, abs_neg]
  simpa only [neg_sq] using hh

theorem prod_one_sub_exp_error {I : Type*} (s : Finset I) (a : I → ℝ)
    (ha0 : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i ≤ 1) :
    |(∏ i ∈ s, (1 - a i)) - Real.exp (-(∑ i ∈ s, a i))| ≤ ∑ i ∈ s, a i ^ 2 := by
  have heq : (∏ i ∈ s, Real.exp (-a i)) = Real.exp (-(∑ i ∈ s, a i)) := by
    rw [← Real.exp_sum, Finset.sum_neg_distrib]
  rw [← heq]
  exact (abs_prod_sub_prod_le s (fun i => 1 - a i) (fun i => Real.exp (-a i))
    (fun i hi => by linarith [ha1 i hi]) (fun i hi => by linarith [ha0 i hi])
    (fun i _hi => (Real.exp_pos _).le)
    (fun i hi => Real.exp_le_one_iff.mpr (by linarith [ha0 i hi]))).trans
      (Finset.sum_le_sum (fun i hi => one_sub_exp_error (ha0 i hi) (ha1 i hi)))

theorem exp_neg_sub_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.exp (-a) - Real.exp (-b) ≤ b - a := by
  have hdiff : 0 ≤ b - a := sub_nonneg.mpr hab
  have hlocal : 1 - Real.exp (-(b - a)) ≤ b - a := by
    have hh := Real.one_sub_le_exp_neg (b - a)
    linarith
  have heq : Real.exp (-a) - Real.exp (-b) = Real.exp (-a) * (1 - Real.exp (-(b - a))) := by
    rw [mul_sub, mul_one, ← Real.exp_add]
    congr 2
    ring
  rw [heq]
  exact (mul_le_mul_of_nonneg_left hlocal (Real.exp_pos _).le).trans
    (mul_le_of_le_one_left hdiff (Real.exp_le_one_iff.mpr (by linarith)))

theorem abs_exp_neg_sub_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| := by
  rcases le_total a b with hab | hba
  · have he : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonneg (sub_nonneg.mpr he), abs_of_nonpos (sub_nonpos.mpr hab)]
    have hh := exp_neg_sub_le ha hab
    linarith
  · rw [abs_sub_comm (Real.exp (-a)), abs_sub_comm a]
    have he : Real.exp (-a) ≤ Real.exp (-b) := Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonneg (sub_nonneg.mpr he), abs_of_nonpos (sub_nonpos.mpr hba)]
    have hh := exp_neg_sub_le hb hba
    linarith

end Erdos4.FGKMT
