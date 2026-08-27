/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTAssignmentPairCode
import ErdosProblems.Erdos4b.FGKMTAssignmentEulerMoment
import ErdosProblems.Erdos4b.FGKMTMovedPrimeMass

/-! # Simultaneous unmarked and logarithmically marked pair bounds -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α ι : Type*} [DecidableEq α] [Fintype α] [DecidableEq ι] [Fintype ι]

theorem sum_assignmentScalarWeight_le_exp {β : Type*} [Fintype β]
    {b : α → ℝ} (hb : ∀ q, 0 ≤ b q) :
    (∑ v : α → Option β, assignmentScalarWeight b v) ≤
      Real.exp (∑ q, (Fintype.card β : ℝ) * b q) := by
  rw [sum_assignmentScalarWeight]
  exact Real.prod_one_add_le_exp_sum _ (fun q => mul_nonneg (Nat.cast_nonneg _) (hb q))

open scoped Classical in
theorem sum_common_moved_affine_le
    (H : (α → Option ι) → ℝ) (hH : ∀ u, 0 ≤ H u)
    (b : α → ℝ) (hb : ∀ q, 0 ≤ b q) {p : α → ℕ} (hp : ∀ q, 0 < p q)
    {D E : ℝ} (hD : 0 ≤ D) (hE : 0 ≤ E) :
    (∑ r : α → Option ι, ∑ s : α → Option ι,
      if SamePrimeSupport r s then
        H (commonAssignment r s) * assignmentScalarWeight b (movedAssignment r s) *
          (D * Real.log (assignmentPrimeProduct p (movedAssignment r s)) + E) else 0) ≤
      (∑ u, H u) * (Real.exp (∑ q, (Fintype.card (ι × ι) : ℝ) * b q) *
        (D * (∑ q, (Fintype.card (ι × ι) : ℝ) * b q * Real.log (p q)) + E)) := by
  classical
  let G := fun v : α → Option (ι × ι) =>
    assignmentScalarWeight b v * (D * Real.log (assignmentPrimeProduct p v) + E)
  let J := fun uv : (α → Option ι) × (α → Option (ι × ι)) => H uv.1 * G uv.2
  have hG : ∀ v, 0 ≤ G v := fun v => mul_nonneg (assignmentScalarWeight_nonneg hb v)
    (add_nonneg (mul_nonneg hD (Real.log_natCast_nonneg _)) hE)
  have hsum : (∑ v, G v) ≤
      Real.exp (∑ q, (Fintype.card (ι × ι) : ℝ) * b q) *
        (D * (∑ q, (Fintype.card (ι × ι) : ℝ) * b q * Real.log (p q)) + E) := by
    calc
      _ = D * (∑ v : α → Option (ι × ι),
          assignmentScalarWeight b v * Real.log (assignmentPrimeProduct p v)) +
          E * (∑ v : α → Option (ι × ι), assignmentScalarWeight b v) := by
        simp only [G, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro v _hv
        ring
      _ ≤ D * (Real.exp (∑ q, (Fintype.card (ι × ι) : ℝ) * b q) *
          ∑ q, (Fintype.card (ι × ι) : ℝ) * b q * Real.log (p q)) +
          E * Real.exp (∑ q, (Fintype.card (ι × ι) : ℝ) * b q) :=
        add_le_add (mul_le_mul_of_nonneg_left (sum_assignmentScalarWeight_logProduct_le hp hb) hD)
          (mul_le_mul_of_nonneg_left (sum_assignmentScalarWeight_le_exp hb) hE)
      _ = _ := by ring
  calc
    _ = ∑ r : α → Option ι, ∑ s : α → Option ι,
        if SamePrimeSupport r s then J (assignmentPairCode (r, s)) else 0 := by
      apply Finset.sum_congr rfl
      intro r _hr
      apply Finset.sum_congr rfl
      intro s _hs
      by_cases h : SamePrimeSupport r s
      · simp only [if_pos h, J, G, assignmentPairCode,
          movedPairAssignment_scalarWeight b h, movedPairAssignment_primeProduct p h, mul_assoc]
      · simp only [if_neg h]
    _ ≤ ∑ u : α → Option ι, ∑ v : α → Option (ι × ι), J (u, v) :=
      sum_supported_pairCode_le J (fun uv => mul_nonneg (hH uv.1) (hG uv.2))
    _ = (∑ u, H u) * ∑ v, G v := by
      simp only [J]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (Finset.sum_nonneg fun u _hu => hH u)

open scoped Classical in
theorem sum_common_moved_affine_le_rough {m k : ℕ} (hk : 2 ≤ k) (hm : m ≤ k)
    {p : α → ℕ} (hinj : Function.Injective p) (hrough : ∀ q, 2 * k ^ 2 < p q)
    (H : (α → Option (Fin m)) → ℝ) (hH : ∀ u, 0 ≤ H u)
    {D E : ℝ} (hD : 0 ≤ D) (hE : 0 ≤ E) :
    (∑ r : α → Option (Fin m), ∑ s : α → Option (Fin m),
      if SamePrimeSupport r s then
        H (commonAssignment r s) *
          assignmentScalarWeight (fun q => 1 / ((p q : ℝ) - k) ^ 2) (movedAssignment r s) *
            (D * Real.log (assignmentPrimeProduct p (movedAssignment r s)) + E) else 0) ≤
      (∑ u, H u) * (Real.exp 4 * (D * (16 * k) + E)) := by
  have hp : ∀ q, 0 < p q := fun q => (by positivity : 0 < 2 * k ^ 2).trans (hrough q)
  have hb : ∀ q, 0 ≤ 1 / ((p q : ℝ) - k) ^ 2 := fun q => div_nonneg zero_le_one (sq_nonneg _)
  have hmk : (m : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg m) (by exact_mod_cast hm) 2
  have hmass : (∑ q, (m : ℝ) ^ 2 / ((p q : ℝ) - k) ^ 2) ≤ 4 := by
    apply le_trans _ (movedPrimeMass_le_four hk hinj hrough)
    apply Finset.sum_le_sum
    intro q _hq
    exact div_le_div_of_nonneg_right hmk (sq_nonneg _)
  have hlogmass : (∑ q, (m : ℝ) ^ 2 / ((p q : ℝ) - k) ^ 2 * Real.log (p q)) ≤ 16 * k := by
    apply le_trans _ (movedPrimeLogMass_le hk hinj hrough)
    apply Finset.sum_le_sum
    intro q _hq
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hmk (sq_nonneg _))
      (Real.log_natCast_nonneg _)
  have h := sum_common_moved_affine_le H hH _ hb hp hD hE
  have hcard : (Fintype.card (Fin m × Fin m) : ℝ) = (m : ℝ) ^ 2 := by simp [pow_two]
  rw [hcard] at h
  simp only [mul_one_div] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg fun u _hu => hH u)
  apply mul_le_mul (Real.exp_le_exp.mpr hmass)
    (add_le_add (mul_le_mul_of_nonneg_left hlogmass hD) le_rfl) _ (Real.exp_pos _).le
  exact add_nonneg (mul_nonneg hD (Finset.sum_nonneg fun q _hq =>
    mul_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)) (Real.log_natCast_nonneg _))) hE

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.sum_common_moved_affine_le
#print axioms Erdos4b.FGKMT.sum_common_moved_affine_le_rough
