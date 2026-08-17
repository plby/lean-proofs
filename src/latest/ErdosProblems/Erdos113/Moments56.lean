import ErdosProblems.Erdos113.Conflict56

open scoped Real SimpleGraph BigOperators

namespace Erdos113Moments56

lemma trace_pow_eq_sum_eigenvalues_pow {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (j : ℕ) :
    Matrix.trace (A ^ j) = ∑ i, hA.eigenvalues i ^ j := by
  conv_lhs => rw [hA.spectral_theorem, ← map_pow]
  simp only [Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_cycle]
  simp [Matrix.diagonal_pow]

lemma closedWalkCount_cast_eq_sum_eigenvalues_pow {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj] (m : ℕ) :
    (Conflict56.closedWalkCount A m : ℝ) =
      ∑ i, ((A.isHermitian_adjMatrix ℝ).eigenvalues i) ^ m := by
  rw [Conflict56.closedWalkCount_cast_eq_trace]
  exact trace_pow_eq_sum_eigenvalues_pow _ _ _

/-- The `L²⁷`--`L²²⁸` interpolation used after cutting a
56-step closed walk into pieces of lengths 27 and 28. -/
lemma closedWalkCount_interpolation_28 {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj] :
    (Conflict56.closedWalkCount A 54 : ℝ) ≤
      (Fintype.card W : ℝ) ^ ((1 : ℝ) / 28) *
        (Conflict56.closedWalkCount A 56 : ℝ) ^ ((27 : ℝ) / 28) := by
  let hA := A.isHermitian_adjMatrix ℝ
  let lam : W → ℝ := hA.eigenvalues
  have hholder : Real.HolderConjugate (28 : ℝ) ((28 : ℝ) / 27) := by
    rw [Real.holderConjugate_iff]
    constructor <;> norm_num
  have hh := Real.inner_le_Lp_mul_Lq_of_nonneg
    (s := Finset.univ) (f := fun _ : W ↦ (1 : ℝ))
    (g := fun i : W ↦ (lam i ^ 2) ^ (27 : ℕ)) hholder
    (by intro i hi; positivity) (by intro i hi; positivity)
  dsimp [hA, lam] at hh
  have hleft (x : ℝ) : x ^ 54 = (x ^ 2) ^ 27 := by ring
  have hright (x : ℝ) :
      ((x ^ 2) ^ (27 : ℕ)) ^ ((28 : ℝ) / 27) = x ^ 56 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (sq_nonneg x)]
    norm_num
    ring
  simp_rw [hright] at hh
  simp_rw [← hleft] at hh
  rw [closedWalkCount_cast_eq_sum_eigenvalues_pow,
    closedWalkCount_cast_eq_sum_eigenvalues_pow]
  simp only [one_mul, Real.one_rpow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at hh
  convert hh using 1 <;> norm_num

end Erdos113Moments56
