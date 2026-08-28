import Wikipedia.NoExoticSixSphere.HilbertSchmidt

/-!
# Finite orthogonal families for the Hilbert--Schmidt form

These sum formulas apply to actual operator families, while leaving the
ambient operator norm unchanged. They will control every linear combination
of the negative directions, not just the individual basis directions.
-/

namespace NoExoticSixSphere.HilbertSchmidt

open GLOrthonormalization

variable {n : ℕ} {ι : Type*}

theorem innerForm_sum_left (s : Finset ι) (A : ι → Vector n →L[ℝ] Vector n)
    (B : Vector n →L[ℝ] Vector n) :
    innerForm (∑ i ∈ s, A i) B = ∑ i ∈ s, innerForm (A i) B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [innerForm]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, innerForm_add_left, ih]

theorem innerForm_sum_right (s : Finset ι) (A : Vector n →L[ℝ] Vector n)
    (B : ι → Vector n →L[ℝ] Vector n) :
    innerForm A (∑ i ∈ s, B i) = ∑ i ∈ s, innerForm A (B i) := by
  rw [innerForm_comm, innerForm_sum_left]
  apply Finset.sum_congr rfl
  intro i _
  exact innerForm_comm _ _

theorem squareNorm_sum_orthogonal [Fintype ι] [DecidableEq ι]
    (A : ι → Vector n →L[ℝ] Vector n) (c : ℝ)
    (hA : ∀ i j, innerForm (A i) (A j) = if i = j then c else 0) (a : ι → ℝ) :
    squareNorm (∑ i, a i • A i) = c * ∑ i, a i ^ 2 := by
  rw [squareNorm, innerForm_sum_left]
  simp_rw [innerForm_smul_left, innerForm_sum_right, innerForm_smul_right, hA]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem sum_orthogonal_eq_zero_iff [Fintype ι] [DecidableEq ι]
    (A : ι → Vector n →L[ℝ] Vector n) {c : ℝ} (hc : 0 < c)
    (hA : ∀ i j, innerForm (A i) (A j) = if i = j then c else 0) (a : ι → ℝ) :
    (∑ i, a i • A i) = 0 ↔ a = 0 := by
  constructor
  · intro h
    have hz : c * ∑ i, a i ^ 2 = 0 := by
      rw [← squareNorm_sum_orthogonal A c hA a, h]
      exact (squareNorm_eq_zero_iff _).mpr rfl
    have hs : ∑ i, a i ^ 2 = 0 := (mul_eq_zero.mp hz).resolve_left hc.ne'
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ sq_nonneg (a i))).mp hs
    funext i
    exact sq_eq_zero_iff.mp (hi i (Finset.mem_univ i))
  · rintro rfl
    simp

end NoExoticSixSphere.HilbertSchmidt
