/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Degree-preserving integer shears of bounded size.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.LeadingSlope

namespace Erdos477.Geometry

variable {K : Type*} [Field K] [CharZero K]

lemma exists_bounded_nat_eval_ne_zero (P : Polynomial K) (hP : P ≠ 0)
    (D : ℕ) (hD : P.natDegree ≤ D) : ∃ a : ℕ, a ≤ D ∧ P.eval (a : K) ≠ 0 := by
  by_contra! h
  apply hP
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P
    (f := fun a : Fin (D + 1) => (a.val : K))
  · intro a b hab
    exact Fin.ext (Nat.cast_injective hab)
  · intro a
    exact h a.val (Nat.le_of_lt_succ a.isLt)
  · simpa only [Fintype.card_fin] using Nat.lt_succ_of_le hD

theorem exists_bounded_degree_shear (P : MvPolynomial (Fin 2) K) (hP : P ≠ 0) :
    ∃ a : ℕ, a ≤ P.totalDegree ∧ (shear (a : K) P).degreeOf 0 = P.totalDegree := by
  obtain ⟨a, ha, hnonzero⟩ := exists_bounded_nat_eval_ne_zero (leadingSlope P)
    (leadingSlope_ne_zero P hP) P.totalDegree (natDegree_leadingSlope P)
  exact ⟨a, ha, degreeOf_shear_eq_of_leadingSlope_ne_zero (a : K) P hnonzero⟩

def integerShear (a : ℕ) (z : Fin 2 → ℤ) : Fin 2 → ℤ := ![z 0, z 1 + a * z 0]

lemma integerShear_injective (a : ℕ) : Function.Injective (integerShear a) := by
  intro z w h
  have h0 : z 0 = w 0 := congrFun h 0
  have h1 : z 1 + a * z 0 = w 1 + a * w 0 := congrFun h 1
  ext i
  fin_cases i
  · exact h0
  · change z 1 = w 1
    rw [h0] at h1
    exact add_right_cancel h1

omit [CharZero K] in
lemma eval_integerShear (a : ℕ) (z : Fin 2 → ℤ) (P : MvPolynomial (Fin 2) K) :
    MvPolynomial.eval (fun i => (integerShear a z i : K)) (shear (a : K) P) =
      MvPolynomial.eval (fun i => (z i : K)) P := by
  have hleft : (fun i => (integerShear a z i : K)) =
      ![(z 0 : K), (z 1 : K) + (a : K) * (z 0 : K)] := by
    ext i
    fin_cases i <;> simp [integerShear]
  have hright : (fun i => (z i : K)) = ![(z 0 : K), (z 1 : K)] := by
    ext i
    fin_cases i <;> rfl
  rw [hleft, hright, eval_shear]

lemma height_integerShear (D a : ℕ) (ha : a ≤ D) (z : Fin 2 → ℤ)
    (B : ℝ) (hB : 0 ≤ B) (hz : ∀ i, |(z i : ℝ)| ≤ B) :
    ∀ i, |(integerShear a z i : ℝ)| ≤ (D + 1 : ℝ) * B := by
  intro i
  fin_cases i
  · change |(z 0 : ℝ)| ≤ _
    have h : (1 : ℝ) ≤ D + 1 := by linarith [show (0 : ℝ) ≤ D from Nat.cast_nonneg D]
    exact (hz 0).trans (le_mul_of_one_le_left hB h)
  · change |((z 1 + (a : ℤ) * z 0 : ℤ) : ℝ)| ≤ _
    push_cast
    calc
      _ ≤ |(z 1 : ℝ)| + |(a : ℝ) * (z 0 : ℝ)| := abs_add_le _ _
      _ = |(z 1 : ℝ)| + (a : ℝ) * |(z 0 : ℝ)| := by
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
      _ ≤ B + (D : ℝ) * B := by gcongr <;> exact hz _
      _ = _ := by ring

#print axioms exists_bounded_degree_shear
-- 'Erdos477.Geometry.exists_bounded_degree_shear' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
