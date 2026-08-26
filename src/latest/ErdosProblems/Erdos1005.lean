/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Formalization by Ricky Cipollini and Wouter van Doorn with Aristotle (Harmonic).
Combined source: https://github.com/Woett/Lean-files/blob/d30552f64c55686d40b928a0a3b8e2396357a4ee/ErdosProblem1005.lean
Original Lean version: 4.28.0. See Erdos1005/README.md for provenance.
-/
import ErdosProblems.Erdos1005.Proof

open Filter Topology

namespace Erdos1005

/-- The largest safe separation of indices in the ordered Farey sequence is
one less than the smallest index difference of a badly ordered pair, hence
is the minimum number of Farey fractions strictly between such a pair.
Values at orders with no badly ordered pair do not affect the limit. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {k | ∃ x y : ℚ, IsFarey n x ∧ IsFarey n y ∧ x < y ∧
    (x.num - y.num) * ((x.den : ℤ) - y.den) < 0 ∧ betweenCount n x y = k}

theorem badlyOrdered_iff_product_neg {n : ℕ} {x y : ℚ} :
    BadlyOrdered n x y ↔ IsFarey n x ∧ IsFarey n y ∧ x < y ∧
      (x.num - y.num) * ((x.den : ℤ) - y.den) < 0 := by
  constructor
  · rintro ⟨hx, hy, hxy, hnum, hden⟩
    refine ⟨hx, hy, hxy, mul_neg_of_neg_of_pos (sub_neg.mpr hnum) ?_⟩
    exact sub_pos.mpr (by exact_mod_cast hden)
  · rintro ⟨hx, hy, hxy, hprod⟩
    rcases mul_neg_iff.mp hprod with ⟨hnum, hden⟩ | ⟨hnum, hden⟩
    · have hyNum : 0 ≤ y.num := Rat.num_nonneg.mpr hy.1
      have hyDen : (0 : ℤ) < y.den := by exact_mod_cast y.pos
      rw [Rat.lt_iff] at hxy
      exfalso
      nlinarith [mul_pos hnum hyDen, mul_nonneg hyNum (neg_nonneg.mpr hden.le)]
    · have hden' : (y.den : ℤ) < x.den := sub_pos.mp hden
      exact ⟨hx, hy, hxy, by omega, by exact_mod_cast hden'⟩

theorem f_eq_fVal (n : ℕ) : f n = fVal n := by
  unfold f fVal
  congr 1
  ext k
  simp only [Set.mem_setOf_eq, badlyOrdered_iff_product_neg, and_assoc]

theorem erdos_1005 :
    Tendsto (fun n : ℕ => (f n : ℝ) / n) atTop (𝓝 (1 / 4)) := by
  simpa only [f_eq_fVal] using source_limit

end Erdos1005
