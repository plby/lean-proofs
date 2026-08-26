/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The monomial family used for the sextic auxiliary-polynomial construction.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.Monomials

namespace Erdos477.Counting

open scoped BigOperators

/-- Sum of the total degrees of two-variable monomials below a threshold. -/
def monomialWeight (m : ℕ) : ℕ := ∑ e ∈ monomialsBelow m, (e.1 + e.2)

lemma monomialWeight_add_deficit (m : ℕ) :
    monomialWeight m + monomialDeficit m = m * (monomialsBelow m).card := by
  rw [monomialWeight, monomialDeficit, ← Finset.sum_add_distrib]
  calc
    _ = ∑ _e ∈ monomialsBelow m, m := by
      apply Finset.sum_congr rfl
      intro e he
      have h := (mem_monomialsBelow.mp he).le
      omega
    _ = _ := by simp [mul_comm]

lemma three_mul_monomialWeight (m : ℕ) :
    3 * monomialWeight m + m * (m + 1) = m ^ 2 * (m + 1) := by
  have hw := monomialWeight_add_deficit m
  have hd := six_mul_monomialDeficit m
  have hc := congrArg (fun n : ℕ => m * n) (two_mul_card_monomialsBelow m)
  nlinarith

/-- The last exponent is below six; the other two exponents fill a triangle.
The indexing parameter `n` gives total degree at most `n+5`. -/
abbrev SexticMonomial (n : ℕ) :=
  Σ k : Fin 6, ↥(monomialsBelow (n + k.val + 1))

def sexticDegree {n : ℕ} (a : SexticMonomial n) : ℕ :=
  a.2.val.1 + a.2.val.2 + (5 - a.1.val)

lemma sexticDegree_le {n : ℕ} (a : SexticMonomial n) : sexticDegree a ≤ n + 5 := by
  have h := mem_monomialsBelow.mp a.2.property
  have hk := a.1.isLt
  unfold sexticDegree
  omega

lemma card_sexticMonomial (n : ℕ) :
    Fintype.card (SexticMonomial n) = 3 * n ^ 2 + 24 * n + 56 := by
  have h : 2 * Fintype.card (SexticMonomial n) = 2 * (3 * n ^ 2 + 24 * n + 56) := by
    rw [Fintype.card_sigma, Finset.mul_sum]
    simp only [Fintype.card_coe, two_mul_card_monomialsBelow]
    simp only [Fin.sum_univ_six]
    norm_num
    ring
  omega

lemma weighted_slice (m k : ℕ) :
    6 * (monomialWeight m + k * (monomialsBelow m).card) + 2 * m * (m + 1) =
      2 * m ^ 2 * (m + 1) + 3 * k * m * (m + 1) := by
  have hw := three_mul_monomialWeight m
  have hc := congrArg (fun n : ℕ => k * n) (two_mul_card_monomialsBelow m)
  nlinarith

lemma sum_sexticDegree (n : ℕ) :
    2 * (∑ a : SexticMonomial n, sexticDegree a) =
      4 * n ^ 3 + 57 * n ^ 2 + 263 * n + 420 := by
  let w : Fin 6 → ℕ := fun k =>
    monomialWeight (n + k.val + 1) +
      (5 - k.val) * (monomialsBelow (n + k.val + 1)).card
  have hsum : (∑ a : SexticMonomial n, sexticDegree a) = ∑ k : Fin 6, w k := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [sexticDegree, w]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul]
    rw [mul_comm]
    congr 1
    exact Finset.sum_coe_sort (monomialsBelow (n + k.val + 1))
      (fun e : ℕ × ℕ => e.1 + e.2)
  rw [hsum]
  have h0 := weighted_slice (n + 1) 5
  have h1 := weighted_slice (n + 2) 4
  have h2 := weighted_slice (n + 3) 3
  have h3 := weighted_slice (n + 4) 2
  have h4 := weighted_slice (n + 5) 1
  have h5 := weighted_slice (n + 6) 0
  simp only [Fin.sum_univ_six, w]
  norm_num
  nlinarith

#print axioms card_sexticMonomial
-- 'Erdos477.Counting.card_sexticMonomial' depends on axioms:
-- [propext, Classical.choice, Quot.sound]
#print axioms sum_sexticDegree
-- 'Erdos477.Counting.sum_sexticDegree' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
