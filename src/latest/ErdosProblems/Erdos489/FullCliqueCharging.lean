import Mathlib
import ErdosProblems.Erdos489.RankKernel

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

open scoped BigOperators

/-- Unweighted full-clique double counting.  If each object `i` has enough
labels to pay for `gap(i)^2`, and each label occurs at most `cap(z)` times,
then the total square mass is bounded by the sum of capacities. -/
theorem unweighted_pair_witness_double_count
    (I : Finset ℕ) (J : Finset (ℕ × ℕ)) (gap : ℕ → ℕ)
    (cap : ℕ × ℕ → ℕ) (R : ℕ → ℕ × ℕ → Prop) [DecidableRel R]
    (K : ℕ)
    (hw : ∀ i ∈ I, (gap i) ^ 2 ≤ K * (J.filter (R i)).card)
    (hcap : ∀ z ∈ J, (I.filter fun i => R i z).card ≤ cap z) :
    (∑ i ∈ I, (gap i) ^ 2) ≤ K * ∑ z ∈ J, cap z := by
  calc
    (∑ i ∈ I, (gap i) ^ 2) ≤
        ∑ i ∈ I, K * (J.filter (R i)).card :=
      Finset.sum_le_sum hw
    _ = K * ∑ i ∈ I, (J.filter (R i)).card := by
      rw [Finset.mul_sum]
    _ = K * ∑ i ∈ I, ∑ z ∈ J, if R i z then 1 else 0 := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.card_filter]
    _ = K * ∑ z ∈ J, ∑ i ∈ I, if R i z then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = K * ∑ z ∈ J, (I.filter fun i => R i z).card := by
      congr 1
      apply Finset.sum_congr rfl
      intro z hz
      rw [Finset.card_filter]
    _ ≤ K * ∑ z ∈ J, cap z := by
      apply Nat.mul_le_mul_left
      exact Finset.sum_le_sum hcap

/-- Actual-prefix capacity architecture.  A quadratic number of pair labels per
gap, together with a primitive-ray capacity

`aᵣaₛ cap(r,s) ≤ 4XC min(r+1,s+1) + 2aᵣaₛ`,

bounds the square-gap mass by a finite rank-kernel sum plus one endpoint term
per rank pair. -/
theorem full_clique_charge_le_rankKernel
    (I : Finset ℕ) (J : Finset (ℕ × ℕ)) (gap : ℕ → ℕ)
    (cap : ℕ × ℕ → ℕ) (R : ℕ → ℕ × ℕ → Prop) [DecidableRel R]
    (a : ℕ → ℕ) (K C X : ℕ)
    (hw : ∀ i ∈ I, (gap i) ^ 2 ≤ K * (J.filter (R i)).card)
    (hocc : ∀ z ∈ J, (I.filter fun i => R i z).card ≤ cap z)
    (ha : ∀ r, 0 < a r)
    (hcap : ∀ z ∈ J,
      a z.1 * a z.2 * cap z ≤
        4 * X * C * min (z.1 + 1) (z.2 + 1) +
          2 * (a z.1 * a z.2)) :
    ((∑ i ∈ I, (gap i) ^ 2 : ℕ) : ℝ) ≤
      (K : ℝ) *
        (4 * (X : ℝ) * (C : ℝ) *
            (∑ z ∈ J, rankPairKernel a z) + 2 * (J.card : ℝ)) := by
  have hdouble := unweighted_pair_witness_double_count
    I J gap cap R K hw hocc
  have hdoubleR : ((∑ i ∈ I, (gap i) ^ 2 : ℕ) : ℝ) ≤
      (K : ℝ) * (∑ z ∈ J, (cap z : ℝ)) := by
    exact_mod_cast hdouble
  have hterm : ∀ z ∈ J,
      (cap z : ℝ) ≤
        4 * (X : ℝ) * (C : ℝ) * rankPairKernel a z + 2 := by
    intro z hz
    have ha1 : (0 : ℝ) < a z.1 := by exact_mod_cast ha z.1
    have ha2 : (0 : ℝ) < a z.2 := by exact_mod_cast ha z.2
    have hab : (0 : ℝ) < (a z.1 : ℝ) * (a z.2 : ℝ) := mul_pos ha1 ha2
    have hc := hcap z hz
    have hcR : ((a z.1 * a z.2 * cap z : ℕ) : ℝ) ≤
        ((4 * X * C * min (z.1 + 1) (z.2 + 1) +
          2 * (a z.1 * a z.2) : ℕ) : ℝ) := by exact_mod_cast hc
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
      Nat.cast_min] at hcR
    dsimp [rankPairKernel]
    rw [show 4 * (X : ℝ) * (C : ℝ) *
        (min ((z.1 : ℝ) + 1) ((z.2 : ℝ) + 1) /
          ((a z.1 : ℝ) * (a z.2 : ℝ))) + 2 =
      (4 * (X : ℝ) * (C : ℝ) *
          min ((z.1 : ℝ) + 1) ((z.2 : ℝ) + 1) +
        2 * ((a z.1 : ℝ) * (a z.2 : ℝ))) /
          ((a z.1 : ℝ) * (a z.2 : ℝ)) by field_simp <;> ring]
    apply (le_div_iff₀ hab).mpr
    calc
      (cap z : ℝ) * ((a z.1 : ℝ) * (a z.2 : ℝ)) =
          (a z.1 : ℝ) * (a z.2 : ℝ) * (cap z : ℝ) := by ring
      _ ≤ 4 * (X : ℝ) * (C : ℝ) *
            min ((z.1 : ℝ) + 1) ((z.2 : ℝ) + 1) +
          2 * ((a z.1 : ℝ) * (a z.2 : ℝ)) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hcR
  have hsum : (∑ z ∈ J, (cap z : ℝ)) ≤
      4 * (X : ℝ) * (C : ℝ) * (∑ z ∈ J, rankPairKernel a z) +
        2 * (J.card : ℝ) := by
    calc
      (∑ z ∈ J, (cap z : ℝ)) ≤
          ∑ z ∈ J, (4 * (X : ℝ) * (C : ℝ) *
            rankPairKernel a z + 2) := Finset.sum_le_sum hterm
      _ = 4 * (X : ℝ) * (C : ℝ) *
            (∑ z ∈ J, rankPairKernel a z) + 2 * (J.card : ℝ) := by
        rw [Finset.sum_add_distrib]
        simp [Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
        ring
  exact hdoubleR.trans (mul_le_mul_of_nonneg_left hsum (by positivity))

end Erdos489
