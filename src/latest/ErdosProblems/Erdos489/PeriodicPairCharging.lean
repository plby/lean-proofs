import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

open scoped BigOperators

/-- Abstract weighted pair-witness double count.

For every index `i`, suppose there are at least `k * gap i` distinct witness
labels.  Suppose also that every label witnessing `i` has weight at least
`c * gap i`, and that a fixed label `z` witnesses at most `cap z` indices.
Then the total squared-gap mass is controlled by the weighted capacities.

In the periodic divisor-sieve application, labels are short pairs of ranked
forbidden moduli, their weight is the smaller one-shifted rank, and `cap` is
the exact number of compatible CRT classes in one period. -/
theorem weighted_pair_witness_double_count
    (I J : Finset ℕ) (gap weight cap : ℕ → ℕ) (R : ℕ → ℕ → Prop)
    [DecidableRel R] (k c : ℕ)
    (hw : ∀ i ∈ I, k * gap i ≤ (J.filter (R i)).card)
    (hweight : ∀ i ∈ I, ∀ z ∈ J, R i z → c * gap i ≤ weight z)
    (hcap : ∀ z ∈ J, (I.filter (fun i => R i z)).card ≤ cap z) :
    k * c * (∑ i ∈ I, (gap i) ^ 2) ≤
      ∑ z ∈ J, weight z * cap z := by
  have hlocal : ∀ i ∈ I,
      k * c * (gap i) ^ 2 ≤ ∑ z ∈ J.filter (R i), weight z := by
    intro i hi
    have hconst :
        (J.filter (R i)).card * (c * gap i) ≤
          ∑ z ∈ J.filter (R i), weight z := by
      calc
        (J.filter (R i)).card * (c * gap i) =
            ∑ _z ∈ J.filter (R i), (c * gap i) := by simp
        _ ≤ ∑ z ∈ J.filter (R i), weight z := by
          apply Finset.sum_le_sum
          intro z hz
          have hzJ : z ∈ J := (Finset.mem_filter.mp hz).1
          have hzR : R i z := (Finset.mem_filter.mp hz).2
          exact hweight i hi z hzJ hzR
    have hprod : (k * gap i) * (c * gap i) ≤
        (J.filter (R i)).card * (c * gap i) :=
      Nat.mul_le_mul_right (c * gap i) (hw i hi)
    calc
      k * c * (gap i) ^ 2 = (k * gap i) * (c * gap i) := by ring
      _ ≤ (J.filter (R i)).card * (c * gap i) := hprod
      _ ≤ ∑ z ∈ J.filter (R i), weight z := hconst
  calc
    k * c * (∑ i ∈ I, (gap i) ^ 2) =
        ∑ i ∈ I, k * c * (gap i) ^ 2 := by
          rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ I, ∑ z ∈ J.filter (R i), weight z :=
      Finset.sum_le_sum hlocal
    _ = ∑ i ∈ I, ∑ z ∈ J, if R i z then weight z else 0 := by
      simp only [Finset.sum_filter]
    _ = ∑ z ∈ J, ∑ i ∈ I, if R i z then weight z else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ z ∈ J, weight z * (I.filter (fun i => R i z)).card := by
      apply Finset.sum_congr rfl
      intro z hz
      calc
        (∑ i ∈ I, if R i z then weight z else 0) =
            weight z * ∑ i ∈ I, if R i z then 1 else 0 := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              by_cases hR : R i z <;> simp [hR]
        _ = weight z * (I.filter (fun i => R i z)).card := by
          rw [Finset.sum_boole]
          simp
    _ ≤ ∑ z ∈ J, weight z * cap z := by
      apply Finset.sum_le_sum
      intro z hz
      exact Nat.mul_le_mul_left (weight z) (hcap z hz)

end Erdos489
