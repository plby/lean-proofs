import Mathlib

open scoped BigOperators
open Finset

namespace Erdos1165

/-- Reindex the positive integers through `n + 1` by the range beginning at zero. -/
lemma sum_Icc_one_succ_eq_sum_range (a : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 (n + 1), a k) =
      ∑ j ∈ Finset.range (n + 1), a (j + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc]
  rw [Finset.range_eq_Ico]
  have hmap : (Finset.Ico 0 (n + 1)).map (addRightEmbedding 1) =
      Finset.Ico 1 (n + 1 + 1) := by
    simpa using Finset.map_add_right_Ico 0 (n + 1) 1
  rw [← hmap]
  rw [Finset.sum_map]
  rfl

/-- Convert the customary `Icc 1 m` renewal inequality to the zero-based form used below. -/
lemma renewal_range_of_Icc
    (f u : ℕ → ℝ)
    (h : ∀ m, 0 < m →
      u m ≤ ∑ k ∈ Finset.Icc 1 m, f k * u (m - k)) :
    ∀ n, u (n + 1) ≤
      ∑ k ∈ Finset.range (n + 1), f (k + 1) * u (n - k) := by
  intro n
  have hn := h (n + 1) (by omega)
  rw [sum_Icc_one_succ_eq_sum_range] at hn
  simpa using hn

private def triangle (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range N).biUnion Finset.HasAntidiagonal.antidiagonal

private lemma antidiagonal_pairwiseDisjoint (N : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.range N) : Set ℕ)
      Finset.HasAntidiagonal.antidiagonal := by
  intro i hi j hj hij
  change Disjoint (Finset.HasAntidiagonal.antidiagonal i)
    (Finset.HasAntidiagonal.antidiagonal j)
  rw [Finset.disjoint_left]
  intro p hpi hpj
  apply hij
  exact (Finset.HasAntidiagonal.mem_antidiagonal.mp hpi).symm.trans
    (Finset.HasAntidiagonal.mem_antidiagonal.mp hpj)

private lemma triangle_subset_product (N : ℕ) :
    triangle N ⊆ Finset.range N ×ˢ Finset.range N := by
  intro p hp
  rcases Finset.mem_biUnion.mp hp with ⟨n, hn, hp⟩
  have hp_sum : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have hn_lt : n < N := Finset.mem_range.mp hn
  rw [Finset.mem_product]
  constructor <;> rw [Finset.mem_range]
  · exact (Nat.le_add_right p.1 p.2).trans_lt (hp_sum.trans_lt hn_lt)
  · exact (Nat.le_add_left p.2 p.1).trans_lt (add_comm p.2 p.1 ▸ hp_sum.trans_lt hn_lt)

private lemma triangle_sum_le_rectangle
    (g u : ℕ → ℝ) (hg : ∀ n, 0 ≤ g n) (hu : ∀ n, 0 ≤ u n) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, g p.1 * u p.2) ≤
      (∑ k ∈ Finset.range N, g k) * ∑ j ∈ Finset.range N, u j := by
  rw [← Finset.sum_biUnion (antidiagonal_pairwiseDisjoint N)]
  rw [Finset.sum_mul_sum]
  calc
    _ ≤ ∑ p ∈ Finset.range N ×ˢ Finset.range N, g p.1 * u p.2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (triangle_subset_product N)
      intro p hp_rect hp_not_triangle
      exact mul_nonneg (hg p.1) (hu p.2)
    _ = _ := by rw [Finset.sum_product]

/-- A nonnegative renewal sequence whose interarrival mass is strictly subprobabilistic is
summable.  The renewal upper bound is written with the indexing used for first-return
probabilities: `f (k + 1)` is the mass of an excursion of length `k + 1`.  An exact renewal
identity is the special case in which the displayed inequality is an equality. -/
theorem summable_of_renewal_subprobability
    (f u : ℕ → ℝ)
    (hf_nonneg : ∀ n, 0 ≤ f n)
    (hu_nonneg : ∀ n, 0 ≤ u n)
    (hu_zero : u 0 = 1)
    (hrenew : ∀ n, u (n + 1) ≤
      ∑ k ∈ Finset.range (n + 1), f (k + 1) * u (n - k))
    (hf_summable : Summable f)
    (hf_mass_lt_one : (∑' n, f n) < 1) :
    Summable u := by
  let q : ℝ := ∑' n, f n
  have hq_nonneg : 0 ≤ q := tsum_nonneg hf_nonneg
  have hq_lt_one : q < 1 := hf_mass_lt_one
  have hf_partial_le (N : ℕ) : ∑ k ∈ Finset.range N, f (k + 1) ≤ q := by
    rw [← Finset.sum_image]
    · exact hf_summable.sum_le_tsum _ (fun n _ ↦ hf_nonneg n)
    · exact fun _ _ _ _ h ↦ Nat.succ.inj h
  have hu_partial_mono (N : ℕ) :
      (∑ j ∈ Finset.range N, u j) ≤ ∑ j ∈ Finset.range (N + 1), u j := by
    rw [Finset.sum_range_succ]
    exact le_add_of_nonneg_right (hu_nonneg N)
  have hpartial (N : ℕ) :
      (∑ j ∈ Finset.range N, u j) ≤ 1 / (1 - q) := by
    cases N with
    | zero =>
        simp only [Finset.range_zero, Finset.sum_empty]
        exact div_nonneg zero_le_one (sub_nonneg.mpr hq_lt_one.le)
    | succ N =>
        have hrenew_sum :
            (∑ n ∈ Finset.range N, u (n + 1)) ≤
              ∑ n ∈ Finset.range N,
                ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
                  f (p.1 + 1) * u p.2 := by
          apply Finset.sum_le_sum
          intro n hn
          exact (hrenew n).trans_eq (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun k j ↦ f (k + 1) * u j) n).symm
        have htriangle := triangle_sum_le_rectangle
          (fun k ↦ f (k + 1)) u (fun k ↦ hf_nonneg (k + 1)) hu_nonneg N
        have hS :
            (∑ j ∈ Finset.range (N + 1), u j) ≤
              1 + q * ∑ j ∈ Finset.range (N + 1), u j := by
          have hUN : 0 ≤ ∑ j ∈ Finset.range N, u j :=
            Finset.sum_nonneg fun j _ ↦ hu_nonneg j
          calc
            (∑ j ∈ Finset.range (N + 1), u j) =
                (∑ n ∈ Finset.range N, u (n + 1)) + 1 := by
              rw [Finset.sum_range_succ', hu_zero]
            _ ≤ (∑ n ∈ Finset.range N,
                ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
                  f (p.1 + 1) * u p.2) + 1 := add_le_add_left hrenew_sum 1
            (∑ n ∈ Finset.range N,
                ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
                  f (p.1 + 1) * u p.2) + 1 ≤
                (∑ k ∈ Finset.range N, f (k + 1)) *
                  (∑ j ∈ Finset.range N, u j) + 1 := add_le_add_left htriangle 1
            _ ≤ q * (∑ j ∈ Finset.range N, u j) + 1 :=
              add_le_add_left (mul_le_mul_of_nonneg_right (hf_partial_le N) hUN) 1
            _ ≤ q * (∑ j ∈ Finset.range (N + 1), u j) + 1 :=
              add_le_add_left (mul_le_mul_of_nonneg_left (hu_partial_mono N) hq_nonneg) 1
            _ = 1 + q * (∑ j ∈ Finset.range (N + 1), u j) := add_comm _ _
        apply (le_div_iff₀ (sub_pos.mpr hq_lt_one)).2
        nlinarith
  exact summable_of_sum_range_le hu_nonneg hpartial

/-- Contrapositive form of `summable_of_renewal_subprobability`: a nonsummable renewal sequence
forces the total interarrival mass to be at least one. -/
theorem one_le_tsum_of_not_summable_renewal
    (f u : ℕ → ℝ)
    (hf_nonneg : ∀ n, 0 ≤ f n)
    (hu_nonneg : ∀ n, 0 ≤ u n)
    (hu_zero : u 0 = 1)
    (hrenew : ∀ n, u (n + 1) ≤
      ∑ k ∈ Finset.range (n + 1), f (k + 1) * u (n - k))
    (hf_summable : Summable f)
    (hu_not_summable : ¬Summable u) :
    1 ≤ ∑' n, f n := by
  by_contra h
  exact hu_not_summable <| summable_of_renewal_subprobability f u hf_nonneg hu_nonneg
    hu_zero hrenew hf_summable (lt_of_not_ge h)

end Erdos1165
