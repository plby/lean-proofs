import ErdosProblems.Erdos19.GraphOutliers

/-! # A large buffer of low graph-degree vertices outside the near-complete case -/

namespace Erdos19

open Finset
open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

theorem sum_nonneighbors_le_outliers_bound {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) (d : ℕ) :
    (∑ v : V, (G.neighborSet v)ᶜ.ncard) ≤
      (degreeOutliers G d).ncard * Fintype.card V + Fintype.card V * d := by
  have hlocal (v : V) : (G.neighborSet v)ᶜ.ncard ≤
      (if v ∈ degreeOutliers G d then Fintype.card V else 0) + d := by
    by_cases hv : v ∈ degreeOutliers G d
    · rw [if_pos hv]
      have h := Set.ncard_le_ncard (Set.subset_univ (G.neighborSet v)ᶜ)
      simp only [Set.ncard_univ, Nat.card_eq_fintype_card] at h
      omega
    · rw [if_neg hv]
      have hdegree : Fintype.card V ≤ (G.neighborSet v).ncard + d := Nat.le_of_not_lt hv
      have hsum := Set.ncard_add_ncard_compl (G.neighborSet v)
      rw [Nat.card_eq_fintype_card] at hsum
      omega
  have hcount : (∑ v : V, if v ∈ degreeOutliers G d then Fintype.card V else 0) =
      (degreeOutliers G d).ncard * Fintype.card V := by
    rw [ncard_eq_sum_indicator, sum_mul]
    apply sum_congr rfl
    intro v _
    split_ifs <;> simp
  calc
    _ ≤ ∑ v : V, ((if v ∈ degreeOutliers G d then Fintype.card V else 0) + d) :=
      sum_le_sum (fun v _ ↦ hlocal v)
    _ = _ := by rw [sum_add_distrib, hcount]; simp

namespace SetHypergraph

theorem low_degree_buffer_card_lower (n s : ℕ) (hn : 0 < n)
    (H : SetHypergraph (Fin n)) (hmissing : n ^ 2 ≤ s * H.missingOrderedPairs.card) :
    n / (4 * s) ≤ (degreeOutliers H.twoGraph (n / (4 * s))).ncard := by
  let q := n / (4 * s)
  let y := (degreeOutliers H.twoGraph q).ncard
  have hsum := sum_nonneighbors_le_outliers_bound H.twoGraph q
  rw [H.sum_twoGraph_nonneighbors n, Fintype.card_fin] at hsum
  change H.missingOrderedPairs.card + n ≤ y * n + n * q at hsum
  change q ≤ y
  by_contra hnot
  have hy : y ≤ q := by omega
  have hytimes := Nat.mul_le_mul_right n hy
  have hbound : H.missingOrderedPairs.card + n ≤ 2 * n * q := by
    nlinarith only [hsum, hytimes]
  have hscale := Nat.mul_le_mul_left s hbound
  have hfloor : (4 * s) * q ≤ n := Nat.mul_div_le n (4 * s)
  have hfloorScale := Nat.mul_le_mul_left n hfloor
  have hn2 : 0 < n ^ 2 := pow_pos hn _
  nlinarith only [hmissing, hscale, hfloorScale, hn2]

#print axioms low_degree_buffer_card_lower

end SetHypergraph

end Erdos19
