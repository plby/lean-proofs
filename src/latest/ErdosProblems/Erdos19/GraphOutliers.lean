import ErdosProblems.Erdos19.MissingPairs
import ErdosProblems.Erdos19.BulkForbiddenBounds

/-! # Bounding exceptional vertices by the total number of missing pairs -/

namespace Erdos19

open Finset
open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

def degreeOutliers {V : Type*} [Fintype V] (G : _root_.SimpleGraph V) (a : ℕ) : Set V :=
  {v | (G.neighborSet v).ncard + a < Fintype.card V}

theorem degreeOutliers_markov {V : Type*} [Fintype V] (G : _root_.SimpleGraph V) (a : ℕ) :
    (degreeOutliers G a).ncard * (a + 1) ≤ ∑ v : V, (G.neighborSet v)ᶜ.ncard := by
  rw [ncard_eq_sum_indicator, sum_mul]
  apply sum_le_sum
  intro v _
  by_cases hv : v ∈ degreeOutliers G a
  · rw [if_pos hv, one_mul]
    have hcount := Set.ncard_add_ncard_compl (G.neighborSet v)
    rw [Nat.card_eq_fintype_card] at hcount
    change (G.neighborSet v).ncard + a < Fintype.card V at hv
    omega
  · rw [if_neg hv, zero_mul]
    exact Nat.zero_le _

theorem induced_compl_neighbor_ncard {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) (X : Set V) (v : ↥(Xᶜ)) :
    ((G.induce Xᶜ).neighborSet v).ncard = (G.neighborSet v.1 \ X).ncard := by
  have hpre : (G.induce Xᶜ).neighborSet v = Subtype.val ⁻¹' G.neighborSet v.1 := rfl
  rw [hpre, compl_subtype_preimage_ncard]

theorem degreeOutliers_bulk_degree {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) (a : ℕ) (v : ↥((degreeOutliers G a)ᶜ)) :
    (degreeOutliers G a)ᶜ.ncard ≤
      ((G.induce (degreeOutliers G a)ᶜ).neighborSet v).ncard + a := by
  have hdegree : Fintype.card V ≤ (G.neighborSet v.1).ncard + a := Nat.le_of_not_lt v.2
  have hcut := Set.ncard_le_ncard_sdiff_add_ncard (G.neighborSet v.1) (degreeOutliers G a)
  have hsplit := Set.ncard_add_ncard_compl (degreeOutliers G a)
  rw [Nat.card_eq_fintype_card] at hsplit
  rw [induced_compl_neighbor_ncard]
  omega

namespace SetHypergraph

theorem sum_twoGraph_nonneighbors (n : ℕ) (H : SetHypergraph (Fin n)) :
    (∑ v : Fin n, (H.twoGraph.neighborSet v)ᶜ.ncard) = H.missingOrderedPairs.card + n := by
  classical
  have hper (p : Fin n × Fin n) : (if ¬H.twoGraph.Adj p.1 p.2 then 1 else 0 : ℕ) =
      (if p.1 ≠ p.2 ∧ ¬H.twoGraph.Adj p.1 p.2 then 1 else 0) +
        (if p.1 = p.2 then 1 else 0) := by
    by_cases heq : p.1 = p.2
    · simp [heq]
    · simp [heq]
  calc
    (∑ v : Fin n, (H.twoGraph.neighborSet v)ᶜ.ncard) =
        ∑ v : Fin n, ∑ w : Fin n, if ¬H.twoGraph.Adj v w then 1 else 0 := by
      simp only [ncard_eq_sum_indicator, Set.mem_compl_iff, mem_neighborSet]
    _ = ∑ p : Fin n × Fin n, if ¬H.twoGraph.Adj p.1 p.2 then 1 else 0 := by
      rw [Fintype.sum_prod_type]
    _ = (∑ p : Fin n × Fin n, if p.1 ≠ p.2 ∧ ¬H.twoGraph.Adj p.1 p.2 then 1 else 0) +
        ∑ p : Fin n × Fin n, if p.1 = p.2 then 1 else 0 := by
      simp only [hper, sum_add_distrib]
    _ = H.missingOrderedPairs.card + n := by
      have hdiag : (∑ p : Fin n × Fin n, if p.1 = p.2 then 1 else 0 : ℕ) = n := by
        rw [Fintype.sum_prod_type]
        simp
      rw [hdiag]
      simp [missingOrderedPairs]

theorem twoGraph_degreeOutliers_markov (n a : ℕ) (H : SetHypergraph (Fin n)) :
    (degreeOutliers H.twoGraph a).ncard * (a + 1) ≤ H.missingOrderedPairs.card + n := by
  rw [← H.sum_twoGraph_nonneighbors n]
  exact degreeOutliers_markov H.twoGraph a

end SetHypergraph

theorem outlier_scale_bound (n s x M : ℕ) (hs : 0 < s)
    (hn : 4 * s * s ≤ n) (hM : 4 * s * s * M < n * n)
    (hcount : x * (n / s + 1) ≤ M + n) : x ≤ n / s := by
  by_contra hx
  have hx' : n / s + 1 ≤ x := by omega
  have hfloor : n < s * (n / s + 1) := Nat.lt_mul_div_succ n hs
  have hsquare : n * n < (s * (n / s + 1)) * (s * (n / s + 1)) :=
    Nat.mul_self_lt_mul_self hfloor
  have hcount' : (n / s + 1) * (n / s + 1) ≤ M + n :=
    (Nat.mul_le_mul_right _ hx').trans hcount
  have hscaled := Nat.mul_le_mul_left (s * s) hcount'
  have hsmall : n * n < (s * s) * M + (s * s) * n := by
    nlinarith only [hsquare, hscaled]
  have hn' := Nat.mul_le_mul_right n hn
  nlinarith only [hsmall, hn', hM]

#print axioms degreeOutliers_bulk_degree
#print axioms outlier_scale_bound

end Erdos19
