import ErdosProblems.Erdos19.ProjectiveCoverBound
import ErdosProblems.Erdos19.DenseCore

/-! # A dense near-projective core excludes very large edges everywhere

The counted family is the core, but the distinguished edge may lie anywhere
in the hypergraph. Thus the upper size bound also controls peeled edges.
-/

namespace Erdos19.SetHypergraph

open Finset

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

theorem dense_core_card_lower (H : SetHypergraph V) (S : Finset H) (k : ℕ)
    (hS : S.Nonempty) (hdense : IsDenseCore H.lineGraph S k) : k ≤ S.card - 1 := by
  classical
  obtain ⟨e, he⟩ := hS
  have hsub : S.filter (H.lineGraph.Adj e) ⊆ S.erase e := by
    intro f hf
    obtain ⟨hfS, hef⟩ := mem_filter.mp hf
    exact mem_erase.mpr ⟨hef.1.symm, hfS⟩
  have h := (hdense e he).trans (card_le_card hsub)
  simpa only [card_erase_of_mem he] using h

theorem edge_size_lt_of_dense_projective_core
    (H : SetHypergraph V) (hlinear : H.IsLinear) (n t k : ℕ)
    (hvertices : Fintype.card V = n)
    (ht : 1024 ≤ t) (hkt : 64 * t ≤ projectiveScale n)
    (hk : n - n / t ≤ k) (S : Finset H) (hS : S.Nonempty)
    (hdense : IsDenseCore H.lineGraph S k)
    (hmin : ∀ e ∈ S, projectiveScale n - projectiveScale n / t ≤ e.1.ncard) :
    ∀ e : H, e.1.ncard < 8 * (n / t) := by
  have hn : 2 ≤ n := by
    by_contra hnot
    have hscale : projectiveScale n ≤ 1 :=
      Nat.find_min' (exists_projectiveScale n) (by omega)
    omega
  have hbudget := projective_outside_budget_saving_arithmetic n (projectiveScale n) t
    ht hkt (projectiveScale_pred_sq_add_le hn) (le_projectiveScale_sq_add n)
  have hSsize := hk.trans (H.dense_core_card_lower S k hS hdense)
  intro e
  by_contra hnot
  have hlarge : 8 * (n / t) ≤ e.1.ncard := Nat.le_of_not_gt hnot
  have hcount := H.edge_family_count_mul_le_outside_pair_budget hlinear S e
    (projectiveScale n - projectiveScale n / t) hmin
  rw [hvertices] at hcount
  have hprod := Nat.mul_le_mul_right
    ((projectiveScale n - projectiveScale n / t - 1) *
      (projectiveScale n - projectiveScale n / t - 2)) hSsize
  have hout : (n - e.1.ncard) * (n - e.1.ncard - 1) ≤
      (n - 8 * (n / t)) * (n - 8 * (n / t) - 1) :=
    Nat.mul_le_mul (Nat.sub_le_sub_left hlarge n)
      (Nat.sub_le_sub_right (Nat.sub_le_sub_left hlarge n) 1)
  omega

#print axioms edge_size_lt_of_dense_projective_core

end Erdos19.SetHypergraph
