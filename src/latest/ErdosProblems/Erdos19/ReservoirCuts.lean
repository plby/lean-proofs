import ErdosProblems.Erdos19.GraphLoadStep

/-! # Cut expansion after deleting bounded reservoir loads -/

namespace Erdos19

open Finset
open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem cut_edge_ncard_le_of_degree_bound (R : _root_.SimpleGraph V)
    (X Y : Finset V) (hXY : Disjoint X Y) (L : ℕ)
    (hL : ∀ v ∈ X, (R.neighborSet v).ncard ≤ L) :
    (R.between (X : Set V) (Y : Set V)).edgeSet.ncard ≤ X.card * L := by
  classical
  let C := R.between (X : Set V) (Y : Set V)
  have hC : C.IsBipartiteWith (X : Set V) (Y : Set V) :=
    R.between_isBipartiteWith (Finset.disjoint_coe.mpr hXY)
  have hcount : C.edgeFinset.card ≤ X.card * L := by
    rw [← C.isBipartiteWith_sum_degrees_eq_card_edges hC]
    calc
      ∑ v ∈ X, C.degree v ≤ ∑ _v ∈ X, L := by
        apply sum_le_sum
        intro v hv
        have hd := Set.ncard_le_ncard (show C.neighborSet v ⊆ R.neighborSet v from fun _ h ↦ h.1)
        simpa only [← card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] using hd.trans (hL v hv)
      _ = X.card * L := by simp
  simpa only [edgeFinset, Set.toFinset_card, Set.fintypeCard_eq_ncard] using hcount

theorem reservoir_cut_after_loads (R U : _root_.SimpleGraph V)
    (X Y : Finset V) (hXY : Disjoint X Y) (L : ℕ)
    (hL : ∀ v ∈ X, ((R ⊓ U).neighborSet v).ncard ≤ L) :
    (R.between (X : Set V) (Y : Set V)).edgeSet.ncard ≤
      ((R \ U).between (X : Set V) (Y : Set V)).edgeSet.ncard + X.card * L := by
  have hdecomp : R.between (X : Set V) (Y : Set V) =
      (R \ U).between (X : Set V) (Y : Set V) ⊔
      (R ⊓ U).between (X : Set V) (Y : Set V) := by
    ext x y
    simp only [between_adj, sup_adj, sdiff_adj, inf_adj]
    tauto
  have hcount := cut_edge_ncard_le_of_degree_bound (R ⊓ U) X Y hXY L hL
  calc
    (R.between (X : Set V) (Y : Set V)).edgeSet.ncard =
        (((R \ U).between (X : Set V) (Y : Set V)).edgeSet ∪
          ((R ⊓ U).between (X : Set V) (Y : Set V)).edgeSet).ncard := by
      rw [hdecomp, edgeSet_sup]
    _ ≤ ((R \ U).between (X : Set V) (Y : Set V)).edgeSet.ncard +
        ((R ⊓ U).between (X : Set V) (Y : Set V)).edgeSet.ncard := Set.ncard_union_le _ _
    _ ≤ ((R \ U).between (X : Set V) (Y : Set V)).edgeSet.ncard + X.card * L :=
      Nat.add_le_add_left hcount _

theorem reservoir_cut_survives_loads (R U : _root_.SimpleGraph V) (q L : ℕ)
    (hL : ∀ v, ((R ⊓ U).neighborSet v).ncard ≤ L)
    (hcut : ∀ X Y : Finset V, Disjoint X Y → X.card = q → Y.card = q →
      q * (L + 1) < (R.between (X : Set V) (Y : Set V)).edgeSet.ncard) :
    ∀ X Y : Finset V, Disjoint X Y → X.card = q → Y.card = q →
      q < ((R \ U).between (X : Set V) (Y : Set V)).edgeFinset.card := by
  intro X Y hXY hX hY
  have hbound := reservoir_cut_after_loads R U X Y hXY L (fun v _ ↦ hL v)
  have hlarge := hcut X Y hXY hX hY
  rw [hX] at hbound
  have h : q < ((R \ U).between (X : Set V) (Y : Set V)).edgeSet.ncard := by
    nlinarith only [hbound, hlarge]
  simpa only [edgeFinset, Set.toFinset_card, Set.fintypeCard_eq_ncard] using h

#print axioms reservoir_cut_survives_loads

end Erdos19
