import ErdosProblems.Erdos19.DenseCore
import ErdosProblems.Erdos19.RankPairBudget
import ErdosProblems.Erdos19.CrossEdgeCounting

/-! # Concentration of a dense linear-hypergraph core

This is the integer double-counting step in the large-edge argument. The
reference edge is explicitly excluded from the nonneighbor family; its
possible contribution is the final one-unit term in the estimate.
-/

namespace Erdos19

open Finset

attribute [local instance] Classical.propDecidable

private theorem card_mul_sub_le_of_bipartite_degree_slack
    {V : Type*} [DecidableEq V] (G : _root_.SimpleGraph V)
    (W X Y : Finset V) (hXW : X ⊆ W) (hYW : Y ⊆ W) (hXY : Disjoint X Y)
    (m b u : ℕ)
    (hleft : ∀ x ∈ X, m ≤ (Y.filter (G.Adj x)).card + u + b)
    (hright : ∀ y ∈ Y, (X.filter (G.Adj y)).card ≤ u) :
    X.card * (m - b) ≤ W.card * u := by
  classical
  have hsum : X.card * m ≤ Y.card * u + X.card * (u + b) := by
    calc
      X.card * m = ∑ _x ∈ X, m := by simp
      _ ≤ ∑ x ∈ X, ((Y.filter (G.Adj x)).card + (u + b)) :=
        sum_le_sum (fun x hx ↦ by simpa only [Nat.add_assoc] using hleft x hx)
      _ = (∑ x ∈ X, (Y.filter (G.Adj x)).card) + X.card * (u + b) := by
        rw [sum_add_distrib]; simp
      _ = (∑ y ∈ Y, (X.filter (G.Adj y)).card) + X.card * (u + b) := by
        congr 1
        calc
          (∑ x ∈ X, (Y.filter (G.Adj x)).card) =
              ∑ x ∈ X, ∑ y ∈ Y, if G.Adj x y then (1 : ℕ) else 0 := by simp
          _ = ∑ y ∈ Y, ∑ x ∈ X, if G.Adj x y then (1 : ℕ) else 0 := by rw [sum_comm]
          _ = ∑ y ∈ Y, (X.filter (G.Adj y)).card := by
            simp [G.adj_comm]
      _ ≤ (∑ _y ∈ Y, u) + X.card * (u + b) := by
        exact Nat.add_le_add_right (sum_le_sum hright) _
      _ = Y.card * u + X.card * (u + b) := by simp
  have hcard : X.card + Y.card ≤ W.card := by
    rw [← card_union_of_disjoint hXY]
    exact card_le_card (union_subset hXW hYW)
  by_cases hbm : b ≤ m
  · have hsub : m - b + b = m := Nat.sub_add_cancel hbm
    have hmul := Nat.mul_le_mul_right u hcard
    nlinarith only [hsum, hsub, hmul]
  · simp only [Nat.sub_eq_zero_of_le (le_of_not_ge hbm), Nat.mul_zero]
    exact Nat.zero_le _

namespace SetHypergraph

variable {X : Type*} [Fintype X]

theorem dense_core_rank_window_card (H : SetHypergraph X)
    (hlinear : H.IsLinear) (S : Finset H) (m r R₁ R₂ b₁ b₂ : ℕ)
    (hr : 2 ≤ r) (hR : R₁ ≤ R₂) (hmin : ∀ f ∈ S, r ≤ f.1.ncard)
    (hdense : IsDenseCore H.lineGraph S m) (e : H) (heS : e ∈ S)
    (her : e.1.ncard = r)
    (hlarge₁ : ((S.filter (H.lineGraph.Adj e)).filter
      fun f ↦ R₁ < f.1.ncard).card ≤ b₁)
    (hlarge₂ : ∀ f ∈ S, H.lineGraph.Adj e f → f.1.ncard ≤ R₁ →
      ((S.filter (H.lineGraph.Adj f)).filter
        fun g ↦ R₂ < g.1.ncard).card ≤ b₂) :
    (m - b₁) * (m - (b₂ + (Fintype.card X - 1) / (r - 1) + 1)) ≤
      (S.filter fun f ↦ f.1.ncard ≤ R₂).card * (r * R₂) := by
  classical
  let N := S.filter (H.lineGraph.Adj e)
  let A := N.filter fun f ↦ f.1.ncard ≤ R₁
  let W := S.filter fun f ↦ f.1.ncard ≤ R₂
  let B := W.filter fun f ↦ f ≠ e ∧ ¬H.lineGraph.Adj e f
  let q := (Fintype.card X - 1) / (r - 1)
  have hAW : A ⊆ W := by
    intro f hf
    obtain ⟨hfN, hfsize⟩ := mem_filter.mp hf
    exact mem_filter.mpr ⟨(mem_filter.mp hfN).1, hfsize.trans hR⟩
  have hBW : B ⊆ W := filter_subset _ _
  have hAB : Disjoint A B := by
    apply disjoint_left.mpr
    intro f hfA hfB
    exact (mem_filter.mp hfB).2.2 (mem_filter.mp (mem_filter.mp hfA).1).2
  have hAcard : m - b₁ ≤ A.card := by
    have hsplit : A.card + (N.filter fun f ↦ ¬f.1.ncard ≤ R₁).card = N.card :=
      card_filter_add_card_filter_not _
    have hN := hdense e heS
    have hlarge : (N.filter fun f ↦ ¬f.1.ncard ≤ R₁).card ≤ b₁ := by
      simpa only [not_le, N] using hlarge₁
    change m ≤ N.card at hN
    omega
  have hleft : ∀ f ∈ A,
      m ≤ (B.filter (H.lineGraph.Adj f)).card + r * R₂ + (b₂ + q + 1) := by
    intro f hfA
    obtain ⟨hfN, hfsize⟩ := mem_filter.mp hfA
    obtain ⟨hfS, hef⟩ := mem_filter.mp hfN
    let D := S.filter (H.lineGraph.Adj f)
    let L := D.filter fun g ↦ R₂ < g.1.ncard
    let C := D.filter (H.lineGraph.Adj e)
    let T := B.filter (H.lineGraph.Adj f)
    have hL : L.card ≤ b₂ := hlarge₂ f hfS hef hfsize
    have hC : C.card ≤ r * R₂ + q := by
      have hraw := H.card_common_neighbors_of_min_rank_le hlinear e f hef.1 hef.2
        C (by
          intro g hg
          obtain ⟨hgD, heg⟩ := mem_filter.mp hg
          exact ⟨heg, (mem_filter.mp hgD).2⟩)
        r hr (fun g hg ↦ hmin g (mem_filter.mp (mem_filter.mp hg).1).1)
      have hprod : (e.1.ncard - 1) * (f.1.ncard - 1) ≤ r * R₂ := by
        rw [her]
        exact Nat.mul_le_mul (Nat.sub_le _ _) ((Nat.sub_le _ _).trans (hfsize.trans hR))
      exact hraw.trans (Nat.add_le_add_right hprod q)
    have hcover : D ⊆ L ∪ C ∪ T ∪ {e} := by
      intro g hg
      by_cases hglarge : R₂ < g.1.ncard
      · exact mem_union_left _ (mem_union_left _
          (mem_union_left _ (mem_filter.mpr ⟨hg, hglarge⟩)))
      by_cases heg : H.lineGraph.Adj e g
      · exact mem_union_left _ (mem_union_left _
          (mem_union_right _ (mem_filter.mpr ⟨hg, heg⟩)))
      by_cases hge : g = e
      · exact mem_union_right _ (mem_singleton.mpr hge)
      · apply mem_union_left
        apply mem_union_right
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_filter.mpr
          ⟨(mem_filter.mp hg).1, le_of_not_gt hglarge⟩, hge, heg⟩,
          (mem_filter.mp hg).2⟩
    have hcard : D.card ≤ L.card + C.card + T.card + 1 := by
      calc
        D.card ≤ (L ∪ C ∪ T ∪ {e}).card := card_le_card hcover
        _ ≤ (L ∪ C ∪ T).card + ({e} : Finset H).card := card_union_le _ _
        _ ≤ (L ∪ C).card + T.card + ({e} : Finset H).card := by
          exact Nat.add_le_add_right (card_union_le _ _) _
        _ ≤ L.card + C.card + T.card + ({e} : Finset H).card := by
          exact Nat.add_le_add_right (Nat.add_le_add_right (card_union_le _ _) _) _
        _ = L.card + C.card + T.card + 1 := by simp
    have hd : m ≤ D.card := hdense f hfS
    change m ≤ T.card + r * R₂ + (b₂ + q + 1)
    omega
  have hright : ∀ f ∈ B, (A.filter (H.lineGraph.Adj f)).card ≤ r * R₂ := by
    intro f hfB
    obtain ⟨hfW, hfe, hef⟩ := mem_filter.mp hfB
    have hdis : Disjoint e.1 f.1 := by
      apply Set.disjoint_left.mpr
      intro x hxe hxf
      exact hef ⟨hfe.symm, x, hxe, hxf⟩
    have hraw := H.card_common_neighbors_of_disjoint_le hlinear e f hdis
      (A.filter (H.lineGraph.Adj f)) (by
        intro g hg
        obtain ⟨hgA, hfg⟩ := mem_filter.mp hg
        exact ⟨(mem_filter.mp (mem_filter.mp hgA).1).2, hfg⟩)
    rw [her] at hraw
    exact hraw.trans (Nat.mul_le_mul_left r (mem_filter.mp hfW).2)
  have hcount := card_mul_sub_le_of_bipartite_degree_slack H.lineGraph W A B
    hAW hBW hAB m (b₂ + q + 1) (r * R₂) hleft hright
  exact (Nat.mul_le_mul_right _ hAcard).trans hcount

#print axioms dense_core_rank_window_card

end SetHypergraph
end Erdos19
