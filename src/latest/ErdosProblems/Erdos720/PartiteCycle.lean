import ErdosProblems.Erdos720.OneCycle

namespace Erdos720

open Finset SimpleGraph

/-- A form of the tripartite cycle lemma exposing exactly the two cross-part
no-hole hypotheses used by the connector construction. -/
lemma tripartite_partite_cycle (m height n : ℕ) (hm : 1 ≤ m)
    (hn : 3 ≤ n) (hnm : n ≤ m) (hh : 0 < height)
    (hpowLo : m ≤ 2 ^ height) (hpowHi : 2 ^ height ≤ 2 * m)
    (hgap : 2 * height + 2 < n)
    (R : SimpleGraph (TripType m))
    (hXY : ∀ X Y : Finset (Fin (128 * m) ⊕ Fin (128 * m)),
      X ⊆ sumLeftPart → Y ⊆ sumRightPart → X.card = m → Y.card = m →
      ∃ x ∈ X, ∃ y ∈ Y, R.Adj (Sum.inl x) (Sum.inl y))
    (hVW : ∀ X : Finset (Fin (128 * m) ⊕ Fin (128 * m)), X.card = m →
      ∀ W : Finset (Fin (2 * m - 1)), W.card = m →
      ∃ x ∈ X, ∃ z ∈ W, R.Adj (Sum.inl x) (Sum.inr z)) :
    cycleGraph n ⊑ R := by
  classical
  have hpowSucc : 2 ^ (height + 1) ≤ 4 * m := by
    rw [pow_succ]
    omega
  rcases Nat.even_or_odd n with heven | hodd
  · obtain ⟨t, ht⟩ := heven
    let q := n - 1 - 2 * height
    have hq : 0 < q := by omega
    have hcap : 1 + q + 2 * (2 ^ (height + 1) - 2) ≤ 9 * m := by
      dsimp [q]
      omega
    let K := completeBipartiteGraph (Fin (128 * m)) (Fin (128 * m))
    let G := (R.comap (fun v => Sum.inl v)) ⊓ K
    have hG : G ≤ K := inf_le_right
    have hredHole : ∀ X Y : Finset (Fin (128 * m) ⊕ Fin (128 * m)),
        X ⊆ sumLeftPart → Y ⊆ sumRightPart → X.card = m → Y.card = m →
        ∃ x ∈ X, ∃ y ∈ Y, G.Adj x y := by
      intro X Y hX hY hXcard hYcard
      obtain ⟨x, hx, y, hy, hxy⟩ := hXY X Y hX hY hXcard hYcard
      refine ⟨x, hx, y, hy, hxy, ?_⟩
      obtain ⟨u, rfl⟩ := mem_sumLeftPart.mp (hX hx)
      obtain ⟨v, rfl⟩ := mem_sumRightPart.mp (hY hy)
      simp [K]
    have hcycleG := bipartite_connector_closes m height q (t - 1) hm hh hq hpowLo
      (by dsimp [q]; omega) hcap G hG hredHole
    have hcycleG' : cycleGraph n ⊑ G := by
      have heq : 2 * height + q + 1 = n := by dsimp [q]; omega
      rw [heq] at hcycleG
      exact hcycleG
    have htoComap : G ⊑ R.comap (fun v => Sum.inl v) :=
      IsContained.of_le inf_le_left
    have htoR : R.comap (fun v => Sum.inl v) ⊑ R :=
      (Embedding.comap Function.Embedding.inl R).isContained
    exact hcycleG'.trans (htoComap.trans htoR)
  · obtain ⟨t, ht⟩ := hodd
    let q := n - 2 - 2 * height
    have hq : 0 < q := by omega
    have hcap : 1 + q + 2 * (2 ^ (height + 1) - 2) ≤ 9 * m := by
      dsimp [q]
      omega
    have hcycle := tripartite_connector_two_edge_closes m height q hm hh hq hpowLo
      hcap R hXY hVW
    have heq : 2 * height + q + 2 = n := by dsimp [q]; omega
    rw [heq] at hcycle
    exact hcycle

end Erdos720
