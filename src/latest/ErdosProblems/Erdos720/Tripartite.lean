import ErdosProblems.Erdos720.OddCycle

namespace Erdos720

open Finset SimpleGraph

lemma tripartite_noHole_cycle (m height n : ℕ) (hm : 1 ≤ m)
    (hn : 3 ≤ n) (hnm : n ≤ m) (hh : 0 < height)
    (hpowLo : m ≤ 2 ^ height) (hpowHi : 2 ^ height ≤ 2 * m)
    (hgap : 2 * height + 2 < n)
    (R : SimpleGraph
      ((Fin (128 * m) ⊕ Fin (128 * m)) ⊕ Fin (2 * m - 1)))
    (hnoHole : ∀ X Y : Finset
        ((Fin (128 * m) ⊕ Fin (128 * m)) ⊕ Fin (2 * m - 1)),
      Disjoint X Y → X.card = m → Y.card = m →
      ∃ x ∈ X, ∃ y ∈ Y, R.Adj x y) :
    cycleGraph n ⊑ R := by
  classical
  let e : (Fin (128 * m) ⊕ Fin (128 * m)) ↪
      ((Fin (128 * m) ⊕ Fin (128 * m)) ⊕ Fin (2 * m - 1)) :=
    Function.Embedding.inl
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
      have hXY : Disjoint X Y := sumParts_disjoint.mono hX hY
      obtain ⟨x, hx, y, hy, hxy⟩ := hnoHole (X.map e) (Y.map e)
        ((Finset.disjoint_map e).2 hXY) (by simpa using hXcard) (by simpa using hYcard)
      rcases Finset.mem_map.mp hx with ⟨x', hx', hxeq⟩
      rcases Finset.mem_map.mp hy with ⟨y', hy', hyeq⟩
      subst x
      subst y
      refine ⟨x', hx', y', hy', hxy, ?_⟩
      obtain ⟨u, rfl⟩ := mem_sumLeftPart.mp (hX hx')
      obtain ⟨v, rfl⟩ := mem_sumRightPart.mp (hY hy')
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
      (Embedding.comap e R).isContained
    exact hcycleG'.trans (htoComap.trans htoR)
  · obtain ⟨t, ht⟩ := hodd
    let q := n - 2 - 2 * height
    have hq : 0 < q := by omega
    have hcap : 1 + q + 2 * (2 ^ (height + 1) - 2) ≤ 9 * m := by
      dsimp [q]
      omega
    have hXY : ∀ X Y : Finset (Fin (128 * m) ⊕ Fin (128 * m)),
        X ⊆ sumLeftPart → Y ⊆ sumRightPart → X.card = m → Y.card = m →
        ∃ x ∈ X, ∃ y ∈ Y, R.Adj (Sum.inl x) (Sum.inl y) := by
      intro X Y hX hY hXcard hYcard
      have hdisj : Disjoint X Y := sumParts_disjoint.mono hX hY
      obtain ⟨x, hx, y, hy, hxy⟩ := hnoHole (X.map e) (Y.map e)
        ((Finset.disjoint_map e).2 hdisj) (by simpa using hXcard) (by simpa using hYcard)
      rcases Finset.mem_map.mp hx with ⟨x', hx', hxeq⟩
      rcases Finset.mem_map.mp hy with ⟨y', hy', hyeq⟩
      subst x
      subst y
      exact ⟨x', hx', y', hy', hxy⟩
    have hVW : ∀ X : Finset (Fin (128 * m) ⊕ Fin (128 * m)), X.card = m →
        ∀ W : Finset (Fin (2 * m - 1)), W.card = m →
        ∃ x ∈ X, ∃ z ∈ W, R.Adj (Sum.inl x) (Sum.inr z) := by
      intro X hXcard W hWcard
      obtain ⟨x, hx, z, hz, hxz⟩ := hnoHole (X.map e)
        (W.map Function.Embedding.inr) (Finset.disjoint_map_inl_map_inr X W)
        (by simpa using hXcard) (by simpa using hWcard)
      rcases Finset.mem_map.mp hx with ⟨x', hx', hxeq⟩
      rcases Finset.mem_map.mp hz with ⟨z', hz', hzeq⟩
      subst x
      subst z
      exact ⟨x', hx', z', hz', hxz⟩
    have hcycle := tripartite_connector_two_edge_closes m height q hm hh hq hpowLo
      hcap R hXY hVW
    have heq : 2 * height + q + 2 = n := by dsimp [q]; omega
    rw [heq] at hcycle
    exact hcycle

lemma tripartite_cycle_or_hole (m height n : ℕ) (hm : 1 ≤ m)
    (hn : 3 ≤ n) (hnm : n ≤ m) (hh : 0 < height)
    (hpowLo : m ≤ 2 ^ height) (hpowHi : 2 ^ height ≤ 2 * m)
    (hgap : 2 * height + 2 < n)
    (R : SimpleGraph
      ((Fin (128 * m) ⊕ Fin (128 * m)) ⊕ Fin (2 * m - 1))) :
    cycleGraph n ⊑ R ∨
      ∃ X Y : Finset
          ((Fin (128 * m) ⊕ Fin (128 * m)) ⊕ Fin (2 * m - 1)),
        Disjoint X Y ∧ X.card = m ∧ Y.card = m ∧
          ∀ x ∈ X, ∀ y ∈ Y, ¬ R.Adj x y := by
  classical
  by_cases hnoHole : ∀ X Y : Finset
      ((Fin (128 * m) ⊕ Fin (128 * m)) ⊕ Fin (2 * m - 1)),
      Disjoint X Y → X.card = m → Y.card = m →
      ∃ x ∈ X, ∃ y ∈ Y, R.Adj x y
  · exact Or.inl (tripartite_noHole_cycle m height n hm hn hnm hh hpowLo hpowHi
      hgap R hnoHole)
  · right
    push_neg at hnoHole
    obtain ⟨X, Y, hdisj, hXcard, hYcard, hnone⟩ := hnoHole
    exact ⟨X, Y, hdisj, hXcard, hYcard, hnone⟩

end Erdos720
