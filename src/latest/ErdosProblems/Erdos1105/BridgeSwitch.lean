import ErdosProblems.Erdos1105.BridgeExchange
import ErdosProblems.Erdos1105.ShortestChain

namespace Erdos1105

open SimpleGraph

/-- A same-colored replacement for `e` crosses the reference cut at `f`. -/
def BridgeSwitch {V C : Type*} (G R : SimpleGraph V) (c : Sym2 V → C)
    (e f : R.edgeSet) : Prop :=
  R.IsBridge f.val ∧ ∃ a b, G.Adj a b ∧ c s(a, b) = c e.val ∧
    ¬(R.deleteEdges {f.val}).Reachable a b

/-- A shortest sequence of bridge-color switches can be performed in
order. At each step the next edge becomes a non-bridge while all later
reference cuts remain intact. -/
theorem bridge_switch_nonbridge_realizable {V C : Type*} {G R : SimpleGraph V}
    {c : Sym2 V → C} (hR : ColorRepresentative G c R) (hconn : R.Preconnected)
    {e f : R.edgeSet} (he : ¬R.IsBridge e.val)
    (hreach : Relation.ReflTransGen (BridgeSwitch G R c) e f) :
    ∃ K : SimpleGraph V, ColorRepresentative G c K ∧ K.Preconnected ∧
      f.val ∈ K.edgeSet ∧ ¬K.IsBridge f.val := by
  classical
  obtain ⟨n, p, hp₀, hpn, hp, hshort⟩ := exists_shortest_chain hreach
  have hbridge (j : ℕ) (hj₀ : 0 < j) (hj : j ≤ n) : R.IsBridge (p j).val := by
    have h := (hp (j - 1) (by omega)).1
    simpa only [Nat.sub_add_cancel hj₀] using h
  have hdistinct (i j : ℕ) (hij : i < j) (hj : j ≤ n) : p i ≠ p j := by
    intro heq
    by_cases hi : i = 0
    · subst i
      have h := hbridge j (by omega) hj
      rw [← heq, hp₀] at h
      exact he h
    · have hprev := hp (i - 1) (by omega)
      have hipos : 1 ≤ i := by omega
      rw [Nat.sub_add_cancel hipos, heq] at hprev
      exact hshort (i - 1) j (by omega) hj hprev
  have hstates : ∀ i, i ≤ n → ∃ K : SimpleGraph V,
      ColorRepresentative G c K ∧ K.Preconnected ∧
      (∀ j, i ≤ j → j ≤ n → (p j).val ∈ K.edgeSet) ∧
      ¬K.IsBridge (p i).val ∧
      (∀ j, i < j → j ≤ n → ∀ a b, K.Adj a b → s(a, b) ≠ (p j).val →
        (R.deleteEdges {(p j).val}).Reachable a b) := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨R, hR, hconn, fun j _ _ ↦ (p j).property, ?_, ?_⟩
      · simpa only [hp₀] using he
      · intro j _ _ a b hab hne
        exact (show (R.deleteEdges {(p j).val}).Adj a b from
          deleteEdges_adj.mpr ⟨hab, hne⟩).reachable
    | succ i ih =>
      intro hi
      obtain ⟨K, hK, hKconn, hfuture, hnb, hrespect⟩ := ih (by omega)
      obtain ⟨_, a, b, hab, hcol, hcross⟩ := hp i (by omega)
      let ei : K.edgeSet := ⟨(p i).val, hfuture i le_rfl (by omega)⟩
      let di : G.edgeSet := ⟨s(a, b), hab⟩
      let dt : (⊤ : SimpleGraph V).edgeSet := ⟨s(a, b), hab.ne⟩
      let K' := swapRepresentative K ei.val di.val
      have hK' : ColorRepresentative G c K' := hK.swap ei di hcol
      have hKconn' : K'.Preconnected := preconnected_swap_of_not_isBridge hKconn hnb dt
      have hnb' : ¬K'.IsBridge (p (i + 1)).val :=
        crossing_swap_makes_nonbridge R K c hK.rainbow hKconn ei hnb (p (i + 1)).val
          (hrespect (i + 1) (by omega) hi) hab.ne hcol hcross
      refine ⟨K', hK', hKconn', ?_, hnb', ?_⟩
      · intro j hij hj
        apply (mem_swapRepresentative K ei.val dt (p j).val).mpr
        refine Or.inl ⟨hfuture j (by omega) hj, ?_⟩
        intro heq
        exact hdistinct i j (by omega) hj (Subtype.ext heq.symm)
      · intro j hij hj x y hxy hne
        have hdi : (R.deleteEdges {(p j).val}).Reachable a b := by
          by_contra hnot
          apply hshort i j (by omega) hj
          exact ⟨hbridge j (by omega) hj, a, b, hab, hcol, hnot⟩
        rcases (mem_swapRepresentative K ei.val dt s(x, y)).mp hxy with hold | hnew
        · exact hrespect j (by omega) hj x y hold.1 hne
        · rcases Sym2.eq_iff.mp hnew with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hdi
          · exact hdi.symm
  obtain ⟨K, hK, hKconn, hfuture, hnb, _⟩ := hstates n le_rfl
  rw [hpn] at hnb
  exact ⟨K, hK, hKconn, hpn ▸ hfuture n le_rfl le_rfl, hnb⟩

theorem bridge_switch_reachable_not_always_bridge {V C : Type*} {G R : SimpleGraph V}
    {c : Sym2 V → C} (hR : ColorRepresentative G c R) (hconn : R.Preconnected)
    {e f : R.edgeSet} (he : ¬R.IsBridge e.val)
    (hreach : Relation.ReflTransGen (BridgeSwitch G R c) e f) :
    ¬AlwaysBridgeColor G c (c f.val) := by
  intro halways
  obtain ⟨K, hK, hKconn, hf, hnb⟩ := bridge_switch_nonbridge_realizable hR hconn he hreach
  exact hnb (halways K hK hKconn f.val hf rfl)

end Erdos1105

#print axioms Erdos1105.bridge_switch_nonbridge_realizable
