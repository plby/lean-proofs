import ErdosProblems.Erdos1105.HamiltonianConnected
import ErdosProblems.Erdos1105.CycleSaturation

namespace Erdos1105

open SimpleGraph Finset

/-- A clique has a spanning path with any two distinct prescribed endpoints. -/
theorem clique_spanning_path {V : Type*} (G : SimpleGraph V) {S : Finset V}
    (hS : G.IsClique (S : Set V)) (hcard : 3 ≤ S.card)
    {a b : V} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    ∃ p : G.Walk a b, p.IsPath ∧ p.length + 1 = S.card ∧
      ∀ v, v ∈ p.support ↔ v ∈ S := by
  classical
  let f : (⊤ : SimpleGraph S) →g G :=
    { toFun := Subtype.val
      map_rel' := fun {x y} hxy ↦ hS x.property y.property
        (fun h ↦ hxy (Subtype.ext h)) }
  obtain ⟨p, hp⟩ := complete_hamiltonian_path (by simpa using hcard)
    (⟨a, ha⟩ : S) ⟨b, hb⟩ (fun h ↦ hab (congrArg Subtype.val h))
  refine ⟨p.map f, hp.isPath.map Subtype.val_injective, ?_, ?_⟩
  · have hlen : p.length = S.card - 1 := by simpa using hp.length_eq
    rw [Walk.length_map]
    omega
  · intro v
    rw [Walk.support_map, List.mem_map]
    constructor
    · rintro ⟨x, _, rfl⟩
      exact x.property
    · intro hv
      exact ⟨⟨v, hv⟩, hp.mem_support ⟨v, hv⟩, rfl⟩

theorem clique_card_lt_of_no_long_cycle {V : Type*} (G : SimpleGraph V)
    {k : ℕ} (hG : NoLongCycle G k) (hk : 3 ≤ k) {S : Finset V}
    (hS : G.IsClique (S : Set V)) : S.card < k := by
  by_contra! hcard
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (show 1 < S.card by omega)
  obtain ⟨p, hp, hlen, _⟩ := clique_spanning_path G hS (by omega) ha hb hab
  have hba := (hS ha hb hab).symm
  have hcycle : (Walk.cons hba p).IsCycle := by
    apply (Walk.cons_isCycle_iff p hba).mpr
    refine ⟨hp, ?_⟩
    intro he
    have h := hp.length_eq_one_of_mem_edges (Sym2.eq_swap ▸ he)
    omega
  have h := hG b (Walk.cons hba p) hcycle
  rw [Walk.length_cons] at h
  omega

/-- A proper clique containing a universal vertex can be extended to a
cycle using one vertex outside the clique, provided deletion of the
universal vertex leaves the graph connected. -/
theorem cone_clique_extended_cycle {V : Type*} (G : SimpleGraph V)
    {u : V} (hu : G.IsUniversal u)
    (hconn : (G.induce {v | v ≠ u}).Preconnected)
    {S : Finset V} (hS : G.IsClique (S : Set V)) (hcard : 3 ≤ S.card)
    (huS : u ∈ S) (hout : ∃ w, w ∉ S) :
    ∃ z, ∃ q : G.Walk z z, q.IsCycle ∧ q.length = S.card + 1 := by
  classical
  obtain ⟨w, hw⟩ := hout
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (show 1 < S.card by omega)
  have hv : ∃ v ∈ S, v ≠ u := by
    by_cases hau : a = u
    · exact ⟨b, hb, fun h ↦ hab (hau.trans h.symm)⟩
    · exact ⟨a, ha, hau⟩
  obtain ⟨v, hvS, hvu⟩ := hv
  have hwu : w ≠ u := fun h ↦ hw (h ▸ huS)
  obtain ⟨p⟩ := hconn (⟨v, hvu⟩ : {v | v ≠ u}) ⟨w, hwu⟩
  obtain ⟨d, _, hdS, hdout⟩ := p.exists_boundary_dart
    {v : {v | v ≠ u} | v.val ∈ S} hvS hw
  obtain ⟨r, hr, hrlen, hrsupp⟩ := clique_spanning_path G hS hcard hdS huS
    d.fst.property
  have hdsnd : d.snd.val ∉ r.support := fun h ↦ hdout ((hrsupp _).mp h)
  let q := Walk.cons (show G.Adj d.snd.val d.fst.val from d.adj.symm) r
  have hq : q.IsPath := (Walk.cons_isPath_iff _ _).mpr ⟨hr, hdsnd⟩
  have huz : G.Adj u d.snd.val := hu d.snd.property.symm
  have hcycle : (Walk.cons huz q).IsCycle := by
    apply (Walk.cons_isCycle_iff q huz).mpr
    refine ⟨hq, ?_⟩
    intro he
    have h := hq.length_eq_one_of_mem_edges (Sym2.eq_swap ▸ he)
    simp only [q, Walk.length_cons] at h
    omega
  exact ⟨u, Walk.cons huz q, hcycle, by simp only [q, Walk.length_cons]; omega⟩

end Erdos1105

#print axioms Erdos1105.cone_clique_extended_cycle
