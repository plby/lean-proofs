import ErdosProblems.Erdos556.BondyChvatal

/-!
# Absorbing outside vertices into a dense core

Closure first completes the core, then its incident edges, then the
remaining edges. Thus no separate path gadget is needed for absorption.
-/

namespace Erdos556

open SimpleGraph Finset

theorem degree_add_one_ge_card_of_clique_at {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (v : V) (hv : v ∈ A)
    (hadj : ∀ u ∈ A, u ≠ v → G.Adj v u) : A.card ≤ G.degree v + 1 := by
  have hsub : A.erase v ⊆ G.neighborFinset v := by
    intro u hu
    rw [mem_erase] at hu
    exact (G.mem_neighborFinset v u).mpr (hadj u hu.2 hu.1)
  have h := card_le_card hsub
  rw [card_erase_of_mem hv, G.card_neighborFinset_eq_degree] at h
  have hp := card_pos.mpr ⟨v, hv⟩
  omega

theorem isHamiltonian_of_dense_core {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (d : ℕ)
    (hN : 3 ≤ Fintype.card V)
    (hsize : Fintype.card V + 2 * d ≤ 2 * A.card)
    (hcore : ∀ v ∈ A, A.card ≤ G.degree v + d)
    (hout : ∀ v ∉ A, Fintype.card V - A.card + 1 ≤ G.degree v) :
    G.IsHamiltonian := by
  classical
  let H := G.erdos556_closure
  have hle : G ≤ H := G.erdos556_self_le_closure
  have hcard : A.card ≤ Fintype.card V := card_le_univ A
  have hcoreH (u v : V) (hu : u ∈ A) (hv : v ∈ A) (huv : u ≠ v) :
      H.Adj u v := by
    apply G.erdos556_closure_spec huv
    change Fintype.card V ≤ H.degree u + H.degree v
    have hu' := (hcore u hu).trans (Nat.add_le_add_right (G.degree_le_of_le hle) d)
    have hv' := (hcore v hv).trans (Nat.add_le_add_right (G.degree_le_of_le hle) d)
    omega
  have hdegA (u : V) (hu : u ∈ A) : A.card ≤ H.degree u + 1 := by
    apply degree_add_one_ge_card_of_clique_at H A u hu
    intro v hv hvu
    exact hcoreH u v hu hv hvu.symm
  have hcross (u v : V) (hu : u ∈ A) (hv : v ∉ A) : H.Adj u v := by
    have huv : u ≠ v := fun h => hv (h ▸ hu)
    apply G.erdos556_closure_spec huv
    change Fintype.card V ≤ H.degree u + H.degree v
    have hu' := hdegA u hu
    have hv' := (hout v hv).trans (G.degree_le_of_le hle)
    omega
  have hdegOut (u : V) (hu : u ∉ A) : A.card ≤ H.degree u := by
    have hsub : A ⊆ H.neighborFinset u := by
      intro v hv
      exact (H.mem_neighborFinset u v).mpr (hcross v u hv hu).symm
    exact card_le_card hsub
  have htop : H = ⊤ := by
    apply top_unique
    intro u v huv
    have hne : u ≠ v := by simpa only [top_adj] using huv
    by_cases hu : u ∈ A
    · by_cases hv : v ∈ A
      · exact hcoreH u v hu hv hne
      · exact hcross u v hu hv
    · by_cases hv : v ∈ A
      · exact (hcross v u hv hu).symm
      · apply G.erdos556_closure_spec hne
        change Fintype.card V ≤ H.degree u + H.degree v
        have hu' := hdegOut u hu
        have hv' := hdegOut v hv
        omega
  apply G.erdos556_from_closure_iff.mp
  change H.IsHamiltonian
  rw [htop]
  apply SimpleGraph.erdos556_dirac_theorem hN
  intro v
  rw [((⊤ : SimpleGraph V).degree_eq_card_sub_one v).mpr (by simp [IsUniversal])]
  omega

#print axioms isHamiltonian_of_dense_core

theorem degree_induce_finset_eq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : (S : Set V)) :
    (G.induce (S : Set V)).degree v = (G.neighborFinset v.val ∩ S).card := by
  classical
  have h := congrArg Finset.card (G.map_neighborFinset_induce v)
  simpa only [card_map, card_neighborFinset_eq_degree, Finset.toFinset_coe,
    ← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using h

theorem isHamiltonian_induce_of_dense_core {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A W : Finset V) (d : ℕ)
    (hdis : Disjoint A W) (hN : 3 ≤ A.card + W.card)
    (hsize : W.card + 2 * d ≤ A.card)
    (hcore : ∀ v ∈ A, A.card ≤ (G.neighborFinset v ∩ A).card + d)
    (hout : ∀ v ∈ W, W.card + 1 ≤ (G.neighborFinset v ∩ A).card) :
    (G.induce ((A ∪ W : Finset V) : Set V)).IsHamiltonian := by
  classical
  let S := A ∪ W
  let H := G.induce (S : Set V)
  let A' : Finset (S : Set V) := univ.filter (fun v => v.val ∈ A)
  have hcard : Fintype.card (S : Set V) = A.card + W.card := by
    calc
      Fintype.card (S : Set V) = (S : Set V).ncard := Nat.card_eq_fintype_card.symm
      _ = S.card := Set.ncard_coe_finset S
      _ = A.card + W.card := card_union_of_disjoint hdis
  have himage : A'.image Subtype.val = A := by
    ext v
    simp only [A', mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hv
      exact ⟨⟨v, mem_union_left W hv⟩, hv, rfl⟩
  have hAcard : A'.card = A.card := by
    rw [← himage, card_image_of_injective _ Subtype.val_injective]
  have hdeg (v : (S : Set V)) : (G.neighborFinset v.val ∩ A).card ≤ H.degree v := by
    rw [degree_induce_finset_eq]
    apply card_le_card
    exact inter_subset_inter_left (subset_union_left : A ⊆ S)
  apply isHamiltonian_of_dense_core H A' d
  · simpa only [hcard] using hN
  · rw [hcard, hAcard]
    omega
  · intro v hv
    have hvA : v.val ∈ A := (mem_filter.mp hv).2
    rw [hAcard]
    exact (hcore v.val hvA).trans (Nat.add_le_add_right (hdeg v) d)
  · intro v hv
    have hvA : v.val ∉ A := by simpa only [A', mem_filter, mem_univ, true_and] using hv
    have hvW : v.val ∈ W := (mem_union.mp v.property).resolve_left hvA
    rw [hcard, hAcard, Nat.add_sub_cancel_left]
    exact (hout v.val hvW).trans (hdeg v)

theorem exists_cycle_of_dense_core {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A W : Finset V) (d : ℕ)
    (hdis : Disjoint A W) (hN : 3 ≤ A.card + W.card)
    (hsize : W.card + 2 * d ≤ A.card)
    (hcore : ∀ v ∈ A, A.card ≤ (G.neighborFinset v ∩ A).card + d)
    (hout : ∀ v ∈ W, W.card + 1 ≤ (G.neighborFinset v ∩ A).card) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = A.card + W.card := by
  classical
  let S := A ∪ W
  have hcard : Fintype.card (S : Set V) = A.card + W.card := by
    calc
      Fintype.card (S : Set V) = (S : Set V).ncard := Nat.card_eq_fintype_card.symm
      _ = S.card := Set.ncard_coe_finset S
      _ = A.card + W.card := card_union_of_disjoint hdis
  have hHam : (G.induce (S : Set V)).IsHamiltonian :=
    isHamiltonian_induce_of_dense_core G A W d hdis hN hsize hcore hout
  letI : Nontrivial (S : Set V) := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨v⟩ := (inferInstance : Nonempty (S : Set V))
  obtain ⟨c, hc⟩ := hHam.exists_isHamiltonianCycle v
  refine ⟨(Embedding.induce (S : Set V)).toHom v,
    c.map (Embedding.induce (S : Set V)).toHom,
    hc.isCycle.map Subtype.val_injective, ?_⟩
  rw [Walk.length_map, hc.length_eq, hcard]

#print axioms exists_cycle_of_dense_core

end Erdos556
