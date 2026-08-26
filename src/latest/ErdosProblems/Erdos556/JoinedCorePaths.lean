import ErdosProblems.Erdos556.CliquePaths

/-!
# Paths through a clique core joined to its bucket

The core may have only `(n-1)/2` vertices. Prescribed paths do not require
the incorrect assertion that every bucket of order `n` already contains `C_n`.
-/

namespace Erdos556

open SimpleGraph Finset

theorem clique_insert_of_joined_core {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A S : Finset V) (hAS : A ⊆ S)
    (hjoin : ∀ a ∈ A, ∀ s ∈ S, a ≠ s → G.Adj a s)
    (u : V) (hu : u ∈ S) : G.IsClique ((insert u A : Finset V) : Set V) := by
  intro x hx y hy hxy
  rcases mem_insert.mp hx with hxu | hxA
  · subst x
    rcases mem_insert.mp hy with hyu | hyA
    · exact (hxy hyu.symm).elim
    · exact (hjoin y hyA u hu hxy.symm).symm
  · rcases mem_insert.mp hy with hyu | hyA
    · subst y
      exact hjoin x hxA u hu hxy
    · exact hjoin x hxA y (hAS hyA) hxy

theorem exists_joined_core_path_to_outside {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A S : Finset V) (hAS : A ⊆ S)
    (hjoin : ∀ a ∈ A, ∀ s ∈ S, a ≠ s → G.Adj a s)
    (L : ℕ) (hL : 3 ≤ L) (hA : L ≤ A.card)
    (u v : V) (hu : u ∈ S) (hv : v ∈ S) (hvA : v ∉ A) (huv : u ≠ v) :
    ∃ p : G.Walk u v, p.IsPath ∧ p.length = L ∧ ∀ x ∈ p.support, x ∈ S := by
  classical
  have hAe : (A.erase u).Nonempty := by
    apply card_pos.mp
    have hc : A.card - 1 ≤ (A.erase u).card := by
      by_cases h : u ∈ A
      · rw [card_erase_of_mem h]
      · rw [erase_eq_of_notMem h]
        omega
    omega
  obtain ⟨a, ha⟩ := hAe
  have haA := mem_of_mem_erase ha
  have hua : u ≠ a := (mem_erase.mp ha).1.symm
  have hC : L ≤ (insert u A).card := hA.trans (card_le_card (subset_insert _ _))
  obtain ⟨p, hp, hlen, hsupp⟩ := exists_path_in_clique G (insert u A)
    (clique_insert_of_joined_core G A S hAS hjoin u hu) (L - 1) (by omega) (by omega)
    u a (mem_insert_self _ _) (mem_insert_of_mem haA) hua
  have hvC : v ∉ insert u A := by
    simp only [mem_insert, not_or]
    exact ⟨huv.symm, hvA⟩
  have hav : G.Adj a v := hjoin a haA v hv (fun h => hvA (h ▸ haA))
  refine ⟨p.concat hav, hp.concat (fun h => hvC (hsupp v h)) hav, ?_, ?_⟩
  · rw [Walk.length_concat, hlen]
    omega
  · intro x hx
    rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | hx
    · rcases mem_insert.mp (hsupp x hx) with hx | hx
      · exact hx ▸ hu
      · exact hAS hx
    · exact hx ▸ hv

theorem exists_path_in_joined_core_bucket {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A S : Finset V) (hAS : A ⊆ S)
    (hjoin : ∀ a ∈ A, ∀ s ∈ S, a ≠ s → G.Adj a s)
    (L : ℕ) (hL : 3 ≤ L) (hA : L ≤ A.card) (hS : L + 1 ≤ S.card)
    (u v : V) (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v) :
    ∃ p : G.Walk u v, p.IsPath ∧ p.length = L ∧ ∀ x ∈ p.support, x ∈ S := by
  classical
  by_cases hvA : v ∈ A
  · by_cases huA : u ∈ A
    · by_cases hsize : L + 1 ≤ A.card
      · have hclique : G.IsClique (A : Set V) := fun _ ha _ hb hab => hjoin _ ha _ (hAS hb) hab
        obtain ⟨p, hp, hlen, hsupp⟩ := exists_path_in_clique G A hclique L (by omega) hsize u v huA hvA huv
        exact ⟨p, hp, hlen, fun x hx => hAS (hsupp x hx)⟩
      · obtain ⟨x, hxS, hxA⟩ := exists_mem_notMem_of_card_lt_card (show A.card < S.card by omega)
        have hsize' : L + 1 ≤ (insert x A).card := by rw [card_insert_of_notMem hxA]; omega
        obtain ⟨p, hp, hlen, hsupp⟩ := exists_path_in_clique G (insert x A)
          (clique_insert_of_joined_core G A S hAS hjoin x hxS) L (by omega) hsize'
          u v (mem_insert_of_mem huA) (mem_insert_of_mem hvA) huv
        refine ⟨p, hp, hlen, ?_⟩
        intro y hy
        rcases mem_insert.mp (hsupp y hy) with hy | hy
        · exact hy ▸ hxS
        · exact hAS hy
    · obtain ⟨p, hp, hlen, hsupp⟩ := exists_joined_core_path_to_outside G A S hAS hjoin
        L hL hA v u hv hu huA huv.symm
      refine ⟨p.reverse, hp.reverse, by simpa only [Walk.length_reverse] using hlen, ?_⟩
      intro x hx
      exact hsupp x (by simpa only [Walk.support_reverse, List.mem_reverse] using hx)
  · exact exists_joined_core_path_to_outside G A S hAS hjoin L hL hA u v hu hv hvA huv

#print axioms exists_path_in_joined_core_bucket

end Erdos556
