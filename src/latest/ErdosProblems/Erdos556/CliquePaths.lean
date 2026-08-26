import ErdosProblems.Erdos556.HamiltonianConnected

/-!
# Exact paths inside a clique

The two-colour reduction and the final core argument use paths of
prescribed length with distinct prescribed endpoints.
-/

namespace Erdos556

open SimpleGraph Finset

theorem exists_path_in_clique {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (A : Finset V) (hA : G.IsClique (A : Set V)) (L : ℕ) (hL : 2 ≤ L)
    (hsize : L + 1 ≤ A.card) (u v : V) (hu : u ∈ A) (hv : v ∈ A) (huv : u ≠ v) :
    ∃ p : G.Walk u v, p.IsPath ∧ p.length = L ∧ ∀ x ∈ p.support, x ∈ A := by
  classical
  have hpair : ({u, v} : Finset V) ⊆ A := by simp only [insert_subset_iff, singleton_subset_iff]; exact ⟨hu, hv⟩
  have hpaircard : ({u, v} : Finset V).card ≤ L + 1 := by
    have h := card_insert_le u ({v} : Finset V)
    simp only [card_singleton] at h
    omega
  obtain ⟨B, hpB, hBA, hBc⟩ := exists_subsuperset_card_eq hpair hpaircard hsize
  have huB : u ∈ B := hpB (by simp)
  have hvB : v ∈ B := hpB (by simp)
  have hcard : Fintype.card (B : Set V) = L + 1 := by
    calc
      Fintype.card (B : Set V) = (B : Set V).ncard := Nat.card_eq_fintype_card.symm
      _ = B.card := Set.ncard_coe_finset B
      _ = L + 1 := hBc
  let f : (⊤ : SimpleGraph (B : Set V)) →g G :=
    { toFun := Subtype.val
      map_rel' := by
        intro x y hxy
        apply hA (hBA x.property) (hBA y.property)
        intro heq
        have hne : x ≠ y := by simpa only [top_adj] using hxy
        exact hne (Subtype.ext heq) }
  obtain ⟨q, hq⟩ := complete_hamiltonian_path (V := (B : Set V)) (by omega)
    ⟨u, huB⟩ ⟨v, hvB⟩ (fun h => huv (congrArg Subtype.val h))
  refine ⟨q.map f, hq.isPath.map Subtype.val_injective, ?_, ?_⟩
  · rw [Walk.length_map, hq.length_eq, hcard]
    omega
  · intro x hx
    rw [Walk.support_map, List.mem_map] at hx
    obtain ⟨y, _, hyx⟩ := hx
    exact hyx ▸ hBA y.property

#print axioms exists_path_in_clique

end Erdos556
