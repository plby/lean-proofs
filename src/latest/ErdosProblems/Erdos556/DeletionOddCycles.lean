import ErdosProblems.Erdos556.DeletionPaths
import ErdosProblems.Erdos556.OddCycles

/-!
# Short odd cycles after deletion

Nonbipartiteness surviving bounded vertex deletion supplies the parity
change needed by the connecting gadgets.
-/

namespace Erdos556

open SimpleGraph

def NonbipartiteAfterDeleting {V : Type*} (G : SimpleGraph V) (b : ℕ) : Prop :=
  ∀ S : Finset V, S.card ≤ b → ¬ (G.induce (S : Set V)ᶜ).Colorable 2

theorem NonbipartiteAfterDeleting.mono {V : Type*} {G : SimpleGraph V} {a b : ℕ}
    (h : NonbipartiteAfterDeleting G b) (hab : a ≤ b) :
    NonbipartiteAfterDeleting G a := fun S hS => h S (hS.trans hab)

theorem nonempty_of_not_two_colorable {V : Type*} (G : SimpleGraph V)
    (h : ¬ G.Colorable 2) : Nonempty V := by
  by_contra hn
  have : IsEmpty V := not_nonempty_iff.mp hn
  apply h
  refine ⟨{ toFun := fun x => isEmptyElim x, map_rel' := ?_ }⟩
  intro x
  exact isEmptyElim x

theorem exists_short_odd_cycle_avoiding {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b d : ℕ)
    (hconn : ConnectedAfterDeleting G b) (hnonbip : NonbipartiteAfterDeleting G b)
    (hd : 0 < d) (hdeg : ∀ w, d + b ≤ G.degree w)
    (S : Finset V) (hS : S.card ≤ b) :
    ∃ (w : V) (c : G.Walk w w), c.IsCycle ∧ Odd c.length ∧
      d * c.length < 6 * Fintype.card V + d ∧ ∀ x ∈ c.support, x ∉ S := by
  classical
  let U := (S : Set V)ᶜ
  have hnb : ¬ (G.induce U).Colorable 2 := hnonbip S hS
  have : Nonempty U := nonempty_of_not_two_colorable _ hnb
  have hc : (G.induce U).Connected := ⟨hconn S hS⟩
  have hmin (v : U) : d ≤ (G.induce U).degree v := by
    have h := degree_le_induce_compl_degree_add_card G S v
    have hg := hdeg v.val
    change G.degree v.val ≤ (G.induce U).degree v + S.card at h
    omega
  obtain ⟨w, c, hcyc, hodd, hlen⟩ := exists_short_odd_cycle (G.induce U) hc hnb d hd hmin
  let f : G.induce U ↪g G := SimpleGraph.Embedding.induce U
  refine ⟨f w, c.map f.toHom, hcyc.map f.injective, ?_, ?_, ?_⟩
  · simpa only [Walk.length_map] using hodd
  · simp only [Walk.length_map]
    have hcard := Fintype.card_le_of_injective (fun x : U => x.val) Subtype.val_injective
    omega
  · intro x hx
    rw [Walk.support_map, List.mem_map] at hx
    obtain ⟨y, _, hy⟩ := hx
    subst x
    exact y.property

#print axioms exists_short_odd_cycle_avoiding

end Erdos556
