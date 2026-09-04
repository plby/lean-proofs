import ErdosProblems.Erdos556.ShortPaths

/-!
# Short paths after vertex deletion

Deletion of `s` vertices reduces every surviving degree by at most `s`.
Together with connectivity after deletion, the diameter bound gives short
paths avoiding an arbitrary prescribed set.
-/

namespace Erdos556

open SimpleGraph Finset

/-- All deletions of at most `b` vertices leave a preconnected graph.
Preconnectedness also covers deletions leaving no vertices. -/
def ConnectedAfterDeleting {V : Type*} (G : SimpleGraph V) (b : ℕ) : Prop :=
  ∀ S : Finset V, S.card ≤ b → (G.induce (S : Set V)ᶜ).Preconnected

theorem ConnectedAfterDeleting.mono {V : Type*} {G : SimpleGraph V} {a b : ℕ}
    (h : ConnectedAfterDeleting G b) (hab : a ≤ b) : ConnectedAfterDeleting G a :=
  fun S hS => h S (hS.trans hab)

theorem degree_le_induce_compl_degree_add_card {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : ↥((S : Set V)ᶜ)) :
    G.degree v.val ≤ (G.induce (S : Set V)ᶜ).degree v + S.card := by
  classical
  have hdeg : (G.induce (S : Set V)ᶜ).degree v =
      (G.neighborFinset v.val \ S).card := by
    have h := congrArg Finset.card (G.map_neighborFinset_induce v)
    simpa [← sdiff_eq_inter_compl] using h
  rw [hdeg, ← G.card_neighborFinset_eq_degree v.val]
  have h := card_sdiff_add_card_inter (G.neighborFinset v.val) S
  have hle := card_le_card (inter_subset_right (s₁ := G.neighborFinset v.val) (s₂ := S))
  omega

/-- The short path avoids `S` on its whole support, including its endpoints. -/
theorem exists_short_path_avoiding {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b d : ℕ)
    (hconn : ConnectedAfterDeleting G b) (hd : 0 < d)
    (hdeg : ∀ w, d + b ≤ G.degree w) (S : Finset V) (hS : S.card ≤ b)
    (u v : V) (hu : u ∉ S) (hv : v ∉ S) :
    ∃ p : G.Walk u v, p.IsPath ∧ d * p.length < 3 * Fintype.card V ∧
      ∀ x ∈ p.support, x ∉ S := by
  classical
  let U := (S : Set V)ᶜ
  let u' : U := ⟨u, hu⟩
  let v' : U := ⟨v, hv⟩
  let : Nonempty U := ⟨u'⟩
  have hc : (G.induce U).Connected := ⟨hconn S hS⟩
  have hmin (w : U) : d ≤ (G.induce U).degree w := by
    have h := degree_le_induce_compl_degree_add_card G S w
    have hg := hdeg w.val
    change G.degree w.val ≤ (G.induce U).degree w + S.card at h
    omega
  obtain ⟨p, hp, hlen⟩ := exists_short_path_of_min_degree
    (G.induce U) hc d hd hmin u' v'
  let f : G.induce U ↪g G := SimpleGraph.Embedding.induce U
  refine ⟨p.map f.toHom, hp.map f.injective, ?_, ?_⟩
  · change d * (p.map f.toHom).length < 3 * Fintype.card V
    simp only [Walk.length_map]
    exact hlen.trans_le (Nat.mul_le_mul_left 3 (Fintype.card_le_of_injective
      (fun x : U => x.val) Subtype.val_injective))
  · intro x hx
    change x ∈ (p.map f.toHom).support at hx
    rw [Walk.support_map, List.mem_map] at hx
    obtain ⟨y, _, hy⟩ := hx
    subst x
    exact y.property

#print axioms exists_short_path_avoiding

end Erdos556
