import ErdosProblems.Erdos556.DeletionPaths

/-!
# Successive induced vertex deletions

The two deleted sets are combined in the original vertex type. In particular,
connectivity surviving a deletion budget loses at most the size of a first
prescribed deletion.
-/

namespace Erdos556

open SimpleGraph Finset

noncomputable def induceDeleteIso {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (T : Finset ↥((S : Set V)ᶜ)) :
    (G.induce (S : Set V)ᶜ).induce (T : Set ↥((S : Set V)ᶜ))ᶜ ≃g
      G.induce (↑(S ∪ T.map (Function.Embedding.subtype (fun v => v ∈ (S : Set V)ᶜ)) :
        Finset V) : Set V)ᶜ := by
  let U := (S : Set V)ᶜ
  let F := S ∪ T.map (Function.Embedding.subtype (fun v => v ∈ U))
  let f : ↥((T : Set U)ᶜ) → ↥((F : Set V)ᶜ) := fun x => ⟨x.val.val, by
    intro hx
    rcases mem_union.mp hx with hxS | hxT
    · exact x.val.property hxS
    · obtain ⟨y, hyT, hyx⟩ := mem_map.mp hxT
      have heq : y = x.val := Subtype.ext hyx
      exact x.property (heq ▸ hyT)⟩
  have hinj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    change (f x).val = (f y).val
    exact congrArg Subtype.val h
  have hsurj : Function.Surjective f := by
    intro y
    have hyS : y.val ∉ S := fun h => y.property (mem_union_left _ h)
    let x : U := ⟨y.val, hyS⟩
    have hxT : x ∉ T := by
      intro h
      exact y.property (mem_union_right S (mem_map.mpr ⟨x, h, rfl⟩))
    exact ⟨⟨x, hxT⟩, rfl⟩
  exact { toEquiv := Equiv.ofBijective f ⟨hinj, hsurj⟩, map_rel_iff' := Iff.rfl }

theorem ConnectedAfterDeleting.induce_compl {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {b s : ℕ} (hG : ConnectedAfterDeleting G (b + s))
    (S : Finset V) (hS : S.card ≤ s) :
    ConnectedAfterDeleting (G.induce (S : Set V)ᶜ) b := by
  classical
  intro T hT
  let F := S ∪ T.map (Function.Embedding.subtype (fun v => v ∈ (S : Set V)ᶜ))
  have hF : F.card ≤ b + s := by
    have h := card_union_le S (T.map (Function.Embedding.subtype (fun v => v ∈ (S : Set V)ᶜ)))
    rw [card_map] at h
    dsimp [F]
    omega
  exact (induceDeleteIso G S T).preconnected_iff.mpr (hG F hF)

#print axioms ConnectedAfterDeleting.induce_compl

end Erdos556
