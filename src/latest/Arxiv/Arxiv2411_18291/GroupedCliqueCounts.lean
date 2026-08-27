import Arxiv.Arxiv2411_18291.RepeatedCliqueRoots

/-!
# Counting successful choices across disjoint groups

Summing the number of successful members over disjoint groups contained in
a family is bounded by the successful-member count in the whole family.
This identifies the expected weighted representative degree.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {X : Type*}

theorem card_filter_subtype_members (s : Finset X) (p : X → Prop) [DecidablePred p] :
    (univ.filter fun x : s => p x.val).card = (s.filter p).card := by
  classical
  have heq : (univ.filter fun x : s => p x.val).map (Function.Embedding.subtype (· ∈ s)) =
      s.filter p := by
    ext x
    simp [and_comm]
  simpa only [card_map] using congrArg Finset.card heq

theorem grouped_filter_card_le (D : Finset X) (G : Finset (Finset X))
    (hsub : ∀ c ∈ G, c ⊆ D) (hdis : Pairwise fun c d : G => Disjoint c.val d.val)
    (p : X → Prop) [DecidablePred p] :
    (∑ c : G, (univ.filter fun x : c.val => p x.val).card) ≤ (D.filter p).card := by
  classical
  have hd : ((univ : Finset G) : Set G).PairwiseDisjoint (fun c => c.val.filter p) := by
    intro c _ d _ hcd
    exact (hdis hcd).mono (filter_subset p c.val) (filter_subset p d.val)
  calc
    _ = ∑ c : G, (c.val.filter p).card := by simp only [card_filter_subtype_members]
    _ = (univ.biUnion fun c : G => c.val.filter p).card := (card_biUnion hd).symm
    _ ≤ _ := by
      apply card_le_card
      intro x hx
      obtain ⟨c, _, hc⟩ := mem_biUnion.mp hx
      exact mem_filter.mpr ⟨hsub c.val c.property (mem_filter.mp hc).1, (mem_filter.mp hc).2⟩

end Arxiv2411_18291
