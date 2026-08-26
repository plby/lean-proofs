import Mathlib

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Candidate-set embedding of rooted forests

This file isolates the purely combinatorial engine needed for shrubs with two
prescribed attachments.  Every forest vertex `a` has its own candidate set
`cand a`.  A root can be chosen whenever its candidate set has at least as many
vertices as the whole forest, and a non-root `a` can be chosen after its parent
`b` whenever *every* candidate for `b` has at least that many neighbours in
`cand a`.  Greedy embedding then preserves all candidate constraints.

Candidate sets may encode several simultaneous external-anchor constraints.  In
particular, taking the candidates of the two terminal vertices to be their
respective prescribed-anchor neighbourhoods gives a bidirectionally attached
shrub of arbitrary interior shape.  The analytic regularity argument is thereby
separated cleanly from the finite collision-free embedding step.
-/

open SimpleGraph Finset

namespace Erdos550

/-
**Candidate-set rooted-forest embedding.**

The uniform reserve `Fintype.card α` pays for all vertices embedded previously.
For roots it is required directly from `cand`; for a child it is required in the
neighbourhood of every possible image of its parent.
-/
set_option maxHeartbeats 2000000 in
theorem candidate_forest_embedding
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {α : Type*} [Fintype α] [DecidableEq α]
    (parent : α → Option α) (rank : α → ℕ)
    (hrank : ∀ a b, parent a = some b → rank b < rank a)
    (cand : α → Finset V)
    (hroot : ∀ a, parent a = none → Fintype.card α ≤ (cand a).card)
    (hchild : ∀ a b, parent a = some b → ∀ v ∈ cand b,
      Fintype.card α ≤ ((cand a).filter (fun w => G.Adj v w)).card) :
    ∃ f : α → V, Function.Injective f ∧
      (∀ a, f a ∈ cand a) ∧
      (∀ a b, parent a = some b → G.Adj (f a) (f b)) := by
  revert cand hroot hchild;
  intro cand hroot hchild
  have h_ind : ∀ S : Finset α, (∀ a ∈ S, ∀ b, parent a = some b → b ∈ S) → ∃ f : α → V, (∀ a ∈ S, f a ∈ cand a) ∧ (∀ a ∈ S, ∀ b ∈ S, a ≠ b → f a ≠ f b) ∧ (∀ a ∈ S, ∀ b ∈ S, parent a = some b → G.Adj (f a) (f b)) ∧ (Finset.univ \ Finset.image f S).card ≥ (Finset.univ \ S).card := by
    intro S hS;
    induction' S using Finset.strongInduction with S ih;
    by_cases hS_empty : S = ∅;
    · simp [hS_empty];
      by_cases hα : Nonempty α;
      · have h_root : ∃ a : α, parent a = none := by
          by_contra h_no_root;
          have h_seq : ∃ seq : ℕ → α, ∀ n, parent (seq n) = some (seq (n + 1)) := by
            choose f hf using fun a => Option.ne_none_iff_exists'.mp ( show parent a ≠ none from fun h => h_no_root ⟨ a, h ⟩ );
            exact ⟨ fun n => Nat.recOn n hα.some fun n ih => f ih, fun n => hf _ ⟩;
          obtain ⟨ seq, hseq ⟩ := h_seq;
          have h_seq_inf : StrictAnti (fun n => rank (seq n)) := by
            exact strictAnti_nat_of_succ_lt fun n => hrank _ _ ( hseq n );
          exact absurd ( Set.infinite_range_of_injective h_seq_inf.injective ) ( Set.not_infinite.mpr <| Set.finite_iff_bddAbove.mpr ⟨ _, Set.forall_mem_range.mpr fun n => h_seq_inf.antitone n.zero_le ⟩ );
        exact ⟨ Or.inr ⟨ Classical.choose ( Finset.card_pos.mp ( lt_of_lt_of_le ( Fintype.card_pos ) ( hroot _ h_root.choose_spec ) ) ) ⟩, le_trans ( hroot _ h_root.choose_spec ) ( Finset.card_le_univ _ ) ⟩;
      · exact ⟨ Or.inl ⟨ fun a => hα ⟨ a ⟩ ⟩, by simp +decide [ Fintype.card_eq_zero_iff.mpr ( show IsEmpty α from ⟨ fun a => hα ⟨ a ⟩ ⟩ ) ] ⟩;
    · -- Let $a$ be an element of $S$ with maximal rank.
      obtain ⟨a, haS, ha_max⟩ : ∃ a ∈ S, ∀ b ∈ S, rank b ≤ rank a := by
        exact Finset.exists_max_image _ _ ( Finset.nonempty_of_ne_empty hS_empty );
      -- Let $T = S \setminus \{a\}$.
      set T := S \ {a} with hT_def;
      -- By the induction hypothesis, there exists a function $f_T$ for $T$.
      obtain ⟨f_T, hf_T⟩ := ih T (by
      grind) (by
      grind);
      by_cases ha_root : parent a = none;
      · -- Since $a$ is a root, we can choose any element from $cand a$ that is not in the image of $f_T$.
        obtain ⟨v, hv⟩ : ∃ v ∈ cand a, v ∉ Finset.image f_T T := by
          have h_card : (cand a).card > (Finset.image f_T T).card := by
            have h_card : (Finset.image f_T T).card ≤ (Finset.univ \ {a}).card := by
              exact Finset.card_image_le.trans ( Finset.card_le_card fun x hx => by aesop );
            grind +qlia;
          exact Finset.not_subset.mp fun h => h_card.not_ge <| Finset.card_le_card h;
        refine' ⟨ fun x => if x = a then v else f_T x, _, _, _, _ ⟩ <;> simp +decide [ * ];
        · grind;
        · grind +suggestions;
        · grind;
        · rw [ show ( univ \ image ( fun x => if x = a then v else f_T x ) S ) = ( univ \ image f_T T ) \ { v } from ?_ ]; all_goals grind;
      · obtain ⟨b, hb⟩ : ∃ b, parent a = some b ∧ b ∈ T := by
          obtain ⟨ b, hb ⟩ := Option.ne_none_iff_exists'.mp ha_root;
          grind;
        -- Let $v$ be a vertex in $cand a$ that is adjacent to $f_T b$ and not in the image of $f_T$.
        obtain ⟨v, hv⟩ : ∃ v ∈ cand a, G.Adj v (f_T b) ∧ v ∉ Finset.image f_T T := by
          have h_card : (Finset.filter (fun w => G.Adj (f_T b) w) (cand a)).card ≥ Fintype.card α := by
            exact hchild a b hb.1 _ ( hf_T.1 b hb.2 );
          have h_card : (Finset.filter (fun w => G.Adj (f_T b) w) (cand a)).card > (Finset.image f_T T).card := by
            refine' lt_of_lt_of_le _ h_card;
            refine' lt_of_le_of_lt ( Finset.card_image_le ) _;
            exact lt_of_lt_of_le ( Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ Finset.sdiff_subset, by aesop ⟩ ) ) ( Finset.card_le_univ _ );
          contrapose! h_card;
          exact Finset.card_le_card fun x hx => h_card x ( Finset.mem_filter.mp hx |>.1 ) ( by simpa [ SimpleGraph.adj_comm ] using! Finset.mem_filter.mp hx |>.2 );
        refine' ⟨ fun x => if x = a then v else f_T x, _, _, _, _ ⟩ <;> simp +decide [ * ];
        · grind;
        · grind;
        · grind;
        · rw [ show ( univ \ image ( fun x => if x = a then v else f_T x ) S ) = ( univ \ image f_T T ) \ { v } from ?_ ]; all_goals grind;
  obtain ⟨ f, hf₁, hf₂, hf₃, hf₄ ⟩ := h_ind Finset.univ ( by simp +decide );
  exact ⟨ f, fun a b hab => Classical.not_not.1 fun h => hf₂ a ( Finset.mem_univ a ) b ( Finset.mem_univ b ) h hab, fun a => hf₁ a ( Finset.mem_univ a ), fun a b hab => hf₃ a ( Finset.mem_univ a ) b ( Finset.mem_univ b ) hab ⟩

/-
Candidate-set embedding with an arbitrary finite family of prescribed
external anchors at every forest vertex.  Membership in `cand a` is required to
imply adjacency to every vertex in `anchors a`; hence roots, terminal leaves, or
several distinguished vertices can all be constrained simultaneously.
-/
theorem candidate_forest_embedding_anchored
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {α : Type*} [Fintype α] [DecidableEq α]
    (parent : α → Option α) (rank : α → ℕ)
    (hrank : ∀ a b, parent a = some b → rank b < rank a)
    (cand : α → Finset V) (anchors : α → Finset V)
    (hcand_anchor : ∀ a v, v ∈ cand a → ∀ z ∈ anchors a, G.Adj z v)
    (hroot : ∀ a, parent a = none → Fintype.card α ≤ (cand a).card)
    (hchild : ∀ a b, parent a = some b → ∀ v ∈ cand b,
      Fintype.card α ≤ ((cand a).filter (fun w => G.Adj v w)).card) :
    ∃ f : α → V, Function.Injective f ∧
      (∀ a, f a ∈ cand a) ∧
      (∀ a b, parent a = some b → G.Adj (f a) (f b)) ∧
      (∀ a z, z ∈ anchors a → G.Adj z (f a)) := by
  convert! candidate_forest_embedding G parent rank hrank cand hroot hchild using 1;
  grind

/-
Two prescribed attachment vertices are a special case of the multi-anchor
candidate engine.  The distinguished forest vertices may coincide; if they do,
the candidate set at that vertex must satisfy both attachment constraints.
-/
theorem candidate_forest_embedding_two_attachments
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {α : Type*} [Fintype α] [DecidableEq α]
    (parent : α → Option α) (rank : α → ℕ)
    (hrank : ∀ a b, parent a = some b → rank b < rank a)
    (cand : α → Finset V)
    (root terminal : α) (leftAnchor rightAnchor : V)
    (hleft : ∀ v ∈ cand root, G.Adj leftAnchor v)
    (hright : ∀ v ∈ cand terminal, G.Adj v rightAnchor)
    (hroot : ∀ a, parent a = none → Fintype.card α ≤ (cand a).card)
    (hchild : ∀ a b, parent a = some b → ∀ v ∈ cand b,
      Fintype.card α ≤ ((cand a).filter (fun w => G.Adj v w)).card) :
    ∃ f : α → V, Function.Injective f ∧
      (∀ a, f a ∈ cand a) ∧
      (∀ a b, parent a = some b → G.Adj (f a) (f b)) ∧
      G.Adj leftAnchor (f root) ∧ G.Adj (f terminal) rightAnchor := by
  obtain ⟨f, hf⟩ := candidate_forest_embedding G parent rank hrank cand hroot hchild;
  exact ⟨ f, hf.1, hf.2.1, hf.2.2, hleft _ ( hf.2.1 _ ), hright _ ( hf.2.1 _ ) ⟩

end Erdos550
