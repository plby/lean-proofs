import Mathlib
import ErdosProblems.Erdos550.ForestEmbedding
import ErdosProblems.Erdos550.Centroid
import ErdosProblems.Erdos550.Allocation

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Profile lemma (Lemma `lem:profile` of the paper)

This file assembles the **profile lemma** of *A Resolution of Erdős Problem 550*
(E. Li) out of three already-proved components:

* the prescribed-root forest embedding (`rooted_forest_embedding`),
* the count-and-load allocation (`count_and_load`), and
* the tree-centroid theory (`tree_centroid`, `branchSize_sum_neighbors`).

We isolate the central **abstract tree-embedding lemma**
`tree_embed_from_allocation`, which takes the forest data (`parent`, `rank`,
`home`) and the allocation as explicit hypotheses and produces the blue copy.
It is built from a per-reservoir embedding `bin_embed`, which in turn uses a
rooted injection (`exists_rooted_inj`) followed by `rooted_forest_embedding`.
-/

open SimpleGraph Finset

namespace Erdos550

/-
**Rooted injection.**  If `B ⊆ W`, the "root" vertices of `α` number at most
`#B`, and `α` numbers at most `#W`, then there is an injection of `α` into `V`
landing inside `W`, sending every root into `B`.
-/
theorem exists_rooted_inj {α : Type*} [Fintype α] [DecidableEq α]
    {V : Type*} [DecidableEq V]
    (W B : Finset V) (hBW : B ⊆ W) (root : α → Prop) [DecidablePred root]
    (hroot : Fintype.card {a // root a} ≤ B.card)
    (hcard : Fintype.card α ≤ W.card) :
    ∃ f : α → V, Function.Injective f ∧ (∀ a, f a ∈ W) ∧ (∀ a, root a → f a ∈ B) := by
  obtain ⟨f, hf_inj⟩ : ∃ f : {a : α // root a} → V, Function.Injective f ∧ (∀ a, f a ∈ B) := by
    have := Finset.exists_subset_card_eq hroot;
    obtain ⟨ t, ht₁, ht₂ ⟩ := this;
    have := Finset.equivOfCardEq ht₂;
    exact ⟨ fun a => this.symm ⟨ a, Finset.mem_univ _ ⟩ |>.1, fun a b h => by simpa [ Subtype.ext_iff ] using! this.symm.injective ( Subtype.ext h ), fun a => ht₁ ( this.symm ⟨ a, Finset.mem_univ _ ⟩ |>.2 ) ⟩;
  obtain ⟨g, hg_inj⟩ : ∃ g : {a : α // ¬root a} → V, Function.Injective g ∧ (∀ a, g a ∈ W \ Finset.image f Finset.univ) := by
    have h_card : Finset.card (W \ Finset.image f Finset.univ) ≥ Fintype.card {a : α // ¬root a} := by
      rw [ Finset.card_sdiff ];
      rw [ Finset.inter_eq_left.mpr ];
      · rw [ Finset.card_image_of_injective _ hf_inj.1 ];
        simp +decide [ Fintype.card_subtype_compl ];
        omega;
      · exact Finset.image_subset_iff.mpr fun a _ => hBW ( hf_inj.2 a );
    have := Finset.exists_subset_card_eq h_card;
    obtain ⟨ t, ht₁, ht₂ ⟩ := this;
    have h_equiv : Nonempty ( {a : α // ¬root a} ≃ t ) := by
      exact ⟨ Fintype.equivOfCardEq <| by simp +decide [ ht₂ ] ⟩;
    exact ⟨ _, Subtype.val_injective.comp h_equiv.some.injective, fun a => ht₁ <| h_equiv.some a |>.2 ⟩;
  refine' ⟨ fun a => if ha : root a then f ⟨ a, ha ⟩ else g ⟨ a, ha ⟩, _, _, _ ⟩ <;> simp_all +decide [ Function.Injective ]; all_goals grind

/-
Degree inside an induced subgraph equals the size of the neighbourhood
intersected with the inducing set.
-/
theorem induce_degree_eq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) (v : V) (hv : v ∈ W) :
    (G.induce (↑W : Set V)).degree ⟨v, hv⟩ = ((G.neighborFinset v) ∩ W).card := by
  refine' Finset.card_bij _ _ _ _;
  use fun a ha => a.val;
  · aesop;
  · grind;
  · simp +decide only [mem_inter, mem_neighborFinset, SetLike.coe_sort_coe, comap_adj, exists_prop,
    Subtype.exists, exists_and_right, exists_eq_right, and_imp];
    exact fun b hb hb' => ⟨ hb', hb ⟩

/-
**Per-reservoir embedding.**  For a fixed reservoir index `i`, the forest of
vertices assigned to `i` embeds into `Gb`, landing inside `W i`, sending each
root (a forest vertex with no parent, i.e. a neighbour of `z`) to a blue
neighbour of `x`, and sending every parent edge to a blue edge.
-/
theorem bin_embed
    {VT : Type*} [Fintype VT] [DecidableEq VT]
    {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph VT) [DecidableRel T.Adj]
    (Gb : SimpleGraph V) [DecidableRel Gb.Adj]
    (q : ℕ) (z : VT) (x : V)
    (W : Fin q → Finset V) (home : VT → Fin q)
    (parent : VT → Option VT) (rank : VT → ℕ)
    (i : Fin q)
    (hparent_ne : ∀ v u, parent v = some u → u ≠ z)
    (hparent_rank : ∀ v u, parent v = some u → rank u < rank v)
    (hroot_adj : ∀ v, v ≠ z → parent v = none → T.Adj z v)
    (hhome_parent : ∀ v u, parent v = some u → home u = home v)
    (hroots : Fintype.card {w : VT // T.Adj z w ∧ home w = i}
        ≤ ((Gb.neighborFinset x) ∩ W i).card)
    (hWcard : Fintype.card {v : VT // v ≠ z ∧ home v = i} ≤ (W i).card)
    (hdeg : ∀ v ∈ W i,
        Fintype.card {w : VT // w ≠ z ∧ home w = i} - 1
          ≤ ((Gb.neighborFinset v) ∩ W i).card) :
    ∃ f : {v : VT // v ≠ z ∧ home v = i} → V,
      Function.Injective f ∧
      (∀ a, f a ∈ W i) ∧
      (∀ a, parent a.1 = none → Gb.Adj x (f a)) ∧
      (∀ a b, parent a.1 = some b.1 → Gb.Adj (f a) (f b)) := by
  obtain ⟨g, hg_inj, hg_mem, hg_root⟩ : ∃ g : {v : VT // v ≠ z ∧ home v = i} → V, Function.Injective g ∧ (∀ a, g a ∈ W i) ∧ (∀ a, parent a.1 = none → g a ∈ Gb.neighborFinset x) := by
    convert! exists_rooted_inj ( W i ) ( Gb.neighborFinset x ∩ W i ) ( Finset.inter_subset_right ) ( fun a => parent a.1 = none ) _ hWcard using 1;
    · grind;
    · refine' le_trans _ hroots;
      refine' Fintype.card_le_of_embedding _;
      refine' ⟨ fun a => ⟨ a.val, hroot_adj _ ( by aesop ) a.2, a.1.2.2 ⟩, fun a b h => _ ⟩ ; aesop;
  -- Define the parent function for the subgraph.
  set parentα : {v : VT // v ≠ z ∧ home v = i} → Option {v : VT // v ≠ z ∧ home v = i} := fun a => match parent a.val with | none => none | some u => if hu : u ≠ z ∧ home u = i then some ⟨u, hu⟩ else none;
  -- Define the rank function for the subgraph.
  set rankα : {v : VT // v ≠ z ∧ home v = i} → ℕ := fun a => rank a.val;
  -- Apply the rooted forest embedding lemma to the subgraph.
  obtain ⟨f, hf_inj, hf_root, hf_edge⟩ : ∃ f : {v : VT // v ≠ z ∧ home v = i} → ↥(W i), Function.Injective f ∧ (∀ a, parentα a = none → f a = ⟨g a, hg_mem a⟩) ∧ (∀ a b, parentα a = some b → Gb.Adj (f a).val (f b).val) := by
    have hdegJ : ∀ vv : ↥(W i), Fintype.card {v : VT // v ≠ z ∧ home v = i} - 1 ≤ (Gb.induce (W i : Set V)).degree vv := by
      intro vv;
      convert! hdeg vv vv.2 using 1;
      convert! induce_degree_eq Gb ( W i ) vv vv.2 using 1;
    have := Erdos550.rooted_forest_embedding ( Gb.induce ( W i : Set V ) ) parentα rankα ( fun a b hab => ?_ ) ( fun vv => hdegJ vv ) ( fun a => ⟨ g a, hg_mem a ⟩ ) ( fun a b hab => ?_ );
    · exact ⟨ this.choose, this.choose_spec.1, this.choose_spec.2.1, fun a b hab => this.choose_spec.2.2 a b hab ⟩;
    · grind;
    · lia;
  refine' ⟨ fun a => f a, _, _, _, _ ⟩;
  · exact Subtype.coe_injective.comp hf_inj;
  · exact fun a => f a |>.2;
  · intro a ha; specialize hf_root a; aesop;
  · grind

/-
**Abstract tree-embedding from an allocation.**

`T` is a tree on `VT`, `z` a distinguished vertex (the centroid), and the forest
`T − z` is encoded by `parent`/`rank` with `home : VT → Fin q` the reservoir
allocation (constant on the components of `T − z`).  Given disjoint reservoirs
`W` in a graph `Gb`, a vertex `x ∉ ⋃ Wᵢ`, with enough blue neighbours of `x`,
large enough reservoirs, and large internal minimum degree, the graph `Gb`
contains a copy of `T`.
-/
theorem tree_embed_from_allocation
    {VT : Type*} [Fintype VT] [DecidableEq VT]
    {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph VT) [DecidableRel T.Adj]
    (Gb : SimpleGraph V) [DecidableRel Gb.Adj]
    (q : ℕ) (z : VT) (x : V)
    (W : Fin q → Finset V)
    (home : VT → Fin q)
    (parent : VT → Option VT) (rank : VT → ℕ)
    (hxW : ∀ i, x ∉ W i)
    (hWdisj : ∀ i j, i ≠ j → Disjoint (W i) (W j))
    (hparent_ne : ∀ v u, parent v = some u → u ≠ z)
    (hparent_rank : ∀ v u, parent v = some u → rank u < rank v)
    (hroot_adj : ∀ v, v ≠ z → parent v = none → T.Adj z v)
    (hnbr_root : ∀ w, T.Adj z w → parent w = none)
    (hhome_parent : ∀ v u, parent v = some u → home u = home v)
    (hedge_parent : ∀ u v, T.Adj u v → u ≠ z → v ≠ z →
      parent u = some v ∨ parent v = some u)
    (hroots : ∀ i, Fintype.card {w : VT // T.Adj z w ∧ home w = i}
        ≤ ((Gb.neighborFinset x) ∩ W i).card)
    (hWcard : ∀ i, Fintype.card {v : VT // v ≠ z ∧ home v = i} ≤ (W i).card)
    (hdeg : ∀ i, ∀ v ∈ W i,
        Fintype.card {w : VT // w ≠ z ∧ home w = i} - 1
          ≤ ((Gb.neighborFinset v) ∩ W i).card) :
    T ⊑ Gb := by
  obtain ⟨f, hf⟩ : ∃ f : VT → V, Function.Injective f ∧ (∀ a b, T.Adj a b → Gb.Adj (f a) (f b)) := by
    -- By `bin_embed`, for each `i`, there exists a function `f_i` that embeds the forest component of `T - z` into `Gb` while respecting the allocation `home`.
    have h_bin_embed : ∀ i, ∃ f_i : {v : VT // v ≠ z ∧ home v = i} → V,
      Function.Injective f_i ∧ (∀ a, f_i a ∈ W i) ∧ (∀ a, parent a.1 = none → Gb.Adj x (f_i a)) ∧ (∀ a b, parent a.1 = some b.1 → Gb.Adj (f_i a) (f_i b)) := by
        exact fun i => bin_embed T Gb q z x W home parent rank i hparent_ne hparent_rank hroot_adj hhome_parent ( hroots i ) ( hWcard i ) ( hdeg i );
    choose f hf_inj hf_mem hf_root hf_edge using h_bin_embed;
    refine' ⟨ fun v => if h : v = z then x else f ( home v ) ⟨ v, h, rfl ⟩, _, _ ⟩;
    · intro u v huv;
      by_cases hu : u = z <;> by_cases hv : v = z <;> simp +decide [ hu, hv ] at huv ⊢;
      · exact False.elim ( hxW ( home v ) ( huv ▸ hf_mem _ _ ) );
      · exact hxW _ ( huv ▸ hf_mem _ _ );
      · by_cases h : home u = home v;
        · grind;
        · exact False.elim ( Finset.disjoint_left.mp ( hWdisj _ _ h ) ( hf_mem _ _ ) ( huv.symm ▸ hf_mem _ _ ) );
    · intro a b hab;
      by_cases ha : a = z <;> by_cases hb : b = z <;> simp +decide only [ne_eq] at hab ⊢;
      · exact hf_root _ _ ( hnbr_root _ hab );
      · exact SimpleGraph.Adj.symm ( hf_root ( home a ) ⟨ a, ha, rfl ⟩ ( hnbr_root a ( by simpa [ SimpleGraph.adj_comm ] using! hab ) ) );
      · cases' hedge_parent a b hab ha hb with h h;
        · grind +revert;
        · convert! hf_edge ( home a ) ⟨ b, hb, by rw [ hhome_parent _ _ h ] ⟩ ⟨ a, ha, rfl ⟩ h |> SimpleGraph.Adj.symm using 1;
          grind;
  refine' ⟨ ⟨ f, _ ⟩, _ ⟩;
  exacts [ fun { a b } hab => hf.2 a b hab, hf.1 ]

end Erdos550
