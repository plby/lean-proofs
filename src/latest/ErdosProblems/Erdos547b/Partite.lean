/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Greedy embeddings respecting a two-colouring

This file proves the partite greedy tree-embedding lemma used in the
extremal arguments for Erdős Problem 547.  The host parts need not cover the
host graph, but they are disjoint.  Each target colour is required to fit in
its prescribed host part, and every vertex of either host part has enough
neighbours in the opposite part for the entire opposite target colour class.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b

open SimpleGraph

/-- A graph embedding respects `c` and the indexed host parts `A` when every
target vertex lands in the part indexed by its colour. -/
def Copy.RespectsParts {r : ℕ} {α β : Type*}
    {T : SimpleGraph α} {G : SimpleGraph β}
    (c : T.Coloring (Fin r)) (A : Fin r → Finset β)
    (f : Copy T G) : Prop :=
  ∀ x, f x ∈ A (c x)

/-- The number of target vertices assigned the colour `i`. -/
def Coloring.partCard {r : ℕ} {α : Type*} [Fintype α]
    {T : SimpleGraph α} (c : T.Coloring (Fin r)) (i : Fin r) : ℕ :=
  (Finset.univ.filter fun x => c x = i).card

private theorem partCard_pos_of_eq {r : ℕ} {α : Type*} [Fintype α]
    {T : SimpleGraph α} (c : T.Coloring (Fin r)) {x : α} {i : Fin r}
    (hx : c x = i) : 0 < Coloring.partCard c i := by
  unfold Coloring.partCard
  exact Finset.card_pos.mpr ⟨x, by simp [hx]⟩

private theorem partCard_induce_compl_singleton_le {r : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] {T : SimpleGraph α} (c : T.Coloring (Fin r))
    (x : α) (i : Fin r) :
    Coloring.partCard (c.comap (Embedding.induce ({x}ᶜ : Set α)).toHom) i ≤
      Coloring.partCard c i := by
  classical
  unfold Coloring.partCard
  rw [← Finset.card_image_of_injective _ Subtype.val_injective]
  apply Finset.card_le_card
  intro a ha
  rcases Finset.mem_image.mp ha with ⟨y, hy, rfl⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
  exact hy

/-- Inductive core of the partite greedy embedding lemma. -/
private theorem tree_embedding_respecting_parts_aux {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (T : SimpleGraph α) (G : SimpleGraph β) [DecidableRel G.Adj]
    (c : T.Coloring (Fin 2)) (A : Fin 2 → Finset β)
    (hA : Set.PairwiseDisjoint Set.univ A)
    (hcap : ∀ i, Coloring.partCard c i ≤ (A i).card)
    (hdeg : ∀ i j, i ≠ j → ∀ v ∈ A i,
      Coloring.partCard c j ≤ ((G.neighborFinset v) ∩ (A j)).card)
    (n : ℕ) (hcard : Fintype.card α = n + 1) (hT : T.IsTree) :
    ∃ f : Copy T G, Copy.RespectsParts c A f := by
  classical
  induction n generalizing α β with
  | zero =>
      obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.mp hcard
      have hpos : 0 < Coloring.partCard c (c x) := partCard_pos_of_eq c rfl
      have hpart : (A (c x)).Nonempty := Finset.card_pos.mp (hpos.trans_le (hcap (c x)))
      obtain ⟨w, hw⟩ := hpart
      let f : α → β := fun _ => w
      have hf : Function.Injective f := by
        intro u v _
        rw [hx u, hx v]
      refine ⟨⟨⟨f, ?_⟩, hf⟩, ?_⟩
      · intro u v huv
        exact False.elim (T.ne_of_adj huv (by rw [hx u, hx v]))
      · intro u
        simpa [f, hx u, hx x] using hw
  | succ n ih =>
      have hcard_large : 1 < Fintype.card α := by omega
      have hnontrivial : Nontrivial α :=
        Fintype.one_lt_card_iff_nontrivial.mp hcard_large
      obtain ⟨x, hx⟩ :=
        @IsTree.exists_vert_degree_one_of_nontrivial α T _ hnontrivial _ hT
      obtain ⟨p, hxp, hp_unique⟩ := degree_eq_one_iff_existsUnique_adj.mp hx
      let s : Set α := {x}ᶜ
      let T' : SimpleGraph s := T.induce s
      let c' : T'.Coloring (Fin 2) := c.comap (Embedding.induce s).toHom
      have hcard' : Fintype.card s = n + 1 := by
        have hc := Fintype.card_subtype_compl (fun a : α => a = x)
        change Fintype.card {a : α // ¬a = x} = n + 1
        rw [hc, hcard]
        simp
      have hT' : T'.IsTree := by
        exact ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hx,
          hT.isAcyclic.induce s⟩
      have hcap' : ∀ i, Coloring.partCard c' i ≤ (A i).card := by
        intro i
        exact (partCard_induce_compl_singleton_le c x i).trans (hcap i)
      have hdeg' : ∀ i j, i ≠ j → ∀ v ∈ A i,
          Coloring.partCard c' j ≤ ((G.neighborFinset v) ∩ (A j)).card := by
        intro i j hij v hv
        exact (partCard_induce_compl_singleton_le c x j).trans (hdeg i j hij v hv)
      rcases ih T' G c' A hA hcap' hdeg' hcard' hT' with ⟨f, hfparts⟩
      let ps : s := ⟨p, by simpa [s] using hxp.ne'⟩
      have hcolors : c p ≠ c x := c.valid hxp.symm
      have hparent_part : f ps ∈ A (c p) := by
        simpa [c', ps] using hfparts ps
      let used : Finset β :=
        (Finset.univ.filter fun a : s => c' a = c x).image f
      have hused_card : used.card = Coloring.partCard c' (c x) := by
        dsimp only [used, Coloring.partCard]
        exact Finset.card_image_iff.mpr fun _ _ _ _ h => f.injective h
      have hpartcard : Coloring.partCard c (c x) =
          Coloring.partCard c' (c x) + 1 := by
        unfold Coloring.partCard
        rw [show (Finset.univ.filter fun a : α => c a = c x) =
            insert x ((Finset.univ.filter fun a : α => c a = c x).erase x) by
          rw [Finset.insert_erase (by simp)]]
        rw [Finset.card_insert_of_notMem]
        · congr 1
          apply Finset.card_bij (fun a ha => ⟨a, by
            have := (Finset.mem_erase.mp ha).1
            simpa [s] using this⟩)
          · intro a ha
            simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at ha
            simpa [c', s, ha.2]
          · intro a₁ ha₁ a₂ ha₂ h
            exact Subtype.ext_iff.mp h
          · intro a ha
            refine ⟨a.1, ?_, rfl⟩
            simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · exact a.2
            · simpa [c', s] using ha
        · simp
      have hcandidate_card : used.card <
          ((G.neighborFinset (f ps)) ∩ (A (c x))).card := by
        rw [hused_card]
        have := hdeg (c p) (c x) hcolors (f ps) hparent_part
        omega
      obtain ⟨w, hw_candidate, hw_unused⟩ :=
        Finset.exists_mem_notMem_of_card_lt_card hcandidate_card
      have hw_adj : G.Adj (f ps) w := by
        exact (G.mem_neighborFinset (f ps) w).mp (Finset.mem_inter.mp hw_candidate).1
      have hw_part : w ∈ A (c x) := (Finset.mem_inter.mp hw_candidate).2
      have hw_not_range : ∀ a : s, w ≠ f a := by
        intro a hwa
        have hca : c a.1 = c x := by
          by_contra hne
          have hdisj := hA (Set.mem_univ (c x)) (Set.mem_univ (c a.1))
            (fun h => hne h.symm)
          have hfa : f a ∈ A (c a.1) := by simpa [c'] using hfparts a
          rw [← hwa] at hfa
          exact Finset.disjoint_left.mp hdisj hw_part hfa
        apply hw_unused
        exact Finset.mem_image.mpr ⟨a, by simpa [c'] using hca, hwa.symm⟩
      let F : α → β := fun a => if h : a = x then w else f ⟨a, by simpa [s] using h⟩
      refine ⟨⟨⟨F, ?_⟩, ?_⟩, ?_⟩
      · intro u v huv
        by_cases hu : u = x
        · subst u
          have hvp : v = p := hp_unique v huv
          subst v
          simpa [F, ps, hxp.ne, hxp.ne'] using hw_adj.symm
        · by_cases hv : v = x
          · subst v
            have hup : u = p := hp_unique u huv.symm
            subst u
            simpa [F, ps, hxp.ne, hxp.ne'] using hw_adj
          · let us : s := ⟨u, by simpa [s] using hu⟩
            let vs : s := ⟨v, by simpa [s] using hv⟩
            have huv' : T'.Adj us vs := by simpa [T', us, vs] using huv
            have hmap := f.toHom.map_adj huv'
            simpa [F, hu, hv, us, vs] using hmap
      · intro u v huv
        by_cases hu : u = x
        · subst u
          by_cases hv : v = x
          · exact hv.symm
          · exfalso
            apply hw_not_range ⟨v, by simpa [s] using hv⟩
            simpa [F, hv] using huv
        · by_cases hv : v = x
          · subst v
            exfalso
            apply hw_not_range ⟨u, by simpa [s] using hu⟩
            simpa [F, hu] using huv.symm
          · have hsub : (⟨u, by simpa [s] using hu⟩ : s) =
                ⟨v, by simpa [s] using hv⟩ := by
              apply f.injective
              simpa [F, hu, hv] using huv
            exact Subtype.ext_iff.mp hsub
      · intro u
        by_cases hu : u = x
        · subst u
          change F x ∈ A (c x)
          simpa [F] using hw_part
        · change F u ∈ A (c u)
          simpa [F, hu, c'] using hfparts ⟨u, by simpa [s] using hu⟩

/-- A finite tree embeds while respecting prescribed host parts if both
target colour classes fit and every host vertex in one part has enough
neighbours in the other part for the entire opposite target class. -/
theorem tree_embedding_respecting_parts {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (T : SimpleGraph α) (G : SimpleGraph β) [DecidableRel G.Adj]
    (hT : T.IsTree) (c : T.Coloring (Fin 2)) (A : Fin 2 → Finset β)
    (hA : Set.PairwiseDisjoint Set.univ A)
    (hcap : ∀ i, Coloring.partCard c i ≤ (A i).card)
    (hdeg : ∀ i j, i ≠ j → ∀ v ∈ A i,
      Coloring.partCard c j ≤ ((G.neighborFinset v) ∩ (A j)).card) :
    ∃ f : Copy T G, Copy.RespectsParts c A f := by
  apply tree_embedding_respecting_parts_aux T G c A hA hcap hdeg (Fintype.card α - 1)
  · have hpos : 0 < Fintype.card α := Fintype.card_pos_iff.mpr hT.connected.nonempty
    omega
  · exact hT

/-- Containment-only corollary of `tree_embedding_respecting_parts`. -/
theorem tree_isContained_of_bicolored_minDegree {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (T : SimpleGraph α) (G : SimpleGraph β) [DecidableRel G.Adj]
    (hT : T.IsTree) (c : T.Coloring (Fin 2)) (A : Fin 2 → Finset β)
    (hA : Set.PairwiseDisjoint Set.univ A)
    (hcap : ∀ i, Coloring.partCard c i ≤ (A i).card)
    (hdeg : ∀ i j, i ≠ j → ∀ v ∈ A i,
      Coloring.partCard c j ≤ ((G.neighborFinset v) ∩ (A j)).card) : T ⊑ G := by
  rcases tree_embedding_respecting_parts T G hT c A hA hcap hdeg with ⟨f, -⟩
  exact ⟨f⟩

end Erdos547b

#print axioms Erdos547b.tree_embedding_respecting_parts
