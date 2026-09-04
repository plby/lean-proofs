import Mathlib
import ErdosProblems.Erdos550.Basic

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Greedy complete-multipartite embedding

This file isolates the purely combinatorial "greedy embedding" engine that the
paper uses three times in the blocker/reservoir part of the argument
(§8 `lem:reservoirs` H-freeness claim, §9 `lem:asetblock` and
`lem:obstructionblock`): from a family of large "candidate pools" with a uniform
common-red-neighbourhood richness condition, one greedily builds a red copy of
the complete multipartite graph `K_{m₀,…,m_{k-1}}`, choosing class `i` inside
pool `C i`.

The key abstraction is `CrossComplete`: a family of vertex sets is
cross-complete when any two vertices lying in *different* sets are adjacent.
A cross-complete family of disjoint sets with the right cardinalities is exactly
a copy of the complete multipartite graph (`kmult_contained_of_sets`), and the
greedy selection (`exists_cross_complete_sets`) produces such a family from the
richness hypothesis `hrich`.
-/

open SimpleGraph Finset

namespace Erdos550

variable {V : Type*}

/-- A family `S : Fin k → Finset V` of vertex sets is *cross-complete* in `Gr`
if any two vertices lying in different sets are `Gr`-adjacent. -/
def CrossComplete (Gr : SimpleGraph V) {k : ℕ} (S : Fin k → Finset V) : Prop :=
  ∀ i j, i ≠ j → ∀ x ∈ S i, ∀ y ∈ S j, Gr.Adj x y

/-
A cross-complete family of pairwise-disjoint sets with `|S i| = m i` is a copy
of the complete multipartite graph `K_{m₀,…,m_{k-1}}` inside `Gr`.
-/
theorem kmult_contained_of_sets (Gr : SimpleGraph V) (k : ℕ) (m : Fin k → ℕ)
    (S : Fin k → Finset V) (hcard : ∀ i, (S i).card = m i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (hcross : CrossComplete Gr S) :
    Kmult k m ⊑ Gr := by
  -- By definition of `Kmult`, we can construct the desired homomorphism.
  have h_hom : ∃ f : (i : Fin k) × Fin (m i) → V, Function.Injective f ∧ ∀ i j, i ≠ j → ∀ x ∈ Finset.univ, ∀ y ∈ Finset.univ, Gr.Adj (f ⟨i, x⟩) (f ⟨j, y⟩) := by
    -- By definition of `S`, we can construct the desired homomorphism.
    obtain ⟨f, hf⟩ : ∃ (f : (i : Fin k) → Fin (m i) → V), (∀ i, Function.Injective (f i)) ∧ (∀ i, ∀ x ∈ Finset.univ, f i x ∈ S i) := by
      have h_equiv : ∀ i, Nonempty (Fin (m i) ≃ S i) := by
        exact fun i => ⟨ Fintype.equivOfCardEq <| by simp +decide [ hcard i ] ⟩;
      exact ⟨ fun i x => ( h_equiv i ).some x |>.1, fun i => fun x y hxy => by simpa using! ( h_equiv i ).some.injective ( Subtype.ext hxy ), fun i x _ => ( h_equiv i ).some x |>.2 ⟩;
    refine' ⟨ fun ⟨ i, x ⟩ => f i x, _, _ ⟩ <;> simp_all +decide only [ne_eq, mem_univ, forall_const];
    · rintro ⟨ i, x ⟩ ⟨ j, y ⟩ h; have := hdisj i j; simp_all +decide [ Finset.disjoint_left ] ;
      grind;
    · exact fun i j hij x y => hcross i j hij _ ( hf.2 i x ) _ ( hf.2 j y );
  obtain ⟨ f, hf_inj, hf_adj ⟩ := h_hom;
  refine' ⟨ ⟨ f, _ ⟩, _ ⟩;
  all_goals simp_all +decide [ Kmult ]

/-
**Greedy selection.**  Given pairwise-disjoint candidate pools `C i` and the
uniform richness condition `hrich` (every pool `C j`, after restricting to the
common red neighbourhood of any already-chosen set `U` of at most `∑ m`
vertices, still has at least `m j` vertices), there is a cross-complete family
of pairwise-disjoint sets `S i ⊆ C i` with `|S i| = m i`.
-/
theorem exists_cross_complete_sets [DecidableEq V] (Gr : SimpleGraph V)
    [DecidableRel Gr.Adj] (k : ℕ) (m : Fin k → ℕ) (C : Fin k → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hrich : ∀ (j : Fin k) (U : Finset V), U.card ≤ ∑ i, m i →
        m j ≤ ((C j).filter (fun v => ∀ u ∈ U, Gr.Adj v u)).card) :
    ∃ S : Fin k → Finset V, (∀ i, (S i).card = m i) ∧
      (∀ i, S i ⊆ C i) ∧
      (∀ i j, i ≠ j → Disjoint (S i) (S j)) ∧ CrossComplete Gr S := by
  induction' k with k ih;
  · simp +decide [ CrossComplete ];
  · obtain ⟨ S', hS' ⟩ := ih ( fun i ↦ m i.castSucc ) ( fun i ↦ C i.castSucc ) ( fun i j hij ↦ hdisj _ _ ( by simpa [ Fin.ext_iff ] using! hij ) ) ( fun j U hU ↦ le_trans ( hrich _ _ <| by simpa [ Fin.sum_univ_castSucc ] using! hU.trans ( by simp +decide ) ) <| by simp +decide );
    -- Let `U = (Finset.univ : Finset (Fin k)).biUnion S'`, the union of all chosen sets.
    set U := Finset.biUnion Finset.univ S' with hU_def;
    -- Apply `hrich` to get a set `F = filter (fun v => ∀ u ∈ U, Gr.Adj v u) (C (Fin.last k))` of card `≥ m (Fin.last k)`.
    obtain ⟨F, hF⟩ : ∃ F : Finset V, F ⊆ C (Fin.last k) ∧ F.card = m (Fin.last k) ∧ ∀ v ∈ F, ∀ u ∈ U, Gr.Adj v u := by
      have hF : m (Fin.last k) ≤ (Finset.filter (fun v => ∀ u ∈ U, Gr.Adj v u) (C (Fin.last k))).card := by
        apply hrich;
        refine' le_trans ( Finset.card_biUnion_le ) _;
        rw [ Fin.sum_univ_castSucc ] ; simp +decide [ hS'.1 ];
      obtain ⟨ F, hF ⟩ := Finset.exists_subset_card_eq hF;
      exact ⟨ F, Finset.Subset.trans hF.1 ( Finset.filter_subset _ _ ), hF.2, fun v hv u hu => Finset.mem_filter.mp ( hF.1 hv ) |>.2 u hu ⟩;
    refine' ⟨ Fin.snoc S' F, _, _, _, _ ⟩;
    · intro i; refine' Fin.lastCases _ _ i <;> simp +decide [ * ] ;
    · intro i; refine' Fin.lastCases _ _ i <;> simp +decide [ * ] ;
    · intro i j hij; cases i using Fin.lastCases <;> cases j using Fin.lastCases <;> simp +decide only [Fin.snoc_castSucc, Fin.snoc_last] at hij ⊢;
      · exact (hij rfl).elim;
      · exact Disjoint.mono hF.1 (hS'.2.1 _) (hdisj _ _ hij);
      · exact Disjoint.mono (hS'.2.1 _) hF.1 (hdisj _ _ hij);
      · exact hS'.2.2.1 _ _ (by simpa [Fin.ext_iff] using! hij);
    · intro i j hij x hx y hy;
      by_cases hi : i.val < k <;> by_cases hj : j.val < k <;> simp +decide [ Fin.snoc, * ] at hx hy ⊢;
      · exact hS'.2.2.2 _ _ ( by simpa [ Fin.ext_iff ] using! hij ) _ hx _ hy;
      · exact hF.2.2 _ hy _ ( Finset.mem_biUnion.mpr ⟨ _, Finset.mem_univ _, hx ⟩ ) |> SimpleGraph.Adj.symm;
      · exact hF.2.2 x hx y ( Finset.mem_biUnion.mpr ⟨ _, Finset.mem_univ _, hy ⟩ );
      · exact False.elim ( hij ( Fin.ext ( by linarith [ Fin.is_lt i, Fin.is_lt j ] ) ) )

/-- **Greedy complete-multipartite embedding.**  Under pairwise-disjoint pools and
the richness condition, `Gr` contains a copy of `K_{m₀,…,m_{k-1}}`. -/
theorem greedy_multipartite_embedding [DecidableEq V] (Gr : SimpleGraph V)
    [DecidableRel Gr.Adj] (k : ℕ) (m : Fin k → ℕ) (C : Fin k → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hrich : ∀ (j : Fin k) (U : Finset V), U.card ≤ ∑ i, m i →
        m j ≤ ((C j).filter (fun v => ∀ u ∈ U, Gr.Adj v u)).card) :
    Kmult k m ⊑ Gr := by
  obtain ⟨S, hcard, _, hdisjS, hcross⟩ :=
    exists_cross_complete_sets Gr k m C hdisj hrich
  exact kmult_contained_of_sets Gr k m S hcard hdisjS hcross

/-
**Ordered greedy selection.**  A weaker, *ordered* richness hypothesis
suffices: for the richness of pool `C j` we only need to control already-chosen
vertices `U` drawn from *earlier* pools `C i` (`i < j`).  This is the form used
in the blocker-hypergraph arguments, where the distinguished first class (the
`a`-set, resp. the obstruction) is selected first and the remaining classes are
chosen from the reservoirs to be red-adjacent to everything already chosen.
-/
theorem exists_cross_complete_sets_ordered [DecidableEq V] (Gr : SimpleGraph V)
    [DecidableRel Gr.Adj] (k : ℕ) (m : Fin k → ℕ) (C : Fin k → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hrich : ∀ (j : Fin k) (U : Finset V),
        (∀ u ∈ U, ∃ i, i < j ∧ u ∈ C i) → U.card ≤ ∑ i, m i →
        m j ≤ ((C j).filter (fun v => ∀ u ∈ U, Gr.Adj v u)).card) :
    ∃ S : Fin k → Finset V, (∀ i, (S i).card = m i) ∧
      (∀ i, S i ⊆ C i) ∧
      (∀ i j, i ≠ j → Disjoint (S i) (S j)) ∧ CrossComplete Gr S := by
  -- We proceed by induction on $k$.
  induction' k with k ih;
  · simp +decide [ CrossComplete ];
  · obtain ⟨ S', hS' ⟩ := ih ( fun i => m i.castSucc ) ( fun i => C i.castSucc ) ( fun i j hij => hdisj _ _ <| by simpa [ Fin.ext_iff ] using! hij ) ( fun j U hU hU' => hrich _ _ ( fun u hu => by obtain ⟨ i, hi, hi' ⟩ := hU u hu; exact ⟨ i.castSucc, by simpa [ Fin.castSucc_lt_last ] using! hi, hi' ⟩ ) <| hU'.trans <| by simp +decide [ Fin.sum_univ_castSucc ] );
    -- Let $U = \bigcup_{i : Fin k} S' i$. Then $|U| \leq \sum_{i : Fin k} |S' i| = \sum_{i : Fin k} m (Fin.castSucc i) \leq \sum_{i : Fin (k + 1)} m i$.
    set U : Finset V := Finset.biUnion Finset.univ S'
    have hU_card : U.card ≤ ∑ i, m i := by
      refine' le_trans ( Finset.card_biUnion_le ) _;
      simp +decide only [hS'.1];
      exact Fin.sum_univ_castSucc m ▸ Nat.le_add_right _ _;
    -- By the richness hypothesis, there exists a subset $F \subseteq C (Fin.last k)$ of size $m (Fin.last k)$ such that every vertex in $F$ is adjacent to every vertex in $U$.
    obtain ⟨F, hF⟩ : ∃ F : Finset V, F ⊆ C (Fin.last k) ∧ F.card = m (Fin.last k) ∧ ∀ v ∈ F, ∀ u ∈ U, Gr.Adj v u := by
      have := hrich ( Fin.last k ) U ?_ hU_card;
      · obtain ⟨ F, hF ⟩ := Finset.exists_subset_card_eq this;
        exact ⟨ F, Finset.Subset.trans hF.1 ( Finset.filter_subset _ _ ), hF.2, fun v hv u hu => Finset.mem_filter.mp ( hF.1 hv ) |>.2 u hu ⟩;
      · simp +zetaDelta at *;
        exact fun u i hi => ⟨ Fin.castSucc i, Fin.castSucc_lt_last i, hS'.2.1 i hi ⟩;
    refine' ⟨ Fin.snoc S' F, _, _, _, _ ⟩;
    · intro i; refine' Fin.lastCases _ _ i <;> simp +decide [ * ] ;
    · intro i; refine' Fin.lastCases _ _ i <;> simp +decide [ * ] ;
    · intro i j hij; induction i using Fin.lastCases <;> induction j using Fin.lastCases <;> simp +decide only [Fin.snoc_castSucc, Fin.snoc_last] at hij ⊢;
      · exact (hij rfl).elim;
      · exact Disjoint.mono hF.1 (hS'.2.1 _) (hdisj _ _ hij);
      · exact Disjoint.mono (hS'.2.1 _) hF.1 (hdisj _ _ hij);
      · exact hS'.2.2.1 _ _ (by simpa [Fin.ext_iff] using! hij);
    · intro i j hij;
      simp +zetaDelta at *;
      cases i using Fin.lastCases <;> cases j using Fin.lastCases <;> simp +decide [ * ] at hij ⊢;
      · exact fun x hx y hy => hF.2.2 x hx y _ hy;
      · exact fun x hx y hy => SimpleGraph.Adj.symm ( hF.2.2 y hy x _ hx );
      · exact hS'.2.2.2 _ _ hij

/-- **Ordered greedy complete-multipartite embedding.**  Under pairwise-disjoint
pools and the *ordered* richness condition, `Gr` contains a copy of
`K_{m₀,…,m_{k-1}}`. -/
theorem greedy_multipartite_embedding_ordered [DecidableEq V] (Gr : SimpleGraph V)
    [DecidableRel Gr.Adj] (k : ℕ) (m : Fin k → ℕ) (C : Fin k → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hrich : ∀ (j : Fin k) (U : Finset V),
        (∀ u ∈ U, ∃ i, i < j ∧ u ∈ C i) → U.card ≤ ∑ i, m i →
        m j ≤ ((C j).filter (fun v => ∀ u ∈ U, Gr.Adj v u)).card) :
    Kmult k m ⊑ Gr := by
  obtain ⟨S, hcard, _, hdisjS, hcross⟩ :=
    exists_cross_complete_sets_ordered Gr k m C hdisj hrich
  exact kmult_contained_of_sets Gr k m S hcard hdisjS hcross

end Erdos550
