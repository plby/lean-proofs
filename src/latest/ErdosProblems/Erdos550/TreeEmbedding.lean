import Mathlib

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Elementary tree-embedding tools

This file develops elementary tree-embedding tools used by the off--Turán
argument.

The cornerstone is the classical *greedy tree-embedding lemma*
`tree_embeds_of_minDegree`: a finite graph whose minimum degree is at least
`|T| - 1` contains every tree `T`.
-/

open SimpleGraph Finset Function

namespace Erdos550

/-
Cardinality of the complement of a singleton, as a subtype.
-/
lemma card_compl_singleton {V : Type} [Fintype V] [DecidableEq V] (ℓ : V) :
    Fintype.card ↥({ℓ}ᶜ : Set V) = Fintype.card V - 1 := by
  rw [ Fintype.card_compl_set ] ; simp +decide

/-
**Free-neighbour lemma.** If `p` has at least `k` neighbours and `S` is a set
of exactly `k` vertices containing `p`, then `p` has a neighbour outside `S`
(using that `p` is never its own neighbour).
-/
lemma exists_fresh_neighbor
    {W : Type} [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj]
    {p : W} {k : ℕ} {S : Finset W} (hp : p ∈ S) (hScard : S.card = k)
    (hdeg : k ≤ (G.neighborFinset p).card) :
    ∃ w, w ∈ G.neighborFinset p ∧ w ∉ S := by
  contrapose! hdeg;
  exact lt_of_lt_of_le ( Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ hdeg, by aesop_cat ⟩ ) ) hScard.le

/-- **Leaf-extension lemma.** Suppose `ℓ` is a vertex of `T` whose only neighbour
is `u`. Given an injective homomorphism `f` from the induced subgraph on `{ℓ}ᶜ`
into `G`, and a vertex `w` of `G` that is adjacent to `f u` and is not in the
image of `f`, one can extend `f` to a copy of the whole graph `T` in `G`. -/
lemma isContained_of_leaf_extension
    {V W : Type} (T : SimpleGraph V) (G : SimpleGraph W)
    {ℓ u : V} (hu : u ∈ ({ℓ}ᶜ : Set V))
    (hadj : ∀ v, T.Adj ℓ v ↔ v = u)
    (f : (T.induce ({ℓ}ᶜ : Set V)) →g G) (hf : Function.Injective f)
    {w : W}
    (hwadj : G.Adj (f ⟨u, hu⟩) w)
    (hwnew : ∀ v : ({ℓ}ᶜ : Set V), (f v) ≠ w) :
    T ⊑ G := by
  classical
  have hℓ : u ≠ ℓ := Set.mem_compl_singleton_iff.mp hu
  have hmem : ∀ {v : V}, v ≠ ℓ → v ∈ ({ℓ}ᶜ : Set V) := by
    intro v h; simpa using! h
  set gf : V → W := fun v => if h : v = ℓ then w else f ⟨v, hmem h⟩ with hgf
  have gf_ℓ : gf ℓ = w := by simp [hgf]
  have gf_ne : ∀ {v : V} (h : v ≠ ℓ), gf v = f ⟨v, hmem h⟩ := by
    intro v h; simp [hgf, h]
  refine ⟨SimpleGraph.Hom.toCopy ⟨gf, ?_⟩ ?_⟩
  · intro a b hab
    have hne : a ≠ b := hab.ne
    by_cases ha : a = ℓ
    · subst ha
      have hb : b = u := (hadj b).mp hab
      subst hb
      rw [gf_ℓ, gf_ne hℓ]
      exact hwadj.symm
    · by_cases hb : b = ℓ
      · subst hb
        have ha' : a = u := (hadj a).mp hab.symm
        subst ha'
        rw [gf_ℓ, gf_ne hℓ]
        exact hwadj
      · rw [gf_ne ha, gf_ne hb]
        exact f.map_adj (by exact hab)
  · intro a b hab
    change gf a = gf b at hab
    by_cases ha : a = ℓ
    · by_cases hb : b = ℓ
      · rw [ha, hb]
      · exfalso
        rw [ha, gf_ℓ, gf_ne hb] at hab
        exact hwnew ⟨b, hmem hb⟩ hab.symm
    · by_cases hb : b = ℓ
      · exfalso
        rw [hb, gf_ℓ, gf_ne ha] at hab
        exact hwnew ⟨a, hmem ha⟩ hab
      · rw [gf_ne ha, gf_ne hb] at hab
        have := hf hab
        exact Subtype.mk_eq_mk.mp this

/-- **Dense-subgraph extraction (average-degree form).**

If, over a finite vertex set `B`, the sum of internal degrees is at least
`d * |B|` (i.e. the average internal degree is at least `d`), then there is a
nonempty subset `A ⊆ B` in which every vertex has at least `d / 2` neighbours
inside `A`.

Here the "internal degree" of `v` in a set `X` is `(G.neighborFinset v ∩ X).card`;
twice the number of internal edges equals the sum of internal degrees. -/
lemma exists_dense_subset
    {W : Type} [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj]
    (d : ℝ) :
    ∀ B : Finset W, B.Nonempty →
      (d * B.card ≤ ∑ v ∈ B, ((G.neighborFinset v ∩ B).card : ℝ)) →
      ∃ A : Finset W, A ⊆ B ∧ A.Nonempty ∧
        ∀ v ∈ A, d / 2 ≤ ((G.neighborFinset v ∩ A).card : ℝ) := by
  intro B
  induction B using Finset.strongInduction with
  | _ B ih =>
  intro hB hsum
  by_cases h_case : ∀ v ∈ B, d / 2 ≤ ((G.neighborFinset v ∩ B).card : ℝ)
  · exact ⟨B, Finset.Subset.refl _, hB, h_case⟩
  · push_neg at h_case
    obtain ⟨v, hvB, hv⟩ := h_case
    set B' := B.erase v with hB'
    have key : ∀ u ∈ B', (G.neighborFinset u ∩ B).card
        = (G.neighborFinset u ∩ B').card + (if G.Adj u v then 1 else 0) := by
      intro u hu
      rw [hB', Finset.inter_erase]
      by_cases hadj : G.Adj u v
      · have hvmem : v ∈ G.neighborFinset u ∩ B := by
          rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
          exact ⟨hadj, hvB⟩
        rw [Finset.card_erase_of_mem hvmem, if_pos hadj]
        have : 1 ≤ (G.neighborFinset u ∩ B).card := Finset.card_pos.mpr ⟨v, hvmem⟩
        omega
      · have hvmem : v ∉ G.neighborFinset u ∩ B := by
          rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
          exact fun h => hadj h.1
        rw [Finset.erase_eq_of_notMem hvmem, if_neg hadj, add_zero]
    have hcount : ∑ u ∈ B', (if G.Adj u v then 1 else 0)
        = (G.neighborFinset v ∩ B).card := by
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]
      congr 1
      ext u
      simp only [Finset.mem_filter, Finset.mem_inter, SimpleGraph.mem_neighborFinset, hB',
        Finset.mem_erase]
      constructor
      · rintro ⟨⟨_, huB⟩, hadj⟩; exact ⟨(G.adj_comm u v).mp hadj, huB⟩
      · rintro ⟨hadj, huB⟩
        exact ⟨⟨hadj.ne', huB⟩, (G.adj_comm v u).mp hadj⟩
    have hnatid : ∑ u ∈ B, (G.neighborFinset u ∩ B).card
        = ∑ u ∈ B', (G.neighborFinset u ∩ B').card + 2 * (G.neighborFinset v ∩ B).card := by
      rw [← Finset.add_sum_erase _ _ hvB, ← hB', Finset.sum_congr rfl key,
        Finset.sum_add_distrib, hcount]
      ring
    have hcardB : (B.card : ℝ) = (B'.card : ℝ) + 1 := by
      rw [hB', Finset.card_erase_of_mem hvB, Nat.cast_sub (Finset.card_pos.mpr ⟨v, hvB⟩)]
      simp
    have hRid : (∑ u ∈ B, ((G.neighborFinset u ∩ B).card : ℝ))
        = (∑ u ∈ B', ((G.neighborFinset u ∩ B').card : ℝ))
          + 2 * ((G.neighborFinset v ∩ B).card : ℝ) := by
      exact_mod_cast hnatid
    have hsum_B' : d * (B'.card : ℝ) ≤ ∑ u ∈ B', ((G.neighborFinset u ∩ B').card : ℝ) := by
      rw [hRid, hcardB] at hsum
      nlinarith [hsum, hv]
    by_cases hB'_ne : B'.Nonempty
    · obtain ⟨A, hAsub, hAne, hAdeg⟩ := ih B' (Finset.erase_ssubset hvB) hB'_ne hsum_B'
      exact ⟨A, hAsub.trans (Finset.erase_subset _ _), hAne, hAdeg⟩
    · rw [Finset.not_nonempty_iff_eq_empty, hB'] at hB'_ne
      have hBv : B = {v} := by
        rw [Finset.erase_eq_empty_iff] at hB'_ne
        rcases hB'_ne with h | h
        · rw [h] at hvB; simp at hvB
        · exact h
      have hd : d ≤ 0 := by
        rw [hBv] at hsum
        have hz : (G.neighborFinset v ∩ {v}) = ∅ :=
          Finset.inter_singleton_of_notMem (G.notMem_neighborFinset_self v)
        simp only [Finset.sum_singleton, Finset.card_singleton, Nat.cast_one, mul_one, hz,
          Finset.card_empty, Nat.cast_zero] at hsum
        exact hsum
      refine ⟨B, Finset.Subset.refl _, hB, ?_⟩
      intro w _
      have : (0:ℝ) ≤ ((G.neighborFinset w ∩ B).card : ℝ) := by positivity
      linarith

/-- **Greedy tree embedding (minimum-degree form).**

If a finite graph `G` on a nonempty vertex set has minimum degree at least
`n - 1`, where `n = Fintype.card V`, then it contains a copy of every tree `T`
on `V`. -/
theorem tree_embeds_of_minDegree :
    ∀ (n : ℕ) {V : Type} [Fintype V] (T : SimpleGraph V) [DecidableRel T.Adj],
      T.IsTree → Fintype.card V = n →
      ∀ {W : Type} [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
        0 < Fintype.card W → n - 1 ≤ G.minDegree → T ⊑ G := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ T _ hT hV W _ _ G _ hG hmin
  classical
  by_cases hV_le_one : Fintype.card V ≤ 1
  · have hT_empty : T = ⊥ := by
      ext v w
      simp only [SimpleGraph.bot_adj, iff_false]
      intro h
      have : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp hV_le_one
      exact h.ne (Subsingleton.elim _ _)
    rw [hT_empty]
    exact SimpleGraph.bot_isContained_iff_card_le.mpr (by omega)
  · have hnt : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (lt_of_not_ge hV_le_one)
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : V, T.degree ℓ = 1 := hT.exists_vert_degree_one_of_nontrivial
    obtain ⟨u, huset⟩ := Finset.card_eq_one.mp hℓ
    have hadju : T.Adj ℓ u := by
      rw [← SimpleGraph.mem_neighborFinset, huset]; exact Finset.mem_singleton_self u
    have hune : u ≠ ℓ := fun h => (h ▸ hadju).ne rfl
    have hu_mem : u ∈ ({ℓ}ᶜ : Set V) := by simpa using! hune
    have hadj : ∀ v, T.Adj ℓ v ↔ v = u := by
      intro v
      rw [← SimpleGraph.mem_neighborFinset, huset, Finset.mem_singleton]
    set s : Set V := {ℓ}ᶜ with hs
    set T' : SimpleGraph s := T.induce s with hT'def
    have hT'_tree : T'.IsTree :=
      ⟨SimpleGraph.Connected.induce_compl_singleton_of_degree_eq_one hT.1 hℓ, hT.2.induce s⟩
    have hcards : Fintype.card ↥s = n - 1 := by
      have h := card_compl_singleton (V := V) ℓ
      rw [hV] at h
      exact h
    obtain ⟨f⟩ : T' ⊑ G :=
      ih (n - 1) (by omega) T' hT'_tree hcards G hG (by omega)
    have hf : Function.Injective f.toHom := f.injective
    set p : W := f.toHom ⟨u, hu_mem⟩ with hp
    set S : Finset W := Finset.image (fun v : ↥s => f.toHom v) Finset.univ with hS
    have hScard : S.card = n - 1 := by
      rw [hS, Finset.card_image_of_injective _ hf, Finset.card_univ, hcards]
    have hpS : p ∈ S := Finset.mem_image.mpr ⟨⟨u, hu_mem⟩, Finset.mem_univ _, rfl⟩
    have hdeg : n - 1 ≤ (G.neighborFinset p).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      exact le_trans hmin (G.minDegree_le_degree p)
    obtain ⟨w, hw_mem, hw_notin⟩ := exists_fresh_neighbor G hpS hScard hdeg
    have hw_adj : G.Adj p w := by rwa [SimpleGraph.mem_neighborFinset] at hw_mem
    have hwnew : ∀ v : ↥s, f.toHom v ≠ w := by
      intro v hv
      exact hw_notin (Finset.mem_image.mpr ⟨v, Finset.mem_univ v, hv⟩)
    exact isContained_of_leaf_extension T G hu_mem hadj f.toHom hf hw_adj hwnew

/-
**Average-degree tree embedding (factor-2 / `c ≥ 1` regime).**

If a finite graph `G` on a nonempty vertex set has average degree at least
`2·(|T| − 1)` (equivalently `2·e(G) ≥ 2·(|T|−1)·|G|`), then it contains every
tree `T` on `V`.  This is the elementary consequence of extracting a dense
subgraph of minimum degree `≥ |T| − 1` (`exists_dense_subset`) and then embedding
greedily (`tree_embeds_of_minDegree`).
-/
theorem tree_embeds_of_avgDegree
    {V : Type} [Fintype V] (T : SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree)
    {W : Type} [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj]
    (hW : 0 < Fintype.card W)
    (hdeg : 2 * ((Fintype.card V : ℝ) - 1) * (Fintype.card W : ℝ)
        ≤ 2 * (G.edgeFinset.card : ℝ)) :
    T ⊑ G := by
  obtain ⟨A, hA⟩ : ∃ A : Finset W, A.Nonempty ∧ A ⊆ Finset.univ ∧ ∀ v ∈ A, ((G.neighborFinset v ∩ A).card : ℝ) ≥ (Fintype.card V - 1 : ℝ) := by
    have := exists_dense_subset G ( 2 * ( Fintype.card V - 1 ) ) Finset.univ ?_ ?_ <;> norm_num at *;
    · exact this;
    · exact Finset.card_pos.mp ( by simpa );
    · convert! hdeg using 1;
      exact mod_cast SimpleGraph.sum_degrees_eq_twice_card_edges G;
  obtain ⟨hA_nonempty, hA_subset, hA_deg⟩ := hA
  have hA_card : Fintype.card V - 1 ≤ (G.induce (↑A : Set W)).minDegree := by
    have hA_card : ∀ v : { x // x ∈ A }, (Fintype.card V - 1 : ℕ) ≤ (G.induce (↑A : Set W)).degree v := by
      intro v; specialize hA_deg v v.2; simp_all +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset ] ;
      norm_cast at hA_deg;
      convert! hA_deg using 2;
      refine' Finset.card_bij ( fun x hx => x ) _ _ _ <;> aesop;
    convert! SimpleGraph.le_minDegree_of_forall_le_degree _ _ hA_card;
    exact ⟨ ⟨ hA_nonempty.choose, hA_nonempty.choose_spec ⟩ ⟩;
  have hA_card : T ⊑ G.induce (↑A : Set W) := by
    apply Erdos550.tree_embeds_of_minDegree (Fintype.card V) T hT rfl;
    · aesop;
    · convert! hA_card using 1;
  convert! hA_card.trans _;
  exact ⟨ ⟨ fun x => x.val, by aesop_cat ⟩, by aesop_cat ⟩

end Erdos550
