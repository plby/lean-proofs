import Mathlib
import ErdosProblems.Erdos550.RegularPairEmbedding
import ErdosProblems.Erdos550.RegularPairTools

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Tree embedding across a single regular pair

This file packages the single-regular-pair rooted-*forest* embedding engine
`Erdos550.regularPair_forest_embedding` into a clean single-regular-pair *tree*
embedding statement `Erdos550.tree_embeds_in_regularPair`: an `n`-vertex tree
embeds into any `ε`-uniform pair `(s,t)` of density `d` whose two sides are large
enough (`n + ε·|c| ≤ (d-ε)·|c|`).

The bridge is `Erdos550.IsTree.exists_rooted_structure`, which turns an abstract
finite tree into the `parent`/`rank`/`col` data required by the forest engine,
together with the key fact that every tree edge is realized as a parent edge (in
one of the two orientations).  When the host is large relative to the tree, a
single dense regular pair has clusters big enough to host the whole bipartite
tree.
-/

open SimpleGraph Finset

namespace Erdos550

private lemma fin2_toggle {x y : Fin 2} (h : x ≠ y) :
    decide (x = 1) ≠ decide (y = 1) := by
  fin_cases x <;> fin_cases y <;> simp_all

/-
In a tree, two adjacent vertices are at different distances from any fixed
root `r`.  (Trees are bipartite, so adjacent vertices have opposite-parity
distances; equivalently, the unique path forbids two geodesics.)
-/
lemma tree_adj_dist_ne {α : Type*} (T : SimpleGraph α) (hT : T.IsTree)
    {r a b : α} (hab : T.Adj a b) : T.dist a r ≠ T.dist b r := by
  grind +suggestions

/-
In a tree, every non-root vertex `a` has a *unique* neighbour `b` closer to
the root `r` (`T.dist b r < T.dist a r`).  This is the parent of `a`.
-/
lemma tree_closer_neighbor_exists_unique {α : Type*} (T : SimpleGraph α)
    (hT : T.IsTree) (r a : α) (ha : a ≠ r) :
    ∃! b : α, T.Adj a b ∧ T.dist b r < T.dist a r := by
  obtain ⟨p, hp⟩ : ∃ p : SimpleGraph.Walk T a r, p.length = T.dist a r ∧ p.IsPath := by
    have := hT.1 a r;
    obtain ⟨ p, hp ⟩ := this.exists_path_of_dist;
    exact ⟨ p, hp.2, hp.1 ⟩;
  rcases p with ( _ | ⟨ b, p ⟩ ) <;> simp_all +decide;
  refine' ⟨ _, ⟨ b, _ ⟩, _ ⟩;
  · linarith [ show T.dist ‹_› r ≤ p.length from SimpleGraph.dist_le _ ];
  · intro y hy
    obtain ⟨q, hq⟩ : ∃ q : SimpleGraph.Walk T y r, q.length = T.dist y r ∧ q.IsPath := by
      have := hT.1 y r;
      obtain ⟨ q, hq ⟩ := this.exists_walk_length_eq_dist;
      grind +suggestions;
    have h_unique : SimpleGraph.Walk.IsPath (SimpleGraph.Walk.cons b p) ∧ SimpleGraph.Walk.IsPath (SimpleGraph.Walk.cons hy.1 q) ∧ (SimpleGraph.Walk.cons b p).length = T.dist a r ∧ (SimpleGraph.Walk.cons hy.1 q).length = T.dist a r := by
      have h_unique : T.dist a r ≤ T.dist y r + 1 := by
        have h_path : T.dist a r ≤ T.dist a y + T.dist y r := by
          have h_dist : ∀ u v w : α, T.Reachable u v → T.Reachable v w → T.dist u w ≤ T.dist u v + T.dist v w := by
            intros u v w hu hv;
            have h_dist : ∀ u v w : α, T.Reachable u v → T.Reachable v w → T.dist u w ≤ T.dist u v + T.dist v w := by
              intros u v w hu hv
              have h_path : ∃ p : SimpleGraph.Walk T u w, p.length = T.dist u v + T.dist v w := by
                obtain ⟨ p, hp ⟩ := hu.exists_walk_length_eq_dist
                obtain ⟨ q, hq ⟩ := hv.exists_walk_length_eq_dist
                use p.append q
                simp [hp, hq]
              exact h_path.elim fun p hp => hp ▸ SimpleGraph.dist_le _;
            exact h_dist u v w hu hv;
          exact h_dist a y r ( SimpleGraph.Adj.reachable hy.1 ) ( q.reachable );
        linarith [ show T.dist a y = 1 from by rw [ SimpleGraph.dist_eq_one_iff_adj ] ; tauto ];
      have h_unique : a ∉ q.support := by
        intro hq_support
        have h_dist : T.dist a r ≤ q.length - 1 := by
          have h_dist : ∃ p : SimpleGraph.Walk T a r, p.length ≤ q.length - 1 := by
            obtain ⟨ p, hp ⟩ := SimpleGraph.Walk.mem_support_iff_exists_append.mp hq_support;
            obtain ⟨ r, hr ⟩ := hp; use r; simp +decide [ hr ] ;
            rcases p with ( _ | ⟨ _, _, p ⟩ ) <;> simp_all +decide;
          exact le_trans ( SimpleGraph.dist_le _ ) h_dist.choose_spec;
        omega;
      simp_all +decide [ SimpleGraph.Walk.cons_isPath_iff ];
      linarith;
    have := hT.existsUnique_path a r;
    have := this.unique h_unique.1 h_unique.2.1; aesop;

/-- **Rooted-tree structure of a finite tree.**

Every finite tree `T` admits a rooting: a `parent : α → Option α` with a strictly
decreasing `rank : α → ℕ` along parent links, a proper 2-colouring `col : α → Bool`
along parent links, and the property that every edge of `T` is a parent link in
one of its two orientations.  This is exactly the data consumed by
`regularPair_forest_embedding`. -/
lemma IsTree.exists_rooted_structure {α : Type*} [Fintype α] [DecidableEq α]
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree) :
    ∃ (parent : α → Option α) (rank : α → ℕ) (col : α → Bool),
      (∀ a b, parent a = some b → rank b < rank a) ∧
      (∀ a b, parent a = some b → col a ≠ col b) ∧
      (∀ a b, T.Adj a b → (parent a = some b ∨ parent b = some a)) := by
  classical
  -- Root the tree (α is nonempty since T is connected).
  obtain ⟨r⟩ : Nonempty α := hT.1.nonempty
  -- 2-colouring.
  obtain ⟨C⟩ : Nonempty (T.Coloring (Fin 2)) := Erdos550.IsTree.colorable_two T hT
  -- Unique closer neighbour = parent.
  have hpar := tree_closer_neighbor_exists_unique T hT r
  choose! par hpar_spec hpar_uniq using fun a (ha : a ≠ r) => hpar a ha
  refine ⟨fun a => if h : a = r then none else some (par a),
          fun a => T.dist a r,
          fun a => decide (C a = 1), ?_, ?_, ?_⟩
  · -- rank strictly decreases along parent
    intro a b hb
    by_cases ha : a = r
    · simp [ha] at hb
    · simp only [dif_neg ha, Option.some.injEq] at hb
      subst b
      exact (hpar_spec a ha).2
  · -- colour changes along parent
    intro a b hb
    by_cases ha : a = r
    · simp [ha] at hb
    · simp only [dif_neg ha, Option.some.injEq] at hb
      subst b
      have hadj : T.Adj a (par a) := (hpar_spec a ha).1
      exact fin2_toggle (C.valid hadj)
  · -- every edge is a parent link, in one orientation
    intro a b hab
    have hne : T.dist a r ≠ T.dist b r := tree_adj_dist_ne T hT hab
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- dist a r < dist b r: a is the closer neighbour of b, so parent b = some a
      right
      have hbr : b ≠ r := by
        rintro rfl
        simp only [SimpleGraph.dist_self] at hlt
        exact Nat.not_lt_zero _ hlt
      have hqual : T.Adj b a ∧ T.dist a r < T.dist b r := ⟨hab.symm, hlt⟩
      have := hpar_uniq b hbr a hqual
      simp [hbr, this]
    · -- dist b r < dist a r: b is the closer neighbour of a, so parent a = some b
      left
      have har : a ≠ r := by
        rintro rfl
        simp only [SimpleGraph.dist_self] at hgt
        exact Nat.not_lt_zero _ hgt
      have hqual : T.Adj a b ∧ T.dist b r < T.dist a r := ⟨hab, hgt⟩
      have := hpar_uniq a har b hqual
      simp [har, this]

/-- **Single-regular-pair tree embedding.**

Let `(s, t)` be an `ε`-uniform pair in `G` (`0 < ε ≤ 1`, both sides nonempty),
with density `d = G.edgeDensity s t`.  If `T` is a finite tree with
`|T| + ε·|c| ≤ (d-ε)·|c|` for both sides `c ∈ {s,t}`, then `T ⊑ G`. -/
theorem tree_embeds_in_regularPair
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {s t : Finset V}
    (hs : s.Nonempty) (ht : t.Nonempty)
    (huni : G.IsUniform ε s t)
    {α : Type*} [Fintype α] [DecidableEq α] (T : SimpleGraph α) [DecidableRel T.Adj]
    (hT : T.IsTree)
    (hcapS : (Fintype.card α : ℝ) + ε * (s.card : ℝ)
        ≤ ((G.edgeDensity s t : ℝ) - ε) * (s.card : ℝ))
    (hcapT : (Fintype.card α : ℝ) + ε * (t.card : ℝ)
        ≤ ((G.edgeDensity s t : ℝ) - ε) * (t.card : ℝ)) :
    T ⊑ G := by
  obtain ⟨parent, rank, col, hrank, hcol, hedge⟩ :=
    Erdos550.IsTree.exists_rooted_structure T hT
  obtain ⟨f, hfinj, hfside, hfadj⟩ :=
    regularPair_forest_embedding G hε0 hε1 hs ht huni parent rank hrank col hcol hcapS hcapT
  refine ⟨SimpleGraph.Hom.toCopy ⟨f, ?_⟩ hfinj⟩
  intro a b hab
  rcases hedge a b hab with h | h
  · exact hfadj a b h
  · exact (hfadj b a h).symm

end Erdos550
