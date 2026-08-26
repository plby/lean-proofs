import Mathlib

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Tree centroid

A finite tree on `n` vertices has a *centroid*: a vertex `z` such that every
"branch" of `T` hanging off `z` (the set of vertices closer to a neighbour `w`
of `z` than to `z` itself) contains at most `n/2` vertices.

This is the classical input to the profile lemma of *A Resolution of Erdős
Problem 550* (E. Li): it lets one apply the count-and-load allocation lemma to
the components of `T - z`, whose sizes are each `≤ n/2`.

We use a distance-based description of branches to avoid `ComponentCompl`
fintype bookkeeping.
-/

open SimpleGraph Finset

namespace Erdos550

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- The branch of `z` towards `w`: the vertices strictly closer to `w` than to
`z`. -/
noncomputable def branch (z w : V) : Finset V :=
  Finset.univ.filter (fun v => G.dist v w < G.dist v z)

/-- The number of vertices in the branch of `z` towards `w`. -/
noncomputable def branchSize (z w : V) : ℕ := (branch G z w).card

variable {G}

/-
For an edge `z ~ w` of a tree, the two branches `branch z w` and
`branch w z` partition the vertex set, so their sizes add up to `n`.
-/
theorem branchSize_add (hG : G.IsTree) {z w : V} (h : G.Adj z w) :
    branchSize G z w + branchSize G w z = Fintype.card V := by
  unfold branchSize branch;
  rw [ ← Finset.card_union_of_disjoint, Finset.filter_union_right ];
  · rw [ Finset.filter_true_of_mem ];
    · rfl;
    · have := hG.dist_ne_of_adj;
      exact fun x _ => lt_or_gt_of_ne ( this x h.symm );
  · exact Finset.disjoint_filter.mpr fun _ _ _ _ => lt_asymm ‹_› ‹_›

/-
Branch nesting: if `z ~ w` and `u` is a neighbour of `w` other than `z`,
then the branch of `w` towards `u` is contained in the branch of `z` towards
`w`; moreover `w` itself lies in the latter but not the former, so the inclusion
is strict.
-/
theorem branch_ssubset (hG : G.IsTree) {z w u : V} (hzw : G.Adj z w)
    (hwu : G.Adj w u) (huz : u ≠ z) :
    branch G w u ⊂ branch G z w := by
  have h_dist_eq : ∀ x : V, x ∈ branch G w u → x ∈ branch G z w := by
    intro x hx; by_contra h_contra; simp_all +decide [ branch ] ;
    have h_dist_eq : G.dist x w = G.dist x z + 1 := by
      grind +suggestions;
    have h_dist_eq : G.dist x u = G.dist x z := by
      have h_dist_eq : ∀ {v w : V}, G.Adj v w → ∀ x : V, G.dist x v = G.dist x w + 1 ∨ G.dist x w = G.dist x v + 1 := by
        intros v w hvw x; exact (by
        have := hG.dist_eq_dist_add_one_of_adj x hvw; aesop;);
      grind;
    have h_unique_path : ∀ (p q : G.Walk x w), p.length = G.dist x w → q.length = G.dist x w → p = q := by
      have := hG.existsUnique_path x w;
      obtain ⟨ p, hp₁, hp₂ ⟩ := this;
      intro p q hp hq; have := hp₂ p ( SimpleGraph.Walk.isPath_of_length_eq_dist p hp ) ;
      have := hp₂ q ( SimpleGraph.Walk.isPath_of_length_eq_dist q hq ) ; aesop;
    obtain ⟨p, hp⟩ : ∃ p : G.Walk x z, p.length = G.dist x z := by
      have := hG.1 x z;
      exact SimpleGraph.Reachable.exists_walk_length_eq_dist this
    obtain ⟨q, hq⟩ : ∃ q : G.Walk x u, q.length = G.dist x u := by
      have := hG.1 x u;
      exact SimpleGraph.Reachable.exists_walk_length_eq_dist this
    have := h_unique_path ( p.append ( SimpleGraph.Walk.cons hzw SimpleGraph.Walk.nil ) ) ( q.append ( SimpleGraph.Walk.cons hwu.symm SimpleGraph.Walk.nil ) ) ?_ ?_ <;> simp_all +decide [ SimpleGraph.Walk.length_append ];
    replace this := congr_arg ( fun p => p.getVert ( p.length - 1 ) ) this ; simp_all +decide [ SimpleGraph.Walk.getVert_append ];
  refine' ⟨ h_dist_eq, _ ⟩;
  intro h; have := @h w; simp_all +decide [ branch ] ;
  exact this.elim ( fun h => huz ( by simp_all +decide ) ) fun h => h ( hzw.symm.reachable )

/-
The branches hanging off `z` (one per neighbour) partition `V \ {z}`, so
their sizes sum to `n - 1`.
-/
theorem branchSize_sum_neighbors [DecidableRel G.Adj] (hG : G.IsTree) (z : V) :
    ∑ w ∈ G.neighborFinset z, branchSize G z w = Fintype.card V - 1 := by
  -- By definition of `branch`, we know that every vertex `v ≠ z` is in exactly one of the `branch G z w` sets for `w ∈ G.neighborFinset z`.
  have h_disjoint : ∀ v ∈ Finset.univ.erase z, ∃! w ∈ G.neighborFinset z, v ∈ branch G z w := by
    intro v hv
    obtain ⟨p, hp⟩ : ∃ p : G.Walk z v, p.length = G.dist z v := by
      have := hG.1;
      exact SimpleGraph.Connected.exists_walk_length_eq_dist this z v
    have h_walk : p.IsPath := by
      exact SimpleGraph.Walk.isPath_of_length_eq_dist p hp
    have h_first_edge : ∃ w ∈ G.neighborFinset z, p.getVert 1 = w := by
      cases p <;> aesop
    obtain ⟨w, hw⟩ := h_first_edge
    have h_branch : v ∈ branch G z w := by
      have h_dist : G.dist v w ≤ G.dist v z - 1 := by
        have h_dist : G.dist v w ≤ (p.tail).length := by
          have h_dist : ∃ q : G.Walk w v, q.length = p.tail.length := by
            cases p <;> aesop;
          obtain ⟨ q, hq ⟩ := h_dist;
          rw [ ← hq, SimpleGraph.dist_comm ];
          exact SimpleGraph.dist_le q;
        cases p <;> simp_all +decide [ SimpleGraph.dist_comm ];
        exact Nat.le_sub_one_of_lt ( lt_of_le_of_lt h_dist ( by linarith ) );
      refine' Finset.mem_filter.mpr ⟨ Finset.mem_univ _, lt_of_le_of_lt h_dist ( Nat.sub_lt _ _ ) ⟩ <;> simp_all +decide [ SimpleGraph.dist_comm ];
      grind +suggestions
    have h_unique : ∀ w' ∈ G.neighborFinset z, v ∈ branch G z w' → w' = w := by
      intro w' hw' hv'
      have h_walk' : ∃ p' : G.Walk z v, p'.length = G.dist z v ∧ p'.getVert 1 = w' := by
        have h_walk' : ∃ p' : G.Walk w' v, p'.length = G.dist w' v := by
          have := hG.1 w' v;
          exact SimpleGraph.Reachable.exists_walk_length_eq_dist this;
        obtain ⟨ p', hp' ⟩ := h_walk'
        use SimpleGraph.Walk.cons (by
        aesop) p'
        generalize_proofs at *;
        simp_all +decide [ branch ];
        grind +suggestions;
      have h_unique : ∀ p p' : G.Walk z v, p.length = G.dist z v → p'.length = G.dist z v → p.IsPath → p'.IsPath → p = p' := by
        have := hG.existsUnique_path z v;
        exact fun p p' hp hp' hp'' hp''' => this.unique hp'' hp''';
      grind +suggestions
    use w, by
      exact ⟨ hw.1, h_branch ⟩;
    exact fun y hy => h_unique y hy.1 hy.2;
  -- By definition of `branchSize`, we know that $\sum_{w \in G.neighborFinset z} \text{branchSize}(G, z, w)$ counts the number of vertices in $V \setminus \{z\}$.
  have h_card : ∑ w ∈ G.neighborFinset z, (branch G z w).card = ∑ v ∈ Finset.univ.erase z, 1 := by
    have h_card : ∑ w ∈ G.neighborFinset z, (branch G z w).card = ∑ v ∈ Finset.univ.erase z, ∑ w ∈ G.neighborFinset z, (if v ∈ branch G z w then 1 else 0) := by
      rw [ Finset.sum_comm, Finset.sum_congr rfl ];
      intro w hw; rw [ Finset.card_eq_sum_ones ] ; rw [ ← Finset.sum_filter ] ; congr; ext; simp +decide [ branch ] ;
      grind;
    rw [ h_card, Finset.sum_congr rfl ];
    intro v hv; obtain ⟨ w, hw₁, hw₂ ⟩ := h_disjoint v hv; rw [ Finset.sum_eq_single w ] <;> aesop;
  aesop

/-
**Tree centroid.**  Every finite tree on a nonempty vertex set has a vertex
`z` such that every branch hanging off `z` has at most `n/2` vertices
(equivalently `2 · branchSize ≤ n`).
-/
theorem tree_centroid (hG : G.IsTree) [Nonempty V] :
    ∃ z : V, ∀ w : V, G.Adj z w → 2 * branchSize G z w ≤ Fintype.card V := by
  by_contra h_contra;
  -- By definition of $M$, we know that for every $z$, there exists a neighbor $w$ such that $branchSize G z w > Fintype.card V / 2$.
  have hM : ∀ z : V, ∃ w : V, G.Adj z w ∧ branchSize G z w > Fintype.card V / 2 := by
    exact fun z => by push_neg at h_contra; exact h_contra z |> fun ⟨ w, hw₁, hw₂ ⟩ => ⟨ w, hw₁, by omega ⟩ ;
  -- Let $z$ be a vertex that minimizes $M(z)$.
  obtain ⟨z, hz⟩ : ∃ z : V, ∀ w : V, branchSize G w (Classical.choose (hM w)) ≥ branchSize G z (Classical.choose (hM z)) := by
    simpa using! Finset.exists_min_image Finset.univ ( fun z => branchSize G z ( Classical.choose ( hM z ) ) ) ⟨ Classical.arbitrary V, Finset.mem_univ _ ⟩;
  -- By definition of $M$, we know that $branchSize G (Classical.choose (hM z)) (Classical.choose (hM (Classical.choose (hM z)))) < branchSize G z (Classical.choose (hM z))$.
  have h_branchSize_choose_choose_z : branchSize G (Classical.choose (hM z)) (Classical.choose (hM (Classical.choose (hM z)))) < branchSize G z (Classical.choose (hM z)) := by
    have h_branchSize_choose_choose_z : ∀ u : V, G.Adj (Classical.choose (hM z)) u → u ≠ z → branchSize G (Classical.choose (hM z)) u < branchSize G z (Classical.choose (hM z)) := by
      intros u hu huz
      have h_branchSize_choose_choose_z : branch G (Classical.choose (hM z)) u ⊂ branch G z (Classical.choose (hM z)) := by
        apply branch_ssubset hG (Classical.choose_spec (hM z)).left hu huz;
      exact Finset.card_lt_card h_branchSize_choose_choose_z;
    grind +suggestions;
  linarith [ hz ( Classical.choose ( hM z ) ) ]

end Erdos550
