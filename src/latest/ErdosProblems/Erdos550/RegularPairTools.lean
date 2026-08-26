import Mathlib
import ErdosProblems.Erdos550.TreeEmbedding

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Elementary tree and regular-pair tools

This module collects the elementary tree-counting and regular-pair lemmas used
by the direct off--Turán embedding:

* `tree_high_degree_card_mul_le` — a tree on `n` vertices has few high-degree
  vertices (`k · |{v : deg v ≥ k}| ≤ 2(n-1)`), the degree-budget fact underlying
  the "distribute the tree's few big vertices across the regular partition" step.
* `IsTree.colorable_two` — every tree is bipartite.
* `isUniform_few_low_degree` — in an `ε`-uniform (regular) pair of edge density
  `d`, all but `< ε·|s|` vertices of `s` have at least `(d-ε)·|t|` neighbours in
  `t`.  This "most vertices of a regular pair have large forward degree" fact is
  the local engine of the greedy tree embedding into a regular pair.
* `isUniform_few_low_degree_subset` — the *candidate-set* form of the previous
  lemma: the forward-degree bound holds into any large subset `t' ⊆ t`
  (`ε·|t| ≤ |t'|`).  This is what keeps the greedy embedding going after several
  vertices have already consumed part of a cluster.
* `isUniform_exists_fresh_neighbor` — the concrete extension step derived from it:
  if the "used" set `U` is small (`|U| < (d-ε)·|t'|`), then all but `< ε·|s|`
  vertices of `s` have a neighbour in `t' \ U`, i.e. the next tree vertex can be
  placed on a fresh image.
-/

open SimpleGraph Finset

namespace Erdos550

/-
**Degree budget of a tree.**  In a finite tree `T` on `V`, for every `k` the
number of vertices of degree at least `k`, multiplied by `k`, is at most twice the
number of edges, i.e. `2·(|V| - 1)`.  (Sum of degrees `= 2·e(T) = 2(|V|-1)`.)
-/
lemma tree_high_degree_card_mul_le
    {V : Type*} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree) (k : ℕ) :
    k * ((univ.filter (fun v => k ≤ T.degree v)).card) ≤ 2 * (Fintype.card V - 1) := by
  -- By the properties of the degree sum formula, we have $\sum_{v \in V} \deg(v) = 2 \cdot |E|$.
  have h_sum_deg : ∑ v : V, T.degree v = 2 * T.edgeFinset.card := by
    rw [ SimpleGraph.sum_degrees_eq_twice_card_edges ];
  have h_sum_deg_filter : ∑ v ∈ Finset.filter (fun v => k ≤ T.degree v) Finset.univ, T.degree v ≥ k * (Finset.filter (fun v => k ≤ T.degree v) Finset.univ).card := by
    exact le_trans ( by simp +decide [ mul_comm ] ) ( Finset.sum_le_sum fun v hv => Finset.mem_filter.mp hv |>.2 );
  refine' le_trans h_sum_deg_filter ( le_trans ( Finset.sum_le_sum_of_subset ( Finset.filter_subset _ _ ) ) _ );
  have := hT.card_edgeFinset;
  grind

/-
**Trees are bipartite.**  Every finite tree is `2`-colourable.
-/
lemma IsTree.colorable_two
    {V : Type*} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree) : T.Colorable 2 := by
  convert! hT.2.isBipartite

/-
**Regular pairs have few low-forward-degree vertices.**

If the pair of finsets `(s, t)` is `ε`-uniform (`ε`-regular) in `G` with
`0 < ε ≤ 1`, then the number of vertices `a ∈ s` whose number of neighbours in
`t` is strictly less than `((G.edgeDensity s t) - ε)·|t|` is strictly less than
`ε·|s|`.

This is the standard "most vertices of a regular pair see a `(d-ε)`-fraction of
the other side" lemma: it lets a greedy tree-embedding across a regular pair
always find fresh neighbours for the next tree vertex.
-/
lemma isUniform_few_low_degree
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {s t : Finset V}
    (hs : s.Nonempty) (ht : t.Nonempty) (huni : G.IsUniform ε s t) :
    ((s.filter (fun a => ((t.filter (fun b => G.Adj a b)).card : ℝ)
        < ((G.edgeDensity s t : ℝ) - ε) * (t.card : ℝ))).card : ℝ) < ε * (s.card : ℝ) := by
  by_contra h_contra;
  -- Let $s'$ be the set of vertices in $s$ with low forward degree in $t$.
  set s' := s.filter (fun a => (t.filter (G.Adj a)).card < ((G.edgeDensity s t : ℝ) - ε) * t.card) with hs';
  -- By the uniformity condition, we have $|(G.edgeDensity s' t : ℝ) - (G.edgeDensity s t : ℝ)| < ε$.
  have h_uniform : |(G.edgeDensity s' t : ℝ) - (G.edgeDensity s t : ℝ)| < ε := by
    apply huni;
    · exact Finset.filter_subset _ _;
    · exact Finset.Subset.refl _;
    · exact le_of_not_gt (by simpa only [mul_comm] using h_contra);
    · exact mul_le_of_le_one_right ( Nat.cast_nonneg _ ) hε1;
  -- By the definition of $s'$, we have $\sum_{a \in s'} \text{deg}(a, t) < \sum_{a \in s'} ((G.edgeDensity s t : ℝ) - ε) * t.card$.
  have h_sum_deg : ∑ a ∈ s', (t.filter (G.Adj a)).card < ∑ a ∈ s', ((G.edgeDensity s t : ℝ) - ε) * t.card := by
    rw [ Nat.cast_sum ];
    refine' Finset.sum_lt_sum _ _;
    · exact fun x hx => le_of_lt ( Finset.mem_filter.mp hx |>.2 );
    · exact Exists.elim ( Finset.card_pos.mp ( Nat.cast_pos.mp ( lt_of_lt_of_le ( mul_pos hε0 ( Nat.cast_pos.mpr hs.card_pos ) ) ( le_of_not_gt h_contra ) ) ) ) fun x hx => ⟨ x, hx, Finset.mem_filter.mp hx |>.2 ⟩;
  -- By the definition of $s'$, we have $\sum_{a \in s'} \text{deg}(a, t) = \text{edgeDensity}(s', t) \cdot |s'| \cdot |t|$.
  have h_sum_deg_eq : ∑ a ∈ s', (t.filter (G.Adj a)).card = (G.edgeDensity s' t : ℝ) * s'.card * t.card := by
    simp +decide [ SimpleGraph.edgeDensity, mul_assoc ];
    simp +decide [ Rel.edgeDensity, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ];
    by_cases hs' : s' = ∅ <;> simp_all +decide [ Rel.interedges ];
    · simp_all +decide [ Finset.ext_iff ];
      exact absurd h_contra ( by rw [ Finset.filter_eq_empty_iff.mpr fun x hx => not_lt_of_ge ( by solve_by_elim ) ] ; norm_num; nlinarith [ show ( s.card : ℝ ) ≥ 1 by exact_mod_cast Finset.card_pos.mpr hs ] );
    · rw [ ← mul_assoc, mul_inv_cancel₀ ( Nat.cast_ne_zero.mpr ht.card_pos.ne' ), one_mul ];
      rw [ Finset.card_filter ];
      rw [ Finset.sum_product ] ; aesop;
  simp_all +decide [ mul_assoc, mul_comm ];
  nlinarith [ abs_lt.mp h_uniform, show ( 0 : ℝ ) < ε * s.card by exact mul_pos hε0 ( Nat.cast_pos.mpr hs.card_pos ) ]

/-
**Regular pairs have few low-forward-degree vertices, relative to a large subset.**

This is the *candidate-set* generalization of `isUniform_few_low_degree`: if
`(s, t)` is `ε`-uniform in `G` (`0 < ε ≤ 1`) and `t' ⊆ t` is *large*, i.e.
`ε·|t| ≤ |t'|`, then the number of vertices `a ∈ s` whose number of neighbours
in the subset `t'` is strictly less than `((G.edgeDensity s t) - ε)·|t'|` is
strictly less than `ε·|s|`.

Taking `t' = t` recovers `isUniform_few_low_degree`.  This relative form is the
engine of the greedy tree embedding across a regular pair: after several tree
vertices have been placed, the surviving candidate set `t'` is still a
`(≥ ε)`-fraction of `t`, so almost every vertex of `s` still sees a
`(d-ε)`-fraction of `t'`, and the embedding can be extended.
-/
lemma isUniform_few_low_degree_subset
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε : ℝ} (hε0 : 0 < ε) (_hε1 : ε ≤ 1) {s t t' : Finset V}
    (ht' : t' ⊆ t) (hs : s.Nonempty)
    (ht'card : ε * (t.card : ℝ) ≤ (t'.card : ℝ))
    (huni : G.IsUniform ε s t) :
    ((s.filter (fun a => ((t'.filter (fun b => G.Adj a b)).card : ℝ)
        < ((G.edgeDensity s t : ℝ) - ε) * (t'.card : ℝ))).card : ℝ) < ε * (s.card : ℝ) := by
  by_contra h;
  obtain ⟨s', hs'⟩ : ∃ s' : Finset V, s' ⊆ s ∧ s'.card ≥ ε * s.card ∧ ∀ a ∈ s', (t'.filter (G.Adj a)).card < (G.edgeDensity s t - ε) * t'.card := by
    exact ⟨ _, Finset.filter_subset _ _, le_of_not_gt h, fun a ha => Finset.mem_filter.mp ha |>.2 ⟩;
  have h_sum : (∑ a ∈ s', (t'.filter (G.Adj a)).card : ℝ) = G.edgeDensity s' t' * s'.card * t'.card := by
    simp +decide [ SimpleGraph.edgeDensity, Rel.edgeDensity, Rel.interedges ];
    by_cases hs' : s' = ∅ <;> by_cases ht' : t' = ∅ <;> simp_all +decide [ mul_assoc ];
    rw_mod_cast [ Finset.card_filter ];
    rw [ Finset.sum_product ] ; aesop;
  have h_sum_lt : (∑ a ∈ s', (t'.filter (G.Adj a)).card : ℝ) < (G.edgeDensity s t - ε) * s'.card * t'.card := by
    convert! Finset.sum_lt_sum_of_nonempty _ fun x hx => hs'.2.2 x hx;
    · simp +decide [ mul_comm, mul_left_comm ];
    · exact Finset.card_pos.mp ( Nat.cast_pos.mp ( lt_of_lt_of_le ( mul_pos hε0 ( Nat.cast_pos.mpr hs.card_pos ) ) hs'.2.1 ) );
  have := huni hs'.1 ht' ( by linarith ) ( by linarith );
  nlinarith [ abs_lt.mp this, show ( 0 : ℝ ) ≤ #s' * #t' by positivity ]

/-
**Regular-pair extension step: almost every vertex has a fresh neighbour.**

Suppose `(s, t)` is `ε`-uniform in `G` (`0 < ε ≤ 1`), `t' ⊆ t` is large
(`ε·|t| ≤ |t'|`), and a "used" set `U` is small in the sense that
`|U| < ((G.edgeDensity s t) - ε)·|t'|`.  Then all but `< ε·|s|` vertices `a ∈ s`
have a neighbour `b ∈ t'` outside `U`.

This is the concrete extension engine of the greedy tree embedding: it is exactly
the step "the next tree vertex, mapped to `s`, still finds an unused image in the
candidate set `t'`".  It follows from `isUniform_few_low_degree_subset`, because a
vertex all of whose `t'`-neighbours lie in `U` has fewer than `(d-ε)·|t'|`
neighbours in `t'`.
-/
lemma isUniform_exists_fresh_neighbor
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {s t t' U : Finset V}
    (ht' : t' ⊆ t) (hs : s.Nonempty)
    (ht'card : ε * (t.card : ℝ) ≤ (t'.card : ℝ))
    (hU : (U.card : ℝ) < ((G.edgeDensity s t : ℝ) - ε) * (t'.card : ℝ))
    (huni : G.IsUniform ε s t) :
    ((s.filter (fun a => ¬ ∃ b ∈ t', G.Adj a b ∧ b ∉ U)).card : ℝ)
      < ε * (s.card : ℝ) := by
  refine lt_of_le_of_lt ?_ (isUniform_few_low_degree_subset G hε0 hε1 ht' hs ht'card huni)
  refine Nat.cast_le.mpr (Finset.card_le_card ?_)
  intro a ha
  rw [Finset.mem_filter] at ha ⊢
  obtain ⟨has, hane⟩ := ha
  refine ⟨has, ?_⟩
  -- every `t'`-neighbour of `a` lies in `U`, so `N(a) ∩ t' ⊆ U ∩ t'`
  push_neg at hane
  have hsub : (t'.filter (fun b => G.Adj a b)) ⊆ (U ∩ t') := by
    intro b hb
    rw [Finset.mem_filter] at hb
    rw [Finset.mem_inter]
    exact ⟨hane b hb.1 hb.2, hb.1⟩
  have h1 : ((t'.filter (fun b => G.Adj a b)).card : ℝ) ≤ ((U ∩ t').card : ℝ) :=
    Nat.cast_le.mpr (Finset.card_le_card hsub)
  have h2 : ((U ∩ t').card : ℝ) ≤ (U.card : ℝ) :=
    Nat.cast_le.mpr (Finset.card_le_card (Finset.inter_subset_left))
  calc ((t'.filter (fun b => G.Adj a b)).card : ℝ) ≤ (U.card : ℝ) := le_trans h1 h2
    _ < ((G.edgeDensity s t : ℝ) - ε) * (t'.card : ℝ) := hU

/-
**Regular-pair extension to a *good* fresh neighbour.**

This strengthens `isUniform_exists_fresh_neighbor` so that the freshly-chosen
image is itself a "good" vertex of the opposite side, which is exactly what a
*backward* greedy tree embedding across a single regular pair needs: every image
must in turn have large forward degree so that *its* children can later be placed.

Suppose `(s, t)` is `ε`-uniform in `G` (`0 < ε ≤ 1`) with both sides nonempty,
`p ∈ s` is good (has `≥ (d-ε)·|t|` neighbours in `t`, where `d = edgeDensity s t`),
and the used set `U` is small: `|U| + ε·|t| < (d-ε)·|t|`.  Then there is a vertex
`w ∈ t` with `G.Adj p w`, `w ∉ U`, and `w` itself good on the `s`-side
(`≥ (d-ε)·|s|` neighbours in `s`).

The good vertices of `t` (on the `s`-side) are all but `< ε·|t|` of `t` by
`isUniform_few_low_degree` applied to the symmetric pair `(t, s)`; intersecting
the `≥ (d-ε)·|t|` neighbours of `p` with the good set and removing `U` leaves a
nonempty choice.
-/
lemma isUniform_good_fresh_neighbor
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {s t : Finset V}
    (hs : s.Nonempty) (ht : t.Nonempty)
    (huni : G.IsUniform ε s t)
    {p : V}
    (hpdeg : ((G.edgeDensity s t : ℝ) - ε) * (t.card : ℝ)
        ≤ ((t.filter (fun b => G.Adj p b)).card : ℝ))
    {U : Finset V}
    (hU : (U.card : ℝ) + ε * (t.card : ℝ)
        < ((G.edgeDensity s t : ℝ) - ε) * (t.card : ℝ)) :
    ∃ w ∈ t, G.Adj p w ∧ w ∉ U ∧
      ((G.edgeDensity s t : ℝ) - ε) * (s.card : ℝ)
        ≤ ((s.filter (fun a => G.Adj w a)).card : ℝ) := by
  contrapose! hU;
  refine' le_trans hpdeg ( le_trans ( Nat.cast_le.mpr <| Finset.card_le_card _ ) _ );
  exact U ∪ t.filter ( fun w => w ∉ U ∧ ( s.filter ( fun a => G.Adj w a ) ).card < ( G.edgeDensity s t - ε ) * s.card );
  · grind;
  · refine' le_trans ( Nat.cast_le.mpr ( Finset.card_union_le _ _ ) ) _;
    simp;
    refine' le_trans _ ( le_of_lt ( isUniform_few_low_degree G hε0 hε1 ht hs huni.symm ) );
    rw [ SimpleGraph.edgeDensity_comm ];
    exact_mod_cast Finset.card_mono fun x hx => by aesop;

/-
**A good, unused vertex of a regular side exists.**

If `(s, t)` is `ε`-uniform in `G` (`0 < ε ≤ 1`, both sides nonempty) and the used
set `U` is small (`|U| + ε·|s| < |s|`), then some `w ∈ s` avoids `U` and is good
on the `t`-side (`≥ (d-ε)·|t|` neighbours in `t`, `d = edgeDensity s t`).  This is
the *root-placement* step of the single-pair tree embedding: the root has no
parent, so we only need a fresh image that is good enough to host its children.
-/
lemma isUniform_exists_good_unused
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {s t : Finset V}
    (hs : s.Nonempty) (ht : t.Nonempty)
    (huni : G.IsUniform ε s t)
    {U : Finset V}
    (hU : (U.card : ℝ) + ε * (s.card : ℝ) < (s.card : ℝ)) :
    ∃ w ∈ s, w ∉ U ∧
      ((G.edgeDensity s t : ℝ) - ε) * (t.card : ℝ)
        ≤ ((t.filter (fun b => G.Adj w b)).card : ℝ) := by
  contrapose! hU;
  have h_card : (s.filter (fun a => ((t.filter (fun b => G.Adj a b)).card : ℝ) < ((G.edgeDensity s t : ℝ) - ε) * (t.card : ℝ))).card ≥ (s \ U).card := by
    exact Finset.card_le_card fun x hx => by aesop;
  have := isUniform_few_low_degree G hε0 hε1 hs ht huni;
  simp_all +decide [ Finset.card_sdiff ];
  exact le_trans ( Nat.cast_le.mpr h_card ) ( by push_cast; nlinarith [ show ( # ( U ∩ s ) : ℝ ) ≤ #U by exact_mod_cast Finset.card_le_card fun x hx => by aesop ] )

/-
**Mirror of `isUniform_good_fresh_neighbor`** with the roles of `s` and `t`
swapped: the already-placed good vertex `p` lies in `t`, and the fresh good
neighbour `w` is produced in `s`.  (Immediate from the original via `huni.symm`
and `SimpleGraph.edgeDensity_comm`.)
-/
lemma isUniform_good_fresh_neighbor_right
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {s t : Finset V}
    (hs : s.Nonempty) (ht : t.Nonempty)
    (huni : G.IsUniform ε s t)
    {p : V}
    (hpdeg : ((G.edgeDensity s t : ℝ) - ε) * (s.card : ℝ)
        ≤ ((s.filter (fun b => G.Adj p b)).card : ℝ))
    {U : Finset V}
    (hU : (U.card : ℝ) + ε * (s.card : ℝ)
        < ((G.edgeDensity s t : ℝ) - ε) * (s.card : ℝ)) :
    ∃ w ∈ s, G.Adj p w ∧ w ∉ U ∧
      ((G.edgeDensity s t : ℝ) - ε) * (t.card : ℝ)
        ≤ ((t.filter (fun a => G.Adj w a)).card : ℝ) := by
  have hcomm : (G.edgeDensity t s : ℝ) = (G.edgeDensity s t : ℝ) := by
    rw [SimpleGraph.edgeDensity_comm]
  have := isUniform_good_fresh_neighbor G hε0 hε1 ht hs huni.symm (p := p)
    (by rw [hcomm]; exact hpdeg) (U := U) (by rw [hcomm]; exact hU)
  simpa [hcomm] using! this

/-
**Mirror of `isUniform_exists_good_unused`** with the roles of `s` and `t`
swapped: a good, unused vertex is produced in `t` (good on the `s`-side).
-/
lemma isUniform_exists_good_unused_right
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {s t : Finset V}
    (hs : s.Nonempty) (ht : t.Nonempty)
    (huni : G.IsUniform ε s t)
    {U : Finset V}
    (hU : (U.card : ℝ) + ε * (t.card : ℝ) < (t.card : ℝ)) :
    ∃ w ∈ t, w ∉ U ∧
      ((G.edgeDensity s t : ℝ) - ε) * (s.card : ℝ)
        ≤ ((s.filter (fun b => G.Adj w b)).card : ℝ) := by
  have hcomm : (G.edgeDensity t s : ℝ) = (G.edgeDensity s t : ℝ) := by
    rw [SimpleGraph.edgeDensity_comm]
  have := isUniform_exists_good_unused G hε0 hε1 ht hs huni.symm (U := U) hU
  simpa [hcomm] using! this

end Erdos550
