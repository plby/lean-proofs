import Mathlib
import ErdosProblems.Erdos550.RemovalLemma

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Erdős–Simonovits stability (Proposition `prop:stability`)

The clean reservoir decomposition uses the **Erdős–Simonovits stability
theorem**.  This module derives the required finitary form from clique removal
and Füredi's clique-stability argument.

We state the theorem here in the finitary form used by the paper and isolate
the genuinely elementary algebraic input it is combined with downstream:
the **Turán variance identity**

  `∑_{i<j} s_i s_j = (N² − ∑_i s_i²)/2`   (with `N = ∑_i s_i`),

which converts "almost `t_q(N)` crossing pairs" into "almost balanced part
sizes".

`turanEdges q N` denotes the number of edges of the balanced complete
`q`-partite Turán graph on `N` vertices, i.e. `t_q(N)`.
-/

open SimpleGraph Finset

namespace Erdos550

/-- `t_q(N)` — the number of edges of the balanced `q`-partite Turán graph on
`N` vertices. -/
noncomputable def turanEdges (q N : ℕ) : ℕ := (turanGraph N q).edgeFinset.card

/-
**Turán variance identity (combinatorial core of stability rounding).**
For nonnegative reals `s i` with total `N = ∑ i, s i`,
`2 * ∑_{i<j} s i * s j = N^2 - ∑ i, (s i)^2`. Equivalently the crossing-pair
count is maximised exactly at the balanced sizes.
-/
theorem sum_pairs_identity {q : ℕ} (s : Fin q → ℝ) :
    2 * ∑ p ∈ Finset.univ.filter (fun p : Fin q × Fin q => p.1 < p.2), s p.1 * s p.2
      = (∑ i, s i) ^ 2 - ∑ i, (s i) ^ 2 := by
  induction' q with q ih <;> simp +decide [ Fin.sum_univ_succ, * ];
  convert! congr_arg ( fun x : ℝ => x + 2 * s 0 * ∑ i : Fin q, s ( Fin.succ i ) ) ( ih fun i => s ( Fin.succ i ) ) using 1 <;> ring_nf;
  simp +decide [ Finset.sum_filter, Finset.mul_sum _ _ _ ];
  erw [ Finset.sum_product, Finset.sum_product ] ; norm_num [ Fin.sum_univ_succ ] ; ring;

/-
**Deviation form of the Turán identity.** Writing `N = ∑ s i`, the crossing
pair-product `P = ∑_{i<j} s_i s_j` satisfies
`(N^2)·(q-1)/q − P` controls `∑_i (s_i − N/q)^2`:
`2P = N^2 − ∑ s_i^2` and `∑ (s_i − N/q)^2 = ∑ s_i^2 − N^2/q`, so
`N^2 (q-1)/(2q) − P = ½ ∑_i (s_i − N/q)^2`.
-/
theorem deviation_identity {q : ℕ} (hq : 0 < q) (s : Fin q → ℝ) :
    let N := ∑ i, s i
    (N ^ 2 * (q - 1) / q) / 2
      - ∑ p ∈ Finset.univ.filter (fun p : Fin q × Fin q => p.1 < p.2), s p.1 * s p.2
      = (∑ i, (s i - N / q) ^ 2) / 2 := by
  have := sum_pairs_identity s; norm_num [ sub_sq, Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul ] at this ⊢; ring_nf at this ⊢;
  norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, hq.ne' ] at *;
  grind

/-
**Turán-number partite step inequality.**

For `q ≥ 1` and `d ≤ N`, attaching an independent set of `N − d` vertices
completely to a `q`-partite Turán graph on `d` vertices yields a `(q+1)`-partite
graph, whence `t_q(d) + d·(N−d) ≤ t_{q+1}(N)`.  Proved by exhibiting the
`(q+1)`-partite witness and invoking Turán's bound.
-/
set_option maxHeartbeats 1600000 in
theorem turanEdges_partite_step (q d N : ℕ) (hq : 1 ≤ q) (hd : d ≤ N) :
    turanEdges q d + d * (N - d) ≤ turanEdges (q + 1) N := by
  -- Let `G := SimpleGraph.comap part (⊤ : SimpleGraph (Fin (q+1)))`, so `G.Adj x y ↔ part x ≠ part y`.
  set G : SimpleGraph (Fin N) := SimpleGraph.comap (fun x => if x.val < d then Fin.castSucc ⟨x.val % q, Nat.mod_lt _ (by omega)⟩ else Fin.last q) (⊤ : SimpleGraph (Fin (q+1)));
  -- The number of non-edges of `G` is `∑_{c : Fin (q+1)} (part⁻¹ c).card.choose 2`.
  have h_non_edges : (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2 ∧ ¬(G.Adj p.1 p.2))).card = ∑ c : Fin (q + 1), (Finset.filter (fun x : Fin N => (if x.val < d then Fin.castSucc ⟨x.val % q, Nat.mod_lt _ (by omega)⟩ else Fin.last q) = c) Finset.univ).card.choose 2 := by
    have h_non_edges : (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2 ∧ ¬(G.Adj p.1 p.2))).card = ∑ c : Fin (q + 1), (Finset.filter (fun p : Fin N × Fin N => p.1 < p.2 ∧ (if p.1.val < d then Fin.castSucc ⟨p.1.val % q, Nat.mod_lt _ (by omega)⟩ else Fin.last q) = c ∧ (if p.2.val < d then Fin.castSucc ⟨p.2.val % q, Nat.mod_lt _ (by omega)⟩ else Fin.last q) = c) Finset.univ).card := by
      rw [ ← Finset.card_biUnion ];
      · congr with p ; aesop;
      · exact fun x _ y _ hxy => Finset.disjoint_left.mpr fun p hp hp' => hxy <| by aesop;
    rw [ h_non_edges ];
    refine' Finset.sum_congr rfl fun c _ => _;
    rw [ ← Finset.card_powersetCard ];
    refine' Finset.card_bij ( fun p hp => { p.1, p.2 } ) _ _ _;
    · grind;
    · simp +contextual [ Finset.Subset.antisymm_iff, Finset.subset_iff ];
      grind;
    · simp +decide only [Fin.castSucc_mk, mem_powersetCard, mem_filter, mem_univ, true_and, exists_prop,
    Prod.exists, and_imp];
      rintro b hb x y hxy rfl; cases lt_or_gt_of_ne hxy <;> [ exact ⟨ x, y, ⟨ ‹_›, by simpa using! hb ( by simp +decide ), by simpa using! hb ( by simp +decide ) ⟩, rfl ⟩ ; exact ⟨ y, x, ⟨ ‹_›, by simpa using! hb ( by simp +decide ), by simpa using! hb ( by simp +decide ) ⟩, by simp +decide [ *, Finset.pair_comm ] ⟩ ] ;
  -- The fibre of `Fin.last q` has size `N - d`; the fibres of `Fin.castSucc i` (`i : Fin q`) partition `[0,d)` by residue mod `q`, matching exactly the colour classes of `turanGraph d q`.
  have h_fibres : ∑ c : Fin (q + 1), (Finset.filter (fun x : Fin N => (if x.val < d then Fin.castSucc ⟨x.val % q, Nat.mod_lt _ (by omega)⟩ else Fin.last q) = c) Finset.univ).card.choose 2 = (N - d).choose 2 + (Finset.univ.filter (fun p : Fin d × Fin d => p.1 < p.2 ∧ ¬(turanGraph d q).Adj p.1 p.2)).card := by
    have h_fibres : ∀ i : Fin q, (Finset.filter (fun x : Fin N => (if x.val < d then Fin.castSucc ⟨x.val % q, Nat.mod_lt _ (by omega)⟩ else Fin.last q) = Fin.castSucc i) Finset.univ).card = (Finset.filter (fun x : Fin d => x.val % q = i.val) Finset.univ).card := by
      intro i;
      refine' Finset.card_bij ( fun x hx => ⟨ x, by
        grind ⟩ ) _ _ _ <;> simp +decide only [mem_filter, mem_univ, true_and, Fin.castSucc_mk];
      · grind;
      · exact fun b hb => ⟨ ⟨ b, by linarith [ Fin.is_lt b ] ⟩, by aesop ⟩;
    have h_fibres_sum : ∑ i : Fin q, (Finset.filter (fun x : Fin d => x.val % q = i.val) Finset.univ).card.choose 2 = (Finset.univ.filter (fun p : Fin d × Fin d => p.1 < p.2 ∧ ¬(turanGraph d q).Adj p.1 p.2)).card := by
      have h_fibres_sum : ∀ i : Fin q, (Finset.filter (fun x : Fin d => x.val % q = i.val) Finset.univ).card.choose 2 = (Finset.univ.filter (fun p : Fin d × Fin d => p.1 < p.2 ∧ p.1.val % q = i.val ∧ p.2.val % q = i.val)).card := by
        intro i
        have h_fibres_sum : (Finset.filter (fun x : Fin d => x.val % q = i.val) Finset.univ).card.choose 2 = (Finset.powersetCard 2 (Finset.filter (fun x : Fin d => x.val % q = i.val) Finset.univ)).card := by
          rw [ Finset.card_powersetCard ];
        convert! h_fibres_sum using 1;
        refine' Finset.card_bij ( fun p hp => { p.1, p.2 } ) _ _ _ <;> simp +decide only [mem_powersetCard, mem_filter, mem_univ, true_and, exists_prop, Prod.exists, and_imp];
        · grind;
        · simp +contextual [ Finset.Subset.antisymm_iff, Finset.subset_iff ];
          grind;
        · intro b hb hb'; rw [ Finset.card_eq_two ] at hb'; obtain ⟨ a, b, hab, rfl ⟩ := hb'; simp_all +decide [ Finset.subset_iff ] ;
          cases lt_or_gt_of_ne hab <;> [ exact ⟨ a, b, ⟨ ‹_›, hb ⟩, rfl ⟩ ; exact ⟨ b, a, ⟨ ‹_›, hb.2, hb.1 ⟩, by rw [ Finset.pair_comm ] ⟩ ];
      simp_all +decide [ turanGraph ];
      rw [ ← Finset.card_biUnion ];
      · congr with p ; simp +decide [  ];
        exact fun _ => ⟨ fun ⟨ x, hx₁, hx₂ ⟩ => hx₁.trans hx₂.symm, fun hx => ⟨ ⟨ p.1 % q, Nat.mod_lt _ hq ⟩, rfl, hx.symm ⟩ ⟩;
      · exact fun i _ j _ hij => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hij <| Fin.ext <| by aesop;
    rw [ ← h_fibres_sum, Fin.sum_univ_castSucc ];
    rw [ add_comm, Finset.sum_congr rfl fun i hi => by rw [ h_fibres i ] ];
    rw [ show ( Finset.univ.filter fun x : Fin N => ( if ( x : ℕ ) < d then Fin.castSucc ⟨ ( x : ℕ ) % q, Nat.mod_lt _ ( by linarith ) ⟩ else Fin.last q ) = Fin.last q ) = Finset.univ \ Finset.univ.filter fun x : Fin N => ( x : ℕ ) < d from ?_ ];
    · simp +decide only [Nat.add_right_cancel_iff];
      rw [ Finset.card_eq_of_bijective ];
      use fun i hi => ⟨ i, by linarith ⟩;
      · exact fun x hx => ⟨ x, Finset.mem_filter.mp hx |>.2, rfl ⟩;
      · grind;
      · grind;
    · grind;
  -- Therefore, the number of edges of `G` is `N.choose 2 - (N - d).choose 2 - (Finset.univ.filter (fun p : Fin d × Fin d => p.1 < p.2 ∧ ¬(turanGraph d q).Adj p.1 p.2)).card`.
  have h_edges_G : G.edgeFinset.card = (N.choose 2) - ((N - d).choose 2 + (Finset.univ.filter (fun p : Fin d × Fin d => p.1 < p.2 ∧ ¬(turanGraph d q).Adj p.1 p.2)).card) := by
    have h_edges_G : G.edgeFinset.card = (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)).card - (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2 ∧ ¬(G.Adj p.1 p.2))).card := by
      rw [ tsub_eq_of_eq_add ];
      have h_edges_G : Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ = Finset.filter (fun p : Fin N × Fin N => p.1 < p.2 ∧ G.Adj p.1 p.2) Finset.univ ∪ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2 ∧ ¬G.Adj p.1 p.2) Finset.univ := by
        grind;
      rw [ h_edges_G, Finset.card_union_of_disjoint ];
      · rw [ show G.edgeFinset = Finset.image ( fun p : Fin N × Fin N => s(p.1, p.2) ) ( Finset.filter ( fun p : Fin N × Fin N => p.1 < p.2 ∧ G.Adj p.1 p.2 ) Finset.univ ) from ?_ ];
        · rw [ Finset.card_image_of_injOn ];
          simp +decide [ Set.InjOn ];
          grind;
        · ext ⟨x, y⟩; simp [G];
          grind;
      · exact Finset.disjoint_filter.mpr ( by aesop );
    rw [ h_edges_G, h_non_edges, h_fibres ];
    rw [ show Finset.filter ( fun p : Fin N × Fin N => p.1 < p.2 ) Finset.univ = Finset.filter ( fun p : Fin N × Fin N => p.1 < p.2 ) Finset.univ from rfl, Finset.card_filter ];
    erw [ Finset.sum_product ] ; norm_num [ Finset.sum_ite, Finset.filter_lt_eq_Ioi ];
    exact congrArg₂ _ ( Nat.recOn N ( by norm_num ) fun n ih => by cases n <;> simp +decide [ Nat.choose, Fin.sum_univ_succ ] at * ; linarith ) rfl;
  -- By definition of `turanEdges`, we know that `turanEdges q d = (d.choose 2) - (Finset.univ.filter (fun p : Fin d × Fin d => p.1 < p.2 ∧ ¬(turanGraph d q).Adj p.1 p.2)).card`.
  have h_turanEdges_d : turanEdges q d = (d.choose 2) - (Finset.univ.filter (fun p : Fin d × Fin d => p.1 < p.2 ∧ ¬(turanGraph d q).Adj p.1 p.2)).card := by
    rw [ Nat.sub_eq_of_eq_add ];
    have h_turanEdges_d : (Finset.univ.filter (fun p : Fin d × Fin d => p.1 < p.2)).card = (turanGraph d q).edgeFinset.card + (Finset.univ.filter (fun p : Fin d × Fin d => p.1 < p.2 ∧ ¬(turanGraph d q).Adj p.1 p.2)).card := by
      rw [ show ( Finset.univ.filter fun p : Fin d × Fin d => p.1 < p.2 ) = ( Finset.univ.filter fun p : Fin d × Fin d => p.1 < p.2 ∧ ( turanGraph d q ).Adj p.1 p.2 ) ∪ ( Finset.univ.filter fun p : Fin d × Fin d => p.1 < p.2 ∧ ¬ ( turanGraph d q ).Adj p.1 p.2 ) from ?_, Finset.card_union_of_disjoint ];
      · refine' congr_arg₂ ( · + · ) _ rfl;
        refine' Finset.card_bij ( fun p hp => s(p.1, p.2) ) _ _ _ <;> simp +decide only [mem_edgeFinset, mem_filter, mem_univ, true_and, exists_prop, Prod.exists];
        · grind;
        · rintro ⟨ a, b ⟩ hab;
          cases lt_trichotomy a b <;> simp_all +decide [  ];
          · exact ⟨ a, b, ⟨ by assumption, hab ⟩, Or.inl ⟨ rfl, rfl ⟩ ⟩;
          · exact ⟨ b, a, ⟨ by aesop, by simpa only [ SimpleGraph.adj_comm ] using! hab ⟩, by aesop ⟩;
      · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by tauto;
      · grind;
    convert! h_turanEdges_d using 1;
    rw [ Nat.choose_two_right ];
    rw [ Finset.card_filter ];
    erw [ Finset.sum_product ] ; norm_num [ Finset.sum_ite, Finset.filter_lt_eq_Ioi ];
    rw [ ← Finset.sum_range_id ];
    rw [ ← Finset.sum_range_reflect, Finset.sum_range ];
  -- Therefore, the number of edges of `G` is `turanEdges q d + d * (N - d)`.
  have h_edges_G_simplified : G.edgeFinset.card = turanEdges q d + d * (N - d) := by
    rw [ h_edges_G, h_turanEdges_d ];
    rw [ show N.choose 2 = d.choose 2 + ( N - d ).choose 2 + d * ( N - d ) from ?_ ];
    · rw [ tsub_eq_of_eq_add ];
      linarith [ Nat.sub_add_cancel ( show Finset.card ( Finset.filter ( fun p : Fin d × Fin d => p.1 < p.2 ∧ ¬ ( turanGraph d q ).Adj p.1 p.2 ) Finset.univ ) ≤ d.choose 2 from by
                                        refine' le_trans ( Finset.card_le_card _ ) _;
                                        exact Finset.filter ( fun p : Fin d × Fin d => p.1 < p.2 ) Finset.univ;
                                        · grind;
                                        · rw [ Nat.choose_two_right ];
                                          rw [ Finset.card_filter ];
                                          convert! Finset.sum_range_id d |> le_of_eq using 1;
                                          erw [ Finset.sum_product ] ; norm_num [ Finset.sum_ite ];
                                          simp +decide [ Finset.filter_lt_eq_Ioi ];
                                          rw [ ← Finset.sum_range_reflect, Finset.sum_range ] ) ];
    · rw [ ← Nat.add_sub_of_le hd ];
      exact Nat.recOn ( N - d ) ( by norm_num ) fun n ih => by simp +decide [ Nat.choose ] at * ; linarith;
  -- By Turán's theorem, `G` is `CliqueFree (q+2)`.
  have h_clique_free : G.CliqueFree (q + 2) := by
    intro s hs;
    have := Finset.card_le_univ ( Finset.image ( fun x : Fin N => if x.val < d then Fin.castSucc ⟨ x.val % q, Nat.mod_lt _ ( by linarith ) ⟩ else Fin.last q ) s ) ; simp_all +decide [  ] ;
    rw [ Finset.card_image_of_injOn ] at this;
    · linarith [ hs.2 ];
    · intro x hx y hy; have := hs.1; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
      have := this hx hy; aesop;
  convert! SimpleGraph.CliqueFree.card_edgeFinset_le h_clique_free using 1;
  · exact h_edges_G_simplified.symm;
  · convert! SimpleGraph.card_edgeFinset_turanGraph using 1;
    norm_num

/-
The subgraph of `J` induced on the neighbourhood of a vertex `v` is
`CliqueFree n` whenever `J` is `CliqueFree (n+1)`: a clique among the neighbours
of `v`, together with `v` itself, would be a clique one larger in `J`.
-/
theorem induce_neighborFinset_cliqueFree {V : Type} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) [DecidableRel J.Adj] (v : V) (n : ℕ)
    (h : J.CliqueFree (n + 1)) :
    (J.induce (↑(J.neighborFinset v) : Set V)).CliqueFree n := by
  contrapose! h;
  simp_all +decide [ SimpleGraph.CliqueFree ];
  obtain ⟨ s, hs ⟩ := h; use Insert.insert v ( s.image Subtype.val ) ; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
  simp_all +decide [ Set.Pairwise, Finset.card_image_of_injective, Function.Injective ];
  exact hs.1

open scoped Classical in
/-- Number of `J`-edges with both endpoints in `S`. -/
noncomputable def edgesIn {V : Type} [Fintype V] (J : SimpleGraph V) (S : Finset V) : ℕ :=
  (J.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ S)).card

open scoped Classical in
/-- Number of monochromatic `J`-edges (under colouring `c`) with both endpoints in `S`. -/
noncomputable def monoIn {V α : Type} [Fintype V] (J : SimpleGraph V) (c : V → α) (S : Finset V) :
    ℕ :=
  (J.edgeFinset.filter (fun e => (∀ x ∈ e, x ∈ S) ∧ ∃ u w, e = s(u, w) ∧ c u = c w)).card

open scoped Classical in
/-- Number of `J`-edges crossing from `A` to `B`. -/
noncomputable def crossCount {V : Type} [Fintype V] (J : SimpleGraph V) (A B : Finset V) : ℕ :=
  (J.edgeFinset.filter (fun e => ∃ a b, e = s(a, b) ∧ a ∈ A ∧ b ∈ B)).card

/-
Induced clique-freeness passes to the (within-`S`) neighbourhood of `v ∈ S`: a clique
among `J`-neighbours of `v` lying in `S`, together with `v`, is one larger and still in `S`.
-/
theorem induce_inter_neighbor_cliqueFree {V : Type} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) [DecidableRel J.Adj] (S : Finset V) (v : V) (hv : v ∈ S) (n : ℕ)
    (h : (J.induce (↑S : Set V)).CliqueFree (n + 1)) :
    (J.induce (↑(J.neighborFinset v ∩ S) : Set V)).CliqueFree n := by
  intro t ht; contrapose! h; simp_all +decide only [SetLike.coe_sort_coe] ;
  refine' ⟨ Insert.insert ⟨ v, hv ⟩ ( t.image fun x => ⟨ x.val, by aesop ⟩ ), _, _ ⟩ <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
  · simp_all +decide [ Set.Pairwise, Function.Embedding.subtype ];
    grind +qlia;
  · rw [ Finset.card_image_of_injective _ fun x y hxy => by aesop, ht.2 ]

/-
Edges inside a disjoint union split into the two internal counts plus the crossing count.
-/
theorem edgesIn_union_disjoint {V : Type} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) [DecidableRel J.Adj] {A B : Finset V} (hAB : Disjoint A B) :
    edgesIn J (A ∪ B) = edgesIn J A + edgesIn J B + crossCount J A B := by
  unfold edgesIn crossCount;
  rw [ ← Finset.card_union_of_disjoint, ← Finset.card_union_of_disjoint ];
  · congr with e;
    rcases e with ⟨ a, b ⟩ ; simp_all +decide [ Finset.disjoint_left ];
    grind;
  · simp_all +decide only [disjoint_union_left];
    rintro a ( ha | ha ) ha' x y rfl hx hy <;> have := ha.2 x <;> have := ha.2 y <;> aesop;
  · simp_all +decide [ Finset.disjoint_left ];
    exact fun a ha ha' => by rcases a with ⟨ x, y ⟩ ; aesop;

/-
Within-set handshake: summing within-`B` degrees double-counts the `B`-internal edges.
-/
theorem sum_neighbor_inter_self {V : Type} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) [DecidableRel J.Adj] (B : Finset V) :
    ∑ u ∈ B, (J.neighborFinset u ∩ B).card = 2 * edgesIn J B := by
  convert! SimpleGraph.sum_degrees_eq_twice_card_edges ( J.induce B ) using 1;
  · simp +decide only [SetLike.coe_sort_coe, univ_eq_attach];
    refine' Finset.sum_bij ( fun x hx => ⟨ x, hx ⟩ ) _ _ _ _ <;> try simp +decide;
    intro a ha; rw [ ← Finset.card_image_of_injective _ Subtype.coe_injective ] ; congr; ext; aesop;
  · convert! rfl;
    refine' Finset.card_bij ( fun e he => Sym2.map ( fun x => x.val ) e ) _ _ _ <;> simp +decide only [SetLike.coe_sort_coe, mem_edgeFinset, mem_filter, Sym2.mem_map, Subtype.exists,
    exists_and_right, exists_eq_right, forall_exists_index, exists_prop, and_imp];
    · rintro ⟨ u, v ⟩ ; aesop;
    · rintro ⟨ x, y ⟩ hxy ⟨ u, v ⟩ huv h; simp_all +decide [  ] ;
    · rintro ⟨ u, v ⟩ huv hu; use Sym2.mk (⟨ u, hu u ( by simp +decide ) ⟩ : B) (⟨ v, hu v ( by simp +decide ) ⟩ : B) ; aesop;

/-
Summing the into-`A` degrees over `B` counts the crossing edges (for disjoint `A`, `B`).
-/
theorem sum_neighbor_inter_cross {V : Type} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) [DecidableRel J.Adj] {A B : Finset V} (hAB : Disjoint A B) :
    ∑ u ∈ B, (J.neighborFinset u ∩ A).card = crossCount J A B := by
  push_cast [ crossCount ];
  simp +decide [ SimpleGraph.neighborFinset ];
  simp +decide only [card_eq_sum_ones];
  rw [ Finset.sum_sigma' ];
  refine' Finset.sum_bij ( fun x hx => s(x.2, x.1) ) _ _ _ _ <;> simp +decide [ SimpleGraph.edgeSet ];
  · exact fun a ha₁ ha₂ ha₃ => ⟨ ha₂.symm, _, _, Or.inl ⟨ rfl, rfl ⟩, ha₃, ha₁ ⟩;
  · simp_all +decide [ Finset.disjoint_left ];
    grind;
  · rintro b hb x y rfl hx hy; use y, x; simp_all +decide [ SimpleGraph.adj_comm ] ;

/-
**Relative Füredi partition lemma.**

For every `S : Finset V` such that the subgraph of `J` induced on `S` is
`K_{q+1}`-free, there is a `q`-colouring of `V` for which the number of
monochromatic `J`-edges inside `S` is at most `t_q(|S|) − e_J(S)`, where `e_J(S)`
counts the `J`-edges inside `S`.  This is Füredi's max-degree induction, kept
relative (all counts inside `Sym2 V`) so the induction is clean.  Proved by
induction on `q` using `turanEdges_partite_step` and the edge-counting helpers.
-/
set_option maxHeartbeats 1600000 in
theorem furedi_rel (q : ℕ) (hq : 1 ≤ q) {V : Type} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) [DecidableRel J.Adj] (S : Finset V)
    (hcf : (J.induce (↑S : Set V)).CliqueFree (q + 1)) :
    ∃ c : V → Fin q, (monoIn J c S : ℝ) ≤ (turanEdges q S.card : ℝ) - edgesIn J S := by
  induction' hq with q hq ih generalizing S;
  · use fun _ => 0; simp +decide [ monoIn, turanEdges ] ;
    rw [ Finset.card_eq_zero.mpr ] <;> norm_num [ edgesIn ];
    · convert! Nat.zero_le _ using 2 ; simp +decide [ SimpleGraph.edgeFinset ];
      contrapose! hcf; simp_all +decide [ SimpleGraph.CliqueFree ] ;
      obtain ⟨ e, he₁, he₂ ⟩ := hcf; rcases e with ⟨ u, v ⟩ ; use { ⟨ u, he₂ u ( by simp +decide ) ⟩, ⟨ v, he₂ v ( by simp +decide ) ⟩ } ; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
      exact ⟨ fun _ => he₁, by rw [ Finset.card_pair ] ; aesop ⟩;
    · contrapose! hcf; simp_all +decide [ SimpleGraph.CliqueFree ] ;
      obtain ⟨ x, y, hxy, hx, hy ⟩ := hcf; use { ⟨ x, hx ⟩, ⟨ y, hy ⟩ } ; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
      exact ⟨ fun _ => hxy, by rw [ Finset.card_pair ] ; aesop ⟩;
  · by_cases hS : S.Nonempty;
    · obtain ⟨ v, hv ⟩ := Finset.exists_max_image S ( fun u => ( J.neighborFinset u ∩ S ).card ) hS;
      -- Let $A = J.neighborFinset v ∩ S$ and $B = S \ A$.
      set A := J.neighborFinset v ∩ S
      set B := S \ A;
      -- By the induction hypothesis, there exists a coloring $c'$ of $A$ such that $monoIn J c' A \leq turanEdges q A.card - edgesIn J A$.
      obtain ⟨ c', hc' ⟩ := ih A (by
      apply induce_inter_neighbor_cliqueFree J S v hv.left (q + 1) hcf);
      -- Define the coloring $c$ for $S$ by extending $c'$ to $B$.
      use fun x => if x ∈ A then Fin.castSucc (c' x) else Fin.last q;
      -- By definition of $c$, we have $monoIn J c S = monoIn J c' A + edgesIn J B$.
      have h_mono : monoIn J (fun x => if x ∈ A then Fin.castSucc (c' x) else Fin.last q) S = monoIn J c' A + edgesIn J B := by
        unfold monoIn edgesIn;
        rw [ ← Finset.card_union_of_disjoint ];
        · congr with e ; simp +decide [ Fin.ext_iff ];
          rcases e with ⟨ u, w ⟩ ; simp_all +decide [  ];
          grind;
        · simp +contextual [ Finset.disjoint_left ];
          grind;
      -- By the properties of the Turán graph, we have $2 * edgesIn J B + crossCount J A B \leq A.card * (S.card - A.card)$.
      have h_turan : 2 * edgesIn J B + crossCount J A B ≤ A.card * (S.card - A.card) := by
        have h_turan : ∑ u ∈ B, (J.neighborFinset u ∩ S).card = 2 * edgesIn J B + crossCount J A B := by
          have h_turan : ∑ u ∈ B, (J.neighborFinset u ∩ S).card = ∑ u ∈ B, (J.neighborFinset u ∩ B).card + ∑ u ∈ B, (J.neighborFinset u ∩ A).card := by
            rw [ ← Finset.sum_add_distrib ];
            refine' Finset.sum_congr rfl fun x hx => _;
            rw [ ← Finset.card_union_of_disjoint ];
            · congr with y ; by_cases hy : y ∈ A <;> aesop;
            · exact Finset.disjoint_left.mpr fun y hy₁ hy₂ => Finset.mem_sdiff.mp ( Finset.mem_inter.mp hy₁ |>.2 ) |>.2 ( Finset.mem_inter.mp hy₂ |>.2 );
          rw [ h_turan, sum_neighbor_inter_self, sum_neighbor_inter_cross ];
          exact Finset.disjoint_sdiff;
        rw [ ← h_turan, mul_comm ];
        refine' le_trans ( Finset.sum_le_sum fun x hx => hv.2 x <| Finset.mem_sdiff.mp hx |>.1 ) _ ; simp +decide [ * ];
        grind;
      -- By the properties of the Turán graph, we have $edgesIn J S = edgesIn J A + edgesIn J B + crossCount J A B$.
      have h_edges : edgesIn J S = edgesIn J A + edgesIn J B + crossCount J A B := by
        convert! edgesIn_union_disjoint J ( Finset.disjoint_sdiff ) using 1;
        rw [ Finset.union_sdiff_of_subset ( Finset.inter_subset_right ) ];
      have := turanEdges_partite_step q A.card S.card hq ( show A.card ≤ S.card from Finset.card_le_card fun x hx => by aesop ) ; norm_cast at * ; simp_all +decide only [Nat.succ_eq_add_one, ge_iff_le] ;
      rw [ Int.subNatNat_eq_coe ] at * ; omega;
    · simp_all +decide only [Nat.succ_eq_add_one];
      unfold monoIn edgesIn; norm_num;
      rw [ Finset.card_eq_zero.mpr ] <;> norm_num;
      · exact ⟨ fun _ => 0, by rintro x hx₁ hx₂ y z rfl; specialize hx₂ y; aesop ⟩;
      · rintro ⟨ u, v ⟩ huv; exact ⟨ u, by simp +decide ⟩ ;

/-
**Füredi's partition theorem (sharp clique-case deletion).**

Every `K_{q+1}`-free graph `J` on a finite vertex set admits a `q`-colouring
whose number of monochromatic edges is at most `t_q(N) − e(J)`.  Equivalently,
deleting `t_q(N) − e(J)` edges turns `J` into a `q`-partite graph.

This is the genuine combinatorial core (Füredi's max-degree induction); it is
here obtained by specialising `furedi_rel` to `S = univ`.
-/
theorem furedi_partition (q : ℕ) (hq : 1 ≤ q) {V : Type} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) [DecidableRel J.Adj]
    (hKfree : ¬ ((⊤ : SimpleGraph (Fin (q + 1))) ⊑ J)) :
    ∃ c : V → Fin q,
      ((J.edgeFinset.filter (fun e => ∃ u v, e = s(u, v) ∧ c u = c v)).card : ℝ)
        ≤ (turanEdges q (Fintype.card V) : ℝ) - J.edgeFinset.card := by
  -- By definition of $turanEdges$, we know that $turanEdges q (Fintype.card V)$ is the maximum number of edges in a $q$-partite graph on $Fintype.card V$ vertices.
  have h_turan : ∀ (V : Type) [Fintype V] [DecidableEq V] (J : SimpleGraph V) [DecidableRel J.Adj], J.CliqueFree (q + 1) → ∃ c : V → Fin q, (monoIn J c Finset.univ : ℝ) ≤ (turanEdges q (Fintype.card V) : ℝ) - edgesIn J Finset.univ := by
    intros V _ _ J _ hKfree
    apply furedi_rel q hq J Finset.univ;
    intro t ht; specialize hKfree ( Finset.image Subtype.val t ) ; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
    simp_all +decide [ SimpleGraph.IsClique, Finset.card_image_of_injective, Function.Injective ];
    exact hKfree <| fun x hx y hy hxy => by obtain ⟨ u, hu, rfl ⟩ := hx; obtain ⟨ v, hv, rfl ⟩ := hy; exact ht.1 hu hv <| by aesop; ;
  convert! h_turan V J _;
  · exact congr_arg Finset.card ( by ext; aesop );
  · exact congr_arg Finset.card ( Finset.ext fun x => by aesop );
  · convert! hKfree using 1;
    convert! SimpleGraph.cliqueFree_iff_top_free using 1;
    all_goals try infer_instance;
    norm_num

/-- **Clique-case (Turán) stability.**

The `K_{q+1}`-free special case of Erdős–Simonovits stability.  Every
`K_{q+1}`-free graph `J` on `N ≥ N₀` vertices with at least `t_q(N) − δ N²`
edges admits a `q`-colouring with at most `η N²` monochromatic edges.

This follows from Füredi's sharp partition theorem `furedi_partition`: taking `δ := η`, the
Füredi bound `mono ≤ t_q(N) − e(J)` combined with `e(J) ≥ t_q(N) − η N²` gives
`mono ≤ η N²`. -/
theorem clique_stability (q : ℕ) (hq : 1 ≤ q) (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
      (J : SimpleGraph V) [DecidableRel J.Adj],
      N₀ ≤ Fintype.card V → ¬ ((⊤ : SimpleGraph (Fin (q + 1))) ⊑ J) →
      (turanEdges q (Fintype.card V) : ℝ) - δ * (Fintype.card V) ^ 2 ≤ J.edgeFinset.card →
      ∃ c : V → Fin q,
        ((J.edgeFinset.filter
          (fun e => ∃ u v, e = s(u, v) ∧ c u = c v)).card : ℝ)
            ≤ η * (Fintype.card V) ^ 2 := by
  refine ⟨η, hη, 0, ?_⟩
  intro V _ _ J _ _ hKfree hedge
  obtain ⟨c, hc⟩ := furedi_partition q hq J hKfree
  exact ⟨c, by linarith⟩

/-- **Graph removal to the clique (`F`-free ⇒ `o(N²)`-close to `K_{q+1}`-free).**

For a fixed graph `F` with chromatic number `q + 1` and any tolerance `ε > 0`,
there is `N₀` so that any `F`-free graph `J` on `N ≥ N₀` vertices admits an edge
set `D` of size at most `ε N²` whose deletion makes `J` contain no `K_{q+1}`.

This is the regularity-based graph removal lemma specialised to the clique; it
follows from `clique_removal` (`RemovalLemma.lean`). -/
theorem removal_to_clique
    {W : Type} [Fintype W] (F : SimpleGraph W) [DecidableRel F.Adj]
    (q : ℕ) (hchi : F.chromaticNumber = q + 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
      (J : SimpleGraph V) [DecidableRel J.Adj],
      N₀ ≤ Fintype.card V → ¬ (F ⊑ J) →
      ∃ D : Finset (Sym2 V), D ⊆ J.edgeFinset ∧
        (D.card : ℝ) ≤ ε * (Fintype.card V) ^ 2 ∧
        ¬ ((⊤ : SimpleGraph (Fin (q + 1))) ⊑ J.deleteEdges ↑D) := by
  have hcol : F.Colorable (q + 1) :=
    SimpleGraph.chromaticNumber_le_iff_colorable.mp (le_of_eq hchi)
  exact clique_removal F q hcol ε hε

/-
**Erdős–Simonovits stability theorem (Proposition `prop:stability`).**

Fix a finite graph `F` with chromatic number `q + 1` and a tolerance `η > 0`.
There are `δ > 0` and `N₀` such that every `F`-free graph `J` on a finite vertex
set of size `N ≥ N₀` with at least `t_q(N) − δ N²` edges admits a `q`-colouring
`c : V → Fin q` whose number of monochromatic (internal) edges is at most
`η N²`.

The proof combines clique stability
(`clique_stability`, derived from `furedi_partition`, `furedi_rel`, and
`turanEdges_partite_step`) with clique removal (`removal_to_clique`, derived
from Szemerédi regularity in `RemovalLemma.lean`).
-/
theorem erdos_simonovits_stability
    {W : Type} [Fintype W] (F : SimpleGraph W) [DecidableRel F.Adj]
    (q : ℕ) (hq : 1 ≤ q) (hchi : F.chromaticNumber = q + 1) (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
      (J : SimpleGraph V) [DecidableRel J.Adj],
      N₀ ≤ Fintype.card V → ¬ (F ⊑ J) →
      (turanEdges q (Fintype.card V) : ℝ) - δ * (Fintype.card V) ^ 2 ≤ J.edgeFinset.card →
      ∃ c : V → Fin q,
        ((J.edgeFinset.filter
          (fun e => ∃ u v, e = s(u, v) ∧ c u = c v)).card : ℝ)
            ≤ η * (Fintype.card V) ^ 2 := by
  -- Apply `clique_stability` with `η/2`.
  obtain ⟨δ₁, hδ₁, N₁, hN₁⟩ := clique_stability q hq (η / 2) (half_pos hη);
  obtain ⟨ N₂, hN₂ ⟩ := removal_to_clique F q hchi ( Min.min ( η / 2 ) ( δ₁ / 2 ) ) ( by positivity );
  refine' ⟨ δ₁ - Min.min ( η / 2 ) ( δ₁ / 2 ), _, Max.max N₁ N₂, _ ⟩;
  · linarith [ min_le_left ( η / 2 ) ( δ₁ / 2 ), min_le_right ( η / 2 ) ( δ₁ / 2 ) ];
  · intro V _ _ J _ hN hF hJ
    obtain ⟨D, hD₁, hD₂, hD₃⟩ := hN₂ J (le_trans (le_max_right N₁ N₂) hN) hF
    have hD₄ : (J.edgeFinset.card : ℝ) - D.card ≥ (turanEdges q (Fintype.card V) : ℝ) - δ₁ * (Fintype.card V) ^ 2 := by
      linarith;
    obtain ⟨ c, hc ⟩ := hN₁ ( J.deleteEdges D ) ( le_trans ( le_max_left N₁ N₂ ) hN ) hD₃ ( by
      convert! hD₄.le using 1;
      rw [ eq_sub_iff_add_eq ] ; norm_cast ; simp +decide only [edgeFinset_deleteEdges] ;
      rw [ Finset.card_sdiff_add_card_eq_card hD₁ ] );
    refine' ⟨ c, le_trans _ ( le_trans ( add_le_add hc hD₂ ) _ ) ⟩;
    · refine' mod_cast le_trans ( Finset.card_le_card _ ) _;
      exact ( J.deleteEdges D ).edgeFinset.filter ( fun e => ∃ u v, e = s(u, v) ∧ c u = c v ) ∪ D;
      · simp +contextual [ Finset.subset_iff ];
        tauto;
      · exact Finset.card_union_le _ _;
    · nlinarith [ min_le_left ( η / 2 ) ( δ₁ / 2 ), min_le_right ( η / 2 ) ( δ₁ / 2 ) ]

end Erdos550
