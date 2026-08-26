import Mathlib
import ErdosProblems.Erdos550.Basic
import ErdosProblems.Erdos550.Blockers
import ErdosProblems.Erdos550.ProfileForest
import ErdosProblems.Erdos550.Reservoirs

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Asymptotic blocker-hypergraph inequalities (§9)

This file records the three **asymptotic ("uniform over the counterexample
sequence", `o(1)`) blocker-hypergraph inequalities** that feed the null-blocker
compactness theorem:

* the **red-profile inequality** `eq:redprofile`
  (`red_profile_inequality`), `∑ᵢ ρᵢ(x) ≥ q − 1 − o(1)` uniformly in `x ∈ X`;
* **`a`-set separation** `lem:asetblock` (`aset_separation`),
  `min_i μ_i(⋂_{x∈S} A_i(x)) = o(1)` uniformly over `a`-sets `S`;
* **obstruction blocking** `lem:obstructionblock` (`obstruction_blocking`),
  `min_{j≠i} μ_j(⋂_{x∈E} A_j(x)) = o(1)` uniformly over obstructions `E ∈ 𝒞ᵢ`.

Here the reservoirs `Wᵢ` carry the uniform probability measure, so the measure of
a set is its cardinality divided by `|Wᵢ|`; the events are red neighbourhoods
`A_i(x) = N_Gᵣ(x) ∩ Wᵢ`, and `ρᵢ(x) = |A_i(x)|/|Wᵢ|`.

The combinatorial hearts are the greedy embeddings
`red_F_from_first_class`, `red_F_from_red_H` in `Blockers.lean`/`Reservoirs.lean`,
and `profile_lemma` in `ProfileForest.lean`.  On top of those cores this file
assembles the `o(1)` "uniform over the sequence" inequalities together with the
clean reservoir decomposition.

To keep the statements faithful and self-contained, the relevant clean-reservoir
hypotheses are listed explicitly:
* `W` are pairwise-disjoint reservoirs, each of size `≥ s₀`,
* `X` (the remainder) is disjoint from every `Wᵢ`,
* the *cross-blue slack* `ζ`: every reservoir vertex has at most `ζ |Wⱼ|`
  blue (non-red) neighbours in every other reservoir `Wⱼ`,
* the red graph `Gᵣ` is `F`-free (`F = Kmult (q+1) m`).
-/

open SimpleGraph Finset

namespace Erdos550

/-- The common red neighbourhood of a set `S` inside a reservoir `Wi` (as a
finset of `Wi`): the vertices of `Wi` red-adjacent to every vertex of `S`. -/
def commonRedNbhd {V : Type*} [DecidableEq V] (Gr : SimpleGraph V) [DecidableRel Gr.Adj]
    (S : Finset V) (Wi : Finset V) : Finset V :=
  Wi.filter (fun v => ∀ x ∈ S, Gr.Adj x v)

/-
**`a`-set separation (`lem:asetblock`), finitary `o(1)` form.**

For every tolerance `δ > 0` there are a cross-blue slack `ζ₀ > 0` and a size
threshold `s₀` such that: in any clean reservoir configuration with an `F`-free
red graph `Gᵣ`, reservoirs of size `≥ s₀` and cross-blue slack `≤ ζ₀`, every
`a`-set `S ⊆ X` (`a = m 0`) is *separated*: in some reservoir its common red
neighbourhood has density `≤ δ`.
-/
set_option maxHeartbeats 1000000 in
theorem aset_separation (q : ℕ) (_hq : 2 ≤ q) (m : Fin (q + 1) → ℕ)
    (_hmono : Monotone m) (_hpos : 1 ≤ m 0) (δ : ℝ) (hδ : 0 < δ) :
    ∃ ζ₀ : ℝ, 0 < ζ₀ ∧ ∃ s₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
      (Gr : SimpleGraph V) [DecidableRel Gr.Adj]
      (W : Fin q → Finset V) (X : Finset V),
      (∀ i j, i ≠ j → Disjoint (W i) (W j)) →
      (∀ i, Disjoint X (W i)) →
      (∀ i, s₀ ≤ (W i).card) →
      (∀ i j, i ≠ j → ∀ w ∈ W i,
        (((W j).filter (fun v => ¬ Gr.Adj w v)).card : ℝ) ≤ ζ₀ * (W j).card) →
      ¬ (Kmult (q + 1) m ⊑ Gr) →
      ∀ S : Finset V, S ⊆ X → S.card = m 0 →
        ∃ i : Fin q, ((commonRedNbhd Gr S (W i)).card : ℝ) ≤ δ * (W i).card := by
  -- Choose ζ₀ = δ / (2 * (∑ i, m i) + 2) and s₀ = ⌈2 * (∑ i, m i) / δ⌉ + 1.
  use δ / (2 * (∑ i, m i) + 2), by
    positivity, Nat.ceil (2 * (∑ i, m i) / δ) + 1;
  intro V _ _ Gr _ W X hdisjW hdisjX hWcard hblue Gr_not_subgraph S hS_subX hS_card;
  by_contra! h_contra;
  apply Gr_not_subgraph;
  convert! Erdos550.greedy_multipartite_embedding_ordered Gr ( q + 1 ) m ( Fin.cons S W ) _ _;
  · simp +decide [ Fin.forall_fin_succ, * ];
    exact ⟨ fun i hi => Finset.disjoint_left.mpr fun x hxS hxW => Finset.disjoint_left.mp ( hdisjX i ) ( hS_subX hxS ) hxW, fun i => ⟨ Finset.disjoint_left.mpr fun x hxW hxS => Finset.disjoint_left.mp ( hdisjX i ) ( hS_subX hxS ) hxW, fun j hj => hdisjW i j hj ⟩ ⟩;
  · intro j U hU hU_card
    by_cases hj : j = 0;
    · simp_all +decide;
    · obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin q, j = Fin.succ i₀ := by
        exact ⟨ Fin.pred j hj, by simp +decide ⟩;
      -- The number of vertices in $W i₀$ that are not adjacent to some $u \in U \setminus S$ is at most $(U \setminus S).card * ζ₀ * (W i₀).card$.
      have h_not_adj : ((W i₀).filter (fun v => ∃ u ∈ U \ S, ¬Gr.Adj v u)).card ≤ (U \ S).card * (δ / (2 * (∑ i, m i) + 2)) * (W i₀).card := by
        have h_not_adj : ((W i₀).filter (fun v => ∃ u ∈ U \ S, ¬Gr.Adj v u)).card ≤ ∑ u ∈ U \ S, ((W i₀).filter (fun v => ¬Gr.Adj u v)).card := by
          have h_not_adj : ((W i₀).filter (fun v => ∃ u ∈ U \ S, ¬Gr.Adj v u)) ⊆ Finset.biUnion (U \ S) (fun u => (W i₀).filter (fun v => ¬Gr.Adj u v)) := by
            simp +contextual [ Finset.subset_iff ];
            exact fun v hv u hu huS huV => ⟨ u, ⟨ hu, huS ⟩, by simpa only [ SimpleGraph.adj_comm ] using! huV ⟩;
          exact le_trans ( Finset.card_le_card h_not_adj ) ( Finset.card_biUnion_le );
        refine' le_trans ( Nat.cast_le.mpr h_not_adj ) _;
        push_cast [ Finset.sum_mul _ _ _ ];
        refine' le_trans ( Finset.sum_le_sum fun x hx => show ( _ : ℝ ) ≤ δ / ( 2 * ∑ i : Fin ( q + 1 ), ( m i : ℝ ) + 2 ) * ( W i₀ |> Finset.card : ℝ ) from _ ) _;
        · obtain ⟨ i, hi, hi' ⟩ := hU x ( Finset.mem_sdiff.mp hx |>.1 ) ; simp_all +decide [ Fin.cons ] ;
          cases i using Fin.inductionOn <;> simp_all +decide [ Fin.cases ];
          exact hblue _ _ ( ne_of_lt hi ) _ hi';
        · norm_num [ mul_assoc ];
      -- Therefore, the number of vertices in $W i₀$ that are adjacent to all vertices in $U$ is at least $(δ - M*ζ₀) * (W i₀).card$.
      have h_adj : ((W i₀).filter (fun v => ∀ u ∈ U, Gr.Adj v u)).card ≥ (δ - (∑ i, m i) * (δ / (2 * (∑ i, m i) + 2))) * (W i₀).card := by
        have h_adj : ((W i₀).filter (fun v => ∀ u ∈ U, Gr.Adj v u)).card ≥ ((commonRedNbhd Gr S (W i₀)).filter (fun v => ∀ u ∈ U \ S, Gr.Adj v u)).card := by
          refine Finset.card_mono ?_;
          simp +contextual [ Finset.subset_iff, commonRedNbhd ];
          intro v hv hvS hvU u hu; specialize hU u hu; rcases hU with ⟨ i, hi, hi' ⟩ ; induction i using Fin.inductionOn <;> simp_all +decide [ Fin.cons ] ;
          · exact hvS u hi' |> SimpleGraph.Adj.symm;
          · exact hvU u hu ( by intro H; have := Finset.disjoint_left.mp ( hdisjX _ ) ( hS_subX H ) hi'; aesop );
        have h_adj : ((commonRedNbhd Gr S (W i₀)).filter (fun v => ∀ u ∈ U \ S, Gr.Adj v u)).card ≥ (commonRedNbhd Gr S (W i₀)).card - ((W i₀).filter (fun v => ∃ u ∈ U \ S, ¬Gr.Adj v u)).card := by
          rw [ ge_iff_le, tsub_le_iff_right ];
          rw [ ← Finset.card_union_add_card_inter ];
          refine' le_trans _ ( Nat.le_add_right _ _ );
          refine Finset.card_le_card ?_;
          grind +locals;
        have h_adj : ((commonRedNbhd Gr S (W i₀)).filter (fun v => ∀ u ∈ U \ S, Gr.Adj v u)).card ≥ (δ * (W i₀).card) - ((U \ S).card * (δ / (2 * (∑ i, m i) + 2)) * (W i₀).card) := by
          refine' le_trans ( sub_le_sub ( le_of_lt ( h_contra i₀ ) ) h_not_adj ) _;
          norm_cast;
          rw [ Int.subNatNat_eq_coe ] ; omega;
        refine le_trans ?_ ( h_adj.trans ?_ );
        · rw [ sub_mul ];
          gcongr;
          grind +extAll;
        · exact_mod_cast ‹#({v ∈ W i₀ | ∀ u ∈ U, Gr.Adj v u}) ≥ #({v ∈ commonRedNbhd Gr S (W i₀) | ∀ u ∈ U \ S, Gr.Adj v u})›;
      -- Since $δ - M*ζ₀ > δ/2$, we have $(δ/2) * (W i₀).card ≥ M$.
      have h_half : (δ / 2) * (W i₀).card ≥ (∑ i, m i) := by
        have := Nat.lt_of_ceil_lt ( hWcard i₀ );
        rw [ div_lt_iff₀ ] at this <;> linarith;
      have h_final : ((W i₀).filter (fun v => ∀ u ∈ U, Gr.Adj v u)).card ≥ (∑ i, m i) := by
        have h_final : (δ - (∑ i, m i) * (δ / (2 * (∑ i, m i) + 2))) * (W i₀).card ≥ (δ / 2) * (W i₀).card := by
          field_simp;
          exact mul_le_mul_of_nonneg_left ( by linarith ) ( Nat.cast_nonneg _ );
        exact_mod_cast h_half.trans ( h_final.trans h_adj );
      exact le_trans ( Finset.single_le_sum ( fun a _ => Nat.zero_le ( m a ) ) ( Finset.mem_univ _ ) ) ( h_final.trans ( Finset.card_mono <| by aesop_cat ) )

/-
Extract the two complete-bipartite sides from a contained `Kbip a b` inside an
induced subgraph `Gr.induce ↑Y`: disjoint finsets `S0, S1 ⊆ Y` of the right
cardinalities, with every cross pair red-adjacent in `Gr`.
-/
lemma bip_sides_of_contained {V : Type*} [DecidableEq V] (Gr : SimpleGraph V)
    [DecidableRel Gr.Adj] (a b : ℕ) (Y : Finset V)
    (h : Kbip a b ⊑ Gr.induce (↑Y)) :
    ∃ S0 S1 : Finset V, S0 ⊆ Y ∧ S1 ⊆ Y ∧ S0.card = a ∧ S1.card = b ∧
      Disjoint S0 S1 ∧ ∀ u ∈ S0, ∀ v ∈ S1, Gr.Adj u v := by
  obtain ⟨ f, hf ⟩ := h;
  refine' ⟨ Finset.image ( fun k : Fin a => ( f ( Sum.inl k ) ).val ) Finset.univ, Finset.image ( fun k : Fin b => ( f ( Sum.inr k ) ).val ) Finset.univ, _, _, _, _, _, _ ⟩ <;> simp +decide;
  all_goals norm_num [ Finset.subset_iff, Finset.disjoint_left ];
  · rw [ Finset.card_image_of_injective _ fun x y hxy => by simpa using! hf <| Subtype.ext hxy, Finset.card_fin ];
  · rw [ Finset.card_image_of_injective _ fun x y hxy => _, Finset.card_fin ];
    exact fun x y hxy => by simpa [ Fin.ext_iff ] using! hf ( Subtype.ext hxy ) ;
  · exact fun i j => hf.ne ( by simp +decide );
  · intro i j; have := f.map_rel ( show ( Kbip a b ).Adj ( Sum.inl i ) ( Sum.inr j ) from by simp +decide [ Kbip ] ) ; aesop;

/-
Index-free counting core of the greedy slack argument: among a dense set
`D ⊆ Wj`, the vertices red-adjacent to *all* of a finite "bad" set `Bad` number at
least `|D|` minus the total slack `∑_{w∈Bad} |{v∈Wj : ¬Gr.Adj v w}|`.
-/
lemma dense_minus_slack {V : Type*} [DecidableEq V] (Gr : SimpleGraph V)
    [DecidableRel Gr.Adj] (Wj D Bad : Finset V) (hDsub : D ⊆ Wj) :
    (D.card : ℝ) - (∑ w ∈ Bad, ((Wj.filter (fun v => ¬ Gr.Adj v w)).card : ℝ))
      ≤ ((D.filter (fun v => ∀ w ∈ Bad, Gr.Adj v w)).card : ℝ) := by
  rw [ sub_le_iff_le_add' ];
  norm_cast;
  have h_card_filter : (D.filter (fun v => ∃ w ∈ Bad, ¬ Gr.Adj v w)).card ≤ ∑ w ∈ Bad, (Wj.filter (fun v => ¬ Gr.Adj v w)).card := by
    refine' le_trans _ ( Finset.card_biUnion_le );
    exact Finset.card_le_card fun x hx => by aesop;
  linarith [ show Finset.card ( Finset.filter ( fun v => ∃ w ∈ Bad, ¬Gr.Adj v w ) D ) + Finset.card ( Finset.filter ( fun v => ∀ w ∈ Bad, Gr.Adj v w ) D ) = D.card from by rw [ Finset.card_filter, Finset.card_filter ] ; rw [ ← Finset.sum_add_distrib ] ; exact Finset.card_eq_sum_ones _ ▸ by congr; ext; by_cases h : ∃ w ∈ Bad, ¬Gr.Adj ‹_› w <;> aesop ]

/-
The greedy slack richness step used by `obstruction_blocking`.  Given a reservoir
`W (i.succAbove k)` whose common red neighbourhood of `E` is dense (`> δ·|W j|`),
plus the cross-blue slack bound, at least `m (k.succ.succ)` of its vertices are
red-adjacent to all of `S0 ∪ S1 ∪ U`.
-/
lemma obstruction_richness {V : Type*} [Fintype V] [DecidableEq V] (Gr : SimpleGraph V)
    [DecidableRel Gr.Adj] (q' : ℕ) (m : Fin (q' + 2 + 1) → ℕ) (δ : ℝ) (hδ : 0 < δ)
    (W : Fin (q' + 2) → Finset V) (E : Finset V) (i : Fin (q' + 2))
    (S0 S1 : Finset V)
    (hS0sub : S0 ⊆ W i ∪ E) (hS1sub : S1 ⊆ W i ∪ E)
    (hS0card : S0.card = m 0) (hS1card : S1.card = m 1)
    (_hdisjW : ∀ a b, a ≠ b → Disjoint (W a) (W b))
    (_hdisjEW : ∀ a, Disjoint E (W a))
    (hWcard : ∀ a, ⌈2 * (∑ x, (m x : ℝ)) / δ⌉₊ + 1 ≤ (W a).card)
    (hblue : ∀ a b, a ≠ b → ∀ w ∈ W a,
        (((W b).filter (fun v => ¬ Gr.Adj w v)).card : ℝ) ≤
          (δ / (4 * (∑ x, (m x : ℝ)) + 4)) * (W b).card)
    (h_contra : ∀ b, b ≠ i → δ * (W b).card < ((commonRedNbhd Gr E (W b)).card : ℝ))
    (k : Fin (q' + 1)) (U : Finset V)
    (hUstruct : ∀ u ∈ U, u ∈ S0 ∨ u ∈ S1 ∨ ∃ k', k' < k ∧ u ∈ W (i.succAbove k'))
    (hUcard : U.card ≤ ∑ x, m x) :
    m (k.succ.succ) ≤ ((W (i.succAbove k)).filter
      (fun v => (∀ s ∈ S0, Gr.Adj v s) ∧ (∀ s ∈ S1, Gr.Adj v s) ∧
        ∀ u ∈ U, Gr.Adj v u)).card := by
  refine' le_trans _ ( Finset.card_mono _ );
  any_goals exact commonRedNbhd Gr E ( W ( Fin.succAbove i k ) ) |> Finset.filter fun v => ∀ w ∈ ( S0 ∪ S1 ∪ U ).filter ( fun w => w ∉ E ), Gr.Adj v w;
  · have h_dense_minus_slack : (Finset.card (commonRedNbhd Gr E (W (Fin.succAbove i k))) : ℝ) - (∑ w ∈ (S0 ∪ S1 ∪ U).filter (fun w => w ∉ E), ((W (Fin.succAbove i k)).filter (fun v => ¬Gr.Adj v w)).card : ℝ) ≥ (δ / 2) * (W (Fin.succAbove i k)).card := by
      have h_dense_minus_slack : (∑ w ∈ (S0 ∪ S1 ∪ U).filter (fun w => w ∉ E), ((W (Fin.succAbove i k)).filter (fun v => ¬Gr.Adj v w)).card : ℝ) ≤ ((S0 ∪ S1 ∪ U).filter (fun w => w ∉ E)).card * (δ / (4 * ∑ x, (m x : ℝ) + 4)) * (W (Fin.succAbove i k)).card := by
        refine' le_trans ( Finset.sum_le_sum fun w hw => show ( _ : ℝ ) ≤ ( δ / ( 4 * ∑ x : Fin ( q' + 2 + 1 ), ( m x : ℝ ) + 4 ) ) * ( W ( Fin.succAbove i k ) |> Finset.card : ℝ ) from _ ) _;
        · by_cases hwW : w ∈ W i;
          · convert! hblue i ( Fin.succAbove i k ) ( by simp +decide [  ] ) w hwW using 1;
            simp +decide only [adj_comm];
          · obtain ⟨k', hk'⟩ : ∃ k' < k, w ∈ W (Fin.succAbove i k') := by
              grind;
            convert! hblue ( Fin.succAbove i k' ) ( Fin.succAbove i k ) _ w hk'.2 using 1;
            · simp +decide only [adj_comm];
            · exact fun h => hk'.1.ne ( by simpa [ Fin.succAbove_ne ] using! h );
        · simp +decide [ mul_assoc ];
      have h_card_filter : ((S0 ∪ S1 ∪ U).filter (fun w => w ∉ E)).card ≤ 2 * ∑ x, (m x : ℝ) := by
        have h_card_filter : ((S0 ∪ S1 ∪ U).filter (fun w => w ∉ E)).card ≤ (S0 ∪ S1 ∪ U).card := by
          exact Finset.card_filter_le _ _;
        have h_card_filter : (S0 ∪ S1 ∪ U).card ≤ m 0 + m 1 + ∑ x, (m x : ℝ) := by
          exact_mod_cast le_trans ( Finset.card_union_le _ _ ) ( add_le_add ( Finset.card_union_le _ _ |> le_trans <| add_le_add hS0card.le hS1card.le ) hUcard );
        refine' le_trans ( Nat.cast_le.mpr ‹_› ) ( h_card_filter.trans _ );
        rw [ Finset.sum_eq_add_sum_sdiff_singleton_of_mem ( Finset.mem_univ 0 ) ];
        linarith [ show ( m 1 : ℝ ) ≤ ∑ x ∈ Finset.univ \ { 0 }, ( m x : ℝ ) from mod_cast Finset.single_le_sum ( fun x _ => Nat.zero_le ( m x ) ) ( by simp +decide ) ];
      have := h_contra ( Fin.succAbove i k ) ( by simp +decide [ Fin.succAbove_ne ] );
      refine' le_trans _ ( sub_le_sub_left h_dense_minus_slack _ );
      field_simp;
      nlinarith [ show 0 ≤ δ * ( Finset.card ( W ( Fin.succAbove i k ) ) : ℝ ) by positivity, show 0 ≤ δ * ( Finset.card ( W ( Fin.succAbove i k ) ) : ℝ ) * ( ∑ x : Fin ( q' + 2 + 1 ), ( m x : ℝ ) ) by positivity ];
    have h_card_filter : (Finset.card (Finset.filter (fun v => ∀ w ∈ (S0 ∪ S1 ∪ U).filter (fun w => w ∉ E), Gr.Adj v w) (commonRedNbhd Gr E (W (Fin.succAbove i k)))) : ℝ) ≥ (δ / 2) * (W (Fin.succAbove i k)).card := by
      refine' le_trans h_dense_minus_slack _;
      convert! dense_minus_slack Gr ( W ( Fin.succAbove i k ) ) ( commonRedNbhd Gr E ( W ( Fin.succAbove i k ) ) ) ( ( S0 ∪ S1 ∪ U ).filter ( fun w => w ∉ E ) ) _ using 1;
      · convert! rfl;
      · grind +locals;
    have h_card_filter : (δ / 2) * (W (Fin.succAbove i k)).card > ∑ x, m x := by
      have := Nat.lt_of_ceil_lt ( hWcard ( Fin.succAbove i k ) );
      rw [ div_lt_iff₀ ] at this <;> norm_num at * <;> linarith;
    exact_mod_cast ( by linarith [ show ( m ( Fin.succ ( Fin.succ k ) ) : ℝ ) ≤ ∑ x : Fin ( q' + 2 + 1 ), m x from mod_cast Finset.single_le_sum ( fun a _ => Nat.zero_le ( m a ) ) ( Finset.mem_univ _ ) ] : ( m ( Fin.succ ( Fin.succ k ) ) : ℝ ) ≤ Finset.card ( Finset.filter ( fun v => ∀ w ∈ { w ∈ S0 ∪ S1 ∪ U | w ∉ E }, Gr.Adj v w ) ( commonRedNbhd Gr E ( W ( Fin.succAbove i k ) ) ) ) );
  · simp +decide [ Finset.subset_iff, commonRedNbhd ];
    intro v hv hvE hvU; refine' ⟨ hv, _, _, _ ⟩ <;> intro w hw <;> specialize hvU w <;> simp_all +decide [ SimpleGraph.adj_comm ] ;
    · grind;
    · grind;
    · grind

/-- `E` is a **obstruction** of the reservoir hypergraph `𝒞ᵢ` (`eq:obstructiondef`):
a nonempty subset of `X` that is inclusion-minimal subject to
`Gᵣ[Wᵢ ∪ E] ⊇ H` (`H = K_{a,b} = Kbip (m 0) (m 1)`). -/
def IsObstruction {V : Type*} [DecidableEq V] (Gr : SimpleGraph V) [DecidableRel Gr.Adj]
    (a b : ℕ) (Wi X E : Finset V) : Prop :=
  E.Nonempty ∧ E ⊆ X ∧ (Kbip a b ⊑ Gr.induce (↑(Wi ∪ E))) ∧
    ∀ E' ⊂ E, ¬ (Kbip a b ⊑ Gr.induce (↑(Wi ∪ E')))

/-
**Obstruction blocking (`lem:obstructionblock`), finitary `o(1)` form.**

For every tolerance `δ > 0` there are a cross-blue slack `ζ₀ > 0` and a size
threshold `s₀` such that: in any clean reservoir configuration with an `F`-free
red graph `Gᵣ` (reservoirs of size `≥ s₀`, cross-blue slack `≤ ζ₀`), for every
`i` and every obstruction `E ∈ 𝒞ᵢ`, some other reservoir `j ≠ i` *blocks* `E`: the
common red neighbourhood of `E` in `Wⱼ` has density `≤ δ`.
-/
theorem obstruction_blocking (q : ℕ) (hq : 2 ≤ q) (m : Fin (q + 1) → ℕ)
    (hmono : Monotone m) (hpos : 1 ≤ m 0) (δ : ℝ) (hδ : 0 < δ) :
    ∃ ζ₀ : ℝ, 0 < ζ₀ ∧ ∃ s₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
      (Gr : SimpleGraph V) [DecidableRel Gr.Adj]
      (W : Fin q → Finset V) (X : Finset V),
      (∀ i j, i ≠ j → Disjoint (W i) (W j)) →
      (∀ i, Disjoint X (W i)) →
      (∀ i, s₀ ≤ (W i).card) →
      (∀ i j, i ≠ j → ∀ w ∈ W i,
        (((W j).filter (fun v => ¬ Gr.Adj w v)).card : ℝ) ≤ ζ₀ * (W j).card) →
      ¬ (Kmult (q + 1) m ⊑ Gr) →
      ∀ (i : Fin q) (E : Finset V), IsObstruction Gr (m 0) (m 1) (W i) X E →
        ∃ j : Fin q, j ≠ i ∧
          ((commonRedNbhd Gr E (W j)).card : ℝ) ≤ δ * (W j).card := by
  refine' ⟨ _, _, _ ⟩;
  exact δ / ( 4 * ( ∑ i, ( m i : ℝ ) ) + 4 );
  · positivity;
  · refine' ⟨ ⌈2 * ( ∑ i, ( m i : ℝ ) ) / δ⌉₊ + 1, _ ⟩;
    intro V _ _ Gr _ W X hdisjW hdisjX hWcard hblue hGr i E hE;
    by_cases h_contra : ∀ j ≠ i, δ * (W j).card < ((commonRedNbhd Gr E (W j)).card : ℝ);
    · obtain ⟨S0, S1, hS0sub, hS1sub, hS0card, hS1card, hdisj, hHred⟩ : ∃ S0 S1 : Finset V, S0 ⊆ W i ∪ E ∧ S1 ⊆ W i ∪ E ∧ S0.card = m 0 ∧ S1.card = m 1 ∧ Disjoint S0 S1 ∧ ∀ u ∈ S0, ∀ v ∈ S1, Gr.Adj u v := by
        apply bip_sides_of_contained;
        exact hE.2.2.1;
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 2 := by
        exact ⟨ q - 2, by rw [ Nat.sub_add_cancel hq ] ⟩;
      have := red_F_from_red_H_ordered Gr ( q' + 1 ) m S0 S1 hS0card hS1card hdisj hHred ( fun k => W ( i.succAbove k ) ) ?_ ?_ ?_ ?_;
      · contradiction;
      · exact fun a b hab => hdisjW _ _ <| by simpa [ Fin.succAbove_ne ] using! hab;
      · intro j; specialize hdisjW i ( i.succAbove j ) ; simp_all +decide [ Finset.disjoint_left ] ;
        intro a ha; specialize hS0sub ha; simp_all +decide [ Finset.subset_iff ] ;
        cases hS0sub <;> [ exact hdisjW ‹_›; exact fun h => hdisjX _ ( hE.2.1 ‹_› ) h ];
      · intro j; specialize hdisjW i ( i.succAbove j ) ; simp_all +decide [ Finset.disjoint_left ] ;
        intro a ha; specialize hS1sub ha; simp_all +decide [ Finset.subset_iff ] ;
        cases hS1sub <;> simp_all +decide [ IsObstruction ];
        exact fun h => hdisjX _ ( hE.2.1 ‹_› ) h;
      · intro k U hUstruct hUcard;
        convert! obstruction_richness Gr q' m δ hδ W E i S0 S1 hS0sub hS1sub hS0card hS1card hdisjW ?_ ?_ ?_ ?_ k U hUstruct hUcard using 1;
        · grind;
        · exact fun a => Finset.disjoint_left.mpr fun x hx hx' => Finset.disjoint_left.mp ( hdisjX a ) ( hE.2.1 hx ) hx';
        · exact hWcard;
        · exact fun a b hab w hw => hblue a b hab w hw;
        · exact h_contra;
    · aesop

/-
**Red-profile inequality (`eq:redprofile`), finitary `o(1)` form.**

For every tolerance `δ > 0` there is a reservoir minimum-degree slack `κ₀ > 0`
such that: in any clean reservoir configuration whose *blue* graph `Gᵣᶜ`
contains no copy of the tree `T` (no blue `T`), with reservoir sizes in the
paper's regime `card VT ≤ |Wᵢ| ≤ (1+κ₀)·card VT` and blue induced minimum degree
`≥ (1 − κ₀)|Wᵢ|` inside each reservoir, every remainder vertex `x ∈ X` has large
total red profile `∑ᵢ |N_Gᵣ(x) ∩ Wᵢ| / |Wᵢ| ≥ q − 1 − δ`.

The size-sandwich hypothesis `card VT ≤ |Wᵢ| ≤ (1+κ₀)·card VT` matches
`|Wᵢ| = (1+o(1)) n` from the clean reservoir decomposition.  The proof is the
contrapositive of `profile_lemma`.
-/
theorem red_profile_inequality (q : ℕ) (hq : 2 ≤ q) (δ : ℝ) (hδ : 0 < δ) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ {VT : Type} [Fintype VT] [DecidableEq VT]
      {V : Type} [Fintype V] [DecidableEq V]
      (T : SimpleGraph VT) [DecidableRel T.Adj]
      (Gr : SimpleGraph V) [DecidableRel Gr.Adj]
      (W : Fin q → Finset V) (X : Finset V),
      T.IsTree → 2 ≤ Fintype.card VT →
      (∀ i j, i ≠ j → Disjoint (W i) (W j)) →
      (∀ i, Disjoint X (W i)) →
      (∀ i, (Fintype.card VT : ℝ) ≤ (W i).card ∧
        ((W i).card : ℝ) ≤ (1 + κ₀) * Fintype.card VT) →
      (∀ i, ∀ v ∈ W i,
        (1 - κ₀) * ((W i).card : ℝ) ≤ (((Grᶜ.neighborFinset v) ∩ W i).card : ℝ)) →
      ¬ (T ⊑ Grᶜ) →
      ∀ x ∈ X,
        (q : ℝ) - 1 - δ ≤
          ∑ i, (((Gr.neighborFinset x) ∩ W i).card : ℝ) / ((W i).card : ℝ) := by
  obtain ⟨κ, δ0, hκ, hδ0, H⟩ := profile_lemma q hq δ hδ;
  use min κ δ0 / 2;
  refine' ⟨ by positivity, _ ⟩;
  intro VT _ _ V _ _ T _ Gr _ W X hT hcardT hdisjW hdisjX hsize hmindeg hnoblueT x hx; contrapose! hnoblueT;
  refine' H T Grᶜ x W hT hcardT _ hdisjW _ _ _;
  · exact fun i => fun hi => Finset.disjoint_left.mp ( hdisjX i ) hx hi;
  · intro i;
    refine' le_trans _ ( le_trans ( hsize i |>.2 ) _ );
    · exact_mod_cast Finset.card_le_card ( Finset.inter_subset_right );
    · exact mul_le_mul_of_nonneg_right ( by linarith [ min_le_left κ δ0, min_le_right κ δ0 ] ) ( Nat.cast_nonneg _ );
  · -- By definition of $redCount$ and $blueCount$, we have $redCount i + blueCount i = |W i|$.
    have h_red_blue : ∀ i, ((Gr.neighborFinset x ∩ W i).card : ℝ) + ((Grᶜ.neighborFinset x ∩ W i).card : ℝ) = (W i).card := by
      intro i; norm_cast; rw [ ← Finset.card_union_of_disjoint ];
      · congr with y ; by_cases hy : Gr.Adj x y <;> simp +decide [ hy ];
        exact fun hy' => by rintro rfl; exact Finset.disjoint_left.mp ( hdisjX i ) hx hy';
      · simp +contextual [ Finset.disjoint_left, SimpleGraph.neighborFinset ];
    -- By definition of $redCount$ and $blueCount$, we have $\sum_{i} \frac{redCount i}{|W i|} < q - 1 - \delta$.
    have h_sum_red : ∑ i, ((Gr.neighborFinset x ∩ W i).card : ℝ) / (W i).card < q - 1 - δ := by
      convert! hnoblueT using 1;
    -- By definition of $redCount$ and $blueCount$, we have $\sum_{i} \frac{blueCount i}{|W i|} > 1 + \delta$.
    have h_sum_blue : ∑ i, ((Grᶜ.neighborFinset x ∩ W i).card : ℝ) / (W i).card > 1 + δ := by
      have h_sum_blue : ∑ i, ((Grᶜ.neighborFinset x ∩ W i).card : ℝ) / (W i).card = ∑ i, (1 - ((Gr.neighborFinset x ∩ W i).card : ℝ) / (W i).card) := by
        refine Finset.sum_congr rfl fun i _ => ?_;
        rw [ one_sub_div ] <;> norm_num [ h_red_blue i ];
        · rw [ ← h_red_blue i, add_sub_cancel_left ];
        · intro h; specialize hsize i; norm_num [ h ] at hsize; linarith [ show ( Fintype.card VT : ℝ ) ≥ 2 by norm_cast ] ;
      norm_num [ h_sum_blue ];
      linarith;
    refine' le_trans _ ( Finset.sum_le_sum fun i _ => show ( Grᶜ.neighborFinset x ∩ W i |> Finset.card : ℝ ) ≥ ( Grᶜ.neighborFinset x ∩ W i |> Finset.card : ℝ ) / ( W i |> Finset.card : ℝ ) * ( Fintype.card VT : ℝ ) from _ );
    · rw [ ← Finset.sum_mul _ _ _ ] ; exact mul_le_mul_of_nonneg_right h_sum_blue.le <| Nat.cast_nonneg _;
    · rw [ div_mul_eq_mul_div, ge_iff_le, div_le_iff₀ ] <;> norm_cast at * <;> nlinarith [ hsize i ];
  · intro i v hv; specialize hmindeg i v hv; nlinarith [ hsize i, show ( 0 : ℝ ) ≤ min κ δ0 by positivity, min_le_left κ δ0, min_le_right κ δ0 ] ;

end Erdos550
