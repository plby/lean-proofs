import Mathlib
import ErdosProblems.Erdos550.Basic
import ErdosProblems.Erdos550.Stability
import ErdosProblems.Erdos550.KovariSosTuran
import ErdosProblems.Erdos550.GreedyEmbedding
import ErdosProblems.Erdos550.Blockers

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Clean reservoir decomposition (Lemma `lem:reservoirs`)

In a hypothetical counterexample to Erdős 550 the red graph `Gr` on `K_N`
(`N = (q+o(1))n`) is `F`-free with `e(Gr) ≥ t_q(N) − o(N²)`.  The clean
reservoir decomposition extracts `q` pairwise-disjoint reservoirs
`W₁,…,W_q` and a small remainder `X = V ∖ ⋃ Wᵢ` such that, uniformly,

* `|Wᵢ| = (1+o(1)) n`,
* the blue induced minimum degree of `Wᵢ` is `|Wᵢ| − o(n)`
  (equivalently the red degree inside `Wᵢ` is `o(n)`),
* the cross-blue degree `max_{w∈Wᵢ, j≠i} d_blue(w, Wⱼ) = o(n)`,
* `Gr[Wᵢ]` is `H`-free, and
* `|X| = o(n)`.

The proof combines **Erdős–Simonovits stability** (`erdos_simonovits_stability`,
file `Stability.lean`), the **Turán variance identity** (`deviation_identity`),
**Kővári–Sós–Turán** (`kovari_sos_turan`, already proved), and the **greedy
complete-multipartite embedding** (`red_F_from_first_class`, already proved) for
the `H`-freeness step.

This file proves the elementary counting input — the **Markov cleaning lemma**
— in full, states the clean reservoir decomposition faithfully, and records the
greedy `H`-freeness step it relies on.
-/

open SimpleGraph Finset

namespace Erdos550

/-
**Markov cleaning lemma.**  For a "badness" function `f : V → ℕ` and a
threshold `d ≥ 1`, the number of vertices with `f v ≥ d` is at most
`(∑ v, f v) / d`; equivalently `d · |{v : f v ≥ d}| ≤ ∑ v, f v`.  This is the
counting step behind both cleaning passes in `lem:reservoirs`.
-/
theorem markov_count {V : Type*} [Fintype V] (f : V → ℕ) (d : ℕ) :
    d * (Finset.univ.filter (fun v => d ≤ f v)).card ≤ ∑ v, f v := by
  exact le_trans ( by rw [ Finset.sum_const, smul_eq_mul, mul_comm ] ) ( Finset.sum_le_sum fun x hx => Finset.mem_filter.mp hx |>.2 ) |> le_trans <| Finset.sum_le_sum_of_subset <| Finset.filter_subset _ _

/-
Real-valued corollary of `markov_count`: with `d ≥ 1`, the count of
`f v ≥ d` is at most `(∑ f) / d`.
-/
theorem markov_count_div {V : Type*} [Fintype V] (f : V → ℕ) (d : ℕ) (hd : 1 ≤ d) :
    ((Finset.univ.filter (fun v => d ≤ f v)).card : ℝ) ≤ (∑ v, f v : ℝ) / d := by
  rw [ le_div_iff₀ ] <;> norm_cast;
  simpa [ mul_comm ] using! markov_count f d

/-
**Greedy red-`F` from a red `H` (combinatorial core of `eq:WHfree`).**
Let `F = K_{m 0,…,m (p+1)}` and let its first two classes be supplied by a red
copy of `H = K_{m 0, m 1}`: disjoint sets `S0` (size `m 0`), `S1` (size `m 1`)
with every cross pair red-adjacent.  Given reservoirs `W : Fin p → Finset V`,
pairwise disjoint and disjoint from `S0, S1`, with the richness condition
`hrich` — for each reservoir `W j` and each already-chosen set `U` of at most
`∑ m` vertices, at least `m (j+2)` vertices of `W j` are red-adjacent to all of
`S0`, all of `S1`, and all of `U` — the red graph `Gr` contains a copy of `F`.

This is exactly the greedy step the paper uses to derive a contradiction from a
red `H` inside a reservoir, establishing the `H`-freeness `eq:WHfree`.
-/
theorem red_F_from_red_H {V : Type*} [DecidableEq V] (Gr : SimpleGraph V)
    [DecidableRel Gr.Adj] (p : ℕ) (m : Fin (p + 2) → ℕ)
    (S0 S1 : Finset V) (hS0 : S0.card = m 0) (hS1 : S1.card = m 1)
    (hHdisj : Disjoint S0 S1)
    (hHred : ∀ u ∈ S0, ∀ v ∈ S1, Gr.Adj u v)
    (W : Fin p → Finset V)
    (hdisjW : ∀ i j, i ≠ j → Disjoint (W i) (W j))
    (hdisjS0W : ∀ j, Disjoint S0 (W j))
    (hdisjS1W : ∀ j, Disjoint S1 (W j))
    (hrich : ∀ (j : Fin p) (U : Finset V), U.card ≤ ∑ i, m i →
        m (j.succ.succ) ≤ ((W j).filter
          (fun v => (∀ s ∈ S0, Gr.Adj v s) ∧ (∀ s ∈ S1, Gr.Adj v s) ∧
            ∀ u ∈ U, Gr.Adj v u)).card) :
    Kmult (p + 2) m ⊑ Gr := by
  convert! greedy_multipartite_embedding_ordered Gr ( p + 2 ) m ( Fin.cons S0 ( Fin.cons S1 W ) ) _ _ using 1;
  · simp +decide [ Fin.forall_fin_succ, * ];
    exact ⟨ hHdisj.symm, fun i => ⟨ Disjoint.symm ( hdisjS0W i ), fun _ => Disjoint.symm ( hdisjS1W i ), fun j hij => hdisjW i j hij ⟩ ⟩;
  · intro j U hU hU';
    rcases j with ( _ | _ | j ) <;> simp_all +decide [  ];
    · convert! hS1.ge using 1;
      exact congr_arg Finset.card ( Finset.filter_true_of_mem fun v hv => fun u hu => SimpleGraph.Adj.symm ( hHred u ( hU u hu ) v hv ) );
    · convert! hrich ⟨ j, by linarith ⟩ U hU' |> le_trans <| Finset.card_mono _ using 1;
      simp +decide [ Fin.cons, Finset.subset_iff ];
      exact fun x hx hx' hx'' hx''' => ⟨ hx, hx''' ⟩

/-
**Ordered variant of `red_F_from_red_H`.**  Same as `red_F_from_red_H`, but the
richness hypothesis only needs to control already-chosen vertices `U` drawn from
the two fixed classes `S0, S1` or from *earlier* reservoirs `R k'` (`k' < k`).
This is the form the §9 obstruction-blocking argument needs (the slack estimate only
applies to vertices living in reservoirs / the fixed `H`).
-/
theorem red_F_from_red_H_ordered {V : Type*} [DecidableEq V] (Gr : SimpleGraph V)
    [DecidableRel Gr.Adj] (p : ℕ) (m : Fin (p + 2) → ℕ)
    (S0 S1 : Finset V) (hS0 : S0.card = m 0) (hS1 : S1.card = m 1)
    (hHdisj : Disjoint S0 S1)
    (hHred : ∀ u ∈ S0, ∀ v ∈ S1, Gr.Adj u v)
    (R : Fin p → Finset V)
    (hdisjR : ∀ i j, i ≠ j → Disjoint (R i) (R j))
    (hdisjS0R : ∀ j, Disjoint S0 (R j))
    (hdisjS1R : ∀ j, Disjoint S1 (R j))
    (hrich : ∀ (k : Fin p) (U : Finset V),
        (∀ u ∈ U, u ∈ S0 ∨ u ∈ S1 ∨ ∃ k', k' < k ∧ u ∈ R k') →
        U.card ≤ ∑ i, m i →
        m (k.succ.succ) ≤ ((R k).filter
          (fun v => (∀ s ∈ S0, Gr.Adj v s) ∧ (∀ s ∈ S1, Gr.Adj v s) ∧
            ∀ u ∈ U, Gr.Adj v u)).card) :
    Kmult (p + 2) m ⊑ Gr := by
  -- Apply the greedy multipartite embedding theorem with the given parameters.
  apply Erdos550.greedy_multipartite_embedding_ordered Gr;
  case C => exact Fin.cons S0 ( Fin.cons S1 R );
  · simp +decide [ Fin.forall_fin_succ, * ];
    exact ⟨ hHdisj.symm, fun i => ⟨ Disjoint.symm ( hdisjS0R i ), fun _ => Disjoint.symm ( hdisjS1R i ), fun j hij => hdisjR i j hij ⟩ ⟩;
  · intro j U hU hUcard;
    rcases j with ( _ | _ | j ) <;> simp +decide [  ] at *;
    · simp_all +decide [ Finset.eq_empty_of_forall_notMem hU ];
    · exact le_trans ( by simp +decide [ hS1 ] ) ( Finset.card_mono <| show S1 ⊆ { v ∈ S1 | ∀ u ∈ U, Gr.Adj v u } from fun v hv => Finset.mem_filter.mpr ⟨ hv, fun u hu => by have := hHred u ( hU u hu ) v hv; exact this.symm ⟩ );
    · convert! hrich ⟨ j, by linarith ⟩ U _ hUcard |> le_trans <| Finset.card_mono _;
      · intro u hu; specialize hU u hu; rcases hU with ⟨ i, hi, hi' ⟩ ; rcases i with ( _ | _ | i ) <;> simp +decide [  ] at hi hi' ⊢;
        · exact Or.inl hi';
        · exact Or.inr <| Or.inl hi';
        · exact Or.inr <| Or.inr <| ⟨ ⟨ i, by linarith ⟩, hi, hi' ⟩;
      · simp +decide [ Fin.cons, Finset.subset_iff ];
        exact fun x hx hx' hx'' hx''' => ⟨ hx, hx''' ⟩

/-
**Lower bound on the Turán edge count.**  `t_q(N) ≥ N²(q-1)/(2q) - q²`.
The error is a constant (independent of `N`), coming from the floor division and
the `(N % q)` correction terms in the exact formula.
-/
lemma turanEdges_ge (q N : ℕ) (hq : 1 ≤ q) :
    (N : ℝ) ^ 2 * (q - 1) / (2 * q) - (q : ℝ) ^ 2 ≤ (turanEdges q N : ℝ) := by
  rcases q with ( _ | _ | q ) <;> norm_num at *;
  · exact le_trans ( by norm_num ) ( Nat.cast_nonneg _ );
  · rw [ div_le_iff₀ ( by positivity ) ];
    have h_turan_edges : (turanEdges (q + 2) N : ℕ) ≥ (N^2 - (N % (q + 2))^2) * (q + 1) / (2 * (q + 2)) := by
      unfold turanEdges;
      rw [ SimpleGraph.card_edgeFinset_turanGraph ];
      exact Nat.le_add_right _ _;
    have h_turan_edges : (N^2 - (N % (q + 2))^2) * (q + 1) ≥ N^2 * (q + 1) - (q + 1)^3 := by
      have h_turan_edges : (N % (q + 2))^2 ≤ (q + 1)^2 := by
        exact Nat.pow_le_pow_left ( Nat.le_of_lt_succ ( Nat.mod_lt _ ( Nat.succ_pos _ ) ) ) _;
      rw [ tsub_mul ] ; exact Nat.sub_le_sub_left ( by nlinarith only [ h_turan_edges ] ) _;
    norm_cast;
    rw [ ge_iff_le, tsub_le_iff_right ] at h_turan_edges;
    nlinarith [ Nat.div_add_mod ( ( N ^ 2 - ( N % ( q + 2 ) ) ^ 2 ) * ( q + 1 ) ) ( 2 * ( q + 2 ) ), Nat.mod_lt ( ( N ^ 2 - ( N % ( q + 2 ) ) ^ 2 ) * ( q + 1 ) ) ( by positivity : 0 < 2 * ( q + 2 ) ) ]

/-
**Chromatic number of a complete multipartite graph.**  With all `k` parts
nonempty, `χ(K_{m 0,…,m (k-1)}) = k`.
-/
lemma chromaticNumber_Kmult (k : ℕ) (m : Fin k → ℕ) (hpos : ∀ i, 1 ≤ m i) :
    (Kmult k m).chromaticNumber = (k : ℕ∞) := by
  refine' le_antisymm ( SimpleGraph.chromaticNumber_le_iff_colorable.mpr _ ) ( _ );
  · use fun x => x.1;
    aesop;
  · refine' le_ciInf fun n => _;
    by_cases hn : n < k <;> simp_all +decide [  ];
    rintro ⟨ f, hf ⟩;
    have h_inj : Function.Injective (fun i : Fin k => f ⟨i, ⟨0, hpos i⟩⟩) := by
      intro i j hij; specialize @hf ⟨ i, ⟨ 0, hpos i ⟩ ⟩ ⟨ j, ⟨ 0, hpos j ⟩ ⟩ ; simp_all +decide [ Kmult ] ;
    exact absurd ( Fintype.card_le_of_injective _ h_inj ) ( by simpa )

/-
**Edge count vs colour-class cross pairs.**  For any `q`-colouring `c`, the
number of edges is at most the number of monochromatic edges plus the total
number of cross pairs `∑_{i<j} |c⁻¹ i| · |c⁻¹ j|`.
-/
lemma edges_le_mono_add_pairs {V : Type*} [Fintype V] [DecidableEq V]
    (Gr : SimpleGraph V) [DecidableRel Gr.Adj] (q : ℕ) (c : V → Fin q) :
    (Gr.edgeFinset.card : ℝ) ≤
      ((Gr.edgeFinset.filter (fun e => ∃ u v, e = s(u, v) ∧ c u = c v)).card : ℝ)
      + ∑ p ∈ Finset.univ.filter (fun p : Fin q × Fin q => p.1 < p.2),
          ((Finset.univ.filter (fun v => c v = p.1)).card : ℝ)
            * ((Finset.univ.filter (fun v => c v = p.2)).card : ℝ) := by
  refine' le_trans _ ( add_le_add_left _ _ );
  rotate_left;
  exact ↑ ( Gr.edgeFinset.card - ∑ p ∈ Finset.univ.filter ( fun p : Fin q × Fin q => p.1 < p.2 ), ( Finset.card ( Finset.filter ( fun v => c v = p.1 ) Finset.univ ) * Finset.card ( Finset.filter ( fun v => c v = p.2 ) Finset.univ ) ) );
  · refine' mod_cast Nat.sub_le_of_le_add _;
    refine' le_trans ( Finset.card_le_card _ ) _;
    exact Finset.image ( fun e => s(e.1, e.2) ) ( Finset.filter ( fun e => Gr.Adj e.1 e.2 ∧ c e.1 = c e.2 ) ( Finset.univ : Finset ( V × V ) ) ) ∪ Finset.biUnion ( Finset.univ.filter ( fun p : Fin q × Fin q => p.1 < p.2 ) ) ( fun p => Finset.image ( fun e => s(e.1, e.2) ) ( Finset.filter ( fun v => c v = p.1 ) Finset.univ ×ˢ Finset.filter ( fun v => c v = p.2 ) Finset.univ ) );
    · intro e he; simp_all +decide [  ] ;
      rcases e with ⟨ a, b ⟩ ; cases lt_trichotomy ( c a ) ( c b ) <;> aesop;
    · refine' le_trans ( Finset.card_union_le _ _ ) ( add_le_add _ _ );
      · refine' Finset.card_le_card _;
        simp +decide [ Finset.subset_iff ];
        rintro _ u v huv huv' rfl; exact ⟨ huv, u, v, rfl, huv' ⟩ ;
      · refine' le_trans ( Finset.card_biUnion_le ) _;
        exact Finset.sum_le_sum fun p hp => Finset.card_image_le.trans ( by rw [ Finset.card_product ] );
  · norm_cast;
    omega

/-- **Extraction of the two sides of a contained complete bipartite graph.**
If `K_{a,b} ⊑ Gr.induce Y` then there are disjoint `S0, S1 ⊆ Y` of sizes `a, b`
with every cross pair red-adjacent. -/
lemma bip_sides_res {V : Type*} [DecidableEq V] (Gr : SimpleGraph V)
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
**Reservoir `H`-freeness from cross-blue slack (`eq:WHfree`).**
If the reservoirs `W` are pairwise disjoint, the cross-blue degree of every
reservoir vertex into every other reservoir is at most `ζ`, every reservoir is
large enough (`(m 0 + m 1 + ∑ m)·ζ + ∑ m ≤ |W b|`), and the red graph has no
red `F = K_{m 0,…,m q}`, then no reservoir induces a red `H = K_{m 0, m 1}`.

Proof: if `W i` contained a red `H`, extract its two sides `S0, S1` via
`bip_sides_res`, then run `red_F_from_red_H_ordered` over the other `q-1`
reservoirs `R k = W (i.succAbove k)`.  The ordered richness for `R k` follows
from counting: the vertices of `R k` adjacent to all of `S0 ∪ S1 ∪ U` number at
least `|R k| − (m 0 + m 1 + ∑ m)·ζ ≥ ∑ m ≥ m (k+2)`, because every `w ∈ S0 ∪
S1 ∪ U` lives in a reservoir different from `R k` (so `hcross` bounds its blue
degree into `R k` by `ζ`).  This produces a red `F`, contradicting `hFfree`.
-/
lemma reservoir_H_free {V : Type*} [Fintype V] [DecidableEq V] (Gr : SimpleGraph V)
    [DecidableRel Gr.Adj] (q : ℕ) (hq : 2 ≤ q) (m : Fin (q + 1) → ℕ)
    (W : Fin q → Finset V)
    (hdisjW : ∀ a b, a ≠ b → Disjoint (W a) (W b))
    (ζ : ℕ)
    (hcross : ∀ a b, a ≠ b → ∀ w ∈ W a,
      ((W b).filter (fun v => ¬ Gr.Adj w v)).card ≤ ζ)
    (hWcard : ∀ b, (m 0 + m 1 + ∑ x, m x) * ζ + (∑ x, m x) ≤ (W b).card)
    (hFfree : ¬ (Kmult (q + 1) m ⊑ Gr)) :
    ∀ i, ¬ (Kbip (m 0) (m 1) ⊑ Gr.induce (↑(W i))) := by
  intro i hi
  obtain ⟨S0, S1, hS0, hS1, hHdisj, hHred⟩ : ∃ S0 S1 : Finset V, S0 ⊆ W i ∧ S1 ⊆ W i ∧ S0.card = m 0 ∧ S1.card = m 1 ∧ Disjoint S0 S1 ∧ ∀ u ∈ S0, ∀ v ∈ S1, Gr.Adj u v := by
    convert! bip_sides_res Gr ( m 0 ) ( m 1 ) ( W i ) hi;
  refine' hFfree _;
  -- Set R : Fin (q-1) → Finset V := fun k => W (i.succAbove k).
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := by
    exact Nat.exists_eq_succ_of_ne_zero ( ne_bot_of_gt hq )
  set R : Fin p → Finset V := fun k => W (i.succAbove k);
  apply red_F_from_red_H_ordered Gr p m S0 S1 hHdisj hHred.left hHred.right.left hHred.right.right R;
  · intro k l hkl; refine' hdisjW _ _ _; simp +decide [ hkl ] ;
  · exact fun k => Disjoint.mono_left hS0 ( hdisjW _ _ ( by simp +decide [  ] ) );
  · exact fun k => Disjoint.mono hS1 ( Finset.Subset.refl _ ) ( hdisjW _ _ ( by simp +decide [  ] ) );
  · intro k U hU hUcard
    have hB : (S0 ∪ S1 ∪ U).card ≤ (m 0 + m 1 + ∑ x, m x) := by
      grind;
    have h_filter_card : (R k \ Finset.biUnion (S0 ∪ S1 ∪ U) (fun w => Finset.filter (fun v => ¬Gr.Adj w v) (R k))).card ≥ m (Fin.succ (Fin.succ k)) := by
      have h_filter_card : (Finset.biUnion (S0 ∪ S1 ∪ U) (fun w => Finset.filter (fun v => ¬Gr.Adj w v) (R k))).card ≤ (m 0 + m 1 + ∑ x, m x) * ζ := by
        refine' le_trans ( Finset.card_biUnion_le ) _;
        refine' le_trans ( Finset.sum_le_sum fun x hx => show #({v ∈ R k | ¬Gr.Adj x v}) ≤ ζ from _ ) _;
        · convert! hcross _ _ _ x _ using 1;
          exact if hx0 : x ∈ S0 then i else if hx1 : x ∈ S1 then i else if hx2 : ∃ k' < k, x ∈ R k' then i.succAbove ( Classical.choose hx2 ) else i;
          · split_ifs <;> simp +decide [  ];
            exact ne_of_lt ( Classical.choose_spec ‹∃ k' < k, x ∈ R k'› |>.1 );
          · grind;
        · simpa using! Nat.mul_le_mul_right ζ hB;
      rw [ Finset.card_sdiff ];
      rw [ Finset.inter_eq_left.mpr ];
      · exact le_tsub_of_add_le_left ( by linarith [ hWcard ( Fin.succAbove i k ), Finset.single_le_sum ( fun a _ => Nat.zero_le ( m a ) ) ( Finset.mem_univ ( Fin.succ ( Fin.succ k ) ) ) ] );
      · exact Finset.biUnion_subset.mpr fun x hx => Finset.filter_subset _ _;
    refine' le_trans h_filter_card ( Finset.card_mono _ );
    intro v hv; by_cases h : ∃ a, ( a ∈ S0 ∨ a ∈ S1 ∨ a ∈ U ) ∧ ¬Gr.Adj a v <;> simp_all +decide [ SimpleGraph.adj_comm ] ;

/-
**Finset Markov inequality.**  `d · |{v ∈ A : d ≤ f v}| ≤ ∑_{v∈A} f v`.
-/
lemma markov_finset {V : Type*} [DecidableEq V] (A : Finset V) (f : V → ℕ) (d : ℕ) :
    d * (A.filter (fun v => d ≤ f v)).card ≤ ∑ v ∈ A, f v := by
  rw [ Finset.card_filter, mul_comm ];
  rw [ Finset.sum_mul _ _ _ ] ; exact Finset.sum_le_sum fun x hx => by split_ifs <;> linarith;

/-
**Monochromatic handshake.**  The sum over vertices of the number of
same-colour red-neighbours equals twice the number of monochromatic edges.
-/
lemma sum_monoDeg_eq {V : Type*} [Fintype V] [DecidableEq V] (Gr : SimpleGraph V)
    [DecidableRel Gr.Adj] (q : ℕ) (c : V → Fin q) :
    (∑ v, ((Finset.univ.filter (fun u => c u = c v ∧ Gr.Adj v u)).card : ℝ))
      = 2 * ((Gr.edgeFinset.filter (fun e => ∃ u v, e = s(u, v) ∧ c u = c v)).card : ℝ) := by
  convert! congr_arg ( ( ↑ ) : ℕ → ℝ ) ( SimpleGraph.sum_degrees_eq_twice_card_edges ( Gr ⊓ SimpleGraph.fromRel ( fun u v => c u = c v ) ) ) using 1;
  · simp +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset ];
    congr! 2;
    congr! 1;
    ext; aesop;
  · -- The edgeFinset of the intersection graph is equal to the set of edges in Gr that are also in the color relation.
    have h_edgeFinset : (Gr ⊓ SimpleGraph.fromRel (fun u v => c u = c v)).edgeFinset = {e ∈ Gr.edgeFinset | ∃ u v, e = s(u, v) ∧ c u = c v} := by
      ext e; simp [SimpleGraph.edgeSet];
      cases e ; aesop;
    simp +decide [  ];
    grind +suggestions

/-
**Cross-pair count.**  The sum over vertices of the number of
different-colour vertices equals `N² − ∑_i |c⁻¹ i|²`.
-/
lemma sum_crossAll_eq {V : Type*} [Fintype V] [DecidableEq V] (q : ℕ) (c : V → Fin q) :
    (∑ v, ((Finset.univ.filter (fun u => c u ≠ c v)).card : ℝ))
      = (Fintype.card V : ℝ) ^ 2
        - ∑ i, ((Finset.univ.filter (fun v => c v = i)).card : ℝ) ^ 2 := by
  have h_sum_sq : ∑ v, ((Finset.univ.filter fun u => c u = c v).card : ℝ) = ∑ i, ((Finset.univ.filter fun v => c v = i).card : ℝ) ^ 2 := by
    have h_sum_sq : ∑ v, ((Finset.univ.filter fun u => c u = c v).card : ℝ) = ∑ i, ∑ v ∈ Finset.univ.filter fun v => c v = i, ((Finset.univ.filter fun u => c u = i).card : ℝ) := by
      simp +decide only [sum_filter];
      rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop;
    simp_all +decide [ sq ];
  simp +decide [ ← h_sum_sq, Finset.filter_not, Finset.card_sdiff ];
  rw [ Finset.sum_congr rfl fun _ _ => Nat.cast_sub <| Finset.card_le_univ _ ] ; simp +decide [ sq ]

/-
**Cross-blue degree total.**  `∑_v |{u : c u ≠ c v ∧ ¬Gr.Adj v u}| = N² - ∑ s_i²
- 2 e(Gr) + 2 · (monochromatic edges)`.
-/
lemma sum_crossBlue_eq {V : Type*} [Fintype V] [DecidableEq V] (Gr : SimpleGraph V)
    [DecidableRel Gr.Adj] (q : ℕ) (c : V → Fin q) :
    (∑ v, ((Finset.univ.filter (fun u => c u ≠ c v ∧ ¬ Gr.Adj v u)).card : ℝ))
      = (Fintype.card V : ℝ) ^ 2
        - (∑ i, ((Finset.univ.filter (fun v => c v = i)).card : ℝ) ^ 2)
        - 2 * (Gr.edgeFinset.card : ℝ)
        + 2 * ((Gr.edgeFinset.filter (fun e => ∃ u v, e = s(u, v) ∧ c u = c v)).card : ℝ) := by
  have h_crossBlue_split : ∀ v, ((Finset.univ.filter (fun u => c u ≠ c v ∧ ¬Gr.Adj v u)).card : ℝ) = ((Finset.univ.filter (fun u => c u ≠ c v)).card : ℝ) - ((Finset.univ.filter (fun u => c u ≠ c v ∧ Gr.Adj v u)).card : ℝ) := by
    intro v; rw [ eq_sub_iff_add_eq' ] ; norm_cast; rw [ ← Finset.card_union_of_disjoint ] ; congr ; ext u ; by_cases hu : Gr.Adj v u <;> simp +decide [ hu ] ;
    exact Finset.disjoint_filter.mpr ( by aesop );
  have h_crossRed_split : ∀ v, ((Finset.univ.filter (fun u => c u ≠ c v ∧ Gr.Adj v u)).card : ℝ) = (Gr.degree v : ℝ) - ((Finset.univ.filter (fun u => c u = c v ∧ Gr.Adj v u)).card : ℝ) := by
    intro v
    simp [SimpleGraph.degree, SimpleGraph.neighborFinset];
    rw [ eq_sub_iff_add_eq ] ; norm_cast ; rw [ ← Finset.card_union_of_disjoint ] ; congr ; ext ; by_cases h : c ‹_› = c v <;> simp +decide [ h ] ;
    exact Finset.disjoint_filter.mpr ( by aesop );
  have h_crossRed_split : (∑ v, ((Finset.univ.filter (fun u => c u ≠ c v ∧ Gr.Adj v u)).card : ℝ)) = 2 * (Gr.edgeFinset.card : ℝ) - (∑ v, ((Finset.univ.filter (fun u => c u = c v ∧ Gr.Adj v u)).card : ℝ)) := by
    convert! Finset.sum_congr rfl fun v _ => h_crossRed_split v using 1;
    simp +decide [ ← Nat.cast_sum, SimpleGraph.sum_degrees_eq_twice_card_edges ];
  have := sum_crossAll_eq q c; have := sum_monoDeg_eq Gr q c; simp_all +decide [  ] ; ring;

/-
**Two-pass cleaning.**  For a `q`-colouring `c` and thresholds `τ₁, τ₂ ≥ 1`,
there are reservoirs `W i ⊆ c⁻¹ i` (pairwise disjoint) on which every vertex has
internal red degree `< τ₁` and cross-blue degree `< τ₂`, and the number of
deleted vertices in each class is at most the Markov bounds
`(∑ monoDeg)/τ₁ + (∑ crossBlueDeg)/τ₂`.
-/
lemma reservoir_cleaning {V : Type*} [Fintype V] [DecidableEq V] (Gr : SimpleGraph V)
    [DecidableRel Gr.Adj] (q : ℕ) (c : V → Fin q) (τ₁ τ₂ : ℕ)
    (hτ₁ : 1 ≤ τ₁) (hτ₂ : 1 ≤ τ₂) :
    ∃ W : Fin q → Finset V,
      (∀ i, W i ⊆ Finset.univ.filter (fun v => c v = i)) ∧
      (∀ i j, i ≠ j → Disjoint (W i) (W j)) ∧
      (∀ i, ∀ w ∈ W i, ((W i).filter (fun v => Gr.Adj w v)).card < τ₁) ∧
      (∀ i j, i ≠ j → ∀ w ∈ W i, ((W j).filter (fun v => ¬ Gr.Adj w v)).card < τ₂) ∧
      (∀ i, ((Finset.univ.filter (fun v => c v = i)).card : ℝ) - ((W i).card : ℝ) ≤
        (∑ v, ((Finset.univ.filter (fun u => c u = c v ∧ Gr.Adj v u)).card : ℝ)) / τ₁
          + (∑ v, ((Finset.univ.filter (fun u => c u ≠ c v ∧ ¬ Gr.Adj v u)).card : ℝ)) / τ₂) := by
  use fun i => Finset.filter ( fun v => ( Finset.univ.filter fun u => c u = i ∧ Gr.Adj u v ).card < τ₁ ∧ ( Finset.univ.filter fun u => c u ≠ i ∧ ¬Gr.Adj u v ).card < τ₂ ) ( Finset.univ.filter fun v => c v = i );
  refine' ⟨ _, _, _, _, _ ⟩;
  · exact fun i => Finset.filter_subset _ _;
  · simp +contextual [ Finset.disjoint_left ];
  · simp +contextual [ Finset.filter_filter ];
    intro i w hi h₁ h₂;
    refine' lt_of_le_of_lt ( Finset.card_le_card _ ) h₁;
    simp +contextual [ Finset.subset_iff, SimpleGraph.adj_comm ];
  · simp +contextual [  ];
    intro i j hij w hw₁ hw₂ hw₃; refine' lt_of_le_of_lt _ hw₃; simp +decide [ Finset.filter_filter ] ;
    refine' Finset.card_mono _ ; intro u hu ; simp_all +decide [ SimpleGraph.adj_comm ] ; aesop;
  · intro i
    have h_card_diff : (Finset.univ.filter (fun v => c v = i)).card - ((Finset.univ.filter (fun v => c v = i)).filter (fun v => (Finset.univ.filter (fun u => c u = i ∧ Gr.Adj u v)).card < τ₁ ∧ (Finset.univ.filter (fun u => c u ≠ i ∧ ¬Gr.Adj u v)).card < τ₂)).card ≤ ((Finset.univ.filter (fun v => c v = i)).filter (fun v => τ₁ ≤ (Finset.univ.filter (fun u => c u = i ∧ Gr.Adj u v)).card)).card + ((Finset.univ.filter (fun v => c v = i)).filter (fun v => τ₂ ≤ (Finset.univ.filter (fun u => c u ≠ i ∧ ¬Gr.Adj u v)).card)).card := by
      rw [ ← Finset.card_union_add_card_inter ];
      refine' le_trans _ ( Nat.le_add_right _ _ );
      rw [ tsub_le_iff_right ];
      refine' le_trans _ ( Finset.card_union_le _ _ );
      exact Finset.card_le_card fun x hx => by by_cases h₁ : τ₁ ≤ Finset.card ( Finset.filter ( fun u => c u = i ∧ Gr.Adj u x ) Finset.univ ) <;> by_cases h₂ : τ₂ ≤ Finset.card ( Finset.filter ( fun u => c u ≠ i ∧ ¬Gr.Adj u x ) Finset.univ ) <;> aesop;
    generalize_proofs at *; (
    refine' le_trans _ ( add_le_add ( markov_count_div _ _ hτ₁ ) ( markov_count_div _ _ hτ₂ ) );
    refine' le_trans _ ( add_le_add _ _ ) <;> norm_cast;
    rw [ Int.subNatNat_of_le ] <;> norm_cast;
    · refine' le_trans h_card_diff ( add_le_add _ _ ) <;> refine' Finset.card_mono _ <;> intro v hv <;> simp_all +decide [ SimpleGraph.adj_comm ] ;
    · grind)

/-
**Colour-class balance.**  If a `q`-colouring has few monochromatic edges and
the graph is near-Turán-dense, then every class size deviates from `N/q` by a
controlled amount: `(|c⁻¹ i| - N/q)² ≤ 2(q² + (δ+β)N²)`.
-/
lemma colour_balance {V : Type*} [Fintype V] [DecidableEq V] (Gr : SimpleGraph V)
    [DecidableRel Gr.Adj] (q : ℕ) (hq : 0 < q) (c : V → Fin q) (β δ : ℝ)
    (hmono : ((Gr.edgeFinset.filter (fun e => ∃ u v, e = s(u, v) ∧ c u = c v)).card : ℝ)
        ≤ β * (Fintype.card V) ^ 2)
    (hdens : (turanEdges q (Fintype.card V) : ℝ) - δ * (Fintype.card V) ^ 2
        ≤ Gr.edgeFinset.card) :
    ∀ i, (((Finset.univ.filter (fun v => c v = i)).card : ℝ) - (Fintype.card V : ℝ) / q) ^ 2
        ≤ 2 * ((q : ℝ) ^ 2 + (δ + β) * (Fintype.card V) ^ 2) := by
  have h_sum_sq_diff_bound : ∑ i : Fin q, ((Finset.univ.filter (fun v => c v = i)).card - (Fintype.card V : ℝ) / q) ^ 2 ≤ 2 * (q ^ 2 + (δ + β) * (Fintype.card V : ℝ) ^ 2) := by
    -- By deviation_identity, we have (N^2*(q-1)/q)/2 - ∑ p∈filter(p.1<p.2), s p.1 * s p.2 = (∑ i,(s i - (∑ s)/q)^2)/2.
    have h_deviation : ((Fintype.card V : ℝ) ^ 2 * (q - 1) / q) / 2 - (∑ p ∈ Finset.univ.filter (fun p : Fin q × Fin q => p.1 < p.2), ((Finset.univ.filter (fun v => c v = p.1)).card : ℝ) * ((Finset.univ.filter (fun v => c v = p.2)).card : ℝ)) = (∑ i : Fin q, ((Finset.univ.filter (fun v => c v = i)).card - (Fintype.card V : ℝ) / q) ^ 2) / 2 := by
      convert! deviation_identity hq ( fun i => ( Finset.card ( Finset.filter ( fun v => c v = i ) Finset.univ ) : ℝ ) ) using 1;
      · rw [ show ( ∑ i : Fin q, ( Finset.card ( Finset.filter ( fun v => c v = i ) Finset.univ ) : ℝ ) ) = Fintype.card V from ?_ ];
        rw_mod_cast [ ← Finset.card_biUnion ] ; congr ; ext i ; aesop;
        exact fun x _ y _ hxy => Finset.disjoint_left.mpr fun v hvx hvy => hxy <| by aesop;
      · rw [ show ( ∑ i : Fin q, ( Finset.card ( Finset.filter ( fun v => c v = i ) Finset.univ ) : ℝ ) ) = Fintype.card V from ?_ ];
        rw_mod_cast [ ← Finset.card_biUnion ] ; congr ; ext i ; aesop;
        exact fun x _ y _ hxy => Finset.disjoint_left.mpr fun v hvx hvy => hxy <| by aesop;
    -- By edges_le_mono_add_pairs, we have e ≤ mono + ∑ p∈filter(p.1<p.2), s p.1 * s p.2.
    have h_edges_le_mono_add_pairs : (Gr.edgeFinset.card : ℝ) ≤ ((Gr.edgeFinset.filter (fun e => ∃ u v, e = s(u, v) ∧ c u = c v)).card : ℝ) + (∑ p ∈ Finset.univ.filter (fun p : Fin q × Fin q => p.1 < p.2), ((Finset.univ.filter (fun v => c v = p.1)).card : ℝ) * ((Finset.univ.filter (fun v => c v = p.2)).card : ℝ)) := by
      convert! edges_le_mono_add_pairs Gr q c using 1;
    -- By turanEdges_ge, we have (N^2*(q-1)/q)/2 - q^2 ≤ turanEdges q N.
    have h_turanEdges_ge : ((Fintype.card V : ℝ) ^ 2 * (q - 1) / q) / 2 - q ^ 2 ≤ (turanEdges q (Fintype.card V) : ℝ) := by
      convert! turanEdges_ge q ( Fintype.card V ) hq using 1;
      ring;
    linarith;
  exact fun i => le_trans ( Finset.single_le_sum ( fun i _ => sq_nonneg ( ( Finset.card ( Finset.filter ( fun v => c v = i ) Finset.univ ) : ℝ ) - Fintype.card V / q ) ) ( Finset.mem_univ i ) ) h_sum_sq_diff_bound

/-
**Cross-blue degree total bound.**  Under the same hypotheses,
`∑_v |{u : c u ≠ c v ∧ ¬Gr.Adj v u}| ≤ 2 q² + 2(δ+β) N²`.
-/
lemma crossblue_total_bound {V : Type*} [Fintype V] [DecidableEq V] (Gr : SimpleGraph V)
    [DecidableRel Gr.Adj] (q : ℕ) (hq : 0 < q) (c : V → Fin q) (β δ : ℝ)
    (hmono : ((Gr.edgeFinset.filter (fun e => ∃ u v, e = s(u, v) ∧ c u = c v)).card : ℝ)
        ≤ β * (Fintype.card V) ^ 2)
    (hdens : (turanEdges q (Fintype.card V) : ℝ) - δ * (Fintype.card V) ^ 2
        ≤ Gr.edgeFinset.card) :
    (∑ v, ((Finset.univ.filter (fun u => c u ≠ c v ∧ ¬ Gr.Adj v u)).card : ℝ))
      ≤ 2 * (q : ℝ) ^ 2 + 2 * (δ + β) * (Fintype.card V) ^ 2 := by
  have h_identity : (∑ v, ((Finset.univ.filter (fun u => c u ≠ c v ∧ ¬ Gr.Adj v u)).card : ℝ)) = (Fintype.card V : ℝ) ^ 2
    - (∑ i, ((Finset.univ.filter (fun v => c v = i)).card : ℝ) ^ 2)
    - 2 * (Gr.edgeFinset.card : ℝ)
    + 2 * ((Gr.edgeFinset.filter (fun e => ∃ u v, e = s(u, v) ∧ c u = c v)).card : ℝ) := by
      convert! sum_crossBlue_eq Gr q c using 1;
  have h_identity : (∑ i, ((Finset.univ.filter (fun v => c v = i)).card : ℝ) ^ 2) ≥ (Fintype.card V : ℝ) ^ 2 / q := by
    have h_identity : (∑ i, ((Finset.univ.filter (fun v => c v = i)).card : ℝ)) = (Fintype.card V : ℝ) := by
      rw_mod_cast [ ← Finset.card_biUnion ] ; congr ; ext i ; aesop;
      exact fun x _ y _ hxy => Finset.disjoint_left.mpr fun z => by aesop;
    have h_identity : (∑ i : Fin q, ((Finset.univ.filter (fun v => c v = i)).card : ℝ) ^ 2) * q ≥ (∑ i : Fin q, ((Finset.univ.filter (fun v => c v = i)).card : ℝ)) ^ 2 := by
      have h_cauchy_schwarz : ∀ (u v : Fin q → ℝ), (∑ i, u i * v i) ^ 2 ≤ (∑ i, u i ^ 2) * (∑ i, v i ^ 2) := by
        exact fun u v => Finset.sum_mul_sq_le_sq_mul_sq univ u v;
      simpa [ mul_comm ] using! h_cauchy_schwarz ( fun i => ( Finset.card ( Finset.filter ( fun v => c v = i ) Finset.univ ) : ℝ ) ) ( fun _ => 1 );
    rw [ ge_iff_le, div_le_iff₀ ] <;> first | positivity | aesop;
  have := turanEdges_ge q ( Fintype.card V ) hq;
  rw [ div_sub', div_le_iff₀ ] at this <;> nlinarith [ show ( q : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ ( ( Fintype.card V : ℝ ) ^ 2 ) ( by positivity : ( q : ℝ ) ≠ 0 ) ]

/-
**Clean reservoir decomposition, parametric core.**  Given a `q`-colouring
`c` with few monochromatic edges (`mono ≤ β N²`), near-Turán density, no red `F`,
and thresholds `τ₁, τ₂` satisfying the explicit numeric smallness/largeness
conditions, the cleaned reservoirs satisfy the full conclusion.  The outer
theorem only has to *choose* `β, δ, N₀, τ₁, τ₂` to meet these conditions.
-/
set_option maxHeartbeats 1600000 in
lemma clean_reservoir_at {V : Type*} [Fintype V] [DecidableEq V] (Gr : SimpleGraph V)
    [DecidableRel Gr.Adj] (q : ℕ) (hq : 2 ≤ q) (m : Fin (q + 1) → ℕ) (η : ℝ)
    (β δ : ℝ) (_hβ : 0 ≤ β) (_hδ : 0 ≤ δ) (c : V → Fin q)
    (hmono_b : ((Gr.edgeFinset.filter (fun e => ∃ u v, e = s(u, v) ∧ c u = c v)).card : ℝ)
        ≤ β * (Fintype.card V) ^ 2)
    (hdens : (turanEdges q (Fintype.card V) : ℝ) - δ * (Fintype.card V) ^ 2
        ≤ Gr.edgeFinset.card)
    (hFfree : ¬ (Kmult (q + 1) m ⊑ Gr))
    (τ₁ τ₂ : ℕ) (hτ₁ : 1 ≤ τ₁) (hτ₂ : 1 ≤ τ₂)
    (hb1 : 2 * ((q : ℝ) ^ 2 + (δ + β) * (Fintype.card V) ^ 2)
        ≤ (η / 2 * ((Fintype.card V : ℝ) / q)) ^ 2)
    (hb2 : 2 * ((q : ℝ) ^ 2 + (δ + β) * (Fintype.card V) ^ 2)
        ≤ (((Fintype.card V : ℝ) / q) / 8) ^ 2)
    (hRM1 : (q : ℝ) * (2 * β * (Fintype.card V) ^ 2 / τ₁
          + (2 * (q : ℝ) ^ 2 + 2 * (δ + β) * (Fintype.card V) ^ 2) / τ₂)
        ≤ η / 2 * ((Fintype.card V : ℝ) / q))
    (hRM2 : (q : ℝ) * (2 * β * (Fintype.card V) ^ 2 / τ₁
          + (2 * (q : ℝ) ^ 2 + 2 * (δ + β) * (Fintype.card V) ^ 2) / τ₂)
        ≤ ((Fintype.card V : ℝ) / q) / 4)
    (hτ₁le : (τ₁ : ℝ) ≤ η * ((Fintype.card V : ℝ) / q))
    (hτ₂le : (τ₂ : ℝ) ≤ η * ((Fintype.card V : ℝ) / q))
    (hHfree_num : ((m 0 + m 1 + ∑ x, m x : ℕ) : ℝ) * τ₂ + ((∑ x, m x : ℕ) : ℝ)
        ≤ ((Fintype.card V : ℝ) / q) / 2) :
    ∃ W : Fin q → Finset V,
      (∀ i j, i ≠ j → Disjoint (W i) (W j)) ∧
      (let n : ℝ := (Fintype.card V : ℝ) / q;
        (∀ i, (1 - η) * n ≤ (W i).card ∧ ((W i).card : ℝ) ≤ (1 + η) * n) ∧
        (∀ i, ∀ w ∈ W i, (((W i).filter (fun v => Gr.Adj w v)).card : ℝ) ≤ η * n) ∧
        (∀ i j, i ≠ j → ∀ w ∈ W i,
          (((W j).filter (fun v => ¬ Gr.Adj w v)).card : ℝ) ≤ η * n) ∧
        (∀ i, ¬ (Kbip (m 0) (m 1) ⊑ Gr.induce (↑(W i)))) ∧
        ((Fintype.card V : ℝ) - ∑ i, (W i).card ≤ η * n)) := by
  obtain ⟨W, hW⟩ : ∃ W : Fin q → Finset V,
    (∀ i, W i ⊆ Finset.univ.filter (fun v => c v = i)) ∧
    (∀ i j, i ≠ j → Disjoint (W i) (W j)) ∧
    (∀ i, ∀ w ∈ W i, ((W i).filter (fun v => Gr.Adj w v)).card < τ₁) ∧
    (∀ i j, i ≠ j → ∀ w ∈ W i, ((W j).filter (fun v => ¬ Gr.Adj w v)).card < τ₂) ∧
    (∀ i, ((Finset.univ.filter (fun v => c v = i)).card : ℝ) - ((W i).card : ℝ) ≤
      (2 * β * (Fintype.card V) ^ 2 / τ₁ + (2 * q ^ 2 + 2 * (δ + β) * (Fintype.card V) ^ 2) / τ₂)) := by
        have := reservoir_cleaning Gr q c τ₁ τ₂ hτ₁ hτ₂;
        obtain ⟨ W, hW₁, hW₂, hW₃, hW₄, hW₅ ⟩ := this; use W; refine' ⟨ hW₁, hW₂, hW₃, hW₄, fun i => le_trans ( hW₅ i ) _ ⟩ ; gcongr;
        · have := sum_monoDeg_eq Gr q c;
          linarith;
        · convert! crossblue_total_bound Gr q ( by linarith ) c β δ hmono_b hdens using 1;
  refine' ⟨ W, hW.2.1, _, _, _, _, _ ⟩;
  · intro i
    have h_card_bound : |((Finset.univ.filter (fun v => c v = i)).card : ℝ) - (Fintype.card V : ℝ) / q| ≤ (η / 2) * (Fintype.card V : ℝ) / q := by
      have := colour_balance Gr q ( by linarith ) c β δ hmono_b hdens i;
      rw [ ← Real.sqrt_sq_eq_abs ];
      rw [ Real.sqrt_le_left ] <;> ring_nf at * <;> nlinarith [ inv_pos.mpr ( by positivity : 0 < ( q : ℝ ) ) ];
    constructor <;> ring_nf at * <;> norm_num at *;
    · have := hW.2.2.2.2 i;
      nlinarith [ abs_le.mp h_card_bound, show ( q : ℝ ) ≥ 2 by norm_cast, mul_inv_cancel₀ ( by positivity : ( q : ℝ ) ≠ 0 ), mul_inv_cancel₀ ( by positivity : ( q ^ 2 : ℝ ) ≠ 0 ), mul_inv_cancel₀ ( by positivity : ( τ₁ : ℝ ) ≠ 0 ), mul_inv_cancel₀ ( by positivity : ( τ₂ : ℝ ) ≠ 0 ) ];
    · have := hW.1 i;
      have := Finset.card_le_card this; norm_num at *;
      linarith [ abs_le.mp h_card_bound, show ( # ( W i ) : ℝ ) ≤ # { v | c v = i } from mod_cast this ];
  · exact fun i w hw => le_trans ( Nat.cast_le.mpr ( Nat.le_of_lt ( hW.2.2.1 i w hw ) ) ) hτ₁le;
  · exact fun i j hij w hw => le_trans ( Nat.cast_le.mpr ( Nat.le_of_lt ( hW.2.2.2.1 i j hij w hw ) ) ) hτ₂le;
  · convert! reservoir_H_free Gr q hq m W hW.2.1 τ₂ _ _ hFfree using 1;
    · exact fun i j hij w hw => Nat.le_of_lt ( hW.2.2.2.1 i j hij w hw );
    · intro i
      have h_card_Wi : (W i).card ≥ (Fintype.card V : ℝ) / q - (Fintype.card V : ℝ) / q / 4 := by
        have h_card_Wi : (Finset.univ.filter (fun v => c v = i)).card ≥ (Fintype.card V : ℝ) / q - (Fintype.card V : ℝ) / q / 8 := by
          have := colour_balance Gr q ( by linarith ) c β δ hmono_b hdens i;
          nlinarith [ show ( 0 : ℝ ) ≤ Fintype.card V / q by positivity ];
        have h_card_Wi : (Finset.univ.filter (fun v => c v = i)).card - (W i).card ≤ (2 * β * (Fintype.card V) ^ 2 / τ₁ + (2 * q ^ 2 + 2 * (δ + β) * (Fintype.card V) ^ 2) / τ₂) := by
          exact hW.2.2.2.2 i;
        nlinarith [ show ( q : ℝ ) ≥ 2 by norm_cast ];
      exact Nat.le_of_lt_succ ( by rw [ ← @Nat.cast_lt ℝ ] ; push_cast at *; nlinarith [ show ( q : ℝ ) ≥ 2 by norm_cast ] );
  · have h_sum_card : ∑ i, ((Finset.univ.filter (fun v => c v = i)).card : ℝ) = (Fintype.card V : ℝ) := by
      rw_mod_cast [ ← Finset.card_biUnion ];
      · convert! Finset.card_univ ; ext v ; simp +decide [ Finset.mem_biUnion ];
      · exact fun i _ j _ hij => Finset.disjoint_left.mpr fun x => by simp +contextual [ hij ] ;
    have := Finset.sum_le_sum fun i ( hi : i ∈ Finset.univ ) => hW.2.2.2.2 i;
    norm_num [ Finset.sum_add_distrib ] at *;
    linarith

/-- For `x ≥ 2`, the floor is at least `x/2`. -/
lemma half_le_floor (x : ℝ) (hx : 2 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have := Nat.sub_one_lt_floor x
  linarith

/-- Floor side-conditions for large `N`. -/
lemma crd_floor (q : ℕ) (hq : 1 ≤ q) (η rate : ℝ) (_hη : 0 < η)
    (hr0 : 0 < rate) (hr1 : rate ≤ η) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (let n : ℝ := (N : ℝ) / q;
        1 ≤ ⌊η * n⌋₊ ∧ 1 ≤ ⌊rate * n⌋₊ ∧ (⌊rate * n⌋₊ : ℝ) ≤ η * n) := by
  refine ⟨⌈(q:ℝ)/rate⌉₊, fun N hN => ?_⟩
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hN' : ((⌈(q:ℝ)/rate⌉₊ : ℝ)) ≤ N := by exact_mod_cast hN
  have hqr : (q:ℝ)/rate ≤ N := le_trans (Nat.le_ceil _) hN'
  have hNr : (q:ℝ) ≤ N * rate := by rw [div_le_iff₀ hr0] at hqr; linarith
  have hn0 : (0:ℝ) ≤ (N:ℝ)/q := by positivity
  have hrn : (1:ℝ) ≤ rate * ((N:ℝ)/q) := by
    rw [mul_div_assoc', le_div_iff₀ hq0]; nlinarith [hNr]
  have hηn : (1:ℝ) ≤ η * ((N:ℝ)/q) := le_trans hrn (by nlinarith [hr1, hn0])
  exact ⟨Nat.le_floor (by exact_mod_cast hηn), Nat.le_floor (by exact_mod_cast hrn),
    le_trans (Nat.floor_le (by positivity)) (by nlinarith [hr1, hn0])⟩

/-- Balance side-conditions for large `N`. -/
lemma crd_hb (q : ℕ) (hq : 1 ≤ q) (η s : ℝ) (hη : 0 < η)
    (hs1 : s ≤ η ^ 2 / (16 * (q : ℝ) ^ 2)) (hs2 : s ≤ 1 / (256 * (q : ℝ) ^ 2)) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (let n : ℝ := (N : ℝ) / q;
        2 * ((q : ℝ) ^ 2 + s * (N : ℝ) ^ 2) ≤ (η / 2 * n) ^ 2 ∧
        2 * ((q : ℝ) ^ 2 + s * (N : ℝ) ^ 2) ≤ (n / 8) ^ 2) := by
  refine ⟨⌈4*(q:ℝ)^2/η⌉₊ + ⌈16*(q:ℝ)^2⌉₊, fun N hN => ?_⟩
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hN1 : 4*(q:ℝ)^2/η ≤ N := le_trans (Nat.le_ceil _) (by exact_mod_cast (le_trans (Nat.le_add_right _ _) hN))
  have hN2 : 16*(q:ℝ)^2 ≤ N := le_trans (Nat.le_ceil _) (by exact_mod_cast (le_trans (Nat.le_add_left _ _) hN))
  have e1 : 4*(q:ℝ)^2 ≤ N * η := by rw [div_le_iff₀ hη] at hN1; linarith
  have hsq1 : s * (16 * (q:ℝ)^2) ≤ η^2 := by rw [le_div_iff₀ (by positivity)] at hs1; linarith
  have hsq2 : s * (256 * (q:ℝ)^2) ≤ 1 := by rw [le_div_iff₀ (by positivity)] at hs2; linarith
  have hexp1 : (η/2*((N:ℝ)/q))^2 = η^2 * N^2 / (4 * q^2) := by field_simp; ring
  have hexp2 : (((N:ℝ)/q)/8)^2 = N^2 / (64 * q^2) := by field_simp; ring
  refine ⟨?_, ?_⟩
  · show 2 * ((q : ℝ) ^ 2 + s * (N : ℝ) ^ 2) ≤ (η / 2 * ((N:ℝ)/q)) ^ 2
    rw [hexp1, le_div_iff₀ (by positivity)]
    nlinarith [hsq1, e1, hq0, mul_le_mul_of_nonneg_right hsq1 (sq_nonneg (N:ℝ))]
  · show 2 * ((q : ℝ) ^ 2 + s * (N : ℝ) ^ 2) ≤ (((N:ℝ)/q) / 8) ^ 2
    rw [hexp2, le_div_iff₀ (by positivity)]
    nlinarith [hsq2, hN2, hq0, mul_le_mul_of_nonneg_right hsq2 (sq_nonneg (N:ℝ))]

set_option maxHeartbeats 1200000 in
/-- Markov-removal side-conditions for large `N`. -/
lemma crd_RM (q : ℕ) (hq : 2 ≤ q) (η rate β s : ℝ) (hη : 0 < η)
    (hr0 : 0 < rate) (hr1 : rate ≤ η) (hβ : 0 ≤ β) (hs0 : 0 ≤ s)
    (hb1 : β ≤ η ^ 2 / (48 * (q : ℝ) ^ 3))
    (hb2 : β ≤ η / (48 * (q : ℝ) ^ 3))
    (hsb1 : s ≤ η * rate / (96 * (q : ℝ) ^ 3))
    (hsb2 : s ≤ rate / (192 * (q : ℝ) ^ 3)) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (let n : ℝ := (N : ℝ) / q;
        (q : ℝ) * (2 * β * (N : ℝ) ^ 2 / ⌊η * n⌋₊
            + (2 * (q : ℝ) ^ 2 + 2 * s * (N : ℝ) ^ 2) / ⌊rate * n⌋₊) ≤ η / 2 * n ∧
        (q : ℝ) * (2 * β * (N : ℝ) ^ 2 / ⌊η * n⌋₊
            + (2 * (q : ℝ) ^ 2 + 2 * s * (N : ℝ) ^ 2) / ⌊rate * n⌋₊) ≤ n / 4) := by
  have hq0 : (0:ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hb1' : 48*(q:ℝ)^3*β ≤ η^2 := by rw [le_div_iff₀ (by positivity)] at hb1; linarith
  have hb2' : 48*(q:ℝ)^3*β ≤ η := by rw [le_div_iff₀ (by positivity)] at hb2; linarith
  have hsb1' : 96*(q:ℝ)^3*s ≤ η*rate := by rw [le_div_iff₀ (by positivity)] at hsb1; linarith
  have hsb2' : 192*(q:ℝ)^3*s ≤ rate := by rw [le_div_iff₀ (by positivity)] at hsb2; linarith
  refine ⟨⌈2*(q:ℝ)/rate⌉₊ + ⌈24*(q:ℝ)^5/(η*rate)⌉₊ + ⌈48*(q:ℝ)^5/rate⌉₊ + 1, fun N hN => ?_⟩
  have hNpos : 0 < N := by omega
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hNpos
  have ht1 : 2*(q:ℝ)/rate ≤ N := le_trans (Nat.le_ceil _) (by exact_mod_cast (by omega : ⌈2*(q:ℝ)/rate⌉₊ ≤ N))
  have ht2 : 24*(q:ℝ)^5/(η*rate) ≤ N := le_trans (Nat.le_ceil _) (by exact_mod_cast (by omega : ⌈24*(q:ℝ)^5/(η*rate)⌉₊ ≤ N))
  have ht3 : 48*(q:ℝ)^5/rate ≤ N := le_trans (Nat.le_ceil _) (by exact_mod_cast (by omega : ⌈48*(q:ℝ)^5/rate⌉₊ ≤ N))
  have ht1' : 2*(q:ℝ) ≤ N*rate := by rw [div_le_iff₀ hr0] at ht1; linarith
  have ht2' : 24*(q:ℝ)^5 ≤ N*(η*rate) := by rw [div_le_iff₀ (by positivity)] at ht2; linarith
  have ht3' : 48*(q:ℝ)^5 ≤ N*rate := by rw [div_le_iff₀ hr0] at ht3; linarith
  have hNN : (N:ℝ) ≤ (N:ℝ)^2 := by nlinarith [hNR]
  set n : ℝ := (N:ℝ)/q with hn_def
  have hn0 : 0 < n := by rw [hn_def]; positivity
  have hrn : 2 ≤ rate * n := by rw [hn_def, mul_div_assoc', le_div_iff₀ hq0]; nlinarith [ht1']
  have hηn : 2 ≤ η * n := le_trans hrn (by nlinarith [hr1, hn0.le])
  have hτ₁ : η*n/2 ≤ (⌊η*n⌋₊:ℝ) := half_le_floor _ hηn
  have hτ₂ : rate*n/2 ≤ (⌊rate*n⌋₊:ℝ) := half_le_floor _ hrn
  have hA : 2*β*(N:ℝ)^2/(⌊η*n⌋₊:ℝ) ≤ 4*β*q*N/η := by
    have e : 2*β*(N:ℝ)^2/(η*n/2) = 4*β*q*N/η := by rw [hn_def]; field_simp; ring
    rw [← e]; gcongr
  have hB : (2*(q:ℝ)^2+2*s*(N:ℝ)^2)/(⌊rate*n⌋₊:ℝ) ≤ 4*q^3/(rate*N) + 4*s*q*N/rate := by
    have e : (2*(q:ℝ)^2+2*s*(N:ℝ)^2)/(rate*n/2) = 4*q^3/(rate*N) + 4*s*q*N/rate := by
      rw [hn_def]; field_simp; ring
    rw [← e]; gcongr
  have hT1 : 4*β*(q:ℝ)^2*N/η ≤ η*N/(6*q) := by
    rw [div_le_iff₀ hη, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]; nlinarith [hb1', hNR]
  have hT2 : 4*(q:ℝ)^4/(rate*N) ≤ η*N/(6*q) := by
    rw [div_le_iff₀ (by positivity), div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [ht2', mul_nonneg (mul_pos hη hr0).le (show (0:ℝ) ≤ (N:ℝ)^2 - N by linarith [hNN])]
  have hT3 : 4*s*(q:ℝ)^2*N/rate ≤ η*N/(6*q) := by
    rw [div_le_iff₀ hr0, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]; nlinarith [hsb1', hNR]
  have hU1 : 4*β*(q:ℝ)^2*N/η ≤ N/(12*q) := by
    rw [div_le_iff₀ hη, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]; nlinarith [hb2', hNR]
  have hU2 : 4*(q:ℝ)^4/(rate*N) ≤ N/(12*q) := by
    rw [div_le_iff₀ (by positivity), div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [ht3', mul_nonneg hr0.le (show (0:ℝ) ≤ (N:ℝ)^2 - N by linarith [hNN])]
  have hU3 : 4*s*(q:ℝ)^2*N/rate ≤ N/(12*q) := by
    rw [div_le_iff₀ hr0, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]; nlinarith [hsb2', hNR]
  have hABsum : (q:ℝ)*(2*β*(N:ℝ)^2/(⌊η*n⌋₊:ℝ) + (2*(q:ℝ)^2+2*s*(N:ℝ)^2)/(⌊rate*n⌋₊:ℝ))
      ≤ 4*β*(q:ℝ)^2*N/η + 4*(q:ℝ)^4/(rate*N) + 4*s*(q:ℝ)^2*N/rate := by
    have hdist : (q:ℝ)*(4*β*q*N/η + (4*q^3/(rate*N) + 4*s*q*N/rate))
        = 4*β*(q:ℝ)^2*N/η + 4*(q:ℝ)^4/(rate*N) + 4*s*(q:ℝ)^2*N/rate := by field_simp; ring
    calc (q:ℝ)*(2*β*(N:ℝ)^2/(⌊η*n⌋₊:ℝ) + (2*(q:ℝ)^2+2*s*(N:ℝ)^2)/(⌊rate*n⌋₊:ℝ))
        ≤ (q:ℝ)*(4*β*q*N/η + (4*q^3/(rate*N) + 4*s*q*N/rate)) := by
          apply mul_le_mul_of_nonneg_left _ hq0.le; linarith [hA, hB]
      _ = _ := hdist
  have e6 : η*(N:ℝ)/(6*q) + η*N/(6*q) + η*N/(6*q) = η/2*n := by rw [hn_def]; field_simp; ring
  have e12 : (N:ℝ)/(12*q) + N/(12*q) + N/(12*q) = n/4 := by rw [hn_def]; field_simp; ring
  have hf1 : 4*β*(q:ℝ)^2*N/η + 4*(q:ℝ)^4/(rate*N) + 4*s*(q:ℝ)^2*N/rate ≤ η/2*n := by
    linarith [hT1, hT2, hT3, e6]
  have hf2 : 4*β*(q:ℝ)^2*N/η + 4*(q:ℝ)^4/(rate*N) + 4*s*(q:ℝ)^2*N/rate ≤ n/4 := by
    linarith [hU1, hU2, hU3, e12]
  exact ⟨le_trans hABsum hf1, le_trans hABsum hf2⟩

/-- `H`-free side-condition for large `N`. -/
lemma crd_Hfree (q : ℕ) (hq : 1 ≤ q) (SM : ℕ) (hSM : 1 ≤ SM) (η rate : ℝ) (_hη : 0 < η)
    (hr0 : 0 < rate) (hr2 : rate ≤ 1 / (8 * ((SM : ℝ) + 1))) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (let n : ℝ := (N : ℝ) / q;
        (3 * (SM : ℝ)) * ⌊rate * n⌋₊ + (SM : ℝ) ≤ n / 2) := by
  refine ⟨⌈8*(SM:ℝ)*q⌉₊, fun N hN => ?_⟩
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hSM1 : (1:ℝ) ≤ SM := by exact_mod_cast hSM
  have hN' : 8*(SM:ℝ)*q ≤ N := le_trans (Nat.le_ceil _) (by exact_mod_cast hN)
  have hn8 : 8*(SM:ℝ) ≤ (N:ℝ)/q := by rw [le_div_iff₀ hq0]; linarith
  have hn0 : (0:ℝ) ≤ (N:ℝ)/q := by positivity
  have hfl : (⌊rate * ((N:ℝ)/q)⌋₊ : ℝ) ≤ rate * ((N:ℝ)/q) := Nat.floor_le (by positivity)
  have hrb : rate * ((N:ℝ)/q) ≤ (1/(8*((SM:ℝ)+1))) * ((N:ℝ)/q) := mul_le_mul_of_nonneg_right hr2 hn0
  have hfloor_b : (⌊rate * ((N:ℝ)/q)⌋₊ : ℝ) ≤ (1/(8*((SM:ℝ)+1))) * ((N:ℝ)/q) := le_trans hfl hrb
  have hc : (3*(SM:ℝ)) * (1/(8*((SM:ℝ)+1))) ≤ 3/8 := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]; nlinarith [hSM1]
  have h3 : (3*(SM:ℝ)) * ⌊rate * ((N:ℝ)/q)⌋₊ ≤ (3/8) * ((N:ℝ)/q) := by
    refine le_trans (mul_le_mul_of_nonneg_left hfloor_b (by positivity)) ?_
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hc hn0
  show (3 * (SM : ℝ)) * ⌊rate * ((N:ℝ)/q)⌋₊ + (SM : ℝ) ≤ ((N:ℝ)/q) / 2
  nlinarith [h3, hn8]

/- **Constant bookkeeping for the clean reservoir decomposition.**  Pure real/nat
arithmetic: there are `β, δ > 0` (with `δ ≤ δs`) and `N₀` such that, writing
`n := N/q`, `rate := min η (1/(8(SM+1)))`, `τ₁ := floor(η n)`, `τ₂ := floor(rate n)`,
all the smallness/largeness conditions required by `clean_reservoir_at` hold for
every `N ≥ N₀`. -/
set_option maxHeartbeats 2000000 in
lemma clean_reservoir_constants (q : ℕ) (hq : 2 ≤ q) (SM : ℕ) (hSM : 1 ≤ SM)
    (η : ℝ) (hη : 0 < η) :
    ∃ β : ℝ, 0 < β ∧ ∀ δs : ℝ, 0 < δs → ∃ δ : ℝ, 0 < δ ∧ δ ≤ δs ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (let n : ℝ := (N : ℝ) / q; let rate : ℝ := min η (1 / (8 * ((SM : ℝ) + 1)));
       let τ₁ : ℕ := ⌊η * n⌋₊; let τ₂ : ℕ := ⌊rate * n⌋₊;
        1 ≤ τ₁ ∧ 1 ≤ τ₂ ∧
        2 * ((q : ℝ) ^ 2 + (δ + β) * (N : ℝ) ^ 2) ≤ (η / 2 * n) ^ 2 ∧
        2 * ((q : ℝ) ^ 2 + (δ + β) * (N : ℝ) ^ 2) ≤ (n / 8) ^ 2 ∧
        (q : ℝ) * (2 * β * (N : ℝ) ^ 2 / τ₁
            + (2 * (q : ℝ) ^ 2 + 2 * (δ + β) * (N : ℝ) ^ 2) / τ₂) ≤ η / 2 * n ∧
        (q : ℝ) * (2 * β * (N : ℝ) ^ 2 / τ₁
            + (2 * (q : ℝ) ^ 2 + 2 * (δ + β) * (N : ℝ) ^ 2) / τ₂) ≤ n / 4 ∧
        (τ₂ : ℝ) ≤ η * n ∧
        (3 * (SM : ℝ)) * τ₂ + (SM : ℝ) ≤ n / 2) := by
  have hq0 : (0:ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  set rate : ℝ := min η (1 / (8 * ((SM : ℝ) + 1))) with hrate_def
  have hr0 : 0 < rate := lt_min hη (by positivity)
  have hr1 : rate ≤ η := min_le_left _ _
  have hr2 : rate ≤ 1 / (8 * ((SM : ℝ) + 1)) := min_le_right _ _
  set β : ℝ := min (η^2/(48*(q:ℝ)^3)) (min (η/(48*(q:ℝ)^3)) (min (η*rate/(192*(q:ℝ)^3))
      (min (rate/(384*(q:ℝ)^3)) (min (η^2/(32*(q:ℝ)^2)) (1/(512*(q:ℝ)^2)))))) with hβ_def
  have hβ1 : β ≤ η^2/(48*(q:ℝ)^3) := min_le_left _ _
  have hβ2 : β ≤ η/(48*(q:ℝ)^3) := le_trans (min_le_right _ _) (min_le_left _ _)
  have hβ3 : β ≤ η*rate/(192*(q:ℝ)^3) := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hβ4 : β ≤ rate/(384*(q:ℝ)^3) := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hβ5 : β ≤ η^2/(32*(q:ℝ)^2) := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hβ6 : β ≤ 1/(512*(q:ℝ)^2) := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
  have hβpos : 0 < β := by
    refine lt_min (by positivity) (lt_min (by positivity) (lt_min ?_ (lt_min ?_ (lt_min (by positivity) (by positivity)))))
    · exact div_pos (mul_pos hη hr0) (by positivity)
    · exact div_pos hr0 (by positivity)
  refine ⟨β, hβpos, fun δs hδs => ?_⟩
  set δ : ℝ := min δs β with hδ_def
  have hδpos : 0 < δ := lt_min hδs hβpos
  have hδle : δ ≤ δs := min_le_left _ _
  have hδβ : δ + β ≤ 2*β := by have : δ ≤ β := min_le_right _ _; linarith
  have hdβ0 : (0:ℝ) ≤ δ + β := by positivity
  have hs1pf : δ+β ≤ η^2/(16*(q:ℝ)^2) := by
    have k : (2:ℝ)*(η^2/(32*(q:ℝ)^2)) = η^2/(16*(q:ℝ)^2) := by ring
    rw [← k]; linarith [hδβ, hβ5]
  have hs2pf : δ+β ≤ 1/(256*(q:ℝ)^2) := by
    have k : (2:ℝ)*(1/(512*(q:ℝ)^2)) = 1/(256*(q:ℝ)^2) := by ring
    rw [← k]; linarith [hδβ, hβ6]
  have hsb1pf : δ+β ≤ η*rate/(96*(q:ℝ)^3) := by
    have k : (2:ℝ)*(η*rate/(192*(q:ℝ)^3)) = η*rate/(96*(q:ℝ)^3) := by ring
    rw [← k]; linarith [hδβ, hβ3]
  have hsb2pf : δ+β ≤ rate/(192*(q:ℝ)^3) := by
    have k : (2:ℝ)*(rate/(384*(q:ℝ)^3)) = rate/(192*(q:ℝ)^3) := by ring
    rw [← k]; linarith [hδβ, hβ4]
  obtain ⟨Nf, hf⟩ := crd_floor q (by omega) η rate hη hr0 hr1
  obtain ⟨Nhb, hhb⟩ := crd_hb q (by omega) η (δ+β) hη hs1pf hs2pf
  obtain ⟨Nrm, hrm⟩ := crd_RM q hq η rate β (δ+β) hη hr0 hr1 hβpos.le hdβ0 hβ1 hβ2 hsb1pf hsb2pf
  obtain ⟨NH, hH⟩ := crd_Hfree q (by omega) SM hSM η rate hη hr0 hr2
  refine ⟨δ, hδpos, hδle, max Nf (max Nhb (max Nrm NH)), fun N hN => ?_⟩
  have hNf : Nf ≤ N := le_trans (le_max_left _ _) hN
  have hNhb : Nhb ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNrm : Nrm ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_trans (le_max_right _ _) hN)
  have hNH : NH ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_trans (le_max_right _ _) hN)
  obtain ⟨hf1, hf2, hf3⟩ := hf N hNf
  obtain ⟨hhb1, hhb2⟩ := hhb N hNhb
  obtain ⟨hrm1, hrm2⟩ := hrm N hNrm
  have hH' := hH N hNH
  exact ⟨hf1, hf2, hhb1, hhb2, hrm1, hrm2, hf3, hH'⟩

/-- **Clean reservoir decomposition (Lemma `lem:reservoirs`), finitary form.**

Fix `q ≥ 2` and class sizes `m : Fin (q+1) → ℕ` (monotone, positive) for
`F = K_{m 0,…,m q}` and `H = K_{m 0, m 1}`.  For every tolerance `η > 0` there
are `δ > 0` and `N₀` such that the following holds.  Let `Gr` be a red graph on a
finite vertex set `V` of size `N ≥ N₀` with `n := ⌈N/q⌉`-scale, no red `F`
(`¬ Kmult (q+1) m ⊑ Gr`), and near-Turán red density
`(turanEdges q N : ℝ) − δ N² ≤ e(Gr)`.  Then there are pairwise-disjoint
reservoirs `W : Fin q → Finset V` with, writing `n := N / q`,

* `(1 - η) * n ≤ |W i|` and `|W i| ≤ (1 + η) * n`,
* red degree inside `W i` is `≤ η * n` for every `w ∈ W i`,
* cross blue degree `≤ η * n`: for `w ∈ W i`, `j ≠ i`,
  `|{v ∈ W j : ¬ Gr.Adj w v}| ≤ η * n`,
* `Gr.induce ↑(W i)` is `H`-free, and
* the remainder `|V ∖ ⋃ W i| ≤ η * n`.

The proof is assembled from `erdos_simonovits_stability`, `deviation_identity`,
`kovari_sos_turan`, the Markov cleaning lemma, and the greedy embedding
`red_F_from_first_class`. -/
theorem clean_reservoir_decomposition
    (q : ℕ) (hq : 2 ≤ q) (m : Fin (q + 1) → ℕ) (hmono : Monotone m)
    (hpos : 1 ≤ m 0) (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (Gr : SimpleGraph V) [DecidableRel Gr.Adj],
        N₀ ≤ Fintype.card V →
        ¬ (Kmult (q + 1) m ⊑ Gr) →
        (turanEdges q (Fintype.card V) : ℝ) - δ * (Fintype.card V) ^ 2 ≤ Gr.edgeFinset.card →
        ∃ W : Fin q → Finset V,
          (∀ i j, i ≠ j → Disjoint (W i) (W j)) ∧
          (let n : ℝ := (Fintype.card V : ℝ) / q;
            (∀ i, (1 - η) * n ≤ (W i).card ∧ ((W i).card : ℝ) ≤ (1 + η) * n) ∧
            (∀ i, ∀ w ∈ W i, (((W i).filter (fun v => Gr.Adj w v)).card : ℝ) ≤ η * n) ∧
            (∀ i j, i ≠ j → ∀ w ∈ W i,
              (((W j).filter (fun v => ¬ Gr.Adj w v)).card : ℝ) ≤ η * n) ∧
            (∀ i, ¬ (Kbip (m 0) (m 1) ⊑ Gr.induce (↑(W i)))) ∧
            ((Fintype.card V : ℝ) - ∑ i, (W i).card ≤ η * n)) := by
  classical
  have hpos' : ∀ i, 1 ≤ m i := fun i => le_trans hpos (hmono (Fin.zero_le i))
  have hSM' : 1 ≤ ∑ x, m x :=
    le_trans hpos (Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ 0))
  have hchi : (Kmult (q + 1) m).chromaticNumber = (q : ℕ∞) + 1 := by
    rw [chromaticNumber_Kmult (q + 1) m hpos']; push_cast; ring
  obtain ⟨β, hβpos, hcond⟩ := clean_reservoir_constants q hq (∑ x, m x) hSM' η hη
  obtain ⟨δs, hδspos, Ns, hstab⟩ :=
    erdos_simonovits_stability (Kmult (q + 1) m) q (by omega) hchi β hβpos
  obtain ⟨δ, hδpos, hδle, N₀c, hcondN⟩ := hcond δs hδspos
  refine ⟨δ, hδpos, max N₀c Ns, ?_⟩
  intro V _ _ Gr _ hN hFfree hedge
  have hNc : N₀c ≤ Fintype.card V := le_trans (le_max_left _ _) hN
  have hNs : Ns ≤ Fintype.card V := le_trans (le_max_right _ _) hN
  have hdens : (turanEdges q (Fintype.card V) : ℝ) - δs * (Fintype.card V) ^ 2
      ≤ Gr.edgeFinset.card := by
    have h : δ * (Fintype.card V : ℝ) ^ 2 ≤ δs * (Fintype.card V : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hδle (by positivity)
    linarith [hedge, h]
  obtain ⟨c, hmono_c⟩ := hstab Gr hNs hFfree hdens
  obtain ⟨h1, h2, hb1, hb2, hRM1, hRM2, hτ₂le, hHf⟩ := hcondN (Fintype.card V) hNc
  have hτ₁le : (⌊η * ((Fintype.card V : ℝ) / q)⌋₊ : ℝ) ≤ η * ((Fintype.card V : ℝ) / q) :=
    Nat.floor_le (by positivity)
  have hτ₂pos : (0:ℝ) ≤ (⌊min η (1 / (8 * (((∑ x, m x : ℕ) : ℝ) + 1))) * ((Fintype.card V : ℝ) / q)⌋₊ : ℝ) :=
    Nat.cast_nonneg _
  have hcast3 : ((m 0 + m 1 + ∑ x, m x : ℕ) : ℝ) ≤ 3 * ((∑ x, m x : ℕ) : ℝ) := by
    have a0 : m 0 ≤ ∑ x, m x := Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ 0)
    have a1 : m 1 ≤ ∑ x, m x := Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ 1)
    have hh : m 0 + m 1 + ∑ x, m x ≤ 3 * ∑ x, m x := by omega
    exact_mod_cast hh
  have hHfn : ((m 0 + m 1 + ∑ x, m x : ℕ) : ℝ)
        * (⌊min η (1 / (8 * (((∑ x, m x : ℕ) : ℝ) + 1))) * ((Fintype.card V : ℝ) / q)⌋₊ : ℝ)
      + ((∑ x, m x : ℕ) : ℝ) ≤ ((Fintype.card V : ℝ) / q) / 2 := by
    nlinarith [hHf, mul_le_mul_of_nonneg_right hcast3 hτ₂pos]
  exact clean_reservoir_at Gr q hq m η β δ hβpos.le hδpos.le c hmono_c hedge hFfree
    (⌊η * ((Fintype.card V : ℝ) / q)⌋₊)
    (⌊min η (1 / (8 * (((∑ x, m x : ℕ) : ℝ) + 1))) * ((Fintype.card V : ℝ) / q)⌋₊)
    h1 h2 hb1 hb2 hRM1 hRM2 hτ₁le hτ₂le hHfn

end Erdos550
