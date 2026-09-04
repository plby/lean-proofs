import Mathlib
import ErdosProblems.Erdos550.Basic
import ErdosProblems.Erdos550.GreedyEmbedding

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Blocker-hypergraph greedy extraction (§9 combinatorial core)

The paper's blocker section (§9) proves three facts — the reservoir
`H`-freeness claim (`lem:reservoirs`), `a`-set separation (`lem:asetblock`),
and obstruction blocking (`lem:obstructionblock`) — all by the *same* greedy
construction: take a distinguished "first class" `S` (an `a`-set, resp. a
obstruction, resp. a red `H`) and extend it to a red copy of the complete
multipartite graph `F = K_{m₀,…,m_q}` by greedily choosing the remaining `q`
classes from the reservoirs `W₀,…,W_{q-1}`, each new class consisting of
vertices red-adjacent to `S` and to everything chosen so far.

This file records that common extraction step, `red_F_from_first_class`, as a
clean finite consequence of the ordered greedy embedding
`greedy_multipartite_embedding_ordered`.  The hypothesis `hrich` is exactly the
quantitative richness the paper verifies in each of the three applications
("the next reservoir contains at least `δn − o(n)` candidates red-adjacent to
all previously selected vertices and to every vertex of `S`, which exceeds the
required class size").
-/

open SimpleGraph Finset

namespace Erdos550

variable {V : Type*}

/-
**Greedy red-`F` from a distinguished first class.**  Let `F = K_{m₀,…,m_q}`.
Given a first class `S` with `|S| = m₀`, pairwise-disjoint reservoirs
`W₀,…,W_{q-1}` disjoint from `S`, and the richness condition `hrich` — for each
reservoir `W j` and every already-chosen set `U` of at most `∑ m` vertices, at
least `m_{j+1}` vertices of `W j` are red-adjacent both to all of `S` and to all
of `U` — the graph `Gr` contains a copy of `F`.

This is the single combinatorial engine behind the paper's reservoir
`H`-freeness claim and the `a`-set–separation and obstruction-blocking lemmas.
-/
theorem red_F_from_first_class [DecidableEq V] (Gr : SimpleGraph V)
    [DecidableRel Gr.Adj] (q : ℕ) (m : Fin (q + 1) → ℕ)
    (S : Finset V) (hS : S.card = m 0)
    (W : Fin q → Finset V)
    (hdisjW : ∀ i j, i ≠ j → Disjoint (W i) (W j))
    (hdisjSW : ∀ j, Disjoint S (W j))
    (hrich : ∀ (j : Fin q) (U : Finset V), U.card ≤ ∑ i, m i →
        m j.succ ≤ ((W j).filter
          (fun v => (∀ s ∈ S, Gr.Adj v s) ∧ ∀ u ∈ U, Gr.Adj v u)).card) :
    Kmult (q + 1) m ⊑ Gr := by
  convert! greedy_multipartite_embedding_ordered Gr ( q + 1 ) m ( Fin.cons S W ) _ _ using 1;
  · simp +decide only [ne_eq];
    exact fun i => ⟨ Disjoint.symm ( hdisjSW i ), fun j hij => hdisjW i j hij ⟩;
  · rintro ( _ | j ) U hU hU' <;> simp_all +decide;
    refine' le_trans ( hrich ⟨ j, by linarith ⟩ U hU' ) _;
    exact Finset.card_le_card fun x hx => by aesop;

end Erdos550
