import Arxiv.Arxiv2411_18291.PolynomialDecomposition
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# The finite-field seed for clique exchange

The graph `Ω₀` of Section 3 has two disjoint clique decompositions, with
distinguished cliques intersecting in exactly one edge. The full exchange
configuration `Ω` requires the subsequent gluing construction as well.
-/

open Finset Polynomial

noncomputable section

namespace Arxiv2411_18291

/-- Initial data for the gluing construction, including its actual two
decompositions and distinguished common edge. -/
structure ExchangeSeed (V : Type*) [Fintype V] [DecidableEq V] (q r : ℕ) where
  graph : Hypergraph V r
  positive : Finset (Block V q)
  negative : Finset (Block V q)
  positive_decomposition : IsDecomposition graph positive
  negative_decomposition : IsDecomposition graph negative
  disjoint : Disjoint positive negative
  positiveClique : Block V q
  negativeClique : Block V q
  commonEdge : Block V r
  positive_mem : positiveClique ∈ positive
  negative_mem : negativeClique ∈ negative
  vertex_inter : positiveClique.val ∩ negativeClique.val = commonEdge.val

theorem ExchangeSeed.edge_inter {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}
    (E : ExchangeSeed V q r) :
    cliqueEdges r E.positiveClique ∩ cliqueEdges r E.negativeClique = {E.commonEdge} :=
  cliqueEdges_inter_eq_singleton _ _ _ E.vertex_inter

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {q r : ℕ}

/-- Zero on the distinguished `r` parts and one on all other parts. -/
def exchangeShift (I : Block (Fin q) r) (i : Fin q) : F := if i ∈ I.val then 0 else 1

/-- The all-zero edge in the distinguished `r` parts. -/
def exchangeEdge (I : Block (Fin q) r) : Block (Fin q × F) r :=
  ⟨I.val.map ⟨fun i => (i, (0 : F)), fun _ _ h => congrArg Prod.fst h⟩,
    by simpa using I.property⟩

omit [Fintype F] [DecidableEq F] in
@[simp] theorem mem_exchangeEdge (I : Block (Fin q) r) (i : Fin q) (x : F) :
    (i, x) ∈ (exchangeEdge (F := F) I).val ↔ i ∈ I.val ∧ x = 0 := by
  simp only [exchangeEdge, mem_map]
  constructor
  · rintro ⟨j, hj, h⟩
    have hji : j = i := congrArg Prod.fst h
    subst j
    exact ⟨hj, (congrArg Prod.snd h).symm⟩
  · rintro ⟨hi, rfl⟩
    exact ⟨i, hi, rfl⟩

omit [Fintype F] in
theorem exchange_vertex_inter (I : Block (Fin q) r) :
    (graphClique (fun _ : Fin q => (0 : F))).val ∩
        (graphClique (exchangeShift (F := F) I)).val = (exchangeEdge (F := F) I).val := by
  ext ⟨i, x⟩
  simp only [mem_inter, mem_graphClique, mem_exchangeEdge]
  by_cases hi : i ∈ I.val
  · simp [exchangeShift, hi]
  · simp only [exchangeShift, hi, false_and, iff_false, not_and]
    intro hx0 hx1
    exact zero_ne_one (hx0.symm.trans hx1)

theorem polynomialDecompositions_disjoint (y : Fin q → F) (hy : Function.Injective y)
    (hqr : r < q) (I : Block (Fin q) r) :
    Disjoint (polynomialDecomposition r y 0)
      (polynomialDecomposition r y (exchangeShift (F := F) I)) := by
  apply Finset.disjoint_left.mpr
  intro Q hQp hQn
  obtain ⟨f, hf, hQf⟩ := (mem_polynomialDecomposition y 0 Q).mp hQp
  obtain ⟨g, hg, hQg⟩ := (mem_polynomialDecomposition y (exchangeShift I) Q).mp hQn
  have hfun := graphClique_injective (hQf.symm.trans hQg)
  have hfg : f = g := by
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq I.val hy.injOn
      (by simpa only [I.property] using hf) (by simpa only [I.property] using hg)
    intro i hi
    simpa [exchangeShift, hi] using congrFun hfun i
  obtain ⟨i, _, hi⟩ := exists_mem_notMem_of_card_lt_card
    (s := I.val) (t := univ) (by simpa only [I.property, card_univ, Fintype.card_fin] using hqr)
  have h := congrFun hfun i
  rw [hfg] at h
  simp [exchangeShift, hi] at h

/-- Construct the seed over any finite field with `q` distinct nodes. -/
def fieldExchangeSeed (y : Fin q → F) (hy : Function.Injective y)
    (hqr : r < q) (I : Block (Fin q) r) : ExchangeSeed (Fin q × F) q r where
  graph := partiteGraph F q r
  positive := polynomialDecomposition r y 0
  negative := polynomialDecomposition r y (exchangeShift I)
  positive_decomposition := polynomialDecomposition_isDecomposition y 0 hy
  negative_decomposition := polynomialDecomposition_isDecomposition y (exchangeShift I) hy
  disjoint := polynomialDecompositions_disjoint y hy hqr I
  positiveClique := graphClique (fun _ => 0)
  negativeClique := graphClique (exchangeShift I)
  commonEdge := exchangeEdge I
  positive_mem := by
    apply (mem_polynomialDecomposition y 0 _).mpr
    refine ⟨0, by simp, ?_⟩
    simp
  negative_mem := by
    apply (mem_polynomialDecomposition y (exchangeShift I) _).mpr
    refine ⟨0, by simp, ?_⟩
    simp
  vertex_inter := exchange_vertex_inter I

theorem fieldExchangeSeed_card (y : Fin q → F) (hy : Function.Injective y)
    (hqr : r < q) (I : Block (Fin q) r) :
    (fieldExchangeSeed y hy hqr I).graph.card = Fintype.card F ^ r * q.choose r :=
  card_partiteGraph y hy hqr.le

/-- The paper's seed exists with a prime part size in `[q,2q]` and at most
`(2q)^r * choose(q,r)` edges. This theorem constructs the field, both
decompositions, and their distinguished cliques without additional hypotheses. -/
theorem exists_prime_exchange_seed (q r : ℕ) (hqr : r < q) :
    ∃ p : ℕ, ∃ hp : p.Prime, q ≤ p ∧ p ≤ 2 * q ∧
      (letI : Fact p.Prime := ⟨hp⟩
       ∃ E : ExchangeSeed (Fin q × ZMod p) q r,
         E.graph.card = p ^ r * q.choose r ∧ E.graph.card ≤ (2 * q) ^ r * q.choose r) := by
  obtain ⟨p, hp, hqp, hpq⟩ := Nat.exists_prime_lt_and_le_two_mul q (by omega)
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨y⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin q) (β := ZMod p) (by simpa using hqp.le)
  obtain ⟨I, _, hI⟩ := exists_subset_card_eq
    (s := (univ : Finset (Fin q))) (n := r) (by simpa using hqr.le)
  refine ⟨p, hp, hqp.le, hpq, fieldExchangeSeed y y.injective hqr ⟨I, hI⟩, ?_, ?_⟩
  · simpa using fieldExchangeSeed_card y y.injective hqr ⟨I, hI⟩
  · rw [fieldExchangeSeed_card]
    simp only [ZMod.card]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hpq r)

end Arxiv2411_18291
