import Arxiv.Arxiv2411_18291.ExchangeSeedIntersections
import Arxiv.Arxiv2411_18291.Relabeling
import Mathlib.Algebra.Polynomial.Roots

/-!
# An exchange seed with small opposite-clique intersections

Translate degree-less-than-`r` polynomial evaluations by a polynomial of
degree exactly `r`. The difference between opposite cliques then has at
most `r` roots. Taking the translation to be the product of the factors
at the distinguished nodes preserves the required common edge.

The graph, both decomposition sizes, prime range, and edge bound are
unchanged. This strengthens the seed for the elimination applications.
-/

open Finset Polynomial
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V W : Type*} [DecidableEq V] [DecidableEq W] {q r : ℕ}

theorem IsCrossSimple.map {P N : Finset (Block V q)} (h : IsCrossSimple r P N) (f : V ↪ W) :
    IsCrossSimple r (mapGraph f P) (mapGraph f N) := by
  intro Q hQ R hR
  obtain ⟨Q₀, hQ₀, rfl⟩ := (mem_mapGraph _ _ _).mp hQ
  obtain ⟨R₀, hR₀, rfl⟩ := (mem_mapGraph _ _ _).mp hR
  change (Q₀.val.map f ∩ R₀.val.map f).card ≤ r
  rw [← map_inter, card_map]
  exact h Q₀ hQ₀ R₀ hR₀

omit [DecidableEq W] in
theorem IsCrossSimple.disjoint {P N : Finset (Block V q)} (h : IsCrossSimple r P N)
    (hqr : r < q) : Disjoint P N := by
  apply disjoint_left.mpr
  intro Q hQP hQN
  have hc := h Q hQP Q hQN
  rw [inter_self, Q.property] at hc
  omega

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem polynomialDecompositions_crossSimple (y : Fin q → F) (hy : Function.Injective y)
    (w : F[X]) (hw : w.degree = r) :
    IsCrossSimple r (polynomialDecomposition r y 0)
      (polynomialDecomposition r y (fun i => w.eval (y i))) := by
  intro P hP Q hQ
  obtain ⟨f, hf, rfl⟩ := (mem_polynomialDecomposition _ _ _).mp hP
  obtain ⟨g, hg, rfl⟩ := (mem_polynomialDecomposition _ _ _).mp hQ
  simp only [Pi.zero_apply, zero_add]
  let T := (graphClique (fun i => f.eval (y i))).val ∩
    (graphClique (fun i => w.eval (y i) + g.eval (y i))).val
  let p := f - (w + g)
  have hwg : (w + g).degree = r := by
    rw [degree_add_eq_left_of_degree_lt (hw ▸ hg), hw]
  have hpdeg : p.degree = r := by
    rw [degree_sub_eq_right_of_degree_lt (hwg ▸ hf), hwg]
  have hpne : p ≠ 0 := by
    intro hp
    rw [hp, degree_zero] at hpdeg
    exact WithBot.bot_ne_coe hpdeg
  have hpn : p.natDegree = r := natDegree_eq_of_degree_eq_some hpdeg
  change T.card ≤ r
  by_contra hcard
  have hnodes : Function.Injective (fun a : T => y a.val.1) := by
    intro a b hab
    have hab' : a.val.1 = b.val.1 := hy hab
    apply Subtype.ext
    apply Prod.ext hab'
    have ha := (mem_graphClique _ a.val.1 a.val.2).mp (mem_inter.mp a.property).1
    have hb := (mem_graphClique _ b.val.1 b.val.2).mp (mem_inter.mp b.property).1
    exact ha.trans ((congrArg (fun i => f.eval (y i)) hab').trans hb.symm)
  have heval (a : T) : p.eval (y a.val.1) = 0 := by
    have ha := (mem_graphClique _ a.val.1 a.val.2).mp (mem_inter.mp a.property).1
    have hb := (mem_graphClique _ a.val.1 a.val.2).mp (mem_inter.mp a.property).2
    simp only [p, eval_sub, eval_add]
    exact sub_eq_zero.mpr (ha.symm.trans hb)
  exact hpne (eq_zero_of_natDegree_lt_card_of_eval_eq_zero p hnodes heval (by
    rw [hpn, Fintype.card_coe]
    omega))

omit [Fintype F] [DecidableEq F] in
def exchangePolynomial (y : Fin q → F) (I : Block (Fin q) r) : F[X] :=
  ∏ i ∈ I.val, (X - C (y i))

omit [Fintype F] [DecidableEq F] in
theorem exchangePolynomial_degree (y : Fin q → F) (I : Block (Fin q) r) :
    (exchangePolynomial y I).degree = r := by
  unfold exchangePolynomial
  rw [degree_eq_natDegree (monic_prod_X_sub_C y I.val).ne_zero]
  simp only [natDegree_finsetProd_X_sub_C_eq_card, I.property]

omit [Fintype F] [DecidableEq F] in
theorem exchangePolynomial_eval_zero_iff (y : Fin q → F) (hy : Function.Injective y)
    (I : Block (Fin q) r) (i : Fin q) : (exchangePolynomial y I).eval (y i) = 0 ↔ i ∈ I.val := by
  simp only [exchangePolynomial, eval_prod, eval_sub, eval_X, eval_C, prod_eq_zero_iff,
    sub_eq_zero, hy.eq_iff]
  constructor
  · rintro ⟨j, hj, hij⟩
    exact hij ▸ hj
  · intro hi
    exact ⟨i, hi, rfl⟩

omit [Fintype F] in
theorem polynomial_exchange_vertex_inter (y : Fin q → F) (hy : Function.Injective y)
    (I : Block (Fin q) r) :
    (graphClique (fun _ : Fin q => (0 : F))).val ∩
      (graphClique (fun i => (exchangePolynomial y I).eval (y i))).val =
        (exchangeEdge (F := F) I).val := by
  ext ⟨i, x⟩
  simp only [mem_inter, mem_graphClique, mem_exchangeEdge]
  constructor
  · rintro ⟨hx, hxp⟩
    exact ⟨(exchangePolynomial_eval_zero_iff y hy I i).mp (hxp.symm.trans hx), hx⟩
  · rintro ⟨hi, hx⟩
    exact ⟨hx, hx.trans ((exchangePolynomial_eval_zero_iff y hy I i).mpr hi).symm⟩

def polynomialExchangeSeed (y : Fin q → F) (hy : Function.Injective y)
    (hqr : r < q) (I : Block (Fin q) r) : ExchangeSeed (Fin q × F) q r where
  graph := partiteGraph F q r
  positive := polynomialDecomposition r y 0
  negative := polynomialDecomposition r y (fun i => (exchangePolynomial y I).eval (y i))
  positive_decomposition := polynomialDecomposition_isDecomposition y 0 hy
  negative_decomposition := polynomialDecomposition_isDecomposition y _ hy
  disjoint := (polynomialDecompositions_crossSimple y hy _
    (exchangePolynomial_degree y I)).disjoint hqr
  positiveClique := graphClique (fun _ => 0)
  negativeClique := graphClique (fun i => (exchangePolynomial y I).eval (y i))
  commonEdge := exchangeEdge I
  positive_mem := by
    apply (mem_polynomialDecomposition _ _ _).mpr
    exact ⟨0, by simp, by simp⟩
  negative_mem := by
    apply (mem_polynomialDecomposition _ _ _).mpr
    exact ⟨0, by simp, by simp⟩
  vertex_inter := polynomial_exchange_vertex_inter y hy I

theorem polynomialExchangeSeed_crossSimple (y : Fin q → F) (hy : Function.Injective y)
    (hqr : r < q) (I : Block (Fin q) r) :
    IsCrossSimple r (polynomialExchangeSeed y hy hqr I).positive
      (polynomialExchangeSeed y hy hqr I).negative :=
  polynomialDecompositions_crossSimple y hy _ (exchangePolynomial_degree y I)

theorem exists_prime_crossSimple_exchange_seed (q r : ℕ) (hqr : r < q) :
    ∃ p : ℕ, ∃ hp : p.Prime, q ≤ p ∧ p ≤ 2 * q ∧
      (letI : Fact p.Prime := ⟨hp⟩
       ∃ E : ExchangeSeed (Fin q × ZMod p) q r,
         E.graph.card = p ^ r * q.choose r ∧ E.graph.card ≤ (2 * q) ^ r * q.choose r ∧
         IsCrossSimple r E.positive E.negative) := by
  obtain ⟨p, hp, hqp, hpq⟩ := Nat.exists_prime_lt_and_le_two_mul q (by omega)
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨y⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin q) (β := ZMod p) (by simpa using hqp.le)
  obtain ⟨I, _, hI⟩ := exists_subset_card_eq
    (s := (univ : Finset (Fin q))) (n := r) (by simpa using hqr.le)
  let E := polynomialExchangeSeed y y.injective hqr ⟨I, hI⟩
  have hcard : E.graph.card = p ^ r * q.choose r := by
    simpa [E, polynomialExchangeSeed] using card_partiteGraph y y.injective hqr.le
  refine ⟨p, hp, hqp.le, hpq, E, hcard, ?_, polynomialExchangeSeed_crossSimple _ _ _ _⟩
  rw [hcard]
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hpq r)

end Arxiv2411_18291
