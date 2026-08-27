import Arxiv.Arxiv2411_18291.Partite
import Mathlib.LinearAlgebra.Lagrange

/-!
# Polynomial decompositions of the complete partite hypergraph

The finite-field construction in the proof of `lem:OO` (Section 3).
Lagrange interpolation is the inverse of the Vandermonde evaluation map
used in the paper. A fixed translation of all evaluation vectors gives
another decomposition of the same graph.
-/

open scoped BigOperators
open Finset Polynomial

noncomputable section

namespace Arxiv2411_18291

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {q r : ℕ}

/-- Evaluate the polynomial with coefficient vector `u` at the chosen nodes,
then translate coordinate `i` by `w i`. -/
def polynomialClique (r : ℕ) (y w : Fin q → F) (u : Fin r → F) :
    Block (Fin q × F) q :=
  graphClique fun i => w i + (((degreeLTEquiv F r).symm u).val).eval (y i)

/-- All shifted polynomial cliques of degree less than `r`. -/
def polynomialDecomposition (r : ℕ) (y w : Fin q → F) : Finset (Block (Fin q × F) q) :=
  univ.image (polynomialClique r y w)

theorem mem_polynomialDecomposition (y w : Fin q → F) (Q : Block (Fin q × F) q) :
    Q ∈ polynomialDecomposition r y w ↔
      ∃ f : F[X], f.degree < r ∧ Q = graphClique (fun i => w i + f.eval (y i)) := by
  simp only [polynomialDecomposition, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨((degreeLTEquiv F r).symm u).val,
      mem_degreeLT.mp ((degreeLTEquiv F r).symm u).property, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    refine ⟨degreeLTEquiv F r ⟨f, mem_degreeLT.mpr hf⟩, ?_⟩
    simp [polynomialClique]

theorem polynomialDecomposition_unique (y w : Fin q → F) (hy : Function.Injective y)
    (e : Block (Fin q × F) r) (he : e ∈ partiteGraph F q r) :
    ∃! Q, Q ∈ polynomialDecomposition r y w ∧ e.val ⊆ Q.val := by
  have heinj := (mem_partiteGraph e).mp he
  have hnodes : Set.InjOn (fun a : Fin q × F => y a.1) (e.val : Set (Fin q × F)) := by
    intro a ha b hb h
    exact heinj ha hb (hy h)
  let f : F[X] := Lagrange.interpolate e.val (fun a : Fin q × F => y a.1)
    (fun a => a.2 - w a.1)
  have hf : f.degree < r := by
    simpa only [e.property] using
      Lagrange.degree_interpolate_lt (fun a : Fin q × F => a.2 - w a.1) hnodes
  have heval (a : Fin q × F) (ha : a ∈ e.val) : f.eval (y a.1) = a.2 - w a.1 :=
    Lagrange.eval_interpolate_at_node _ hnodes ha
  refine ⟨graphClique (fun i => w i + f.eval (y i)), ⟨?_, ?_⟩, ?_⟩
  · exact (mem_polynomialDecomposition y w _).mpr ⟨f, hf, rfl⟩
  · intro a ha
    rw [mem_graphClique]
    simp [heval a ha]
  · intro Q hQ
    obtain ⟨hQD, heQ⟩ := hQ
    obtain ⟨g, hg, rfl⟩ := (mem_polynomialDecomposition y w Q).mp hQD
    have hgf : g = f := by
      apply Polynomial.eq_of_degrees_lt_of_eval_index_eq e.val hnodes
        (by simpa only [e.property] using hg) (by simpa only [e.property] using hf)
      intro a ha
      have hx : a.2 = w a.1 + g.eval (y a.1) :=
        (mem_graphClique _ a.1 a.2).mp (heQ ha)
      rw [heval a ha, hx]
      simp
    rw [hgf]

/-- Every shifted polynomial family is a true clique decomposition. -/
theorem polynomialDecomposition_isDecomposition (y w : Fin q → F)
    (hy : Function.Injective y) :
    IsDecomposition (partiteGraph F q r) (polynomialDecomposition r y w) := by
  apply isDecomposition_of_unique
  · intro Q hQ
    obtain ⟨f, _, rfl⟩ := (mem_polynomialDecomposition y w Q).mp hQ
    exact graphClique_edges_subset _
  · exact polynomialDecomposition_unique y w hy

omit [Fintype F] [DecidableEq F] in
theorem polynomialClique_injective (y w : Fin q → F) (hy : Function.Injective y)
    (hqr : r ≤ q) : Function.Injective (polynomialClique r y w) := by
  intro u v huv
  have hfun := graphClique_injective huv
  have hpoly : ((degreeLTEquiv F r).symm u).val = ((degreeLTEquiv F r).symm v).val := by
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq (univ : Finset (Fin q)) hy.injOn
    · have h := mem_degreeLT.mp ((degreeLTEquiv F r).symm u).property
      exact h.trans_le (by simpa using (WithBot.coe_le_coe.mpr hqr))
    · have h := mem_degreeLT.mp ((degreeLTEquiv F r).symm v).property
      exact h.trans_le (by simpa using (WithBot.coe_le_coe.mpr hqr))
    · intro i _
      exact add_left_cancel (congrFun hfun i)
  exact (degreeLTEquiv F r).symm.injective (Subtype.ext hpoly)

theorem card_polynomialDecomposition (y w : Fin q → F) (hy : Function.Injective y)
    (hqr : r ≤ q) : (polynomialDecomposition r y w).card = Fintype.card F ^ r := by
  rw [polynomialDecomposition, card_image_of_injective _ (polynomialClique_injective y w hy hqr)]
  simp

/-- The number of edges in a clique decomposition is `choose(q,r)` times
the number of cliques. -/
theorem IsDecomposition.card_eq {V : Type*} [Fintype V] [DecidableEq V]
    {G : Hypergraph V r} {D : Finset (Block V q)} (hD : IsDecomposition G D) :
    G.card = q.choose r * D.card := by
  have h := degree_boundary (indicator D) ∅ (Nat.zero_le r)
  rw [hD, degree_indicator, degree_indicator] at h
  simp only [card_empty, Nat.sub_zero, empty_subset, filter_true] at h
  exact_mod_cast h

theorem card_partiteGraph (y : Fin q → F) (hy : Function.Injective y) (hqr : r ≤ q) :
    (partiteGraph F q r).card = Fintype.card F ^ r * q.choose r := by
  rw [(polynomialDecomposition_isDecomposition y 0 hy).card_eq,
    card_polynomialDecomposition y 0 hy hqr, mul_comm]

end Arxiv2411_18291
