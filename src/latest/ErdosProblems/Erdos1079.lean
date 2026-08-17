/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic

/-!
# Erdős Problem 1079

We prove the dense-neighbourhood extension of Turán's theorem.  In fact, the witness can be
chosen to have maximum degree.  At the strict Turán threshold the neighbourhood inequality is
strict, which is Bondy's strengthening of the Bollobás--Thomason result.
-/

open Finset Fintype
open scoped Classical SimpleGraph

namespace Erdos1079

attribute [local instance] Fintype.ofFinite

/-- The extremal number `ex(n, K_r)`. -/
noncomputable def cliqueExtremalNumber (n r : ℕ) : ℕ :=
  SimpleGraph.extremalNumber n (⊤ : SimpleGraph (Fin r))

/-- The number of edges of a finite graph, stated without a decidability parameter. -/
noncomputable def edgeCount {V : Type*} [Finite V] (G : SimpleGraph V) : ℕ :=
  Nat.card G.edgeSet

/-- The graph induced by the open neighbourhood of `v`. -/
abbrev link {V : Type*} [Finite V] (G : SimpleGraph V) (v : V) :
    SimpleGraph (G.neighborFinset v) :=
  G.induce (G.neighborFinset v)

/-- The number of edges spanned by the open neighbourhood of `v`. -/
noncomputable def linkEdgeCount {V : Type*} [Finite V]
    (G : SimpleGraph V) (v : V) : ℕ :=
  {e : Sym2 V | e ∈ G.edgeSet ∧ ∀ x, x ∈ e → G.Adj v x}.ncard

lemma edgeCount_eq_card_edgeFinset {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : edgeCount G = #G.edgeFinset := by
  simp only [edgeCount, Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card]

/-- Join every vertex of `G` to every vertex of an independent set on `W`. -/
def joinIndependent {V W : Type*} (G : SimpleGraph V) : SimpleGraph (V ⊕ W) where
  Adj x y :=
    match x, y with
    | .inl u, .inl v => G.Adj u v
    | .inl _, .inr _ => True
    | .inr _, .inl _ => True
    | .inr _, .inr _ => False
  symm := ⟨by
    intro x y
    cases x <;> cases y <;> simp only
    · exact fun h => h.symm
    · exact id
    · exact id
    · exact id
    ⟩
  loopless := ⟨by
    intro x
    cases x <;> simp
    ⟩

instance {V W : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] :
    DecidableRel (joinIndependent (W := W) G).Adj := by
  intro x y
  cases x <;> cases y <;> simp only [joinIndependent] <;> infer_instance

@[simp] lemma joinIndependent_adj_inl_inl {V W : Type*} {G : SimpleGraph V} {u v : V} :
    (joinIndependent (W := W) G).Adj (.inl u) (.inl v) ↔ G.Adj u v := by
  rfl

@[simp] lemma joinIndependent_adj_inl_inr {V W : Type*} {G : SimpleGraph V} {u : V} {w : W} :
    (joinIndependent G).Adj (.inl u) (.inr w) := by
  simp [joinIndependent]

@[simp] lemma joinIndependent_adj_inr_inl {V W : Type*} {G : SimpleGraph V} {w : W} {u : V} :
    (joinIndependent G).Adj (.inr w) (.inl u) := by
  simp [joinIndependent]

@[simp] lemma not_joinIndependent_adj_inr_inr {V W : Type*} {G : SimpleGraph V} {w z : W} :
    ¬(joinIndependent G).Adj (.inr w) (.inr z) := by
  simp [joinIndependent]

/-- The one-extra-part construction is `q`-colourable. -/
noncomputable def turanJoinColoring {d b q : ℕ} (hq : 2 ≤ q) :
    SimpleGraph.Coloring
      (joinIndependent (W := Fin b) (SimpleGraph.turanGraph d (q - 1))) (Fin q) :=
  SimpleGraph.Coloring.mk
    (fun x => match x with
      | .inl v => ⟨v % (q - 1), (Nat.mod_lt _ (by omega)).trans_le (by omega)⟩
      | .inr _ => ⟨q - 1, by omega⟩)
    (by
      intro x y hxy
      cases x with
      | inl x =>
          cases y with
          | inl y =>
              simp only [joinIndependent_adj_inl_inl, SimpleGraph.turanGraph_adj] at hxy
              simpa [Fin.ext_iff] using hxy
          | inr y =>
              simp only [ne_eq, Fin.ext_iff]
              exact (Nat.mod_lt _ (by omega)).ne
      | inr x =>
          cases y with
          | inl y =>
              simp only [ne_eq, Fin.ext_iff]
              exact (Nat.mod_lt _ (by omega)).ne'
          | inr y => exact (not_joinIndependent_adj_inr_inr hxy).elim)

lemma turanJoin_cliqueFree {d b q : ℕ} (hq : 2 ≤ q) :
    (joinIndependent (W := Fin b) (SimpleGraph.turanGraph d (q - 1))).CliqueFree (q + 1) := by
  have hc : (joinIndependent (W := Fin b)
      (SimpleGraph.turanGraph d (q - 1))).Colorable q := by
    simpa using (turanJoinColoring hq).colorable
  exact hc.cliqueFree (by omega)

lemma degree_joinIndependent_inl {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (joinIndependent (W := W) G).degree (.inl v) = G.degree v + Fintype.card W := by
  classical
  let e : (joinIndependent (W := W) G).neighborSet (.inl v) ≃
      (G.neighborSet v ⊕ W) :=
    { toFun := fun
        | ⟨.inl u, hu⟩ => .inl ⟨u, hu⟩
        | ⟨.inr w, _⟩ => .inr w
      invFun := fun
        | .inl ⟨u, hu⟩ => ⟨.inl u, hu⟩
        | .inr w => ⟨.inr w, trivial⟩
      left_inv := fun
        | ⟨.inl _, _⟩ => rfl
        | ⟨.inr _, _⟩ => rfl
      right_inv := fun
        | .inl ⟨_, _⟩ => rfl
        | .inr _ => rfl }
  calc
    (joinIndependent (W := W) G).degree (.inl v) =
        Fintype.card ((joinIndependent (W := W) G).neighborSet (.inl v)) :=
      ((joinIndependent (W := W) G).card_neighborSet_eq_degree (.inl v)).symm
    _ = Fintype.card (G.neighborSet v ⊕ W) := Fintype.card_congr e
    _ = Fintype.card (G.neighborSet v) + Fintype.card W := Fintype.card_sum
    _ = G.degree v + Fintype.card W := by rw [G.card_neighborSet_eq_degree]

lemma degree_joinIndependent_inr {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : W) :
    (joinIndependent (W := W) G).degree (.inr w) = Fintype.card V := by
  classical
  let e : (joinIndependent (W := W) G).neighborSet (.inr w) ≃ V :=
    { toFun := fun
        | ⟨.inl u, _⟩ => u
        | ⟨.inr _, h⟩ => False.elim h
      invFun := fun u => ⟨.inl u, trivial⟩
      left_inv := fun
        | ⟨.inl _, _⟩ => rfl
        | ⟨.inr _, h⟩ => False.elim h
      right_inv := fun _ => rfl }
  calc
    (joinIndependent (W := W) G).degree (.inr w) =
        Fintype.card ((joinIndependent (W := W) G).neighborSet (.inr w)) :=
      ((joinIndependent (W := W) G).card_neighborSet_eq_degree (.inr w)).symm
    _ = Fintype.card V := Fintype.card_congr e

/-- Exact edge count of the one-extra-part construction. -/
lemma card_edgeFinset_joinIndependent {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    #(joinIndependent (W := W) G).edgeFinset =
      #G.edgeFinset + Fintype.card V * Fintype.card W := by
  classical
  have hjoin := (joinIndependent (W := W) G).sum_degrees_eq_twice_card_edges
  have hG := G.sum_degrees_eq_twice_card_edges
  simp_rw [Fintype.sum_sum_type, degree_joinIndependent_inl,
    degree_joinIndependent_inr] at hjoin
  simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul] at hjoin
  nlinarith [hjoin, hG]

/-- The exact Turán recurrence inequality obtained by adjoining one independent part. -/
lemma turan_split_le {n d q : ℕ} (hq : 2 ≤ q) (hd : d ≤ n) :
    #(SimpleGraph.turanGraph d (q - 1)).edgeFinset + d * (n - d) ≤
      #(SimpleGraph.turanGraph n q).edgeFinset := by
  let J := joinIndependent (W := Fin (n - d)) (SimpleGraph.turanGraph d (q - 1))
  letI : Nontrivial (Fin (q + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hfree : (⊤ : SimpleGraph (Fin (q + 1))).Free J := by
    apply (SimpleGraph.cliqueFree_iff_top_free (G := J) (β := Fin (q + 1))).mp
    simpa [J] using turanJoin_cliqueFree (d := d) (b := n - d) hq
  have hExt := SimpleGraph.card_edgeFinset_le_extremalNumber hfree
  have hcard : Fintype.card (Fin d ⊕ Fin (n - d)) = n := by
    simp [Nat.add_sub_of_le hd]
  rw [hcard, SimpleGraph.extremalNumber_top] at hExt
  have hqcard : Fintype.card (Fin (q + 1)) = q + 1 := by
    rw [← Nat.card_eq_fintype_card]
    simp
  rw [hqcard, Nat.add_sub_cancel] at hExt
  simpa [J, card_edgeFinset_joinIndependent] using hExt

/-- The edges internal to a neighbourhood are exactly the edges of its link. -/
lemma card_internal_neighbor_edges {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj] (v : V) :
    #{e ∈ G.edgeFinset | e.toFinset ⊆ G.neighborFinset v} = linkEdgeCount G v := by
  classical
  rw [← Set.ncard_coe_finset]
  unfold linkEdgeCount
  congr 1
  ext e
  simp only [Finset.mem_coe, Finset.mem_filter, SimpleGraph.mem_edgeFinset,
    Set.mem_ofPred_eq, and_congr_right_iff]
  intro _he
  constructor
  · intro h x hx
    exact (G.mem_neighborFinset v x).mp (h (Sym2.mem_toFinset.mpr hx))
  · intro h x hx
    exact (G.mem_neighborFinset v x).mpr (h x (Sym2.mem_toFinset.mp hx))

/-- Every edge not internal to a maximum-degree neighbourhood is charged to an endpoint outside
that neighbourhood. -/
lemma maximumDegree_edge_bound {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (hv : G.degree v = G.maxDegree) :
    edgeCount G ≤ linkEdgeCount G v +
      G.degree v * (Fintype.card V - G.degree v) := by
  classical
  let A := G.neighborFinset v
  let B := Aᶜ
  let inside := {e ∈ G.edgeFinset | e.toFinset ⊆ A}
  let outside := G.edgeFinset \ inside
  have hinside : inside ⊆ G.edgeFinset := by
    intro e he
    exact (Finset.mem_filter.mp he).1
  have houtside : outside ⊆ B.biUnion fun x => G.incidenceFinset x := by
    intro e he
    have he' := Finset.mem_sdiff.mp he
    have hnsub : ¬e.toFinset ⊆ A := by
      intro hsub
      exact he'.2 (Finset.mem_filter.mpr ⟨he'.1, hsub⟩)
    rw [Finset.not_subset] at hnsub
    obtain ⟨x, hxe, hxA⟩ := hnsub
    rw [Finset.mem_biUnion]
    refine ⟨x, ?_, ?_⟩
    · simpa [B] using hxA
    · rw [G.incidenceFinset_eq_filter]
      exact Finset.mem_filter.mpr ⟨he'.1, Sym2.mem_toFinset.mp hxe⟩
  have houtside : #outside ≤ (Fintype.card V - G.degree v) * G.degree v := by
    calc
      #outside ≤ #(B.biUnion fun x => G.incidenceFinset x) :=
        Finset.card_le_card houtside
      _ ≤ ∑ x ∈ B, #(G.incidenceFinset x) := Finset.card_biUnion_le
      _ = ∑ x ∈ B, G.degree x := by
        apply Finset.sum_congr rfl
        intro x hx
        exact G.card_incidenceFinset_eq_degree x
      _ ≤ ∑ _x ∈ B, G.degree v := by
        apply Finset.sum_le_sum
        intro x hx
        simpa [hv] using G.degree_le_maxDegree x
      _ = #B * G.degree v := by simp
      _ = (Fintype.card V - G.degree v) * G.degree v := by
        have hB : #B = Fintype.card V - G.degree v := by
          rw [show B = Aᶜ from rfl, Finset.card_compl]
          simp only [A, SimpleGraph.card_neighborFinset_eq_degree]
        rw [hB]
  have hdecomp : #outside + #inside = #G.edgeFinset := by
    simpa [outside] using Finset.card_sdiff_add_card_eq_card hinside
  have hinternal : #inside = linkEdgeCount G v := by
    simpa [inside, A] using card_internal_neighbor_edges G v
  have houtside' : #outside ≤ G.degree v * (Fintype.card V - G.degree v) := by
    simpa [Nat.mul_comm] using houtside
  rw [edgeCount_eq_card_edgeFinset]
  omega

/-- The one-part Turán inequality in the conventional `ex(n, K_r)` notation. -/
lemma cliqueExtremal_split_le {n d r : ℕ} (hr : 4 ≤ r) (hd : d ≤ n) :
    cliqueExtremalNumber d (r - 1) + d * (n - d) ≤
      cliqueExtremalNumber n r := by
  letI : Nontrivial (Fin (r - 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  letI : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.mpr (by omega)
  unfold cliqueExtremalNumber
  rw [SimpleGraph.extremalNumber_top (n := d) (α := Fin (r - 1)),
    SimpleGraph.extremalNumber_top (n := n) (α := Fin r)]
  have hcardr₁ : Fintype.card (Fin (r - 1)) = r - 1 := by
    rw [← Nat.card_eq_fintype_card]
    simp
  have hcardr : Fintype.card (Fin r) = r := by
    rw [← Nat.card_eq_fintype_card]
    simp
  rw [hcardr₁, hcardr]
  exact turan_split_le (q := r - 1) (by omega) hd

/-- At the non-strict Turán threshold, every chosen maximum-degree vertex has an extremal-size
link. -/
theorem maximumDegree_link_at_turan_threshold {n r : ℕ} (hr : 4 ≤ r) (hn : 1 ≤ n)
    (G : SimpleGraph (Fin n))
    (hG : cliqueExtremalNumber n r ≤ edgeCount G) :
    ∃ v : Fin n, G.degree v = G.maxDegree ∧
      cliqueExtremalNumber (G.degree v) (r - 1) ≤ linkEdgeCount G v := by
  classical
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  have hd : G.degree v ≤ n := by
    have := G.degree_lt_card_verts v
    simpa using this.le
  have hedge := maximumDegree_edge_bound G v hv.symm
  have hcardn : Fintype.card (Fin n) = n := by
    rw [← Nat.card_eq_fintype_card]
    simp
  rw [hcardn] at hedge
  have hsplit := cliqueExtremal_split_le hr hd
  refine ⟨v, hv.symm, ?_⟩
  omega

/-- Bondy's strict-threshold strengthening: a maximum-degree vertex has a link strictly over the
next Turán threshold. -/
theorem maximumDegree_link_above_turan_threshold {n r : ℕ} (hr : 4 ≤ r) (hn : 1 ≤ n)
    (G : SimpleGraph (Fin n))
    (hG : cliqueExtremalNumber n r < edgeCount G) :
    ∃ v : Fin n, G.degree v = G.maxDegree ∧
      cliqueExtremalNumber (G.degree v) (r - 1) < linkEdgeCount G v := by
  classical
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  have hd : G.degree v ≤ n := by
    have := G.degree_lt_card_verts v
    simpa using this.le
  have hedge := maximumDegree_edge_bound G v hv.symm
  have hcardn : Fintype.card (Fin n) = n := by
    rw [← Nat.card_eq_fintype_card]
    simp
  rw [hcardn] at hedge
  have hsplit := cliqueExtremal_split_le hr hd
  refine ⟨v, hv.symm, ?_⟩
  omega

lemma sq_le_four_mul_card_turanGraph_two_add_one (n : ℕ) :
    n ^ 2 ≤ 4 * #(SimpleGraph.turanGraph n 2).edgeFinset + 1 := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [SimpleGraph.card_edgeFinset_turanGraph]
  | one => norm_num [SimpleGraph.card_edgeFinset_turanGraph]
  | more n ih₀ _ih₁ =>
      rw [SimpleGraph.card_edgeFinset_turanGraph_add (n := n) (r := 2)]
      norm_num only [Nat.reduceSub, Nat.choose]
      nlinarith

/-- The balanced complete bipartite graph is admissible for every `K_r` problem with `r ≥ 4`. -/
lemma card_turanGraph_two_le_cliqueExtremalNumber {n r : ℕ} (hr : 4 ≤ r) :
    #(SimpleGraph.turanGraph n 2).edgeFinset ≤ cliqueExtremalNumber n r := by
  letI : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hcf : (SimpleGraph.turanGraph n 2).CliqueFree r :=
    (SimpleGraph.turanGraph_cliqueFree (n := n) (r := 2) (by omega)).mono (by omega)
  have hfree : (⊤ : SimpleGraph (Fin r)).Free (SimpleGraph.turanGraph n 2) := by
    apply (SimpleGraph.cliqueFree_iff_top_free
      (G := SimpleGraph.turanGraph n 2) (β := Fin r)).mp
    simpa using hcf
  simpa [cliqueExtremalNumber] using
    SimpleGraph.card_edgeFinset_le_extremalNumber hfree

/-- A graph at the `K_r` Turán threshold has maximum degree at least half its order. -/
lemma card_le_twice_maxDegree_of_turan_threshold {n r : ℕ} (hr : 4 ≤ r) (hn : 2 ≤ n)
    (G : SimpleGraph (Fin n))
    (hG : cliqueExtremalNumber n r ≤ edgeCount G) :
    n ≤ 2 * G.maxDegree := by
  classical
  have hturan : #(SimpleGraph.turanGraph n 2).edgeFinset ≤ edgeCount G :=
    (card_turanGraph_two_le_cliqueExtremalNumber hr).trans hG
  have hdegree : 2 * edgeCount G ≤ n * G.maxDegree := by
    rw [edgeCount_eq_card_edgeFinset, ← G.sum_degrees_eq_twice_card_edges]
    calc
      ∑ v, G.degree v ≤ ∑ _v : Fin n, G.maxDegree := by
        apply Finset.sum_le_sum
        intro v hv
        exact G.degree_le_maxDegree v
      _ = n * G.maxDegree := by simp
  have hsquare := sq_le_four_mul_card_turanGraph_two_add_one n
  by_contra h
  push Not at h
  nlinarith

/-- **Resolution of Erdős Problem 1079.**

For `r ≥ 4`, every `n`-vertex graph at the `K_r` Turán threshold has a maximum-degree vertex
whose degree is at least `n / 2` and whose open neighbourhood spans at least
`ex(d, K_{r-1})` edges.  The explicit inequality `n ≤ 2d` is a uniform version of the problem's
`d ≫_r n`.  The assumption `2 ≤ n` is necessary for any positive linear degree conclusion. -/
theorem erdos_problem_1079 {n r : ℕ} (hr : 4 ≤ r) (hn : 2 ≤ n)
    (G : SimpleGraph (Fin n))
    (hG : cliqueExtremalNumber n r ≤ edgeCount G) :
    ∃ v : Fin n,
      G.degree v = G.maxDegree ∧
      n ≤ 2 * G.degree v ∧
      cliqueExtremalNumber (G.degree v) (r - 1) ≤ linkEdgeCount G v := by
  obtain ⟨v, hv, hlink⟩ := maximumDegree_link_at_turan_threshold hr (by omega) G hG
  have hlinear := card_le_twice_maxDegree_of_turan_threshold hr hn G hG
  refine ⟨v, hv, ?_, hlink⟩
  simpa [← hv] using hlinear

/-- Bondy's strict version of the resolution: above the Turán threshold the same maximum-degree
vertex has strictly more than `ex(d, K_{r-1})` edges in its neighbourhood. -/
theorem erdos_problem_1079_strict {n r : ℕ} (hr : 4 ≤ r) (hn : 2 ≤ n)
    (G : SimpleGraph (Fin n))
    (hG : cliqueExtremalNumber n r < edgeCount G) :
    ∃ v : Fin n,
      G.degree v = G.maxDegree ∧
      n ≤ 2 * G.degree v ∧
      cliqueExtremalNumber (G.degree v) (r - 1) < linkEdgeCount G v := by
  obtain ⟨v, hv, hlink⟩ := maximumDegree_link_above_turan_threshold hr (by omega) G hG
  have hlinear := card_le_twice_maxDegree_of_turan_threshold hr hn G hG.le
  refine ⟨v, hv, ?_, hlink⟩
  simpa [← hv] using hlinear

end Erdos1079

#print axioms Erdos1079.erdos_problem_1079
#print axioms Erdos1079.erdos_problem_1079_strict
