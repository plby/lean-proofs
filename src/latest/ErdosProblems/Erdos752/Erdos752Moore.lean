/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos182.Elementary
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.Tactic

/-!
# The Moore-bound component of Erdős Problem 752

This file isolates the finite high-girth counting argument used in the
Sudakov--Verstraëte expansion lemma.
-/

open Finset
open SimpleGraph

namespace Erdos752

universe u

/-- Every simple cycle of `G` has length strictly greater than `n`. -/
def GirthGreaterThan {V : Type u} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∀ (v : V) (p : G.Walk v v), p.IsCycle → n < p.length

/-- A rooted simple path of prescribed length, with its endpoint included in
the data so that paths with varying endpoints form one finite type. -/
abbrev RootedPath {V : Type u} (G : SimpleGraph V) (root : V) (n : ℕ) :=
  Σ end_ : V, {p : G.Walk root end_ // p.IsPath ∧ p.length = n}

namespace GirthGreaterThan

lemma mono {V : Type u} {G : SimpleGraph V} {m n : ℕ}
    (h : GirthGreaterThan G n) (hmn : m ≤ n) : GirthGreaterThan G m := by
  intro v p hp
  exact hmn.trans_lt (h v p hp)

lemma of_le {V : Type u} {G H : SimpleGraph V} {n : ℕ}
    (h : GirthGreaterThan G n) (hHG : H ≤ G) : GirthGreaterThan H n := by
  intro v p hp
  let q : G.Walk v v := p.mapLe hHG
  have hq : q.IsCycle := hp.mapLe hHG
  simpa [q] using h v q hq

lemma of_injective_hom {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {n : ℕ} (h : GirthGreaterThan G n) (f : H →g G)
    (hf : Function.Injective f) : GirthGreaterThan H n := by
  intro v p hp
  have hcycle : (p.map f).IsCycle := hp.map hf
  simpa using h (f v) (p.map f) hcycle

/-- Below the girth threshold there cannot be two different simple paths with
the same endpoints.  This is the injectivity step in the Moore bound. -/
lemma paths_eq_of_length_add_le {V : Type u} {G : SimpleGraph V} {n : ℕ}
    (h : GirthGreaterThan G n) {a b : V} {p q : G.Walk a b}
    (hp : p.IsPath) (hq : q.IsPath) (hlen : p.length + q.length ≤ n) : p = q := by
  by_contra hpq
  obtain ⟨w, _hwp, _hwq, c, hc, hclen⟩ :=
    hp.exists_isCycle_length_le_add_of_ne hq hpq
  have := h w c hc
  omega

/-- In a graph of girth greater than `2*n`, the endpoint determines a rooted
path of length `n`. -/
lemma rootedPath_endpoint_injective {V : Type u} {G : SimpleGraph V} {root : V}
    {n : ℕ} (h : GirthGreaterThan G (2 * n)) :
    Function.Injective (fun p : RootedPath G root n ↦ p.1) := by
  intro p q hend
  rcases p with ⟨vp, p, hp, hplen⟩
  rcases q with ⟨vq, q, hq, hqlen⟩
  dsimp at hend
  subst vq
  have hpq : p = q := h.paths_eq_of_length_add_le hp hq (by omega)
  subst q
  rfl

/-- The number of rooted paths of length `n` is at most the number of
vertices, provided the girth is greater than `2*n`. -/
lemma card_rootedPath_le_card_vertices {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {root : V} {n : ℕ}
    (h : GirthGreaterThan G (2 * n)) :
    Fintype.card (RootedPath G root n) ≤ Fintype.card V := by
  classical
  exact Fintype.card_le_of_injective _ h.rootedPath_endpoint_injective

/-- For positive length the root itself is not an endpoint, so endpoint
injectivity gives a strict cardinal inequality. -/
lemma card_rootedPath_lt_card_vertices {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {root : V} {n : ℕ} (hn : 0 < n)
    (h : GirthGreaterThan G (2 * n)) :
    Fintype.card (RootedPath G root n) < Fintype.card V := by
  classical
  let f : RootedPath G root n → V := fun p ↦ p.1
  apply Fintype.card_lt_of_injective_of_notMem f h.rootedPath_endpoint_injective
  rintro ⟨p, hp⟩
  rcases p with ⟨v, p, hpath, hplen⟩
  dsimp [f] at hp
  subst v
  have hnil : p.Nil := Walk.isPath_iff_nil.mp hpath
  have hz := hnil.length_eq_zero
  omega

/-- A path of length below the girth has no chord incident with its endpoint:
among vertices already on the path, only the penultimate one can be adjacent
to the endpoint. -/
lemma eq_penultimate_of_mem_support_of_adj {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {N : ℕ} (h : GirthGreaterThan G N) {a b w : V} {p : G.Walk a b}
    (hp : p.IsPath) (hp0 : 0 < p.length) (hplen : p.length + 1 ≤ N)
    (hw : w ∈ p.support) (hadj : G.Adj b w) : w = p.penultimate := by
  by_cases hedge : s(b, w) ∈ p.edges
  · exact hp.eq_penultimate_of_mem_edges hedge
  have hdrop : (p.dropUntil w hw).IsPath := hp.dropUntil hw
  have hnedge : s(b, w) ∉ (p.dropUntil w hw).edges := by
    intro he
    exact hedge (p.edges_dropUntil_subset_edges hw he)
  have hcyc : (Walk.cons hadj (p.dropUntil w hw)).IsCycle :=
    (Walk.cons_isCycle_iff (p.dropUntil w hw) hadj).2 ⟨hdrop, hnedge⟩
  have hlong := h b (Walk.cons hadj (p.dropUntil w hw)) hcyc
  have hle : (Walk.cons hadj (p.dropUntil w hw)).length ≤ p.length + 1 := by
    simp only [Walk.length_cons]
    have := p.length_dropUntil_le_length hw
    omega
  omega

end GirthGreaterThan

section PathCounting

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The possible next vertices that extend a rooted path while preserving
simplicity. -/
def pathExtensions {root : V} {n : ℕ} (p : RootedPath G root n) : Finset V :=
  G.neighborFinset p.1 \ p.2.1.support.toFinset

@[simp] lemma mem_pathExtensions {root : V} {n : ℕ} (p : RootedPath G root n)
    (w : V) : w ∈ pathExtensions p ↔ G.Adj p.1 w ∧ w ∉ p.2.1.support := by
  simp [pathExtensions]

/-- If `p` is nontrivial and lies below the girth threshold, deleting its
support from the endpoint's neighborhood removes exactly one possible next
vertex (the penultimate vertex), and in particular at most one. -/
lemma card_pathExtensions_add_one_ge_degree {root : V} {n N : ℕ}
    (h : GirthGreaterThan G N) (hn : 0 < n) (hnN : n + 1 ≤ N)
    (p : RootedPath G root n) :
    G.degree p.1 ≤ #(pathExtensions p) + 1 := by
  classical
  let I := G.neighborFinset p.1 ∩ p.2.1.support.toFinset
  have hI : I ⊆ {p.2.1.penultimate} := by
    intro w hw
    simp only [I, Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      List.mem_toFinset] at hw
    have heq := h.eq_penultimate_of_mem_support_of_adj p.2.2.1
      (by simpa [p.2.2.2] using hn) (by simpa [p.2.2.2] using hnN) hw.2 hw.1
    simpa [heq]
  have hIcard : #I ≤ 1 := by
    calc
      #I ≤ #({p.2.1.penultimate} : Finset V) := Finset.card_le_card hI
      _ = 1 := by simp
  have hsplit := Finset.card_sdiff_add_card_inter
    (G.neighborFinset p.1) p.2.1.support.toFinset
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hsplit
  dsimp [pathExtensions]
  dsimp [I] at hIcard
  omega

/-- A rooted path together with an admissible next vertex. -/
abbrev RootedPathExtension (root : V) (n : ℕ) :=
  Σ p : RootedPath G root n, ↥(pathExtensions p)

/-- Append an admissible vertex to a rooted path. -/
def extendRootedPath {root : V} {n : ℕ} (x : RootedPathExtension (G := G) root n) :
    RootedPath G root (n + 1) := by
  let p := x.1
  let w := x.2.1
  have hw : G.Adj p.1 w ∧ w ∉ p.2.1.support :=
    (mem_pathExtensions p w).1 x.2.2
  exact ⟨w, p.2.1.concat hw.1, p.2.2.1.concat hw.2 hw.1, by simp [p.2.2.2]⟩

/-- Remove the last vertex of a nontrivial rooted path. -/
def unextendRootedPath {root : V} {n : ℕ} (q : RootedPath G root (n + 1)) :
    RootedPathExtension (G := G) root n := by
  have hq0 : ¬q.2.1.Nil := by
    intro hnil
    have := hnil.length_eq_zero
    rw [q.2.2.2] at this
    omega
  have hadj : G.Adj q.2.1.penultimate q.1 := q.2.1.adj_penultimate hq0
  let p : RootedPath G root n :=
    ⟨q.2.1.penultimate, q.2.1.dropLast, q.2.2.1.dropLast, by
      rw [Walk.length_dropLast, q.2.2.2]
      omega⟩
  have hnot : q.1 ∉ p.2.1.support := by
    have hrec : p.2.1.concat hadj = q.2.1 := by
      exact q.2.1.concat_dropLast hadj
    have hpath : (p.2.1.concat hadj).IsPath := hrec ▸ q.2.2.1
    exact (Walk.concat_isPath_iff hadj).1 hpath |>.2
  exact ⟨p, ⟨q.1, (mem_pathExtensions p q.1).2 ⟨hadj, hnot⟩⟩⟩

/-- Copying the endpoints of a walk does not change the corresponding
subtype element, up to heterogeneous equality.  This tiny transport lemma
keeps the inverse calculation below independent of the proof terms generated
by `Walk.dropLast_concat`. -/
private lemma walkSubtype_copy_heq {a b a' b' : V} (p : G.Walk a b)
    (ha : a = a') (hb : b = b') (n : ℕ)
    (hp' : (p.copy ha hb).IsPath ∧ (p.copy ha hb).length = n)
    (hp : p.IsPath ∧ p.length = n) :
    (⟨p.copy ha hb, hp'⟩ : {q : G.Walk a' b' // q.IsPath ∧ q.length = n}) ≍
      (⟨p, hp⟩ : {q : G.Walk a b // q.IsPath ∧ q.length = n}) := by
  subst a'
  subst b'
  rfl

lemma unextend_extendRootedPath {root : V} {n : ℕ}
    (x : RootedPathExtension (G := G) root n) :
    unextendRootedPath (extendRootedPath x) = x := by
  rcases x with ⟨⟨v, p, hp, hplen⟩, ⟨w, hw⟩⟩
  ext <;> simp [extendRootedPath, unextendRootedPath]
  exact walkSubtype_copy_heq p _ _ n _ ⟨hp, hplen⟩

lemma extend_unextendRootedPath {root : V} {n : ℕ}
    (q : RootedPath G root (n + 1)) :
    extendRootedPath (unextendRootedPath q) = q := by
  rcases q with ⟨v, q, hq, hqlen⟩
  ext <;> simp [extendRootedPath, unextendRootedPath]

/-- Appending and deleting the last vertex identify paths of length `n+1`
with extensions of paths of length `n`. -/
def rootedPathSuccEquiv (root : V) (n : ℕ) :
    RootedPathExtension (G := G) root n ≃ RootedPath G root (n + 1) where
  toFun := extendRootedPath
  invFun := unextendRootedPath
  left_inv := unextend_extendRootedPath
  right_inv := extend_unextendRootedPath

lemma card_rootedPath_succ_eq_sum (root : V) (n : ℕ) :
    Fintype.card (RootedPath G root (n + 1)) =
      ∑ p : RootedPath G root n, #(pathExtensions p) := by
  classical
  rw [← Fintype.card_congr (rootedPathSuccEquiv (G := G) root n)]
  simpa only [Fintype.card_coe] using
    (Fintype.card_sigma (ι := RootedPath G root n)
      (α := fun p ↦ ↥(pathExtensions p)))

lemma degree_le_card_pathExtensions_add_one {root : V} {n N : ℕ}
    (h : GirthGreaterThan G N) (hnN : n + 1 ≤ N)
    (p : RootedPath G root n) :
    G.degree p.1 ≤ #(pathExtensions p) + 1 := by
  rcases n with _ | n
  · rcases p with ⟨v, p, hp, hplen⟩
    cases p with
    | nil =>
        have heq : G.neighborFinset root \ {root} = G.neighborFinset root := by
          ext w
          simp only [Finset.mem_sdiff, Finset.mem_singleton]
          constructor
          · exact fun hw ↦ hw.1
          · intro hw
            exact ⟨hw, fun hwr ↦ G.notMem_neighborFinset_self root (hwr ▸ hw)⟩
        rw [show pathExtensions (G := G)
            (⟨root, Walk.nil, hp, hplen⟩ : RootedPath G root 0) =
            G.neighborFinset root \ {root} by
              ext w
              simp [pathExtensions]]
        rw [heq, SimpleGraph.card_neighborFinset_eq_degree]
        change G.degree root ≤ G.degree root + 1
        omega
    | cons hadj p => simp at hplen
  · exact card_pathExtensions_add_one_ge_degree h (by omega) hnN p

/-- At every stage below radius `r`, a minimum degree of `d+1` gives at
least `d` continuations per rooted path. -/
lemma card_rootedPath_mul_le_succ {root : V} {d r n : ℕ}
    (hmin : d + 1 ≤ G.minDegree) (hgirth : GirthGreaterThan G (2 * r))
    (hn : n < r) :
    d * Fintype.card (RootedPath G root n) ≤
      Fintype.card (RootedPath G root (n + 1)) := by
  classical
  rw [card_rootedPath_succ_eq_sum]
  calc
    d * Fintype.card (RootedPath G root n) =
        ∑ _p : RootedPath G root n, d := by simp [Nat.mul_comm]
    _ ≤ ∑ p : RootedPath G root n, #(pathExtensions p) := by
      apply Finset.sum_le_sum
      intro p _hp
      have hdegree : d + 1 ≤ G.degree p.1 :=
        hmin.trans (G.minDegree_le_degree p.1)
      have hremove := degree_le_card_pathExtensions_add_one hgirth (p := p) (by
        have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.2 (by omega)
        omega)
      omega

/-- There are at least `d^n` rooted paths of length `n`, as long as `n` is
at most the high-girth radius. -/
lemma pow_le_card_rootedPath {root : V} {d r n : ℕ}
    (hmin : d + 1 ≤ G.minDegree) (hgirth : GirthGreaterThan G (2 * r))
    (hn : n ≤ r) :
    d ^ n ≤ Fintype.card (RootedPath G root n) := by
  induction n with
  | zero =>
      have hne : Nonempty (RootedPath G root 0) :=
        ⟨⟨root, Walk.nil, by simp, rfl⟩⟩
      have hcard : 1 ≤ Fintype.card (RootedPath G root 0) :=
        Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero
      simpa only [pow_zero] using hcard
  | succ n ih =>
      have hnr : n < r := by omega
      calc
        d ^ (n + 1) = d * d ^ n := by simp [pow_succ, Nat.mul_comm]
        _ ≤ d * Fintype.card (RootedPath G root n) :=
          Nat.mul_le_mul_left d (ih (by omega))
        _ ≤ Fintype.card (RootedPath G root (n + 1)) :=
          card_rootedPath_mul_le_succ hmin hgirth hnr

/-- The Moore lower bound in the form needed for Erdős 752: minimum degree
at least `d+1` and girth greater than `2*r` force at least `d^r` vertices. -/
theorem moore_bound {d r : ℕ} (hmin : d + 1 ≤ G.minDegree)
    (hgirth : GirthGreaterThan G (2 * r)) :
    d ^ r ≤ Fintype.card V := by
  classical
  by_cases hV : IsEmpty V
  · letI : IsEmpty V := hV
    have hzero : G.minDegree = 0 := by simp [SimpleGraph.minDegree]
    simp [hzero] at hmin
  · letI : Nonempty V := not_isEmpty_iff.mp hV
    let root : V := Classical.choice inferInstance
    exact (pow_le_card_rootedPath (G := G) (root := root) hmin hgirth le_rfl).trans
      (hgirth.card_rootedPath_le_card_vertices (root := root))

/-- The strict Moore bound for positive radius.  The extra vertex is the root,
which cannot be the endpoint of a positive-length simple rooted path. -/
theorem moore_bound_strict {d r : ℕ} (hr : 0 < r)
    (hmin : d + 1 ≤ G.minDegree) (hgirth : GirthGreaterThan G (2 * r)) :
    d ^ r < Fintype.card V := by
  classical
  by_cases hV : IsEmpty V
  · letI : IsEmpty V := hV
    have hzero : G.minDegree = 0 := by simp [SimpleGraph.minDegree]
    simp [hzero] at hmin
  · letI : Nonempty V := not_isEmpty_iff.mp hV
    let root : V := Classical.choice inferInstance
    exact (pow_le_card_rootedPath (G := G) (root := root) hmin hgirth le_rfl).trans_lt
      (hgirth.card_rootedPath_lt_card_vertices (root := root) hr)

end PathCounting

section SmallSetExpansion

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The external vertex boundary of a finite vertex set. -/
noncomputable def externalBoundary (G : SimpleGraph V) (X : Finset V) : Finset V :=
  by
    classical
    exact Finset.univ.filter fun w ↦ w ∉ X ∧ ∃ v ∈ X, G.Adj v w

/-- The set together with its external vertex boundary. -/
noncomputable def closedNeighborhood (G : SimpleGraph V) (X : Finset V) : Finset V :=
  X ∪ externalBoundary G X

@[simp] lemma mem_externalBoundary {X : Finset V} {w : V} :
    w ∈ externalBoundary G X ↔ w ∉ X ∧ ∃ v ∈ X, G.Adj v w := by
  simp [externalBoundary]

@[simp] lemma mem_closedNeighborhood {X : Finset V} {w : V} :
    w ∈ closedNeighborhood G X ↔ w ∈ X ∨ ∃ v ∈ X, G.Adj v w := by
  by_cases hw : w ∈ X
  · simp [closedNeighborhood, hw]
  · simp [closedNeighborhood, hw]

lemma neighborSet_subset_closedNeighborhood {X : Finset V} {v : V} (hv : v ∈ X) :
    G.neighborSet v ⊆ (↑(closedNeighborhood G X) : Set V) := by
  intro w hw
  exact (mem_closedNeighborhood (G := G)).2 (Or.inr ⟨v, hv, hw⟩)

lemma card_closedNeighborhood_le {X : Finset V} :
    #(closedNeighborhood G X) ≤ #X + #(externalBoundary G X) := by
  exact Finset.card_union_le _ _

/-- Small sets expand by a factor greater than two, including the exact
integral cutoff `3 * |X| = d ^ r`.  The strict inequality is the point of
using `moore_bound_strict`: the root contributes the one extra vertex that
rules out equality at the cutoff. -/
theorem small_set_expansion {d r : ℕ} (hr : 0 < r)
    (hmin : 6 * (d + 1) ≤ G.minDegree)
    (hgirth : GirthGreaterThan G (2 * r))
    {X : Finset V} (hX : X.Nonempty) (hXsmall : 3 * #X ≤ d ^ r) :
    2 * #X < #(externalBoundary G X) := by
  classical
  by_contra hnot
  have hboundary : #(externalBoundary G X) ≤ 2 * #X := by omega
  let S : Finset V := closedNeighborhood G X
  letI : Fintype (↥S) :=
    Subtype.fintype (fun x : V ↦ x ∈ (↑S : Set V))
  let H : SimpleGraph (↥S) := G.induce (↑S : Set V)
  let e : ↥X ↪ ↥S :=
    { toFun := fun x ↦ ⟨x.1, by
        dsimp [S]
        exact (mem_closedNeighborhood (G := G)).2 (Or.inl x.2)⟩
      inj' := by
        intro x y h
        apply Subtype.ext
        exact congrArg (fun z : ↥S ↦ (z : V)) h }
  let Y : Finset (↥S) := Finset.univ.map e
  have hYcard : #Y = #X := by simp [Y]
  have hdegree (y : ↥S) (hy : y ∈ Y) : 6 * (d + 1) ≤ H.degree y := by
    rw [Finset.mem_map] at hy
    obtain ⟨x, _hx, rfl⟩ := hy
    have hsub : G.neighborSet (e x) ⊆ (↑S : Set V) := by
      change G.neighborSet (x : V) ⊆ (↑S : Set V)
      simpa [S] using neighborSet_subset_closedNeighborhood (G := G) x.2
    change 6 * (d + 1) ≤ (G.induce (↑S : Set V)).degree (e x)
    have heq : (G.induce (↑S : Set V)).degree (e x) = G.degree (e x).1 :=
      G.degree_induce_of_neighborSet_subset (v := e x) hsub
    rw [heq]
    exact hmin.trans (G.minDegree_le_degree x.1)
  have hdenseSum : 6 * (d + 1) * #X ≤ ∑ y : ↥S, H.degree y := by
    calc
      6 * (d + 1) * #X = ∑ _y ∈ Y, 6 * (d + 1) := by
        simp [hYcard, Nat.mul_comm]
      _ ≤ ∑ y ∈ Y, H.degree y := by
        apply Finset.sum_le_sum
        intro y hy
        exact hdegree y hy
      _ ≤ ∑ y : ↥S, H.degree y := by
        exact Finset.sum_le_sum_of_subset (Finset.subset_univ Y)
  have hdenseEdges : 6 * (d + 1) * #X ≤ 2 * #H.edgeFinset := by
    rw [H.sum_degrees_eq_twice_card_edges] at hdenseSum
    exact hdenseSum
  have hScard : Fintype.card (↥S) ≤ 3 * #X := by
    change Fintype.card (↥(↑S : Set V)) ≤ 3 * #X
    rw [Set.fintypeCard_eq_ncard]
    change (↑S : Set V).ncard ≤ 3 * #X
    simp only [Set.ncard_coe_finset]
    calc
      #S ≤ #X + #(externalBoundary G X) := card_closedNeighborhood_le (G := G)
      _ ≤ 3 * #X := by omega
  have hsupport : H.support.ncard ≤ 3 * #X := by
    calc
      H.support.ncard ≤ Fintype.card (↥S) := by
        simpa only [Nat.card_eq_fintype_card] using Set.ncard_le_card H.support
      _ ≤ 3 * #X := hScard
  have hcoreDense : (2 * (d + 1)) * H.support.ncard ≤ 2 * #H.edgeFinset := by
    calc
      (2 * (d + 1)) * H.support.ncard ≤ (2 * (d + 1)) * (3 * #X) :=
        Nat.mul_le_mul_left _ hsupport
      _ = 6 * (d + 1) * #X := by ring
      _ ≤ 2 * #H.edgeFinset := hdenseEdges
  have hHE : H.edgeFinset.Nonempty := by
    apply Finset.card_pos.mp
    by_contra hnotpos
    have hz : #H.edgeFinset = 0 := Nat.eq_zero_of_not_pos hnotpos
    rw [hz] at hdenseEdges
    have hXpos := Finset.card_pos.mpr hX
    have hleft : 0 < 6 * (d + 1) * #X := by positivity
    omega
  obtain ⟨K, instK, hKsupport, hKH, _hedges, hKmin⟩ :=
    Erdos182.exists_induced_minDegree_core H (2 * (d + 1)) hHE hcoreDense
  letI : DecidableRel K.Adj := instK
  let J : SimpleGraph K.support := K.induce K.support
  letI : Nonempty K.support := hKsupport.to_subtype
  have hJmin : d + 1 ≤ J.minDegree := by
    dsimp [J]
    omega
  let fJK : J →g K := (SimpleGraph.Embedding.induce (G := K) K.support).toHom
  let fKH : K →g H := SimpleGraph.Hom.ofLE hKH
  let fHG : H →g G :=
    (SimpleGraph.Embedding.induce (G := G) (↑S : Set V)).toHom
  let f : J →g G := fHG.comp (fKH.comp fJK)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact hxy
  have hJgirth : GirthGreaterThan J (2 * r) :=
    hgirth.of_injective_hom f hf
  have hMoore : d ^ r < Fintype.card K.support :=
    moore_bound_strict (G := J) hr hJmin hJgirth
  have hKcard : Fintype.card K.support ≤ 3 * #X := by
    calc
      Fintype.card K.support = K.support.ncard := Set.fintypeCard_eq_ncard K.support
      _ ≤ H.support.ncard := by
        apply Set.ncard_le_ncard
        · intro x hx
          rcases hx with ⟨y, hxy⟩
          exact ⟨y, hKH hxy⟩
        · exact Set.toFinite _
      _ ≤ 3 * #X := hsupport
  omega

end SmallSetExpansion

end Erdos752
