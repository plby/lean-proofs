/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle, Boris Alexeev
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.List.Count
import Mathlib.Order.Extension.Linear

/-!
# Erdős Problem 1006

Erdős, crediting Ore, asked whether every finite graph without triangles or
quadrilaterals has an acyclic orientation which stays acyclic after reversing
any one edge.  Nešetřil and Rödl proved that the answer is negative; indeed,
there are counterexamples of arbitrarily large girth.

This file formalizes the directed notions literally.  In particular,
`DirectedAcyclic` is defined using the nonempty transitive closure of the arc
relation, not Mathlib's unrelated predicate for an undirected forest.
-/

namespace Erdos1006

open Relation

/-! ## The statement of the orientation problem -/

/-- A directed graph, represented by its arc relation. -/
abbrev Digraph (V : Type*) := V → V → Prop

/-- A directed relation contains no directed closed walk of positive length. -/
def DirectedAcyclic {V : Type*} (D : Digraph V) : Prop :=
  ∀ v, ¬ Relation.TransGen D v v

/-- Exactly one of two propositions holds. -/
def ExactlyOne (p q : Prop) : Prop :=
  (p ∧ ¬q) ∨ (q ∧ ¬p)

/-- `D` chooses exactly one direction of every edge of `G`, and has no arcs
outside `G`. -/
def IsOrientation {V : Type*} (G : SimpleGraph V) (D : Digraph V) : Prop :=
  (∀ ⦃u v⦄, D u v → G.Adj u v) ∧
    ∀ ⦃u v⦄, G.Adj u v → ExactlyOne (D u v) (D v u)

/-- Delete the ordered arc `a → b`. -/
def eraseArc {V : Type*} (D : Digraph V) (a b : V) : Digraph V :=
  fun x y ↦ D x y ∧ ¬(x = a ∧ y = b)

/-- Delete `a → b`, insert `b → a`, and leave all other arcs unchanged. -/
def reverseArc {V : Type*} (D : Digraph V) (a b : V) : Digraph V :=
  fun x y ↦ eraseArc D a b x y ∨ (x = b ∧ y = a)

/-- The orientation requested in Problem 1006: it is acyclic, and every
one-arc reversal is still acyclic. -/
def GoodOrientation {V : Type*} (G : SimpleGraph V) (D : Digraph V) : Prop :=
  IsOrientation G D ∧ DirectedAcyclic D ∧
    ∀ ⦃a b⦄, D a b → DirectedAcyclic (reverseArc D a b)

/-- A graph admits an orientation of the kind requested in Problem 1006. -/
def HasGoodOrientation {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ D : Digraph V, GoodOrientation G D

/-- A triangle, written with the distinctness conditions made explicit. -/
def HasTriangle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj c a

/-- A simple cycle of length four.  Diagonals are allowed. -/
def HasFourCycle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ a b c d,
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a

/-- The hypothesis called “girth greater than four” in the problem: there is
no cycle of length three or four. -/
def GirthGreaterThanFour {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬HasTriangle G ∧ ¬HasFourCycle G

lemma IsOrientation.asymm {V : Type*} {G : SimpleGraph V} {D : Digraph V}
    (hD : IsOrientation G D) {u v : V} (huv : D u v) : ¬D v u := by
  intro hvu
  rcases hD.2 (hD.1 huv) with h | h
  · exact h.2 hvu
  · exact h.2 huv

/-! ## Topological orders and dependent arcs -/

/-- A strict total order in which every arc points forward. -/
def TopologicalOrder {V : Type*} (D : Digraph V) (lt : V → V → Prop) : Prop :=
  IsStrictTotalOrder V lt ∧ ∀ ⦃a b⦄, D a b → lt a b

/-- Every acyclic directed relation has a topological strict total order.
This is the order-extension step used in the Nešetřil--Rödl deduction. -/
theorem exists_topologicalOrder {V : Type*} (D : Digraph V)
    (hacyc : DirectedAcyclic D) :
    ∃ lt : V → V → Prop, TopologicalOrder D lt := by
  let tc : V → V → Prop := Relation.TransGen D
  letI : IsStrictOrder V tc := {
    irrefl := hacyc
    trans := fun _ _ _ ↦ Relation.TransGen.trans
  }
  letI : PartialOrder V := partialOrderOfSO tc
  obtain ⟨le, hle, hext⟩ := extend_partialOrder ((· ≤ ·) : V → V → Prop)
  let lt : V → V → Prop := fun a b ↦ le a b ∧ a ≠ b
  refine ⟨lt, ?_, ?_⟩
  · have hirr : ∀ a, ¬lt a a := by
      intro a ha
      exact ha.2 rfl
    have htrans : ∀ a b c, lt a b → lt b c → lt a c := by
      rintro a b c ⟨hab, habne⟩ ⟨hbc, _⟩
      refine ⟨hle.trans a b c hab hbc, ?_⟩
      intro hac
      subst c
      exact habne (hle.antisymm a b hab hbc)
    have htri : ∀ a b, ¬lt a b → ¬lt b a → a = b := by
      intro a b hnab hnba
      rcases hle.total a b with hab | hba
      · by_contra hne
        exact hnab ⟨hab, hne⟩
      · by_contra hne
        exact hnba ⟨hba, Ne.symm hne⟩
    exact { trichotomous := htri, irrefl := hirr, trans := htrans }
  · intro a b hab
    refine ⟨hext a b (Or.inr (Relation.TransGen.single hab)), ?_⟩
    intro heq
    subst b
    exact hacyc a (Relation.TransGen.single hab)

lemma topologicalOrder_directedAcyclic {V : Type*} {D lt : V → V → Prop}
    (htop : TopologicalOrder D lt) : DirectedAcyclic D := by
  intro v hv
  have hreach : ∀ ⦃a b⦄, Relation.TransGen D a b → lt a b := by
    intro a b hab
    induction hab with
    | single h => exact htop.2 h
    | @tail b c _ hbc ih => exact htop.1.trans _ _ _ ih (htop.2 hbc)
  exact htop.1.irrefl v (hreach hv)

theorem directedAcyclic_iff_exists_topologicalOrder {V : Type*} (D : Digraph V) :
    DirectedAcyclic D ↔ ∃ lt : V → V → Prop, TopologicalOrder D lt :=
  ⟨exists_topologicalOrder D,
    fun ⟨_, htop⟩ ↦ topologicalOrder_directedAcyclic htop⟩

/-- The underlying undirected support of an exact orientation. -/
lemma orientation_support {V : Type*} {G : SimpleGraph V} {D : Digraph V}
    (hD : IsOrientation G D) (u v : V) :
    G.Adj u v ↔ D u v ∨ D v u := by
  constructor
  · intro huv
    rcases hD.2 huv with huvD | hvuD
    · exact Or.inl huvD.1
    · exact Or.inr hvuD.1
  · rintro (huvD | hvuD)
    · exact hD.1 huvD
    · exact G.adj_symm (hD.1 hvuD)

/-- There is a directed path from `a` to `b` which avoids the arc `a → b`. -/
def HasAlternativePath {V : Type*} (D : Digraph V) (a b : V) : Prop :=
  Relation.TransGen (eraseArc D a b) a b

/-- An alternative path is closed by the newly inserted reverse arc. -/
lemma reverseArc_has_cycle_of_alternativePath {V : Type*} {D : Digraph V}
    {a b : V} (hpath : HasAlternativePath D a b) :
    Relation.TransGen (reverseArc D a b) b b := by
  have hba : reverseArc D a b b a := Or.inr ⟨rfl, rfl⟩
  have hab : Relation.TransGen (reverseArc D a b) a b := by
    have hmono : (fun x y ↦ D x y ∧ ¬(x = a ∧ y = b)) ≤ reverseArc D a b := by
      intro x y hxy
      exact Or.inl hxy
    exact (Relation.TransGen.mono hmono) a b hpath
  exact Relation.TransGen.trans (Relation.TransGen.single hba) hab

/-- Reversing an arc with an alternative path destroys acyclicity. -/
lemma reverseArc_not_acyclic_of_alternativePath {V : Type*} {D : Digraph V}
    {a b : V} (hpath : HasAlternativePath D a b) :
    ¬DirectedAcyclic (reverseArc D a b) := by
  intro hacyc
  exact hacyc b (reverseArc_has_cycle_of_alternativePath hpath)

private lemma transGen_addArc_cases {V : Type*} {r : Digraph V} {u v x y : V}
    (h : Relation.TransGen (fun a b ↦ r a b ∨ (a = v ∧ b = u)) x y) :
    Relation.TransGen r x y ∨
      (Relation.ReflTransGen (fun a b ↦ r a b ∨ (a = v ∧ b = u)) x v ∧
        Relation.ReflTransGen (fun a b ↦ r a b ∨ (a = v ∧ b = u)) u y) := by
  induction h with
  | single hxy =>
      rcases hxy with hxy | ⟨rfl, rfl⟩
      · exact Or.inl (.single hxy)
      · exact Or.inr ⟨.refl, .refl⟩
  | tail hxy hyz ih =>
      rcases ih with hxy | ⟨hxv, huy⟩
      · rcases hyz with hyz | ⟨rfl, rfl⟩
        · exact Or.inl (hxy.tail hyz)
        · exact Or.inr ⟨hxy.to_reflTransGen, .refl⟩
      · exact Or.inr ⟨hxv, huy.tail hyz⟩

private lemma addArc_reachable_from_target {V : Type*} {r : Digraph V} {u v x : V}
    (h : Relation.ReflTransGen (fun a b ↦ r a b ∨ (a = v ∧ b = u)) u x) :
    Relation.ReflTransGen r u x := by
  induction h with
  | refl => exact .refl
  | tail _ hxy ih =>
      rcases hxy with hxy | ⟨rfl, rfl⟩
      · exact ih.tail hxy
      · exact .refl

private lemma directedAcyclic_addArc_iff {V : Type*} {r : Digraph V} {u v : V}
    (huv : u ≠ v) (hr : DirectedAcyclic r) :
    DirectedAcyclic (fun a b ↦ r a b ∨ (a = v ∧ b = u)) ↔
      ¬Relation.TransGen r u v := by
  constructor
  · intro h hpath
    apply h v
    let s : Digraph V := fun a b ↦ r a b ∨ (a = v ∧ b = u)
    have hvu : s v u := Or.inr ⟨rfl, rfl⟩
    exact (@Relation.TransGen.single V s v u hvu).trans
      (Relation.TransGen.mono (r := r) (fun _ _ h ↦ Or.inl h) _ _ hpath)
  · intro hno x hcycle
    rcases transGen_addArc_cases hcycle with hbase | ⟨hxv, hux⟩
    · exact hr x hbase
    · have huv' : Relation.ReflTransGen r u v :=
        addArc_reachable_from_target (hux.trans hxv)
      rcases reflTransGen_iff_eq_or_transGen.mp huv' with hvu | huv'
      · exact huv hvu.symm
      · exact hno huv'

/-- Exact alternative-path criterion for reversing an arc. -/
lemma directedAcyclic_reverseArc_iff {V : Type*} {D : Digraph V} {a b : V}
    (hab : a ≠ b) (hD : DirectedAcyclic D) :
    DirectedAcyclic (reverseArc D a b) ↔ ¬HasAlternativePath D a b := by
  apply directedAcyclic_addArc_iff hab
  intro x hx
  exact hD x (Relation.TransGen.mono (r := eraseArc D a b) (fun _ _ h ↦ h.1) _ _ hx)

/-- For an exact acyclic orientation, robustness says exactly that no arc has
an alternative directed path between the same endpoints. -/
lemma goodOrientation_iff_acyclic_no_alternative {V : Type*}
    {G : SimpleGraph V} {D : Digraph V} (hD : IsOrientation G D) :
    GoodOrientation G D ↔ DirectedAcyclic D ∧
      ∀ ⦃a b⦄, D a b → ¬HasAlternativePath D a b := by
  constructor
  · rintro ⟨_, hacyc, hrev⟩
    refine ⟨hacyc, fun {a b} hab ↦ ?_⟩
    exact (directedAcyclic_reverseArc_iff (hD.1 hab).ne hacyc).mp
      (hrev hab)
  · rintro ⟨hacyc, hno⟩
    refine ⟨hD, hacyc, fun {a b} hab ↦ ?_⟩
    exact (directedAcyclic_reverseArc_iff (hD.1 hab).ne hacyc).mpr
      (hno hab)

/-- Orient an undirected adjacency relation forward in a strict order. -/
def forwardArcs {V : Type*} (E lt : V → V → Prop) : Digraph V :=
  fun x y ↦ E x y ∧ lt x y

lemma forwardArcs_directedAcyclic {V : Type*} {E lt : V → V → Prop}
    (hlt : IsStrictOrder V lt) : DirectedAcyclic (forwardArcs E lt) := by
  intro v hv
  have hreach : ∀ ⦃a b⦄, Relation.TransGen (forwardArcs E lt) a b → lt a b := by
    intro a b hab
    induction hab with
    | single h => exact h.2
    | @tail b c _ hbc ih => exact hlt.trans _ _ _ ih hbc.2
  exact hlt.irrefl v (hreach hv)

/-- In a topological order, an exact orientation is precisely the forward
orientation of its underlying graph. -/
lemma forwardArcs_eq_of_topologicalOrder {V : Type*} {G : SimpleGraph V}
    {D lt : V → V → Prop} (hD : IsOrientation G D)
    (htop : TopologicalOrder D lt) :
    forwardArcs G.Adj lt = D := by
  funext x y
  apply propext
  constructor
  · rintro ⟨hG, hxy⟩
    rcases (orientation_support hD x y).mp hG with hDxy | hDyx
    · exact hDxy
    · have hyx := htop.2 hDyx
      exact (htop.1.irrefl y (htop.1.trans y x y hyx hxy)).elim
  · intro hDxy
    exact ⟨hD.1 hDxy, htop.2 hDxy⟩

/-! ## The ordered-cycle implication -/

/-- A nonempty directed path with exactly `n` arcs. -/
inductive PathN {V : Type*} (R : V → V → Prop) : ℕ → V → V → Prop
  | single {a b : V} : R a b → PathN R 1 a b
  | tail {n : ℕ} {a b c : V} : PathN R n a b → R b c → PathN R (n + 1) a c

lemma PathN.toTransGen {V : Type*} {R : V → V → Prop}
    {n : ℕ} {a b : V} (h : PathN R n a b) : Relation.TransGen R a b := by
  induction h with
  | single hab => exact .single hab
  | tail _ hbc ih => exact ih.tail hbc

/-- A monotone cycle of length `s`: its closing edge `a--b` points forward,
and its other `s - 1` edges form a forward path from `a` to `b`. -/
def HasMonotoneCycle {V : Type*} (G : SimpleGraph V) (s : ℕ)
    (lt : V → V → Prop) : Prop :=
  ∃ a b,
    forwardArcs G.Adj lt a b ∧
      PathN (eraseArc (forwardArcs G.Adj lt) a b) (s - 1) a b

/-- Every strict total ordering of the vertices exposes a monotone
`s`-cycle. -/
def EveryOrderHasMonotoneCycle {V : Type*} (G : SimpleGraph V) (s : ℕ) : Prop :=
  ∀ lt : V → V → Prop, IsStrictTotalOrder V lt → HasMonotoneCycle G s lt

lemma HasMonotoneCycle.hasAlternativePath {V : Type*} {G : SimpleGraph V}
    {s : ℕ} {lt : V → V → Prop} (h : HasMonotoneCycle G s lt) :
    ∃ a b,
      forwardArcs G.Adj lt a b ∧
        HasAlternativePath (forwardArcs G.Adj lt) a b := by
  obtain ⟨a, b, hab, hpath⟩ := h
  exact ⟨a, b, hab, hpath.toTransGen⟩

/-- The deterministic Nešetřil--Rödl bridge: an unavoidable monotone cycle
forces every exact orientation either to be cyclic already or to acquire a
directed cycle after one arc is reversed. -/
theorem orientation_cyclic_or_badReversal_of_everyOrderHasMonotoneCycle
    {V : Type*} {G : SimpleGraph V} {s : ℕ}
    (hmono : EveryOrderHasMonotoneCycle G s)
    (D : Digraph V) (hD : IsOrientation G D) :
    ¬DirectedAcyclic D ∨
      ∃ a b, D a b ∧ ¬DirectedAcyclic (reverseArc D a b) := by
  by_cases hacyc : DirectedAcyclic D
  · right
    obtain ⟨lt, htop⟩ := exists_topologicalOrder D hacyc
    obtain ⟨a, b, hab, hpath⟩ :=
      (hmono lt htop.1).hasAlternativePath
    have hforward : forwardArcs G.Adj lt = D :=
      forwardArcs_eq_of_topologicalOrder hD htop
    rw [hforward] at hab hpath
    exact ⟨a, b, hab, reverseArc_not_acyclic_of_alternativePath hpath⟩
  · exact Or.inl hacyc

/-- A graph with the unavoidable monotone-cycle property has no good
orientation. -/
theorem not_hasGoodOrientation_of_everyOrderHasMonotoneCycle
    {V : Type*} {G : SimpleGraph V} {s : ℕ}
    (hmono : EveryOrderHasMonotoneCycle G s) :
    ¬HasGoodOrientation G := by
  rintro ⟨D, hgood⟩
  rcases orientation_cyclic_or_badReversal_of_everyOrderHasMonotoneCycle
      hmono D hgood.1 with hcyc | ⟨a, b, hab, hrev⟩
  · exact hcyc hgood.2.1
  · exact hrev (hgood.2.2 hab)

end Erdos1006
