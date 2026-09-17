/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 Allen20202020. Released under Apache 2.0.
AI-assisted formal contribution: OpenAI Codex.
The forcing proof is imported unchanged from the separately attributed Erdos816 module.
-/
/-
Erdős Problem 816: symbolic sharpness, standard simple-path correspondence,
and explicit treatment of the exceptional parameter.
https://www.erdosproblems.com/816

Informal authors: Paul Erdős; András Hajnal; Kaizhe Chen; Jie Ma;
Zhen Liu; Qinghou Zeng.
Formal contribution: Allen20202020 with OpenAI Codex assistance.
The complete forcing proof is prior work by Codex / GPT-5.6 Sol in Erdos816.
Public source and attribution:
https://github.com/Allen20202020/erdos-816-sharp-threshold
-/
import ErdosProblems.Erdos816
import Mathlib.Combinatorics.SimpleGraph.Paths

namespace Erdos816Sharpness
open SimpleGraph Finset
open scoped BigOperators

/-- The literal conclusion using Mathlib's simple-path predicate. -/
def HasEqualDegreePathThree {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ u v : V, u ≠ v ∧ G.degree u = G.degree v ∧
    ∃ p : G.Walk u v, p.IsPath ∧ p.length = 3

/-- Convert the credited source's four-vertex predicate into a standard simple path. -/
theorem joined_iff_path {V : Type*} (G : SimpleGraph V) (u v : V) :
    Erdos816.JoinedByPathThree G u v ↔
      ∃ p : G.Walk u v, p.IsPath ∧ p.length = 3 := by
  constructor
  · rintro ⟨x, y, hux, huy, huv, hxy, hxv, hyv, h₁, h₂, h₃⟩
    refine ⟨.cons h₁ (.cons h₂ (.cons h₃ .nil)), ?_, rfl⟩
    simp_all [Walk.isPath_def]
  · rintro ⟨p, hp, hlen⟩
    cases p with
    | nil => simp at hlen
    | cons h₁ p =>
      cases p with
      | nil => simp at hlen
      | cons h₂ p =>
        cases p with
        | nil => simp at hlen
        | cons h₃ p =>
          have hz : p.length = 0 := by simpa using hlen
          cases p with
          | cons _ _ => simp at hz
          | nil =>
            simp only [Walk.isPath_def, Walk.support_cons, Walk.support_nil,
              List.nodup_cons, List.mem_cons, List.not_mem_nil,
              List.nodup_nil, and_true, not_or, not_false_eq_true] at hp
            exact ⟨_, _, hp.1.1, hp.1.2.1, hp.1.2.2, hp.2.1.1, hp.2.1.2,
              hp.2.2, h₁, h₂, h₃⟩

/-- Full original conclusion; no high-minimum-degree or asymptotic restriction. -/
theorem solution {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) (hn : 2 ≤ n) (hcard : Fintype.card V = 2 * n + 1)
    (hedges : n ^ 2 + n + 1 ≤ G.edgeFinset.card) :
    HasEqualDegreePathThree G := by
  obtain ⟨u, v, huv, hdeg, hpath⟩ :=
    Erdos816.erdos_816_of_at_least G n hn hcard hedges
  exact ⟨u, v, huv, hdeg, (joined_iff_path G u v).mp hpath⟩

/-- The graph which makes the edge threshold optimal. -/
abbrev sharpGraph (n : ℕ) : SimpleGraph (Fin n ⊕ Fin (n + 1)) :=
  completeBipartiteGraph (Fin n) (Fin (n + 1))

instance sharpGraph_decidable (n : ℕ) : DecidableRel (sharpGraph n).Adj :=
  inferInstanceAs (DecidableRel fun u v : Fin n ⊕ Fin (n + 1) =>
    u.isLeft ∧ v.isRight ∨ u.isRight ∧ v.isLeft)

@[simp] theorem sharpGraph_degree_left (n : ℕ) (u : Fin n) :
    (sharpGraph n).degree (.inl u) = n + 1 := by
  have hneigh : (sharpGraph n).neighborFinset (.inl u) =
      (univ : Finset (Fin (n + 1))).map Function.Embedding.inr := by
    ext v
    cases v <;> simp [sharpGraph, mem_neighborFinset]
  rw [degree, hneigh, card_map]
  simp

@[simp] theorem sharpGraph_degree_right (n : ℕ) (v : Fin (n + 1)) :
    (sharpGraph n).degree (.inr v) = n := by
  have hneigh : (sharpGraph n).neighborFinset (.inr v) =
      (univ : Finset (Fin n)).map Function.Embedding.inl := by
    ext u
    cases u <;> simp [sharpGraph, mem_neighborFinset]
  rw [degree, hneigh, card_map]
  simp

/-- A symbolic edge count, valid for every n, without finite enumeration. -/
theorem sharpGraph_edges (n : ℕ) :
    (sharpGraph n).edgeFinset.card = n ^ 2 + n := by
  have hs := (sharpGraph n).sum_degrees_eq_twice_card_edges
  simp only [Fintype.sum_sum_type, sharpGraph_degree_left, sharpGraph_degree_right,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hs
  nlinarith

/-- Odd paths in the bipartite construction end in opposite parts,
whose degrees differ by one. -/
theorem sharpGraph_avoids (n : ℕ) : ¬ HasEqualDegreePathThree (sharpGraph n) := by
  rintro ⟨u, v, _, hdeg, p, hp, hlen⟩
  obtain ⟨x, y, _, _, _, _, _, _, hux, hxy, hyv⟩ :=
    (joined_iff_path (sharpGraph n) u v).mpr ⟨p, hp, hlen⟩
  cases u <;> cases x <;> cases y <;> cases v <;>
    simp only [sharpGraph, completeBipartiteGraph_adj, Sum.isLeft_inl, Sum.isRight_inl,
      Sum.isLeft_inr, Sum.isRight_inr, Bool.false_eq_true,
      and_self, and_false, false_and, or_self, or_false, false_or] at hux hxy hyv
  all_goals simp_all only [sharpGraph_degree_left, sharpGraph_degree_right]
  all_goals omega

/-- Every counterexample in the valid range has at most n(n+1) edges. -/
theorem extremal_upper {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) (hn : 2 ≤ n) (hcard : Fintype.card V = 2 * n + 1)
    (havoid : ¬ HasEqualDegreePathThree G) :
    G.edgeFinset.card ≤ n ^ 2 + n := by
  by_contra h
  exact havoid (solution G n hn hcard (by omega))

/-- Exact maximum: the upper bound and an attaining graph are both proved. -/
theorem sharp_extremal (n : ℕ) (hn : 2 ≤ n) :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = 2 * n + 1 → ¬ HasEqualDegreePathThree G →
        G.edgeFinset.card ≤ n ^ 2 + n) ∧
    (Fintype.card (Fin n ⊕ Fin (n + 1)) = 2 * n + 1 ∧
      (sharpGraph n).edgeFinset.card = n ^ 2 + n ∧
      ¬ HasEqualDegreePathThree (sharpGraph n)) := by
  refine ⟨fun G _ hcard havoid => extremal_upper G n hn hcard havoid, ?_,
    sharpGraph_edges n, sharpGraph_avoids n⟩
  simp
  omega

/-- The omitted n=1 case really fails: a triangle cannot have a simple
path on four distinct vertices. -/
theorem triangle_exception :
    (⊤ : SimpleGraph (Fin 3)).edgeFinset.card = 1 ^ 2 + 1 + 1 ∧
      ¬ HasEqualDegreePathThree (⊤ : SimpleGraph (Fin 3)) := by
  constructor
  · decide
  · rintro ⟨u, v, _, _, p, hp, hlen⟩
    obtain ⟨x, y, hux, huy, huv, hxy, hxv, hyv, _, _, _⟩ :=
      (joined_iff_path (⊤ : SimpleGraph (Fin 3)) u v).mpr ⟨p, hp, hlen⟩
    fin_cases u <;> fin_cases v <;> fin_cases x <;> fin_cases y <;> simp_all

/-- The least edge threshold is exactly n²+n+1 for every n ≥ 2. -/
theorem edge_threshold_iff (n q : ℕ) (hn : 2 ≤ n) :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = 2 * n + 1 → q ≤ G.edgeFinset.card →
        HasEqualDegreePathThree G) ↔ n ^ 2 + n + 1 ≤ q := by
  constructor
  · intro h
    by_contra hq
    have hc : Fintype.card (Fin n ⊕ Fin (n + 1)) = 2 * n + 1 := by
      simp
      omega
    apply sharpGraph_avoids n
    apply h (sharpGraph n) hc
    rw [sharpGraph_edges]
    omega
  · intro hq V _ G _ hc he
    exact solution G n hn hc (hq.trans he)

/-- The original assertion with every natural-number parameter made explicit.
Its sole exceptional parameter is n=1; at n=0 the edge hypothesis is impossible. -/
theorem original_guarantee_iff (n : ℕ) :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = 2 * n + 1 → n ^ 2 + n + 1 ≤ G.edgeFinset.card →
        HasEqualDegreePathThree G) ↔ n ≠ 1 := by
  constructor
  · intro h hn
    subst n
    exact triangle_exception.2 (h (⊤ : SimpleGraph (Fin 3)) (by decide)
      triangle_exception.1.ge)
  · intro hn V _ G _ hc he
    by_cases hn2 : 2 ≤ n
    · exact solution G n hn2 hc he
    · have hn0 : n = 0 := by omega
      subst n
      have hc1 : Fintype.card V = 1 := by simpa using hc
      have hb0 : G.edgeFinset.card ≤ 0 := by
        simpa [hc1] using G.card_edgeFinset_le_card_choose_two
      have he1 : 1 ≤ G.edgeFinset.card := by simpa using he
      exact False.elim ((Nat.not_succ_le_zero 0) (he1.trans hb0))


end Erdos816Sharpness

set_option linter.hashCommand false in
#print axioms Erdos816Sharpness.edge_threshold_iff
-- depends on axioms: [propext, Classical.choice, Quot.sound]
set_option linter.hashCommand false in
#print axioms Erdos816Sharpness.original_guarantee_iff
-- depends on axioms: [propext, Classical.choice, Quot.sound]
