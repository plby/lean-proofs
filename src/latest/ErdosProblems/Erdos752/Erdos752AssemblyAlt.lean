/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib

/-!
# Path assembly for Erdős Problem 752

This file isolates the part of the proof that turns a long path in two
consecutive breadth-first layers into many distinct cycle lengths.  The
tree used in the paper is deliberately absent from the statement: its only
job is to supply a family of equal-length paths whose internal vertices lie
strictly below the lower layer.
-/

open Function Set SimpleGraph

namespace Erdos752

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

variable {V : Type u}

/-- The length of the initial segment of `p` ending at a member of `B`. -/
private def prefixLength {G : SimpleGraph V} {a z : V} (p : G.Walk a z)
    (B : Finset V) (hB : ∀ b ∈ B, b ∈ p.support) (b : ↑B) : ℕ :=
  (p.takeUntil b.1 (hB b.1 b.2)).length

/-- Distinct vertices on a path have distinct initial-segment lengths. -/
private lemma prefixLength_injective {G : SimpleGraph V} {a z : V}
    (p : G.Walk a z) (B : Finset V) (hB : ∀ b ∈ B, b ∈ p.support) :
    Function.Injective (prefixLength p B hB) := by
  intro b c hbc
  have hbend := p.getVert_length_takeUntil (hB b.1 b.2)
  have hcend := p.getVert_length_takeUntil (hB c.1 c.2)
  apply Subtype.ext
  dsimp only [prefixLength] at hbc
  rw [← hbend, ← hcend, hbc]

/-- A vertex in the tail of a path is different from its initial vertex. -/
private lemma ne_start_of_mem_tail {G : SimpleGraph V} {a b x : V}
    {p : G.Walk a b} (hp : p.IsPath) (hx : x ∈ p.support.tail) : x ≠ a := by
  intro hxa
  subst x
  have hcons : p.support = a :: p.support.tail := p.cons_tail_support.symm
  have hn : (a :: p.support.tail).Nodup := by
    rw [← hcons]
    exact hp.support_nodup
  exact (List.nodup_cons.mp hn).1 hx

/--
Let `p` start at `a`, and let `B` be a finite set of vertices on `p`.
Assume every vertex of `p` is in breadth-first level at least `i`.  If for
each `b ∈ B` there is an `a`--`b` path of one fixed length `d > 1` whose
internal vertices lie below level `i`, then `G` has at least `|B|` distinct
cycle lengths.

In the application, `p` lies in levels `i` and `i+1`; the paths `q b` are
the equal-length paths through two different branches of a minimal BFS
subtree.  Thus the hypotheses here are exactly the output needed from the
tree argument, while the cycle construction itself does not mention a
tree.
-/
theorem exists_distinct_cycle_lengths_of_uniform_detours
    {G : SimpleGraph V} {root a z : V} {i d : ℕ}
    (p : G.Walk a z) (hp : p.IsPath)
    (B : Finset V) (hB : ∀ b ∈ B, b ∈ p.support)
    (hpLevel : ∀ x ∈ p.support, i ≤ G.dist root x)
    (q : ∀ b : ↑B, G.Walk a b.1)
    (hqPath : ∀ b, (q b).IsPath)
    (hqLength : ∀ b, (q b).length = d)
    (hd : 1 < d)
    (hqBelow : ∀ b x, x ∈ (q b).support → x ≠ a → x ≠ b.1 →
      G.dist root x < i) :
    ∃ L : Finset ℕ, L.card = B.card ∧
      ∀ l ∈ L, ∃ v : V, ∃ c : G.Walk v v,
        c.IsCycle ∧ c.length = l := by
  let f : ↑B → ℕ := fun b ↦ prefixLength p B hB b + d
  let L : Finset ℕ := B.attach.image f
  have hf : Function.Injective f := by
    intro b c hbc
    apply prefixLength_injective p B hB
    dsimp only [f] at hbc
    omega
  refine ⟨L, ?_, ?_⟩
  · simp [L, Finset.card_image_of_injective _ hf]
  · intro l hl
    rw [Finset.mem_image] at hl
    obtain ⟨b, hb, rfl⟩ := hl
    let pb : G.Walk a b.1 := p.takeUntil b.1 (hB b.1 b.2)
    have hpbPath : pb.IsPath := hp.takeUntil (hB b.1 b.2)
    have hdisj : pb.support.tail.Disjoint (q b).reverse.support.tail := by
      rw [List.disjoint_left]
      intro x hxpb hxq
      have hxpbSupport : x ∈ p.support :=
        p.support_takeUntil_subset_support (hB b.1 b.2) (List.mem_of_mem_tail hxpb)
      have hxa : x ≠ a := ne_start_of_mem_tail hpbPath hxpb
      have hxb : x ≠ b.1 := by
        have hqrevPath : (q b).reverse.IsPath := (hqPath b).reverse
        exact ne_start_of_mem_tail hqrevPath hxq
      have hxqSupport : x ∈ (q b).support := by
        simpa [SimpleGraph.Walk.support_reverse] using List.mem_of_mem_tail hxq
      exact (Nat.not_lt_of_ge (hpLevel x hxpbSupport))
        (hqBelow b x hxqSupport hxa hxb)
    have hcycle : (pb.append (q b).reverse).IsCycle := by
      apply hpbPath.isCycle_append (hqPath b).reverse hdisj
      right
      simpa [SimpleGraph.Walk.length_reverse, hqLength b] using hd
    refine ⟨a, pb.append (q b).reverse, hcycle, ?_⟩
    simp [f, prefixLength, pb, SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.length_reverse, hqLength b]

end

end Erdos752
