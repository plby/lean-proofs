/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 110.
https://www.erdosproblems.com/forum/thread/110

Informal authors:
- Chris Lambie-Hanson

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos110.md
-/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos110.FiniteEstimate

/-!
# Erdős Problem 110

There is no uniform eventual bound on the order of finite subgraphs of
prescribed chromatic number in graphs of chromatic number `ℵ₁`.

The mathematical construction and a lemma-by-lemma Leanization plan are in
`tex/110.tex`.
-/

open Filter Set

namespace Erdos110

noncomputable section

universe u

/-- Exact chromatic number `ℵ₁`: an `ω₁`-coloring exists, but a countable
coloring does not. -/
def IsAlephOneChromatic {V : Type u} (G : SimpleGraph V) : Prop :=
  Nonempty (G.Coloring (Set.Iio (Ordinal.omega.{0} 1))) ∧
    IsEmpty (G.Coloring ℕ)

/-- A graph together with its vertex type.  The universe is fixed only so
that the collection of graphs quantified over below is itself a Lean type. -/
structure BundledGraph where
  Vertex : Type 1
  graph : SimpleGraph Vertex

/-- `F` is the uniform bound proposed in Problem 110.  The subgraph is an
arbitrary (not necessarily induced) Mathlib subgraph, and finiteness is stated
explicitly because `Set.ncard` is zero on infinite sets. -/
def HasUniformBound (F : ℕ → ℕ) : Prop :=
  ∀ X : BundledGraph,
    IsAlephOneChromatic X.graph →
      ∀ᶠ n : ℕ in atTop,
        ∃ H : X.graph.Subgraph,
          H.verts.Finite ∧ H.verts.ncard ≤ F n ∧
            H.coe.chromaticNumber = n

/-- A graph witnessing failure of `F` at arbitrarily large chromatic
numbers.  This is exactly the pointwise negation needed for the eventual
quantifier in `HasUniformBound`. -/
def IsCounterexampleFor (F : ℕ → ℕ) (X : BundledGraph) : Prop :=
  IsAlephOneChromatic X.graph ∧
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∀ H : X.graph.Subgraph,
        H.verts.Finite → H.verts.ncard ≤ F n →
          H.coe.chromaticNumber ≠ n

/-- The quantitative conclusion of Lambie-Hanson's theorem, in the form
needed here.  Every finite subgraph on fewer than `f n` vertices has
chromatic number strictly below `n`, simultaneously for all `n ≥ 3`. -/
def HasSlowFiniteGrowth (f : ℕ → ℕ) (X : BundledGraph) : Prop :=
  IsAlephOneChromatic X.graph ∧
    ∀ n : ℕ, 3 ≤ n → ∀ H : X.graph.Subgraph,
      H.verts.Finite → H.verts.ncard < f n →
        H.coe.chromaticNumber < n

/-- An arbitrarily-late pointwise counterexample defeats an eventual uniform
bound. -/
lemma not_hasUniformBound_of_counterexample {F : ℕ → ℕ} {X : BundledGraph}
    (hX : IsCounterexampleFor F X) : ¬HasUniformBound F := by
  intro hF
  obtain ⟨N, hN⟩ := (eventually_atTop.1 (hF X hX.1))
  obtain ⟨n, hnN, hn⟩ := hX.2 N
  obtain ⟨H, hHfin, hHcard, hHchi⟩ := hN n hnN
  exact hn H hHfin hHcard hHchi

/-- The specialized form of Lambie-Hanson's ZFC construction needed for
Problem 110. -/
def LambieHansonConclusion : Prop :=
  ∀ F : ℕ → ℕ, ∃ X : BundledGraph, IsCounterexampleFor F X

/-- The full quantitative existence theorem proved by Lambie-Hanson. -/
def LambieHansonTheorem : Prop :=
  ∀ f : ℕ → ℕ, ∃ X : BundledGraph, HasSlowFiniteGrowth f X

/-- The published strict-cardinality formulation implies the pointwise
counterexamples required to negate Problem 110. -/
lemma lambieHansonConclusion_of_theorem
    (hLH : LambieHansonTheorem) : LambieHansonConclusion := by
  intro F
  obtain ⟨X, hX⟩ := hLH (fun n ↦ F n + 1)
  refine ⟨X, hX.1, ?_⟩
  intro N
  let n := max N 3
  refine ⟨n, le_max_left _ _, ?_⟩
  intro H hHfin hHcard hHeq
  have hn3 : 3 ≤ n := le_max_right _ _
  have hHlt : H.verts.ncard < F n + 1 := Nat.lt_succ_of_le hHcard
  have hchi := hX.2 n hn3 H hHfin hHlt
  exact hchi.ne hHeq

/-- Lambie-Hanson's construction immediately gives the exact logical
negation of the proposed uniform bound. -/
lemma not_exists_uniformBound_of_lambieHanson
    (hLH : LambieHansonConclusion) : ¬∃ F : ℕ → ℕ, HasUniformBound F := by
  rintro ⟨F, hF⟩
  obtain ⟨X, hX⟩ := hLH F
  exact not_hasUniformBound_of_counterexample hX hF

/-- The ZFC Lambie--Hanson construction, specialized to the exponentially
spaced chromatic targets needed to refute a proposed bound `F`. -/
theorem lambieHansonConclusion : LambieHansonConclusion := by
  intro F
  let target : ℕ → ℕ := fun k ↦ 2 ^ (k + 1) + 1
  let q : ℕ → ℕ := fun k ↦ F (target k)
  obtain ⟨C, hC⟩ := Height.exists_clubGuessing
  let X : BundledGraph :=
    ⟨Construction.Vertex, Construction.graph C q⟩
  refine ⟨X, ?_, ?_⟩
  · exact ⟨Construction.has_omegaOne_coloring C q,
      Construction.no_nat_coloring C q hC⟩
  · intro N
    let k := N
    have hNk : N ≤ target k := by
      have hpow : N < 2 ^ N := N.lt_two_pow_self
      have hmono : 2 ^ N ≤ 2 ^ (N + 1) :=
        Nat.pow_le_pow_right (by omega) (Nat.le_succ N)
      dsimp [target, k]
      omega
    refine ⟨target k, hNk, ?_⟩
    intro H hHfin hHcard
    have hsmall : H.coe.chromaticNumber ≤ (2 ^ (k + 1) : ℕ) := by
      apply FiniteEstimate.chromaticNumber_le C q H k hHfin
      simpa [q, target] using hHcard
    intro heq
    rw [heq] at hsmall
    have hsmallNat : target k ≤ 2 ^ (k + 1) := by
      exact_mod_cast hsmall
    dsimp [target] at hsmallNat
    omega

/-- Resolution of Erdős Problem 110: the proposed eventual uniform bound
does not exist. -/
theorem not_erdos_110 :
    ¬ ∃ F : ℕ → ℕ, HasUniformBound F := by
  exact not_exists_uniformBound_of_lambieHanson lambieHansonConclusion

end

end Erdos110

alias _root_.Erdos110.erdos_110 := _root_.Erdos110.not_erdos_110
