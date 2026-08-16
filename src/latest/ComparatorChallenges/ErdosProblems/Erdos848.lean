/-
leanprover/lean4:v4.33.0  mathlib v4.33.0

Erdős Problem #848 — Lean 4 Formalization (Asymptotic Result)

Contributors:
- Raymond Jung (@the-obstacle-is-the-way)
- Claude Opus 4.5, GPT-5.2 Pro/xHigh, Gemini 3.0, Aristotle

Ported and adapted for this repository by OpenAI Codex.
-/

/-
Erdős Problem #848 — Self-Contained Formalization

The comparator target is Sawhney's asymptotic theorem (2025), NOT the full
Erdős conjecture.

Original Problem 848 (STILL OPEN):
  Is max|A| ≤ |A₇(N)| for ALL N?

Asymptotic statement:
  ∃ N₀, ∀ N ≥ N₀, max|A| ≤ |A₇(N)|  (asymptotic result)

Citation: Sawhney (2025)
-/

-- ============================================================================
-- IMPORTS (Mathlib only - no local imports)
-- ============================================================================

import Mathlib

open scoped BigOperators
open scoped Finset
open scoped Nat.Prime


namespace Erdos848

-- ============================================================================
-- SECTION 1: CORE DEFINITIONS
-- ============================================================================

/-- Problem metadata -/
structure ErdosProblem where
  id : Nat
  title : String
  status : String
  deriving Repr

def problem : ErdosProblem := {
  id := 848
  title := "Erdős-Sárközy Squarefree Products"
  status := "asymptotically resolved"
}

/-- A set A has the non-squarefree product property if ab+1 is not squarefree
    for all a, b in A. -/
def NonSquarefreeProductProp (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ¬ Squarefree (a * b + 1)

/-! ### Indexing Convention

We use `Finset.range N` which gives {0, 1, ..., N-1} rather than the paper's {1, ..., N}.
This is the standard Mathlib convention and is mathematically equivalent because:
- 0 cannot satisfy `NonSquarefreeProductProp` (since 0·0+1 = 1 is squarefree)
- The asymptotic bounds for "sufficiently large N" are unaffected
-/

/-- The candidate extremal set: {n ∈ {0,…,N-1} : n ≡ 7 (mod 25)} -/
def A₇ (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun n => n % 25 = 7)

/-- Alternative candidate: {n ∈ {0,…,N-1} : n ≡ 18 (mod 25)} -/
def A₁₈ (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun n => n % 25 = 18)

/-- The diagonal filter: n is a candidate if n² + 1 is not squarefree. -/
def DiagonalCandidates (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun n => ¬ Squarefree (n * n + 1))

def Erdos848For (N : ℕ) : Prop :=
  ∀ A : Finset ℕ, A ⊆ Finset.range N → NonSquarefreeProductProp A →
    A.card ≤ (A₇ N).card

/-- Decidability instance for NonSquarefreeProductProp -/
instance instDecidableNonSquarefreeProductProp (A : Finset ℕ) :
    Decidable (NonSquarefreeProductProp A) := by
  unfold NonSquarefreeProductProp
  infer_instance

theorem erdos_848.variants.asymptotic : ∀ᶠ N in Filter.atTop, Erdos848For N := by
  sorry
