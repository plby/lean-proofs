import Mathlib

/-!
# Erdős Problem 899

Ruzsa's translate-layer proof that an infinite set of natural numbers of
asymptotic density zero has an unbounded positive-difference/count ratio.

The mathematical proof and a detailed formalization guide are in `tex/899.tex`.
-/

open Filter Set
open scoped Pointwise Topology

namespace Erdos899

syntax (name := answerSyntax899) "answer(" term ")" : term
macro_rules
  | `(answer($t)) => `($t)

/-! ## Finite-window counting and increasing enumerations -/

/-- The finite window consisting of the elements of `S` in `[1, N]`. -/
noncomputable def window (S : Set ℕ) (N : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.Icc 1 N).filter (fun n ↦ n ∈ S)

/-- The number of elements of `S` in the natural-number interval `[1, N]`. -/
noncomputable def countIn (S : Set ℕ) (N : ℕ) : ℕ :=
  (window S N).card

@[simp] lemma mem_window {S : Set ℕ} {N x : ℕ} :
    x ∈ window S N ↔ 1 ≤ x ∧ x ≤ N ∧ x ∈ S := by
  classical
  simp [window, and_assoc]

theorem erdos_899 : answer(True) ↔ ∀ (A : Set ℕ), A.Infinite →
    Tendsto (fun N => (A ∩ Icc 1 N |>.ncard : ℝ) / N) atTop (𝓝 0) →
    atTop.limsup (fun N => ((A - A : Set ℕ) ∩ Icc 1 N |>.ncard : EReal) /
      (A ∩ Icc 1 N).ncard) = ⊤ := by
  sorry

